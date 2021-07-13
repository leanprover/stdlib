/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather
-/
import algebra.free_monoid
import algebra.opposites
import control.traversable.instances
import control.traversable.lemmas
import category_theory.category
import category_theory.endomorphism
import category_theory.types
import category_theory.category.Kleisli

/-!

# List folds generalized to `traversable`

Informally, we can think of `foldl` as a special case of `traverse` where we do not care about the
reconstructed data structure and, in a state monad, we care about the final state.

The obvious way to define `foldl` would be to use the state monad but it
is nicer to reason about a more abstract interface with `fold_map` as a
primitive and `fold_map_hom` as a defining property.

```
def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω := ...

lemma fold_map_hom (α β)
  [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
...
```

`fold_map` uses a monoid ω to accumulate a value for every element of
a data structure and `fold_map_hom` uses a monoid homomorphism to
substitute the monoid used by `fold_map`. The two are sufficient to
define `foldl`, `foldr` and `to_list`. `to_list` permits the
formulation of specifications in terms of operations on lists.

Each fold function can be defined using a specialized
monoid. `to_list` uses a free monoid represented as a list with
concatenation while `foldl` uses endofunctions together with function
composition.

The definition through monoids uses `traverse` together with the
applicative functor `const m` (where `m` is the monoid). As an
implementation, `const` guarantees that no resource is spent on
reconstructing the structure during traversal.

A special class could be defined for `foldable`, similarly to Haskell,
but the author cannot think of instances of `foldable` that are not also
`traversable`.
-/

universes u v

open ulift category_theory opposite

namespace monoid
variables {m : Type u → Type u} [monad m]
variables {α β : Type u}
/--
For a list, foldl f x [y₀,y₁] reduces as follows:

```
calc  foldl f x [y₀,y₁]
    = foldl f (f x y₀) [y₁]      : rfl
... = foldl f (f (f x y₀) y₁) [] : rfl
... = f (f x y₀) y₁              : rfl
```
with
```
f : α → β → α
x : α
[y₀,y₁] : list β
```

We can view the above as a composition of functions:
```
... = f (f x y₀) y₁              : rfl
... = flip f y₁ (flip f y₀ x)    : rfl
... = (flip f y₁ ∘ flip f y₀) x  : rfl
```

We can use traverse and const to construct this composition:
```
calc   const.run (traverse (λ y, const.mk' (flip f y)) [y₀,y₁]) x
     = const.run ((::) <$> const.mk' (flip f y₀) <*> traverse (λ y, const.mk' (flip f y)) [y₁]) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> traverse (λ y, const.mk' (flip f y)) [] )) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
         ((::) <$> const.mk' (flip f y₀)) ) x
...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
...  = f (f x y₀) y₁
```

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `foldl`.
-/
@[reducible] def foldl (α : Type u) : Type u := (End α)ᵒᵖ
def foldl.mk (f : α → α) : foldl α := op f
def foldl.get (x : foldl α) : α → α := unop x
def foldl.of_free_monoid (f : β → α → β) (xs : free_monoid α) : monoid.foldl β :=
op $ flip (list.foldl f) xs

@[reducible] def foldr (α : Type u) : Type u := End α
def foldr.mk (f : α → α) : foldr α := f
def foldr.get (x : foldr α) : α → α := x
def foldr.of_free_monoid (f : α → β → β) (xs : free_monoid α) : monoid.foldr β :=
flip (list.foldr f) xs

@[reducible] def mfoldl (m : Type u → Type u) [monad m] (α : Type u) : Type u :=
opposite $ End $ Kleisli.mk m α
def mfoldl.mk (f : α → m α) : mfoldl m α := op f
def mfoldl.get (x : mfoldl m α) : α → m α := unop x
def mfoldl.of_free_monoid (f : β → α → m β) (xs : free_monoid α) : monoid.mfoldl m β :=
op $ flip (list.mfoldl f) xs

@[reducible] def mfoldr (m : Type u → Type u) [monad m] (α : Type u) : Type u :=
End $ Kleisli.mk m α
def mfoldr.mk (f : α → m α) : mfoldr m α := f
def mfoldr.get (x : mfoldr m α) : α → m α := x
def mfoldr.of_free_monoid (f : α → β → m β) (xs : free_monoid α) : monoid.mfoldr m β :=
flip (list.mfoldr f) xs

end monoid

namespace traversable
open monoid functor

section defs
variables {α β : Type u} {t : Type u → Type u} [traversable t]

def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω :=
traverse (const.mk' ∘ f)

def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
(fold_map (foldl.mk ∘ flip f) xs).get x

def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
(fold_map (foldr.mk ∘ f) xs).get x

/--
Conceptually, `to_list` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma to_list_spec (x : t α) : to_list x = fold_map free_monoid.mk x`.

The definition of `to_list` is based on `foldl` and `list.cons` for
speed. It is faster than using `fold_map free_monoid.mk` because, by
using `foldl` and `list.cons`, each insertion is done in constant
time. As a consequence, `to_list` performs in linear.

On the other hand, `fold_map free_monoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time. -/
def to_list : t α → list α :=
list.reverse ∘ foldl (flip list.cons) []

def length (xs : t α) : ℕ :=
down $ foldl (λ l _, up $ l.down + 1) (up 0) xs

variables {m : Type u → Type u} [monad m]

def mfoldl (f : α → β → m α) (x : α) (xs : t β) : m α :=
(fold_map (mfoldl.mk ∘ flip f) xs).get x

def mfoldr (f : α → β → m β) (x : β) (xs : t α) : m β :=
(fold_map (mfoldr.mk ∘ f) xs).get x

end defs

section applicative_transformation
variables {α β γ : Type u}

open function (hiding const) is_monoid_hom

def map_fold [monoid α] [monoid β] {f : α → β} (hf : is_monoid_hom f) :
  applicative_transformation (const α) (const β) :=
{ app := λ x, f,
  preserves_seq'  := by { intros, simp only [map_mul hf, (<*>)], },
  preserves_pure' := by { intros, simp only [map_one hf, pure] } }

def free.mk : α → free_monoid α := list.ret

def free.map (f : α → β) : free_monoid α → free_monoid β := list.map f

lemma free.map_eq_map (f : α → β) (xs : list α) :
  f <$> xs = free.map f xs := rfl

lemma free.map.is_monoid_hom (f : α → β) : is_monoid_hom (free.map f) :=
{ map_mul := λ x y,
    by simp only [free.map, free_monoid.mul_def, list.map_append, free_add_monoid.add_def],
  map_one := by simp only [free.map, free_monoid.one_def, list.map, free_add_monoid.zero_def] }

lemma fold_foldl (f : β → α → β) :
  is_monoid_hom (foldl.of_free_monoid f) :=
{ map_one := rfl,
  map_mul := by intros; simp only [free_monoid.mul_def, foldl.of_free_monoid, flip, unop_op,
    list.foldl_append, op_inj_iff]; refl }

lemma foldl.unop_of_free_monoid  (f : β → α → β) (xs : free_monoid α) (a : β) :
  unop (foldl.of_free_monoid f xs) a = list.foldl f a xs := rfl

lemma fold_foldr (f : α → β → β) :
  is_monoid_hom (foldr.of_free_monoid f) :=
{ map_one := rfl,
  map_mul :=
    begin
      intros,
      simp only [free_monoid.mul_def, foldr.of_free_monoid, list.foldr_append, flip],
      refl
    end }

variables (m : Type u → Type u) [monad m] [is_lawful_monad m]

@[simp]
lemma mfoldl.unop_of_free_monoid  (f : β → α → m β) (xs : free_monoid α) (a : β) :
  unop (mfoldl.of_free_monoid f xs) a = list.mfoldl f a xs := rfl

lemma fold_mfoldl (f : β → α → m β) :
  is_monoid_hom (mfoldl.of_free_monoid f) :=
{ map_one := rfl,
  map_mul := by intros; apply unop_injective; ext; apply list.mfoldl_append }

lemma fold_mfoldr (f : α → β → m β) :
  is_monoid_hom (mfoldr.of_free_monoid f) :=
{ map_one := rfl,
  map_mul := by intros; ext; apply list.mfoldr_append }

variables {t : Type u → Type u} [traversable t] [is_lawful_traversable t]
open is_lawful_traversable

lemma fold_map_hom
  [monoid α] [monoid β] {f : α → β} (hf : is_monoid_hom f)
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
calc  f (fold_map g x)
    = f (traverse (const.mk' ∘ g) x)  : rfl
... = (map_fold hf).app _ (traverse (const.mk' ∘ g) x) : rfl
... = traverse ((map_fold hf).app _ ∘ (const.mk' ∘ g)) x : naturality (map_fold hf) _ _
... = fold_map (f ∘ g) x : rfl

lemma fold_map_hom_free
  [monoid β] {f : free_monoid α → β} (hf : is_monoid_hom f) (x : t α) :
  f (fold_map free.mk x) = fold_map (f ∘ free.mk) x :=
fold_map_hom hf _ x

variable {m}

lemma fold_mfoldl_cons (f : α → β → m α) (x : β) (y : α) :
  list.mfoldl f y (free.mk x) = f y x :=
by simp only [free.mk, list.ret, list.mfoldl, bind_pure]

lemma fold_mfoldr_cons (f : β → α → m α) (x : β) (y : α) :
  list.mfoldr f y (free.mk x) = f x y :=
by simp only [free.mk, list.ret, list.mfoldr, pure_bind]

end applicative_transformation

section equalities
open is_lawful_traversable list (cons)
variables {α β γ : Type u}
variables {t : Type u → Type u} [traversable t] [is_lawful_traversable t]

@[simp]
lemma foldl.of_free_monoid_comp_free_mk (f : α → β → α) :
  foldl.of_free_monoid f ∘ free.mk = foldl.mk ∘ flip f := rfl

@[simp]
lemma foldr.of_free_monoid_comp_free_mk (f : β → α → α) :
  foldr.of_free_monoid f ∘ free.mk = foldr.mk ∘ f := rfl

@[simp]
lemma mfoldl.of_free_monoid_comp_free_mk {m} [monad m] [is_lawful_monad m] (f : α → β → m α) :
  mfoldl.of_free_monoid f ∘ free.mk = mfoldl.mk ∘ flip f :=
by ext; simp only [(∘), mfoldl.of_free_monoid, mfoldl.mk, flip, fold_mfoldl_cons]; refl

@[simp]
lemma mfoldr.of_free_monoid_comp_free_mk {m} [monad m] [is_lawful_monad m] (f : β → α → m α) :
  mfoldr.of_free_monoid f ∘ free.mk = mfoldr.mk ∘ f :=
by { ext, simp only [(∘), mfoldr.of_free_monoid, mfoldr.mk, flip, fold_mfoldr_cons] }

lemma to_list_spec (xs : t α) :
  to_list xs = (fold_map free.mk xs : free_monoid _) :=
eq.symm $
calc  fold_map free.mk xs
    = (fold_map free.mk xs).reverse.reverse : by simp only [list.reverse_reverse]
... = (list.foldr cons [] (fold_map free.mk xs).reverse).reverse
                 : by simp only [list.foldr_eta]
... = (unop (foldl.of_free_monoid (flip cons) (fold_map free.mk xs)) []).reverse
                 : by simp only [flip,list.foldr_reverse,foldl.of_free_monoid, unop_op]
... = to_list xs : begin
                     have : is_monoid_hom (foldl.of_free_monoid (flip $ @cons α)),
                      { apply fold_foldl },
                     rw fold_map_hom_free this,
                     simp only [to_list, foldl, list.reverse_inj, foldl.get,
                       foldl.of_free_monoid_comp_free_mk],
                     all_goals { apply_instance }
                   end

lemma fold_map_map [monoid γ]  (f : α → β) (g : β → γ) (xs : t α) :
  fold_map g (f <$> xs) = fold_map (g ∘ f) xs :=
by simp only [fold_map,traverse_map]

lemma foldl_to_list (f : α → β → α) (xs : t β) (x : α) :
  foldl f x xs = list.foldl f x (to_list xs) :=
begin
  rw ← foldl.unop_of_free_monoid,
  simp only [foldl, to_list_spec, fold_map_hom_free (fold_foldl f),
    foldl.of_free_monoid_comp_free_mk, foldl.get]
end

lemma foldr_to_list (f : α → β → β) (xs : t α) (x : β) :
  foldr f x xs = list.foldr f x (to_list xs) :=
begin
  change _ = foldr.of_free_monoid _ _ _,
  simp only [foldr, to_list_spec, fold_map_hom_free (fold_foldr f),
    foldr.of_free_monoid_comp_free_mk, foldr.get]
end

lemma to_list_map (f : α → β) (xs : t α) :
  to_list (f <$> xs) = f <$> to_list xs := by
{ simp only [to_list_spec,free.map_eq_map,fold_map_hom (free.map.is_monoid_hom f), fold_map_map];
  refl }

@[simp] theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
  foldl f a (g <$> l) = foldl (λ x y, f x (g y)) a l :=
by simp only [foldl, fold_map_map, (∘), flip]

@[simp] theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) :
  foldr f a (g <$> l) = foldr (f ∘ g) a l :=
by simp only [foldr, fold_map_map, (∘), flip]

@[simp] theorem to_list_eq_self {xs : list α} : to_list xs = xs :=
begin
  simp only [to_list_spec, fold_map, traverse],
  induction xs,
  case list.nil { refl },
  case list.cons : _ _ ih { unfold list.traverse list.ret, rw ih, refl }
end

theorem length_to_list {xs : t α} : length xs = list.length (to_list xs) :=
begin
  unfold length,
  rw foldl_to_list,
  generalize : to_list xs = ys,
  let f := λ (n : ℕ) (a : α), n + 1,
  transitivity list.foldl f 0 ys,
  { generalize : 0 = n,
    induction ys with _ _ ih generalizing n,
    { simp only [list.foldl_nil] },
    { simp only [list.foldl, ih (n+1)] } },
  { induction ys with _ tl ih,
    { simp only [list.length, list.foldl_nil] },
    { simp only [list.foldl, list.length],
      rw [← ih],
      exact tl.foldl_hom (λx, x+1) f f 0 (λ n x, rfl) } }
end

variables {m : Type u → Type u} [monad m] [is_lawful_monad m]

section
local attribute [semireducible] opposite
lemma mfoldl_to_list {f : α → β → m α} {x : α} {xs : t β} :
  mfoldl f x xs = list.mfoldl f x (to_list xs) :=
begin
  change _ = unop (mfoldl.of_free_monoid f (to_list xs)) x,
  simp only [mfoldl, to_list_spec, fold_map_hom_free (fold_mfoldl (λ (β : Type u), m β) f),
    mfoldl.of_free_monoid_comp_free_mk, mfoldl.get]
end
end

lemma mfoldr_to_list (f : α → β → m β) (x : β) (xs : t α) :
  mfoldr f x xs = list.mfoldr f x (to_list xs) :=
begin
  change _ = mfoldr.of_free_monoid f (to_list xs) x,
  simp only [mfoldr, to_list_spec, fold_map_hom_free (fold_mfoldr (λ (β : Type u), m β) f),
    mfoldr.of_free_monoid_comp_free_mk, mfoldr.get]
end

@[simp] theorem mfoldl_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
  mfoldl f a (g <$> l) = mfoldl (λ x y, f x (g y)) a l :=
by simp only [mfoldl, fold_map_map, (∘), flip]

@[simp] theorem mfoldr_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) :
  mfoldr f a (g <$> l) = mfoldr (f ∘ g) a l :=
by simp only [mfoldr, fold_map_map, (∘), flip]

end equalities

end traversable
