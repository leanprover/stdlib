/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov
-/
import algebra.star.basic

/-!
# Free monoid over a given alphabet

## Main definitions

* `free_monoid α`: free monoid over alphabet `α`; defined as a synonym for `list α`
  with multiplication given by `(++)`.
* `free_monoid.of`: embedding `α → free_monoid α` sending each element `x` to `[x]`;
* `free_monoid.lift`: natural equivalence between `α → M` and `free_monoid α →* M`
* `free_monoid.map`: embedding of `α → β` into `free_monoid α →* free_monoid β` given by `list.map`.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [monoid M] {N : Type*} [monoid N]

/-- Free monoid over a given alphabet. -/
@[to_additive "Free nonabelian additive monoid over a given alphabet"]
def free_monoid (α) := list α

namespace free_monoid

@[to_additive]
instance : monoid (free_monoid α) :=
{ one := [],
  mul := λ x y, (x ++ y : list α),
  mul_one := by intros; apply list.append_nil,
  one_mul := by intros; refl,
  mul_assoc := by intros; apply list.append_assoc }

@[to_additive]
instance : inhabited (free_monoid α) := ⟨1⟩

@[to_additive]
lemma one_def : (1 : free_monoid α) = [] := rfl

@[to_additive]
lemma mul_def (xs ys : list α) : (xs * ys : free_monoid α) = (xs ++ ys : list α) :=
rfl

/-- Embeds an element of `α` into `free_monoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `free_add_monoid α` as a singleton list." ]
def of (x : α) : free_monoid α := [x]

@[to_additive]
lemma of_def (x : α) : of x = [x] := rfl

lemma of_injective : function.injective (@of α) :=
λ a b, list.head_eq_of_cons_eq

/-- Recursor for `free_monoid` using `1` and `of x * xs` instead of `[]` and `x :: xs`. -/
@[to_additive "Recursor for `free_add_monoid` using `0` and `of x + xs` instead of `[]` and `x :: xs`."]
def rec_on {C : free_monoid α → Sort*} (xs : free_monoid α) (h0 : C 1)
  (ih : Π x xs, C xs → C (of x * xs)) : C xs := list.rec_on xs h0 ih

attribute [elab_as_eliminator] rec_on free_add_monoid.rec_on

@[to_additive]
lemma hom_eq ⦃f g : free_monoid α →* M⦄ (h : ∀ x, f (of x) = g (of x)) :
  f = g :=
monoid_hom.ext $ λ l, rec_on l (f.map_one.trans g.map_one.symm) $
  λ x xs hxs, by simp only [h, hxs, monoid_hom.map_mul]

attribute [ext] hom_eq free_add_monoid.hom_eq

/-- Equivalence between maps `α → M` and monoid homomorphisms `free_monoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`free_add_monoid α →+ A`."]
def lift : (α → M) ≃ (free_monoid α →* M) :=
{ to_fun := λ f, ⟨λ l, (l.map f).prod, rfl,
    λ l₁ l₂, by simp only [mul_def, list.map_append, list.prod_append]⟩,
  inv_fun := λ f x, f (of x),
  left_inv := λ f, funext $ λ x, one_mul (f x),
  right_inv := λ f, hom_eq $ λ x, one_mul (f (of x)) }

@[simp, to_additive]
lemma lift_symm_apply (f : free_monoid α →* M) : lift.symm f = f ∘ of := rfl

@[to_additive]
lemma lift_apply (f : α → M) (l : free_monoid α) : lift f l = (l.map f).prod := rfl

@[to_additive]
lemma lift_comp_of (f : α → M) : (lift f) ∘ of = f := lift.symm_apply_apply f

@[simp, to_additive]
lemma lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x :=
congr_fun (lift_comp_of f) x

@[simp, to_additive]
lemma lift_restrict (f : free_monoid α →* M) : lift (f ∘ of) = f :=
lift.apply_symm_apply f

lemma comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) :=
by { ext, simp }

lemma hom_map_lift (g : M →* N) (f : α → M) (x : free_monoid α) : g (lift f x) = lift (g ∘ f) x :=
monoid_hom.ext_iff.1 (comp_lift g f) x

/-- The unique monoid homomorphism `free_monoid α →* free_monoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `free_add_monoid α →+ free_add_monoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : free_monoid α →* free_monoid β :=
{ to_fun := list.map f,
  map_one' := rfl,
  map_mul' := λ l₁ l₂, list.map_append _ _ _ }

@[simp, to_additive] lemma map_of (f : α → β) (x : α) : map f (of x) = of (f x) := rfl

@[to_additive]
lemma lift_of_comp_eq_map (f : α → β) :
  lift (λ x, of (f x)) = map f :=
hom_eq $ λ x, rfl

@[to_additive]
lemma map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) :=
hom_eq $ λ x, rfl

instance : star_monoid (free_monoid α) :=
{ star := list.reverse,
  star_involutive := list.reverse_reverse,
  star_mul := list.reverse_append, }

@[simp]
lemma star_of (x : α) : star (of x) = of x := rfl

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp]
lemma star_one : star (1 : free_monoid α) = 1 := rfl

end free_monoid
