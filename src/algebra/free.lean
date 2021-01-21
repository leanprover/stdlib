/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.equiv.basic
import control.applicative

/-!
# Free constructions

## Main definitions

* `free_magma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `magma.free_semigroup α`: free semigroup over magma `α`.
* `free_semigroup α`: free semigroup over alphabet `α`, defined as a synonym for `α × list α`
  (i.e. nonempty lists), with traversable instance and decidable equality.
* `free_semigroup_free_magma α`: isomorphism between `magma.free_semigroup (free_magma α)` and
  `free_semigroup α`.
-/

universes u v l

/-- Free magma over a given alphabet. -/
@[derive decidable_eq]
inductive free_magma (α : Type u) : Type u
| of : α → free_magma
| mul : free_magma → free_magma → free_magma

/-- Free nonabelian additive magma over a given alphabet. -/
@[derive decidable_eq]
inductive free_add_magma (α : Type u) : Type u
| of : α → free_add_magma
| add : free_add_magma → free_add_magma → free_add_magma

attribute [to_additive] free_magma

namespace free_magma

variables {α : Type u}

@[to_additive]
instance [inhabited α] : inhabited (free_magma α) := ⟨of (default _)⟩

@[to_additive]
instance : has_mul (free_magma α) := ⟨free_magma.mul⟩

attribute [pattern] has_mul.mul

@[simp, to_additive]
theorem mul_eq (x y : free_magma α) : mul x y = x * y := rfl

/-- Recursor for `free_magma` using `x * y` instead of `free_magma.mul x y`. -/
@[to_additive "Recursor for `free_add_magma` using `x + y` instead of `free_add_magma.add x y`."]
def rec_on' {C : free_magma α → Sort l} (x)
  (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
  C x :=
free_magma.rec_on x ih1 ih2
attribute [elab_as_eliminator] rec_on' free_add_magma.rec_on'

end free_magma

/-- Lifts a function `α → β` to a magma homomorphism `free_magma α → β` given a magma `β`. -/
def free_magma.lift {α : Type u} {β : Type v} [has_mul β] (f : α → β) : free_magma α → β
| (free_magma.of x) := f x
| (x * y)           := x.lift * y.lift

/-- Lifts a function `α → β` to an additive magma homomorphism `free_add_magma α → β` given
an additive magma `β`. -/
def free_add_magma.lift {α : Type u} {β : Type v} [has_add β] (f : α → β) : free_add_magma α → β
| (free_add_magma.of x) := f x
| (x + y)               := x.lift + y.lift

attribute [to_additive free_add_magma.lift] free_magma.lift

namespace free_magma

variables {α : Type u} {β : Type v} [has_mul β] (f : α → β)

@[simp, to_additive] lemma lift_of (x) : lift f (of x) = f x := rfl
@[simp, to_additive] lemma lift_mul (x y) : lift f (x * y) = lift f x * lift f y := rfl

@[to_additive]
theorem lift_unique (f : free_magma α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  f = lift (f ∘ of) :=
funext $ λ x, free_magma.rec_on x (λ x, rfl) $ λ x y ih1 ih2,
(hf x y).trans $ congr (congr_arg _ ih1) ih2

end free_magma

/-- The unique magma homomorphism `free_magma α → free_magma β` that sends
each `of x` to `of (f x)`. -/
def free_magma.map {α : Type u} {β : Type v} (f : α → β) : free_magma α → free_magma β
| (free_magma.of x) := free_magma.of (f x)
| (x * y)           := x.map * y.map

/-- The unique additive magma homomorphism `free_add_magma α → free_add_magma β` that sends
each `of x` to `of (f x)`. -/
def free_add_magma.map {α : Type u} {β : Type v} (f : α → β) : free_add_magma α → free_add_magma β
| (free_add_magma.of x) := free_add_magma.of (f x)
| (x + y)               := x.map + y.map

attribute [to_additive free_add_magma.map] free_magma.map

namespace free_magma

variables {α : Type u}

section map

variables {β : Type v} (f : α → β)

@[simp, to_additive] lemma map_of (x) : map f (of x) = of (f x) := rfl
@[simp, to_additive] lemma map_mul (x y) : map f (x * y) = map f x * map f y := rfl

end map

section category

@[to_additive]
instance : monad free_magma :=
{ pure := λ _, of,
  bind := λ _ _ x f, lift f x }

/-- Recursor on `free_magma` using `pure` instead of `of`. -/
@[elab_as_eliminator, to_additive "Recursor on `free_add_magma` using `pure` instead of `of`."]
protected def rec_on'' {C : free_magma α → Sort l} (x)
  (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
  C x :=
free_magma.rec_on' x ih1 ih2

variables {β : Type u}

@[simp, to_additive]
lemma map_pure (f : α → β) (x) : (f <$> pure x : free_magma β) = pure (f x) := rfl

@[simp, to_additive]
lemma map_mul' (f : α → β) (x y : free_magma α) : (f <$> (x * y)) = (f <$> x * f <$> y) := rfl

@[simp, to_additive]
lemma pure_bind (f : α → free_magma β) (x) : (pure x >>= f) = f x := rfl

@[simp, to_additive]
lemma mul_bind (f : α → free_magma β) (x y : free_magma α) :
  (x * y >>= f) = ((x >>= f) * (y >>= f)) := rfl

@[simp, to_additive]
lemma pure_seq {α β : Type u} {f : α → β} {x : free_magma α} : pure f <*> x = f <$> x := rfl

@[simp, to_additive]
lemma mul_seq {α β : Type u} {f g : free_magma (α → β)} {x : free_magma α} :
  (f * g) <*> x = (f <*> x) * (g <*> x) := rfl

@[to_additive]
instance : is_lawful_monad free_magma.{u} :=
{ pure_bind := λ _ _ _ _, rfl,
  bind_assoc := λ α β γ x f g, free_magma.rec_on'' x (λ x, rfl)
    (λ x y ih1 ih2, by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]),
  id_map := λ α x, free_magma.rec_on'' x (λ _, rfl)
    (λ x y ih1 ih2, by rw [map_mul', ih1, ih2]) }

end category

end free_magma

/-- `free_magma` is traversable. -/
protected def free_magma.traverse {m : Type u → Type u} [applicative m] {α β : Type u}
  (F : α → m β) :
  free_magma α → m (free_magma β)
| (free_magma.of x) := free_magma.of <$> F x
| (x * y)           := (*) <$> x.traverse <*> y.traverse

/-- `free_add_magma` is traversable. -/
protected def free_add_magma.traverse {m : Type u → Type u} [applicative m] {α β : Type u}
  (F : α → m β) :
  free_add_magma α → m (free_add_magma β)
| (free_add_magma.of x) := free_add_magma.of <$> F x
| (x + y)               := (+) <$> x.traverse <*> y.traverse

attribute [to_additive free_add_magma.traverse] free_magma.traverse

namespace free_magma

variables {α : Type u}

section category

variables {β : Type u}

@[to_additive]
instance : traversable free_magma := ⟨@free_magma.traverse⟩

variables {m : Type u → Type u} [applicative m] (F : α → m β)

@[simp, to_additive]
lemma traverse_pure (x) : traverse F (pure x : free_magma α) = pure <$> F x := rfl

@[simp, to_additive]
lemma traverse_pure' : traverse F ∘ pure = λ x, (pure <$> F x : m (free_magma β)) := rfl

@[simp, to_additive]
lemma traverse_mul (x y : free_magma α) :
  traverse F (x * y) = (*) <$> traverse F x <*> traverse F y := rfl

@[simp, to_additive]
lemma traverse_mul' :
  function.comp (traverse F) ∘ @has_mul.mul (free_magma α) _ =
    λ x y, (*) <$> traverse F x <*> traverse F y := rfl

@[simp, to_additive]
lemma traverse_eq (x) : free_magma.traverse F x = traverse F x := rfl

@[simp, to_additive]
lemma mul_map_seq (x y : free_magma α) :
  ((*) <$> x <*> y : id (free_magma α)) = (x * y : free_magma α) := rfl

@[to_additive]
instance : is_lawful_traversable free_magma.{u} :=
{ id_traverse := λ α x, free_magma.rec_on'' x (λ x, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, mul_map_seq]),
  comp_traverse := λ F G hf1 hg1 hf2 hg2 α β γ f g x, free_magma.rec_on'' x
    (λ x, by resetI; simp only [traverse_pure, traverse_pure'] with functor_norm)
    (λ x y ih1 ih2, by resetI; rw [traverse_mul, ih1, ih2, traverse_mul];
      simp only [traverse_mul'] with functor_norm),
  naturality := λ F G hf1 hg1 hf2 hg2 η α β f x, free_magma.rec_on'' x
    (λ x, by simp only [traverse_pure] with functor_norm)
    (λ x y ih1 ih2, by simp only [traverse_mul] with functor_norm; rw [ih1, ih2]),
  traverse_eq_map_id := λ α β f x, free_magma.rec_on'' x (λ _, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; refl),
  .. free_magma.is_lawful_monad }

end category

end free_magma

/-- Representation of an element of a free magma. -/
protected def free_magma.repr {α : Type u} [has_repr α] : free_magma α → string
| (free_magma.of x) := repr x
| (x * y)           := "( " ++ x.repr ++ " * " ++ y.repr ++ " )"

/-- Representation of an element of a free additive magma. -/
protected def free_add_magma.repr {α : Type u} [has_repr α] : free_add_magma α → string
| (free_add_magma.of x) := repr x
| (x + y)               := "( " ++ x.repr ++ " + " ++ y.repr ++ " )"

attribute [to_additive free_add_magma.repr] free_magma.repr

@[to_additive]
instance {α : Type u} [has_repr α] : has_repr (free_magma α) := ⟨free_magma.repr⟩

/-- Length of an element of a free magma. -/
def free_magma.length {α : Type u} : free_magma α → ℕ
| (free_magma.of x) := 1
| (x * y)           := x.length + y.length

/-- Length of an element of a free additive magma. -/
def free_add_magma.length {α : Type u} : free_add_magma α → ℕ
| (free_add_magma.of x) := 1
| (x + y)               := x.length + y.length

attribute [to_additive free_add_magma.length] free_magma.length

/-- Associativity relations for a magma. -/
inductive magma.free_semigroup.r (α : Type u) [has_mul α] : α → α → Prop
| intro : ∀ x y z, magma.free_semigroup.r ((x * y) * z) (x * (y * z))
| left : ∀ w x y z, magma.free_semigroup.r (w * ((x * y) * z)) (w * (x * (y * z)))

/-- Associativity relations for an additive magma. -/
inductive add_magma.free_add_semigroup.r (α : Type u) [has_add α] : α → α → Prop
| intro : ∀ x y z, add_magma.free_add_semigroup.r ((x + y) + z) (x + (y + z))
| left : ∀ w x y z, add_magma.free_add_semigroup.r (w + ((x + y) + z)) (w + (x + (y + z)))

attribute [to_additive add_magma.free_add_semigroup.r] magma.free_semigroup.r

namespace magma

/-- Free semigroup over a magma. -/
@[to_additive add_magma.free_add_semigroup "Free additive semigroup over an additive magma."]
def free_semigroup (α : Type u) [has_mul α] : Type u :=
quot $ free_semigroup.r α

namespace free_semigroup

variables {α : Type u} [has_mul α]

/-- Embedding from magma to its free semigroup. -/
@[to_additive "Embedding from additive magma to its free additive semigroup."]
def of : α → free_semigroup α := quot.mk _

@[to_additive]
instance [inhabited α] : inhabited (free_semigroup α) := ⟨of (default _)⟩

@[elab_as_eliminator, to_additive]
protected lemma induction_on {C : free_semigroup α → Prop} (x : free_semigroup α)
  (ih : ∀ x, C (of x)) : C x :=
quot.induction_on x ih

@[to_additive]
theorem of_mul_assoc (x y z : α) : of ((x * y) * z) = of (x * (y * z)) :=
quot.sound $ r.intro x y z

@[to_additive]
theorem of_mul_assoc_left (w x y z : α) : of (w * ((x * y) * z)) = of (w * (x * (y * z))) :=
quot.sound $ r.left w x y z

@[to_additive]
theorem of_mul_assoc_right (w x y z : α) : of (((w * x) * y) * z) = of ((w * (x * y)) * z) :=
by rw [of_mul_assoc, of_mul_assoc, of_mul_assoc, of_mul_assoc_left]

@[to_additive]
instance : semigroup (free_semigroup α) :=
{ mul := λ x y, begin
    refine quot.lift_on x (λ p, quot.lift_on y (λ q, (quot.mk _ $ p * q : free_semigroup α)) _) _,
    { rintros a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); change of _ = of _,
      { rw of_mul_assoc_left },
      { rw [← of_mul_assoc, of_mul_assoc_left, of_mul_assoc] } },
    { refine quot.induction_on y (λ q, _),
      rintros a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); change of _ = of _,
      { rw of_mul_assoc_right },
      { rw [of_mul_assoc, of_mul_assoc, of_mul_assoc_left, of_mul_assoc_left, of_mul_assoc_left,
          ← of_mul_assoc c d, ← of_mul_assoc c d, of_mul_assoc_left] } }
  end,
  mul_assoc := λ x y z, quot.induction_on x $ λ p, quot.induction_on y $ λ q,
    quot.induction_on z $ λ r, of_mul_assoc p q r }

@[to_additive]
theorem of_mul (x y : α) : of (x * y) = of x * of y := rfl

section lift

variables {β : Type v} [semigroup β] (f : α → β)

/-- Lifts a magma homomorphism `α → β` to a semigroup homomorphism `magma.free_semigroup α → β`
given a semigroup `β`. -/
@[to_additive "Lifts an additive magma homomorphism `α → β` to an additive semigroup homomorphism
`add_magma.free_add_semigroup α → β` given an additive semigroup `β`."]
def lift (hf : ∀ x y, f (x * y) = f x * f y) : free_semigroup α → β :=
quot.lift f $ by rintros a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); simp only [hf, mul_assoc]

@[simp, to_additive] lemma lift_of {hf} (x : α) : lift f hf (of x) = f x := rfl

@[simp, to_additive] lemma lift_mul {hf} (x y) : lift f hf (x * y) = lift f hf x * lift f hf y :=
quot.induction_on x $ λ p, quot.induction_on y $ λ q, hf p q

@[to_additive]
theorem lift_unique (f : free_semigroup α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  f = lift (f ∘ of) (λ p q, hf (of p) (of q)) :=
funext $ λ x, quot.induction_on x $ λ p, rfl

end lift

variables {β : Type v} [has_mul β] (f : α → β)

/-- From a magma homomorphism `α → β` to a semigroup homomorphism
`magma.free_semigroup α → magma.free_semigroup β`. -/
@[to_additive "From an additive magma homomorphism `α → β` to an additive semigroup homomorphism
`add_magma.free_add_semigroup α → add_magma.free_add_semigroup β`."]
def map (hf : ∀ x y, f (x * y) = f x * f y) : free_semigroup α → free_semigroup β :=
lift (of ∘ f) (λ x y, congr_arg of $ hf x y)

@[simp, to_additive] lemma map_of {hf} (x) : map f hf (of x) = of (f x) := rfl
@[simp, to_additive] lemma map_mul {hf} (x y) : map f hf (x * y) = map f hf x * map f hf y :=
lift_mul _ _ _

end free_semigroup

end magma

/-- Free semigroup over a given alphabet.
(Note: In this definition, the free semigroup does not contain the empty word.) -/
@[to_additive "Free additive semigroup over a given alphabet."]
def free_semigroup (α : Type u) : Type u :=
α × list α

namespace free_semigroup

variables {α : Type u}

@[to_additive]
instance : semigroup (free_semigroup α) :=
{ mul := λ L1 L2, (L1.1, L1.2 ++ L2.1 :: L2.2),
  mul_assoc := λ L1 L2 L3, prod.ext rfl $ list.append_assoc _ _ _ }

/-- The embedding `α → free_semigroup α`. -/
@[to_additive "The embedding `α → free_add_semigroup α`."]
def of (x : α) : free_semigroup α :=
(x, [])

@[to_additive]
instance [inhabited α] : inhabited (free_semigroup α) := ⟨of (default _)⟩

/-- Recursor for free semigroup using `of` and `*`. -/
@[elab_as_eliminator, to_additive "Recursor for free additive semigroup using `of` and `+`."]
protected def rec_on {C : free_semigroup α → Sort l} (x)
  (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) :
  C x :=
prod.rec_on x $ λ f s, list.rec_on s ih1 (λ hd tl ih f, ih2 f (hd, tl) (ih1 f) (ih hd)) f

end free_semigroup

/-- Auxiliary function for `free_semigroup.lift`. -/
def free_semigroup.lift' {α : Type u} {β : Type v} [semigroup β] (f : α → β) : α → list α → β
| x [] := f x
| x (hd::tl) := f x * free_semigroup.lift' hd tl

/-- Auxiliary function for `free_semigroup.lift`. -/
def free_add_semigroup.lift' {α : Type u} {β : Type v} [add_semigroup β] (f : α → β) :
  α → list α → β
| x [] := f x
| x (hd::tl) := f x + free_add_semigroup.lift' hd tl

attribute [to_additive free_add_semigroup.lift'] free_semigroup.lift'

namespace free_semigroup

variables {α : Type u}

section lift

variables {β : Type v} [semigroup β] (f : α → β)

/-- Lifts a function `α → β` to a semigroup homomorphism `free_semigroup α → β` given
a semigroup `β`. -/
@[to_additive "Lifts a function `α → β` to an additive semigroup homomorphism
`free_add_semigroup α → β` given an additive semigroup `β`."]
def lift (x : free_semigroup α) : β :=
lift' f x.1 x.2

@[simp, to_additive] lemma lift_of (x : α) : lift f (of x) = f x := rfl
@[to_additive] lemma lift_of_mul (x y) : lift f (of x * y) = f x * lift f y := rfl

@[simp, to_additive] lemma lift_mul (x y) : lift f (x * y) = lift f x * lift f y :=
free_semigroup.rec_on x (λ p, rfl)
  (λ p x ih1 ih2, by rw [mul_assoc, lift_of_mul, lift_of_mul, mul_assoc, ih2])

@[to_additive]
theorem lift_unique (f : free_semigroup α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  f = lift (f ∘ of) :=
funext $ λ ⟨x, L⟩, list.rec_on L (λ x, rfl) (λ hd tl ih x,
  (hf (of x) (hd, tl)).trans $ congr_arg _ $ ih _) x

end lift

section map

variables {β : Type v} (f : α → β)

/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
@[to_additive "The unique additive semigroup homomorphism that sends `of x` to `of (f x)`."]
def map : free_semigroup α → free_semigroup β :=
lift $ of ∘ f

@[simp, to_additive] lemma map_of (x) : map f (of x) = of (f x) := rfl
@[simp, to_additive] lemma map_mul (x y) : map f (x * y) = map f x * map f y :=
lift_mul _ _ _

end map

section category

variables {β : Type u}

@[to_additive]
instance : monad free_semigroup :=
{ pure := λ _, of,
  bind := λ _ _ x f, lift f x }

/-- Recursor that uses `pure` instead of `of`. -/
@[elab_as_eliminator, to_additive "Recursor that uses `pure` instead of `of`."]
def rec_on' {C : free_semigroup α → Sort l} (x)
  (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C (pure x) → C y → C (pure x * y)) :
  C x :=
free_semigroup.rec_on x ih1 ih2

@[simp, to_additive]
lemma map_pure (f : α → β) (x) : (f <$> pure x : free_semigroup β) = pure (f x) := rfl

@[simp, to_additive]
lemma map_mul' (f : α → β) (x y : free_semigroup α) :
  (f <$> (x * y)) = (f <$> x * f <$> y) :=
map_mul _ _ _

@[simp, to_additive] lemma pure_bind (f : α → free_semigroup β) (x) :
  (pure x >>= f) = f x := rfl

@[simp, to_additive]
lemma mul_bind (f : α → free_semigroup β) (x y : free_semigroup α) :
  (x * y >>= f) = ((x >>= f) * (y >>= f)) :=
lift_mul _ _ _

@[simp, to_additive] lemma pure_seq {f : α → β} {x : free_semigroup α} :
  pure f <*> x = f <$> x := rfl

@[simp, to_additive]
lemma mul_seq {f g : free_semigroup (α → β)} {x : free_semigroup α} :
  (f * g) <*> x = (f <*> x) * (g <*> x) :=
mul_bind _ _ _

@[to_additive]
instance : is_lawful_monad free_semigroup.{u} :=
{ pure_bind := λ _ _ _ _, rfl,
  bind_assoc := λ α β γ x f g, rec_on' x (λ x, rfl)
    (λ x y ih1 ih2, by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]),
  id_map := λ α x, rec_on' x (λ _, rfl) (λ x y ih1 ih2, by rw [map_mul', ih1, ih2]) }

/-- `free_semigroup` is traversable. -/
@[to_additive "`free_add_semigroup` is traversable."]
protected def traverse {m : Type u → Type u} [applicative m]
  {α β : Type u} (F : α → m β) (x : free_semigroup α) : m (free_semigroup β) :=
rec_on' x (λ x, pure <$> F x) (λ x y ihx ihy, (*) <$> ihx <*> ihy)

@[to_additive]
instance : traversable free_semigroup := ⟨@free_semigroup.traverse⟩

variables {m : Type u → Type u} [applicative m] (F : α → m β)

@[simp, to_additive]
lemma traverse_pure (x) :traverse F (pure x : free_semigroup α) = pure <$> F x := rfl
@[simp, to_additive]
lemma traverse_pure' : traverse F ∘ pure = λ x, (pure <$> F x : m (free_semigroup β)) := rfl

section
variables [is_lawful_applicative m]
@[simp, to_additive] lemma traverse_mul (x y : free_semigroup α) :
  traverse F (x * y) = (*) <$> traverse F x <*> traverse F y :=
let ⟨x, L1⟩ := x, ⟨y, L2⟩ := y in
list.rec_on L1 (λ x, rfl) (λ hd tl ih x,
  show (*) <$> pure <$> F x <*> traverse F ((hd, tl) * (y, L2) : free_semigroup α) =
  (*) <$> ((*) <$> pure <$> F x <*> traverse F (hd, tl)) <*> traverse F (y, L2),
  by rw ih; simp only [(∘), (mul_assoc _ _ _).symm] with functor_norm) x

@[simp, to_additive] lemma traverse_mul' :
  function.comp (traverse F) ∘ @has_mul.mul (free_semigroup α) _ =
    λ x y, (*) <$> traverse F x <*> traverse F y :=
funext $ λ x, funext $ λ y, traverse_mul F x y
end

@[simp, to_additive] lemma traverse_eq (x) : free_semigroup.traverse F x = traverse F x := rfl

@[simp, to_additive] lemma mul_map_seq (x y : free_semigroup α) :
  ((*) <$> x <*> y : id (free_semigroup α)) = (x * y : free_semigroup α) := rfl

@[to_additive]
instance : is_lawful_traversable free_semigroup.{u} :=
{ id_traverse := λ α x, free_semigroup.rec_on x (λ x, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, mul_map_seq]),
  comp_traverse := λ F G hf1 hg1 hf2 hg2 α β γ f g x, rec_on' x
    (λ x, by resetI; simp only [traverse_pure, traverse_pure'] with functor_norm)
    (λ x y ih1 ih2, by resetI; rw [traverse_mul, ih1, ih2, traverse_mul];
      simp only [traverse_mul'] with functor_norm),
  naturality := λ F G hf1 hg1 hf2 hg2 η α β f x, rec_on' x
    (λ x, by simp only [traverse_pure] with functor_norm)
    (λ x y ih1 ih2, by resetI; simp only [traverse_mul] with functor_norm; rw [ih1, ih2]),
  traverse_eq_map_id := λ α β f x, free_semigroup.rec_on x (λ _, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; refl),
  .. free_semigroup.is_lawful_monad }

end category

@[to_additive]
instance [decidable_eq α] : decidable_eq (free_semigroup α) := prod.decidable_eq

end free_semigroup

/-- Isomorphism between `magma.free_semigroup (free_magma α)` and `free_semigroup α`. -/
@[to_additive "Isomorphism between
`add_magma.free_add_semigroup (free_add_magma α)` and `free_add_semigroup α`."]
def free_semigroup_free_magma (α : Type u) :
  magma.free_semigroup (free_magma α) ≃ free_semigroup α :=
{ to_fun := magma.free_semigroup.lift (free_magma.lift free_semigroup.of) (free_magma.lift_mul _),
  inv_fun := free_semigroup.lift (magma.free_semigroup.of ∘ free_magma.of),
  left_inv := λ x, magma.free_semigroup.induction_on x $ λ p, by rw magma.free_semigroup.lift_of;
    exact free_magma.rec_on' p
      (λ x, by rw [free_magma.lift_of, free_semigroup.lift_of])
      (λ x y ihx ihy, by rw [free_magma.lift_mul, free_semigroup.lift_mul, ihx, ihy,
        magma.free_semigroup.of_mul]),
  right_inv := λ x, free_semigroup.rec_on x
    (λ x, by rw [free_semigroup.lift_of, magma.free_semigroup.lift_of, free_magma.lift_of])
    (λ x y ihx ihy, by rw [free_semigroup.lift_mul, magma.free_semigroup.lift_mul, ihx, ihy]) }

@[simp, to_additive] lemma free_semigroup_free_magma_mul {α : Type u} (x y) :
  free_semigroup_free_magma α (x * y) = free_semigroup_free_magma α x *
    free_semigroup_free_magma α y :=
magma.free_semigroup.lift_mul _ _ _
