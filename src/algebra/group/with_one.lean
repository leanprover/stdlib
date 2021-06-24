/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import algebra.ring.basic
import data.equiv.basic

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in `algebra.category.Mon.adjunctions`.

Another result says that adjoining to a group an element `zero` gives a `group_with_zero`. For more
information about these structures (which are not that standard in informal mathematics, see
`algebra.group_with_zero.basic`)
-/

universes u v w
variable {α : Type u}

/-- Add an extra element `1` to a type -/
@[to_additive "Add an extra element `0` to a type"]
def with_one (α) := option α

namespace with_one

@[to_additive]
instance : monad with_one := option.monad

@[to_additive]
instance : has_one (with_one α) := ⟨none⟩

@[to_additive]
instance [has_mul α] : has_mul (with_one α) := ⟨option.lift_or_get (*)⟩

@[to_additive]
instance : inhabited (with_one α) := ⟨1⟩

@[to_additive]
instance [nonempty α] : nontrivial (with_one α) := option.nontrivial

@[to_additive]
instance : has_coe_t α (with_one α) := ⟨some⟩

@[to_additive]
lemma some_eq_coe {a : α} : (some a : with_one α) = ↑a := rfl

@[simp, to_additive]
lemma coe_ne_one {a : α} : (a : with_one α) ≠ (1 : with_one α) :=
option.some_ne_none a

@[simp, to_additive]
lemma one_ne_coe {a : α} : (1 : with_one α) ≠ a :=
coe_ne_one.symm

@[to_additive]
lemma ne_one_iff_exists {x : with_one α} : x ≠ 1 ↔ ∃ (a : α), ↑a = x :=
option.ne_none_iff_exists

-- `to_additive` fails to generate some meta info around eqn lemmas, so `lift` doesn't work
-- unless we explicitly define this instance
instance : can_lift (with_one α) α :=
{ coe := coe,
  cond := λ a, a ≠ 1,
  prf := λ a, ne_one_iff_exists.1 }

@[simp, norm_cast, to_additive]
lemma coe_inj {a b : α} : (a : with_one α) = b ↔ a = b :=
option.some_inj

@[elab_as_eliminator, to_additive]
protected lemma cases_on {P : with_one α → Prop} :
  ∀ (x : with_one α), P 1 → (∀ a : α, P a) → P x :=
option.cases_on

-- the `show` statements in the proofs are important, because otherwise the generated lemmas
-- `with_one.mul_one_class._proof_{1,2}` have an ill-typed statement after `with_one` is made
-- irreducible.
@[to_additive]
instance [has_mul α] : mul_one_class (with_one α) :=
{ mul := (*),
  one := (1),
  one_mul   := show ∀ x : with_one α, 1 * x = x, from (option.lift_or_get_is_left_id _).1,
  mul_one   := show ∀ x : with_one α, x * 1 = x, from (option.lift_or_get_is_right_id _).1 }

@[to_additive]
instance [semigroup α] : monoid (with_one α) :=
{ mul_assoc := (option.lift_or_get_assoc _).1,
  ..with_one.mul_one_class }

example [semigroup α] :
  @monoid.to_mul_one_class _ (@with_one.monoid α _) = @with_one.mul_one_class α _ := rfl

@[to_additive]
instance [comm_semigroup α] : comm_monoid (with_one α) :=
{ mul_comm := (option.lift_or_get_comm _).1,
  ..with_one.monoid }

section
-- workaround: we make `with_one`/`with_zero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
local attribute [irreducible] with_one with_zero
/-- `coe` as a bundled morphism -/
@[to_additive "`coe` as a bundled morphism", simps apply]
def coe_mul_hom [has_mul α] : mul_hom α (with_one α) :=
{ to_fun := coe, map_mul' := λ x y, rfl }

end

section lift

variables [has_mul α] {β : Type v} [mul_one_class β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism."]
def lift : mul_hom α β ≃ (with_one α →* β) :=
{ to_fun := λ f,
  { to_fun := λ x, option.cases_on x 1 f,
    map_one' := rfl,
    map_mul' := λ x y,
      with_one.cases_on x (by { rw one_mul, exact (one_mul _).symm }) $ λ x,
      with_one.cases_on y (by { rw mul_one, exact (mul_one _).symm }) $ λ y,
      f.map_mul x y },
  inv_fun := λ F, F.to_mul_hom.comp coe_mul_hom,
  left_inv := λ f, mul_hom.ext $ λ x, rfl,
  right_inv := λ F, monoid_hom.ext $ λ x, with_one.cases_on x F.map_one.symm $ λ x, rfl }

variables (f : mul_hom α β)

@[simp, to_additive]
lemma lift_coe (x : α) : lift f x = f x := rfl

@[simp, to_additive]
lemma lift_one : lift f 1 = 1 := rfl

@[to_additive]
theorem lift_unique (f : with_one α →* β) : f = lift (f.to_mul_hom.comp coe_mul_hom) :=
(lift.apply_symm_apply f).symm

end lift

section map

variables {β : Type v} [has_mul α] [has_mul β]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive "Given an additive map from `α → β` returns an add_monoid homomorphism
  from `with_zero α` to `with_zero β`"]
def map (f : mul_hom α β) : with_one α →* with_one β :=
lift (coe_mul_hom.comp f)

@[simp, to_additive]
lemma map_id : map (mul_hom.id α) = monoid_hom.id (with_one α) :=
by { ext, cases x; refl }

@[simp, to_additive]
lemma map_comp {γ : Type w} [has_mul γ] (f : mul_hom α β) (g : mul_hom β γ) :
map (g.comp f) = (map g).comp (map f) :=
by { ext, cases x; refl }

end map

attribute [irreducible] with_one

@[simp, norm_cast, to_additive]
lemma coe_mul [has_mul α] (a b : α) : ((a * b : α) : with_one α) = a * b := rfl

end with_one

namespace with_zero

-- `to_additive` fails to generate some meta info around eqn lemmas, so `lift` doesn't work
-- unless we explicitly define this instance
instance : can_lift (with_zero α) α :=
{ coe := coe,
  cond := λ a, a ≠ 0,
  prf := λ a, ne_zero_iff_exists.1 }

attribute [to_additive] with_one.can_lift

instance [one : has_one α] : has_one (with_zero α) :=
{ ..one }

@[simp, norm_cast] lemma coe_one [has_one α] : ((1 : α) : with_zero α) = 1 := rfl

instance [has_mul α] : mul_zero_class (with_zero α) :=
{ mul       := λ o₁ o₂, o₁.bind (λ a, option.map (λ b, a * b) o₂),
  zero_mul  := λ a, rfl,
  mul_zero  := λ a, by cases a; refl,
  ..with_zero.has_zero }

@[simp, norm_cast] lemma coe_mul {α : Type u} [has_mul α]
  {a b : α} : ((a * b : α) : with_zero α) = a * b := rfl

@[simp] lemma zero_mul {α : Type u} [has_mul α]
  (a : with_zero α) : 0 * a = 0 := rfl

@[simp] lemma mul_zero {α : Type u} [has_mul α]
  (a : with_zero α) : a * 0 = 0 := by cases a; refl

instance [semigroup α] : semigroup_with_zero (with_zero α) :=
{ mul_assoc := λ a b c, match a, b, c with
    | none,   _,      _      := rfl
    | some a, none,   _      := rfl
    | some a, some b, none   := rfl
    | some a, some b, some c := congr_arg some (mul_assoc _ _ _)
    end,
  ..with_zero.mul_zero_class }

instance [comm_semigroup α] : comm_semigroup (with_zero α) :=
{ mul_comm := λ a b, match a, b with
    | none,   _      := (mul_zero _).symm
    | some a, none   := rfl
    | some a, some b := congr_arg some (mul_comm _ _)
    end,
  ..with_zero.semigroup_with_zero }

instance [mul_one_class α] : mul_zero_one_class (with_zero α) :=
{ one_mul := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ one_mul _
    end,
  mul_one := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ mul_one _
    end,
  ..with_zero.mul_zero_class,
  ..with_zero.has_one }

instance [monoid α] : monoid_with_zero (with_zero α) :=
{ ..with_zero.mul_zero_one_class,
  ..with_zero.semigroup_with_zero }

instance [comm_monoid α] : comm_monoid_with_zero (with_zero α) :=
{ ..with_zero.monoid_with_zero, ..with_zero.comm_semigroup }

/-- Given an inverse operation on `α` there is an inverse operation
  on `with_zero α` sending `0` to `0`-/
definition inv [has_inv α] (x : with_zero α) : with_zero α :=
do a ← x, return a⁻¹

instance [has_inv α] : has_inv (with_zero α) := ⟨with_zero.inv⟩

@[simp, norm_cast] lemma coe_inv [has_inv α] (a : α) :
  ((a⁻¹ : α) : with_zero α) = a⁻¹ := rfl

@[simp] lemma inv_zero [has_inv α] :
  (0 : with_zero α)⁻¹ = 0 := rfl

section group
variables [group α]

@[simp] lemma inv_one : (1 : with_zero α)⁻¹ = 1 :=
show ((1⁻¹ : α) : with_zero α) = 1, by simp

/-- if `G` is a group then `with_zero G` is a group with zero. -/
instance : group_with_zero (with_zero α) :=
{ inv_zero := inv_zero,
  mul_inv_cancel := by { intros a ha, lift a to α using ha, norm_cast, apply mul_right_inv },
  .. with_zero.monoid_with_zero,
  .. with_zero.has_inv,
  .. with_zero.nontrivial }

@[norm_cast]
lemma div_coe (a b : α) : (a : with_zero α) / b = (a * b⁻¹ : α) := rfl

end group

instance [comm_group α] : comm_group_with_zero (with_zero α) :=
{ .. with_zero.group_with_zero, .. with_zero.comm_monoid_with_zero }

instance [semiring α] : semiring (with_zero α) :=
{ left_distrib := λ a b c, begin
    cases a with a, {refl},
    cases b with b; cases c with c; try {refl},
    exact congr_arg some (left_distrib _ _ _)
  end,
  right_distrib := λ a b c, begin
    cases c with c,
    { change (a + b) * 0 = a * 0 + b * 0, simp },
    cases a with a; cases b with b; try {refl},
    exact congr_arg some (right_distrib _ _ _)
  end,
  ..with_zero.add_comm_monoid,
  ..with_zero.mul_zero_class,
  ..with_zero.monoid_with_zero }

attribute [irreducible] with_zero

end with_zero
