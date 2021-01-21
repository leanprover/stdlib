/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.CommRing.basic
import category_theory.limits.concrete_category

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `comm_ring` and `ring_hom`.
-/

universes u v

open category_theory
open category_theory.limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
/-
`#print comm_ring` says:

structure comm_ring : Type u → Type u
fields:
comm_ring.zero : Π (α : Type u) [c : comm_ring α], α
comm_ring.one : Π (α : Type u) [c : comm_ring α], α
comm_ring.neg : Π {α : Type u} [c : comm_ring α], α → α
comm_ring.add : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.mul : Π {α : Type u} [c : comm_ring α], α → α → α

comm_ring.zero_add : ∀ {α : Type u} [c : comm_ring α] (a : α), 0 + a = a
comm_ring.add_zero : ∀ {α : Type u} [c : comm_ring α] (a : α), a + 0 = a
comm_ring.one_mul : ∀ {α : Type u} [c : comm_ring α] (a : α), 1 * a = a
comm_ring.mul_one : ∀ {α : Type u} [c : comm_ring α] (a : α), a * 1 = a
comm_ring.add_left_neg : ∀ {α : Type u} [c : comm_ring α] (a : α), -a + a = 0
comm_ring.add_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a + b = b + a
comm_ring.mul_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a * b = b * a
comm_ring.add_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
comm_ring.mul_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
comm_ring.left_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * (b + c_1) = a * b + a * c_1
comm_ring.right_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), (a + b) * c_1 = a * c_1 + b * c_1
-/

namespace CommRing.colimits
/-!
We build the colimit of a diagram in `CommRing` by constructing the
free commutative ring on the disjoint union of all the commutative rings in the diagram,
then taking the quotient by the commutative ring laws within each commutative ring,
and the identifications given by the morphisms in the diagram.
-/

variables {J : Type v} [small_category J] (F : J ⥤ CommRing.{v})

/--
An inductive type representing all commutative ring expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : F.obj j), prequotient
-- Then one generator for each operation
| zero : prequotient
| one : prequotient
| neg : prequotient → prequotient
| add : prequotient → prequotient → prequotient
| mul : prequotient → prequotient → prequotient

instance : inhabited (prequotient F) := ⟨prequotient.zero⟩

open prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the commutative ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
-- Make it an equivalence relation:
| refl : Π (x), relation x x
| symm : Π (x y) (h : relation x y), relation y x
| trans : Π (x y z) (h : relation x y) (k : relation y z), relation x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (x : F.obj j), relation (of j' (F.map f x)) (of j x)
-- Then one relation per operation, describing the interaction with `of`
| zero : Π (j), relation (of j 0) zero
| one : Π (j), relation (of j 1) one
| neg : Π (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
| add : Π (j) (x y : F.obj j), relation (of j (x + y)) (add (of j x) (of j y))
| mul : Π (j) (x y : F.obj j), relation (of j (x * y)) (mul (of j x) (of j y))
-- Then one relation per argument of each operation
| neg_1 : Π (x x') (r : relation x x'), relation (neg x) (neg x')
| add_1 : Π (x x' y) (r : relation x x'), relation (add x y) (add x' y)
| add_2 : Π (x y y') (r : relation y y'), relation (add x y) (add x y')
| mul_1 : Π (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
| mul_2 : Π (x y y') (r : relation y y'), relation (mul x y) (mul x y')
-- And one relation per axiom
| zero_add      : Π (x), relation (add zero x) x
| add_zero      : Π (x), relation (add x zero) x
| one_mul       : Π (x), relation (mul one x) x
| mul_one       : Π (x), relation (mul x one) x
| add_left_neg  : Π (x), relation (add (neg x) x) zero
| add_comm      : Π (x y), relation (add x y) (add y x)
| mul_comm      : Π (x y), relation (mul x y) (mul y x)
| add_assoc     : Π (x y z), relation (add (add x y) z) (add x (add y z))
| mul_assoc     : Π (x y z), relation (mul (mul x y) z) (mul x (mul y z))
| left_distrib  : Π (x y z), relation (mul x (add y z)) (add (mul x y) (mul x z))
| right_distrib : Π (x y z), relation (mul (add x y) z) (add (mul x z) (mul y z))

/--
The setoid corresponding to commutative expressions modulo monoid relations and identifications.
-/
def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

/--
The underlying type of the colimit of a diagram in `CommRing`.
-/
@[derive inhabited]
def colimit_type : Type v := quotient (colimit_setoid F)

instance : comm_ring (colimit_type F) :=
{ zero :=
  begin
    exact quot.mk _ zero
  end,
  one :=
  begin
    exact quot.mk _ one
  end,
  neg :=
  begin
    fapply @quot.lift,
    { intro x,
      exact quot.mk _ (neg x) },
    { intros x x' r,
      apply quot.sound,
      exact relation.neg_1 _ _ r },
  end,
  add :=
  begin
    fapply @quot.lift _ _ ((colimit_type F) → (colimit_type F)),
    { intro x,
      fapply @quot.lift,
      { intro y,
        exact quot.mk _ (add x y) },
      { intros y y' r,
        apply quot.sound,
        exact relation.add_2 _ _ _ r } },
    { intros x x' r,
      funext y,
      induction y,
      dsimp,
      apply quot.sound,
      { exact relation.add_1 _ _ _ r },
      { refl } },
  end,
  mul :=
  begin
    fapply @quot.lift _ _ ((colimit_type F) → (colimit_type F)),
    { intro x,
      fapply @quot.lift,
      { intro y,
        exact quot.mk _ (mul x y) },
      { intros y y' r,
        apply quot.sound,
        exact relation.mul_2 _ _ _ r } },
    { intros x x' r,
      funext y,
      induction y,
      dsimp,
      apply quot.sound,
      { exact relation.mul_1 _ _ _ r },
      { refl } },
  end,
  zero_add := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.zero_add,
    refl,
  end,
  add_zero := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.add_zero,
    refl,
  end,
  one_mul := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.one_mul,
    refl,
  end,
  mul_one := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.mul_one,
    refl,
  end,
  add_left_neg := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.add_left_neg,
    refl,
  end,
  add_comm := λ x y,
  begin
    induction x,
    induction y,
    dsimp,
    apply quot.sound,
    apply relation.add_comm,
    refl,
    refl,
  end,
  mul_comm := λ x y,
  begin
    induction x,
    induction y,
    dsimp,
    apply quot.sound,
    apply relation.mul_comm,
    refl,
    refl,
  end,
  add_assoc := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.add_assoc,
    refl,
    refl,
    refl,
  end,
  mul_assoc := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.mul_assoc,
    refl,
    refl,
    refl,
  end,
  left_distrib := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.left_distrib,
    refl,
    refl,
    refl,
  end,
  right_distrib := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.right_distrib,
    refl,
    refl,
    refl,
  end, }

@[simp] lemma quot_zero : quot.mk setoid.r zero = (0 : colimit_type F) := rfl
@[simp] lemma quot_one : quot.mk setoid.r one = (1 : colimit_type F) := rfl
@[simp] lemma quot_neg (x) :
  quot.mk setoid.r (neg x) = (-(quot.mk setoid.r x) : colimit_type F) := rfl
@[simp] lemma quot_add (x y) :
  quot.mk setoid.r (add x y) = ((quot.mk setoid.r x) + (quot.mk setoid.r y) : colimit_type F) := rfl
@[simp] lemma quot_mul (x y) :
  quot.mk setoid.r (mul x y) = ((quot.mk setoid.r x) * (quot.mk setoid.r y) : colimit_type F) := rfl

/-- The bundled commutative ring giving the colimit of a diagram. -/
def colimit : CommRing := CommRing.of (colimit_type F)

/-- The function from a given commutative ring in the diagram to the colimit commutative ring. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
quot.mk _ (of j x)

/-- The ring homomorphism from a given commutative ring in the diagram to the colimit commutative
ring. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := cocone_fun F j,
  map_one' := by apply quot.sound; apply relation.one,
  map_mul' := by intros; apply quot.sound; apply relation.mul,
  map_zero' := by apply quot.sound; apply relation.zero,
  map_add' := by intros; apply quot.sound; apply relation.add }

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  ext,
  apply quot.sound,
  apply relation.map,
end

@[simp] lemma cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j):
  (cocone_morphism F j') (F.map f x) = (cocone_morphism F j) x :=
by { rw ←cocone_naturality F f, refl }

/-- The cocone over the proposed colimit commutative ring. -/
def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F } }.

/-- The function from the free commutative ring on the diagram to the cone point of any other
cocone. -/
@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| zero      := 0
| one       := 1
| (neg x)   := -(desc_fun_lift x)
| (add x y) := desc_fun_lift x + desc_fun_lift y
| (mul x y) := desc_fun_lift x * desc_fun_lift y

/-- The function from the colimit commutative ring to the cone point of any other cocone. -/
def desc_fun (s : cocone F) : colimit_type F → s.X :=
begin
  fapply quot.lift,
  { exact desc_fun_lift F s },
  { intros x y r,
    induction r; try { dsimp },
    -- refl
    { refl },
    -- symm
    { exact r_ih.symm },
    -- trans
    { exact eq.trans r_ih_h r_ih_k },
    -- map
    { simp, },
    -- zero
    { simp, },
    -- one
    { simp, },
    -- neg
    { simp, },
    -- add
    { simp, },
    -- mul
    { simp, },
    -- neg_1
    { rw r_ih, },
    -- add_1
    { rw r_ih, },
    -- add_2
    { rw r_ih, },
    -- mul_1
    { rw r_ih, },
    -- mul_2
    { rw r_ih, },
    -- zero_add
    { rw zero_add, },
    -- add_zero
    { rw add_zero, },
    -- one_mul
    { rw one_mul, },
    -- mul_one
    { rw mul_one, },
    -- add_left_neg
    { rw add_left_neg, },
    -- add_comm
    { rw add_comm, },
    -- mul_comm
    { rw mul_comm, },
    -- add_assoc
    { rw add_assoc, },
    -- mul_assoc
    { rw mul_assoc, },
    -- left_distrib
    { rw left_distrib, },
    -- right_distrib
    { rw right_distrib, },
  }
end

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ to_fun := desc_fun F s,
  map_one' := rfl,
  map_zero' := rfl,
  map_add' := λ x y, by { induction x; induction y; refl },
  map_mul' := λ x y, by { induction x; induction y; refl }, }

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w,
  begin
    ext,
    induction x,
    induction x,
    { have w' := congr_fun (congr_arg (λ f : F.obj x_j ⟶ s.X, (f : F.obj x_j → s.X)) (w x_j)) x_x,
      erw w',
      refl, },
    { simp, },
    { simp, },
    { simp *, },
    { simp *, },
    { simp *, },
    refl
  end }.

instance has_colimits_CommRing : has_colimits CommRing :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone := colimit_cocone F,
      is_colimit := colimit_is_colimit F } } }

end CommRing.colimits
