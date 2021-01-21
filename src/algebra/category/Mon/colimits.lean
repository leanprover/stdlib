/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import category_theory.limits.concrete_category

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at the output of `#print monoid`:

  -- structure monoid : Type u → Type u
  -- fields:
  -- monoid.mul : Π {α : Type u} [c : monoid α], α → α → α
  -- monoid.mul_assoc : ∀ {α : Type u} [c : monoid α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  -- monoid.one : Π (α : Type u) [c : monoid α], α
  -- monoid.one_mul : ∀ {α : Type u} [c : monoid α] (a : α), 1 * a = a
  -- monoid.mul_one : ∀ {α : Type u} [c : monoid α] (a : α), a * 1 = a

and if we'd fed it the output of `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.
-/

universes v

open category_theory
open category_theory.limits

namespace Mon.colimits
/-!
We build the colimit of a diagram in `Mon` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/

variables {J : Type v} [small_category J] (F : J ⥤ Mon.{v})

/--
An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : F.obj j), prequotient
-- Then one generator for each operation
| one : prequotient
| mul : prequotient → prequotient → prequotient

instance : inhabited (prequotient F) := ⟨prequotient.one⟩

open prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
-- Make it an equivalence relation:
| refl : Π (x), relation x x
| symm : Π (x y) (h : relation x y), relation y x
| trans : Π (x y z) (h : relation x y) (k : relation y z), relation x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (x : F.obj j), relation (of j' ((F.map f) x)) (of j x)
-- Then one relation per operation, describing the interaction with `of`
| mul : Π (j) (x y : F.obj j), relation (of j (x * y)) (mul (of j x) (of j y))
| one : Π (j), relation (of j 1) one
-- Then one relation per argument of each operation
| mul_1 : Π (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
| mul_2 : Π (x y y') (r : relation y y'), relation (mul x y) (mul x y')
-- And one relation per axiom
| mul_assoc : Π (x y z), relation (mul (mul x y) z) (mul x (mul y z))
| one_mul : Π (x), relation (mul one x) x
| mul_one : Π (x), relation (mul x one) x

/--
The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

/--
The underlying type of the colimit of a diagram in `Mon`.
-/
@[derive inhabited]
def colimit_type : Type v := quotient (colimit_setoid F)

instance monoid_colimit_type : monoid (colimit_type F) :=
{ mul :=
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
  one :=
  begin
    exact quot.mk _ one
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
  end }

@[simp] lemma quot_one : quot.mk setoid.r one = (1 : colimit_type F) := rfl
@[simp] lemma quot_mul (x y) : quot.mk setoid.r (mul x y) = ((quot.mk setoid.r x) * (quot.mk setoid.r y) : colimit_type F) := rfl

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : Mon := ⟨colimit_type F, by apply_instance⟩

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
quot.mk _ (of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := cocone_fun F j,
  map_one' := quot.sound (relation.one _),
  map_mul' := λ x y, quot.sound (relation.mul _ _ _) }

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

/-- The cocone over the proposed colimit monoid. -/
def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F, } }.

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| one       := 1
| (mul x y) := desc_fun_lift x * desc_fun_lift y

/-- The function from the colimit monoid to the cone point of any other cocone. -/
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
    -- mul
    { simp, },
    -- one
    { simp, },
    -- mul_1
    { rw r_ih, },
    -- mul_2
    { rw r_ih, },
    -- mul_assoc
    { rw mul_assoc, },
    -- one_mul
    { rw one_mul, },
    -- mul_one
    { rw mul_one, } }
end

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ to_fun := desc_fun F s,
  map_one' := rfl,
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
    { simp *, },
    { simp *, },
    refl
  end }.

instance has_colimits_Mon : has_colimits Mon :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone := colimit_cocone F,
      is_colimit := colimit_is_colimit F } } }

end Mon.colimits
