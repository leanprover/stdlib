/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.preadditive
import group_theory.quotient_group
import category_theory.limits.concrete_category
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.concrete_category

/-!
# The category of additive commutative groups has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `add_comm_group` and `monoid_hom`.

TODO:
In fact, in `AddCommGroup` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/

universes u v

open category_theory
open category_theory.limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.

namespace AddCommGroup.colimits
/-!
We build the colimit of a diagram in `AddCommGroup` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

variables {J : Type v} [small_category J] (F : J ⥤ AddCommGroup.{v})

/--
An inductive type representing all group expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : F.obj j), prequotient
-- Then one generator for each operation
| zero : prequotient
| neg : prequotient → prequotient
| add : prequotient → prequotient → prequotient

instance : inhabited (prequotient F) := ⟨prequotient.zero⟩

open prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the abelian group laws, or
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
| neg : Π (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
| add : Π (j) (x y : F.obj j), relation (of j (x + y)) (add (of j x) (of j y))
-- Then one relation per argument of each operation
| neg_1 : Π (x x') (r : relation x x'), relation (neg x) (neg x')
| add_1 : Π (x x' y) (r : relation x x'), relation (add x y) (add x' y)
| add_2 : Π (x y y') (r : relation y y'), relation (add x y) (add x y')
-- And one relation per axiom
| zero_add      : Π (x), relation (add zero x) x
| add_zero      : Π (x), relation (add x zero) x
| add_left_neg  : Π (x), relation (add (neg x) x) zero
| add_comm      : Π (x y), relation (add x y) (add y x)
| add_assoc     : Π (x y z), relation (add (add x y) z) (add x (add y z))

/--
The setoid corresponding to group expressions modulo abelian group relations and identifications.
-/
def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

/--
The underlying type of the colimit of a diagram in `AddCommGroup`.
-/
@[derive inhabited]
def colimit_type : Type v := quotient (colimit_setoid F)

instance : add_comm_group (colimit_type F) :=
{ zero :=
  begin
    exact quot.mk _ zero
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
  end, }

@[simp] lemma quot_zero : quot.mk setoid.r zero = (0 : colimit_type F) := rfl
@[simp] lemma quot_neg (x) :
  quot.mk setoid.r (neg x) = (-(quot.mk setoid.r x) : colimit_type F) := rfl
@[simp] lemma quot_add (x y) :
  quot.mk setoid.r (add x y) = ((quot.mk setoid.r x) + (quot.mk setoid.r y) : colimit_type F) := rfl

/-- The bundled abelian group giving the colimit of a diagram. -/
def colimit : AddCommGroup := AddCommGroup.of (colimit_type F)

/-- The function from a given abelian group in the diagram to the colimit abelian group. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
quot.mk _ (of j x)

/-- The group homomorphism from a given abelian group in the diagram to the colimit abelian
group. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := cocone_fun F j,
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

/-- The cocone over the proposed colimit abelian group. -/
def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F } }.

/-- The function from the free abelian group on the diagram to the cone point of any other
cocone. -/
@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| zero      := 0
| (neg x)   := -(desc_fun_lift x)
| (add x y) := desc_fun_lift x + desc_fun_lift y

/-- The function from the colimit abelian group to the cone point of any other cocone. -/
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
    -- neg
    { simp, },
    -- add
    { simp, },
    -- neg_1
    { rw r_ih, },
    -- add_1
    { rw r_ih, },
    -- add_2
    { rw r_ih, },
    -- zero_add
    { rw zero_add, },
    -- add_zero
    { rw add_zero, },
    -- add_left_neg
    { rw add_left_neg, },
    -- add_comm
    { rw add_comm, },
    -- add_assoc
    { rw add_assoc, },
  }
end

/-- The group homomorphism from the colimit abelian group to the cone point of any other cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ to_fun := desc_fun F s,
  map_zero' := rfl,
  map_add' := λ x y, by { induction x; induction y; refl }, }

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_cocone_is_colimit : is_colimit (colimit_cocone F) :=
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
    { simp *, },
    refl
  end }.

instance has_colimits_AddCommGroup : has_colimits AddCommGroup :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone := colimit_cocone F,
      is_colimit := colimit_cocone_is_colimit F } } }

end AddCommGroup.colimits

namespace AddCommGroup

open quotient_add_group

/--
The categorical cokernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernel_iso_quotient {G H : AddCommGroup} (f : G ⟶ H) :
  cokernel f ≅ AddCommGroup.of (quotient (add_monoid_hom.range f)) :=
{ hom := cokernel.desc f (mk' _)
    (by { ext, apply quotient.sound, fsplit, exact -x,
          simp only [add_zero, add_monoid_hom.map_neg], }),
  inv := quotient_add_group.lift _ (cokernel.π f)
    (by { intros x H_1, cases H_1, induction H_1_h,
          simp only [cokernel.condition_apply, zero_apply]}),
  -- obviously can take care of the next goals, but it is really slow
  hom_inv_id' := begin
    ext1, simp only [coequalizer_as_cokernel, category.comp_id, cokernel.π_desc_assoc], ext1, refl,
  end,
  inv_hom_id' := begin
    ext1, induction x,
    { simp only [colimit.ι_desc_apply, id_apply, add_monoid_hom.coe_of, lift_quot_mk,
                 cofork.of_π_ι_app, comp_apply], refl },
    { refl }
  end, }

end AddCommGroup
