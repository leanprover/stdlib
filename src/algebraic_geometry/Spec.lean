/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf
import data.equiv.transfer_instance

/-!
# $Spec$ as a functor to locally ringed spaces.

We define the functor $Spec$ from commutative rings to locally ringed spaces.

## Implementation notes

We define $Spec$ in three consecutive steps, each with more structure than the last:

1. `Spec.to_Top`, valued in the category of topological spaces,
2. `Spec.to_SheafedSpace`, valued in the category of sheafed spaces and
3. `Spec.to_LocallyRingedSpace`, valued in the category of locally ringed spaces.

Additionally, we provide `Spec.to_PresheafedSpace` as a composition of `Spec.to_SheafedSpace` with
a forgetful functor.

## Future work

Adjunction between `Γ` and `Spec`

-/

noncomputable theory

namespace algebraic_geometry
open opposite
open category_theory
open structure_sheaf

/--
The spectrum of a commutative ring, as a topological space.
-/
def Spec.Top_obj (R : CommRing) : Top := Top.of (prime_spectrum R)

/--
The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
@[simps] def Spec.Top_map {R S : CommRing} (f : R ⟶ S) :
  Spec.Top_obj S ⟶ Spec.Top_obj R :=
{ to_fun := prime_spectrum.comap f,
  continuous_to_fun := prime_spectrum.comap_continuous f }

@[simp] lemma Spec.Top_map_id (R : CommRing) :
  Spec.Top_map (𝟙 R) = 𝟙 (Spec.Top_obj R) :=
continuous_map.ext $ λ x,
by erw [Spec.Top_map_to_fun, prime_spectrum.comap_id, id.def, Top.id_app]

lemma Spec.Top_map_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  Spec.Top_map (f ≫ g) = Spec.Top_map g ≫ Spec.Top_map f :=
continuous_map.ext $ λ x,
begin
  dsimp only [Spec.Top_map_to_fun, Top.comp_app],
  erw prime_spectrum.comap_comp,
end

/--
The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps] def Spec.to_Top : CommRingᵒᵖ ⥤ Top :=
{ obj := λ R, Spec.Top_obj (unop R),
  map := λ R S f, Spec.Top_map f.unop,
  map_id' := λ R, by rw [unop_id, Spec.Top_map_id],
  map_comp' := λ R S T f g, by rw [unop_comp, Spec.Top_map_comp] }

/--
The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps] def Spec.SheafedSpace_obj (R : CommRing) : SheafedSpace CommRing :=
{ carrier := Spec.Top_obj R, ..structure_sheaf R }

/--
The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps] def Spec.SheafedSpace_map {R S : CommRing} (f : R ⟶ S) :
  Spec.SheafedSpace_obj S ⟶ Spec.SheafedSpace_obj R :=
{ base := Spec.Top_map f,
  c :=
  { app := λ U, comap f (unop U) ((topological_space.opens.map (Spec.Top_map f)).obj (unop U))
      (λ p, id),
    naturality' := λ U V i, ring_hom.ext $ λ s, subtype.eq $ funext $ λ p, rfl } }

@[simp] lemma Spec.SheafedSpace_map_id {R : CommRing} :
  Spec.SheafedSpace_map (𝟙 R) = 𝟙 (Spec.SheafedSpace_obj R) :=
PresheafedSpace.ext _ _ (Spec.Top_map_id R) $ nat_trans.ext _ _ $ funext $ λ U,
begin
  dsimp,
  erw [PresheafedSpace.id_c_app, comap_id], swap,
    { rw [Spec.Top_map_id, topological_space.opens.map_id_obj_unop] },
  rw [eq_to_hom_op, eq_to_hom_map, eq_to_hom_trans],
  refl,
end

lemma Spec.SheafedSpace_map_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  Spec.SheafedSpace_map (f ≫ g) = Spec.SheafedSpace_map g ≫ Spec.SheafedSpace_map f :=
PresheafedSpace.ext _ _ (Spec.Top_map_comp f g) $ nat_trans.ext _ _ $ funext $ λ U,
begin
  dsimp,
  erw [Top.presheaf.pushforward.comp_inv_app, ← category.assoc, category.comp_id,
    (structure_sheaf T).presheaf.map_id, category.comp_id, comap_comp],
  refl,
end

/--
Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps] def Spec.to_SheafedSpace : CommRingᵒᵖ ⥤ SheafedSpace CommRing :=
{ obj := λ R, Spec.SheafedSpace_obj (unop R),
  map := λ R S f, Spec.SheafedSpace_map f.unop,
  map_id' := λ R, by rw [unop_id, Spec.SheafedSpace_map_id],
  map_comp' := λ R S T f g, by rw [unop_comp, Spec.SheafedSpace_map_comp] }

/--
Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def Spec.to_PresheafedSpace : CommRingᵒᵖ ⥤ PresheafedSpace CommRing :=
  Spec.to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace

@[simp] lemma Spec.to_PresheafedSpace_obj (R : CommRingᵒᵖ) :
  Spec.to_PresheafedSpace.obj R = (Spec.SheafedSpace_obj (unop R)).to_PresheafedSpace := rfl

lemma Spec.to_PresheafedSpace_obj_op (R : CommRing) :
  Spec.to_PresheafedSpace.obj (op R) = (Spec.SheafedSpace_obj R).to_PresheafedSpace := rfl

@[simp] lemma Spec.to_PresheafedSpace_map (R S : CommRingᵒᵖ) (f : R ⟶ S) :
  Spec.to_PresheafedSpace.map f = Spec.SheafedSpace_map f.unop := rfl

lemma Spec.to_PresheafedSpace_map_op (R S : CommRing) (f : R ⟶ S) :
  Spec.to_PresheafedSpace.map f.op = Spec.SheafedSpace_map f := rfl

/--
The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps] def Spec.LocallyRingedSpace_obj (R : CommRing) : LocallyRingedSpace :=
{ local_ring := λ x, @@ring_equiv.local_ring _
    (show local_ring (localization.at_prime _), by apply_instance) _
    (iso.CommRing_iso_to_ring_equiv $ stalk_iso R x).symm,
  .. Spec.SheafedSpace_obj R }

@[elementwise]
lemma stalk_map_to_stalk {R S : CommRing} (f : R ⟶ S) (p : prime_spectrum S) :
  to_stalk R (prime_spectrum.comap f p) ≫
  PresheafedSpace.stalk_map (Spec.SheafedSpace_map f) p =
  f ≫ to_stalk S p :=
begin
  erw [← to_open_germ S ⊤ ⟨p, trivial⟩, ← to_open_germ R ⊤ ⟨prime_spectrum.comap f p, trivial⟩,
    category.assoc, PresheafedSpace.stalk_map_germ (Spec.SheafedSpace_map f) ⊤ ⟨p, trivial⟩,
    Spec.SheafedSpace_map_c_app, to_open_comp_comap_assoc],
  refl
end

/--
Under the isomorphisms `stalk_iso`, the map `stalk_map (Spec.SheafedSpace_map f) p` corresponds
to the induced local ring homomorphism `localization.local_ring_hom`.
-/
@[elementwise]
lemma local_ring_hom_comp_stalk_iso {R S : CommRing} (f : R ⟶ S) (p : prime_spectrum S) :
  (stalk_iso R (prime_spectrum.comap f p)).hom ≫
    @category_struct.comp _ _
      (CommRing.of (localization.at_prime (prime_spectrum.comap f p).as_ideal))
      (CommRing.of (localization.at_prime p.as_ideal)) _
      (localization.local_ring_hom (prime_spectrum.comap f p).as_ideal p.as_ideal f rfl)
      (stalk_iso S p).inv =
  PresheafedSpace.stalk_map (Spec.SheafedSpace_map f) p :=
(stalk_iso R (prime_spectrum.comap f p)).eq_inv_comp.mp $ (stalk_iso S p).comp_inv_eq.mpr $
localization.local_ring_hom_unique _ _ _ _ $ λ x, by
rw [stalk_iso_hom, stalk_iso_inv, comp_apply, comp_apply, localization_to_stalk_of,
  stalk_map_to_stalk_apply, stalk_to_fiber_ring_hom_to_stalk]

/--
The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps] def Spec.LocallyRingedSpace_map {R S : CommRing} (f : R ⟶ S) :
  Spec.LocallyRingedSpace_obj S ⟶ Spec.LocallyRingedSpace_obj R :=
subtype.mk (Spec.SheafedSpace_map f) $ λ p, is_local_ring_hom.mk $ λ a ha,
begin
  -- Here, we are showing that the map on prime spectra induced by `f` is really a morphism of
  -- *locally* ringed spaces, i.e. that the induced map on the stalks is a local ring homomorphism.
  rw ← local_ring_hom_comp_stalk_iso_apply at ha,
  replace ha := (stalk_iso S p).hom.is_unit_map ha,
  rw coe_inv_hom_id at ha,
  replace ha := is_local_ring_hom.map_nonunit _ ha,
  convert ring_hom.is_unit_map (stalk_iso R (prime_spectrum.comap f p)).inv ha,
  rw coe_hom_inv_id,
end

@[simp] lemma Spec.LocallyRingedSpace_map_id (R : CommRing) :
  Spec.LocallyRingedSpace_map (𝟙 R) = 𝟙 (Spec.LocallyRingedSpace_obj R) :=
subtype.ext $ by { rw [Spec.LocallyRingedSpace_map_coe, Spec.SheafedSpace_map_id], refl }

lemma Spec.LocallyRingedSpace_map_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  Spec.LocallyRingedSpace_map (f ≫ g) =
  Spec.LocallyRingedSpace_map g ≫ Spec.LocallyRingedSpace_map f :=
subtype.ext $ by { rw [Spec.LocallyRingedSpace_map_coe, Spec.SheafedSpace_map_comp], refl }

/--
Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps] def Spec.to_LocallyRingedSpace : CommRingᵒᵖ ⥤ LocallyRingedSpace :=
{ obj := λ R, Spec.LocallyRingedSpace_obj (unop R),
  map := λ R S f, Spec.LocallyRingedSpace_map f.unop,
  map_id' := λ R, by rw [unop_id, Spec.LocallyRingedSpace_map_id],
  map_comp' := λ R S T f g, by rw [unop_comp, Spec.LocallyRingedSpace_map_comp] }


end algebraic_geometry
