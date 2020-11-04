/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction
import category_theory.elements
import category_theory.limits.functor_category
import category_theory.limits.preserves.limits
import category_theory.limits.shapes.terminal
import category_theory.limits.types

/-!
# Colimit of representables

This file constructs an adjunction `yoneda_adjunction` between `(Cᵒᵖ ⥤ Type u)` and `ℰ` given a
functor `A : C ⥤ ℰ`, where the right adjoint sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)` (provided `ℰ`
has colimits).

This adjunction is used to show that every presheaf is a colimit of representables.

Further, the left adjoint `colimit_adj.extend_along_yoneda : (Cᵒᵖ ⥤ Type u) ⥤ ℰ` satisfies
`yoneda ⋙ L ≅ A`, that is, an extension of `A : C ⥤ ℰ` to `(Cᵒᵖ ⥤ Type u) ⥤ ℰ` through
`yoneda : C ⥤ Cᵒᵖ ⥤ Type u`. It is the left Kan extension of `A` along the yoneda embedding,
sometimes known as the Yoneda extension.

`unique_extension_along_yoneda` shows `extend_along_yoneda` is unique amongst cocontinuous functors
with this property, establishing the presheaf category as the free cocompletion of a small category.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

namespace category_theory

noncomputable theory

open category limits
universes u₁ u₂

variables {C : Type u₁} [small_category C]
variables {ℰ : Type u₂} [category.{u₁} ℰ]
variable (A : C ⥤ ℰ)

namespace colimit_adj

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps {rhs_md := semireducible}]
def restricted_yoneda : ℰ ⥤ (Cᵒᵖ ⥤ Type u₁) :=
yoneda ⋙ (whiskering_left _ _ (Type u₁)).obj (functor.op A)

/--
The functor `restricted_yoneda` is isomorphic to the identity functor when evaluated at the yoneda
embedding.
-/
def restricted_yoneda_yoneda : restricted_yoneda (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ≅ 𝟭 _ :=
nat_iso.of_components
(λ P, nat_iso.of_components (λ X, yoneda_sections_small X.unop _)
  (λ X Y f, funext $ λ x,
  begin
    dsimp,
    rw ← functor_to_types.naturality _ _ x f (𝟙 _),
    dsimp,
    simp,
  end))
(λ _ _ _, rfl)

/--
(Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimit_adj.restricted_yoneda`.
It is shown in `restrict_yoneda_hom_equiv_natural` that this is a natural bijection.
-/
def restrict_yoneda_hom_equiv (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ)
  {c : cocone ((category_of_elements.π P).left_op ⋙ A)} (t : is_colimit c) :
  (c.X ⟶ E) ≃ (P ⟶ (restricted_yoneda A).obj E) :=
(t.hom_iso' E).to_equiv.trans
{ to_fun := λ k,
  { app := λ c p, k.1 (opposite.op ⟨_, p⟩),
    naturality' := λ c c' f, funext $ λ p,
      (k.2 (has_hom.hom.op ⟨f, rfl⟩ :
              (opposite.op ⟨c', P.map f p⟩ : P.elementsᵒᵖ) ⟶ opposite.op ⟨c, p⟩)).symm },
  inv_fun := λ τ,
  { val := λ p, τ.app p.unop.1 p.unop.2,
    property := λ p p' f,
    begin
      simp_rw [← f.unop.2],
      apply (congr_fun (τ.naturality f.unop.1) p'.unop.2).symm,
    end },
  left_inv :=
  begin
    rintro ⟨k₁, k₂⟩,
    ext,
    dsimp,
    congr' 1,
    simp,
  end,
  right_inv :=
  begin
    rintro ⟨_, _⟩,
    refl,
  end }

/--
(Implementation). Show that the bijection in `restrict_yoneda_hom_equiv` is natural (on the right).
-/
lemma restrict_yoneda_hom_equiv_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂)
  {c : cocone _} (t : is_colimit c) (k : c.X ⟶ E₁) :
restrict_yoneda_hom_equiv A P E₂ t (k ≫ g) =
  restrict_yoneda_hom_equiv A P E₁ t k ≫ (restricted_yoneda A).map g :=
begin
  ext _ X p,
  apply (assoc _ _ _).symm,
end

variables [has_colimits ℰ]

/--
The left adjoint to the functor `restricted_yoneda` (shown in `yoneda_adjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `is_extension_along_yoneda`), in particular
it is the left Kan extension of `A` through the yoneda embedding.
-/
def extend_along_yoneda : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
adjunction.left_adjoint_of_equiv
  (λ P E, restrict_yoneda_hom_equiv A P E (colimit.is_colimit _))
  (λ P E E' g, restrict_yoneda_hom_equiv_natural A P E E' g _)

@[simp]
lemma extend_along_yoneda_obj (P : Cᵒᵖ ⥤ Type u₁) : (extend_along_yoneda A).obj P =
colimit ((category_of_elements.π P).left_op ⋙ A) := rfl

/--
Show `extend_along_yoneda` is left adjoint to `restricted_yoneda`.

The construction of [MM92], Chapter I, Section 5, Theorem 2.
-/
def yoneda_adjunction : extend_along_yoneda A ⊣ restricted_yoneda A :=
adjunction.adjunction_of_equiv_left _ _

/--
The initial object in the category of elements for a representable functor. In `is_initial` it is
shown that this is initial.
-/
def elements.initial (A : C) : (yoneda.obj A).elements :=
⟨opposite.op A, 𝟙 _⟩

/--
Show that `elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def is_initial (A : C) : is_initial (elements.initial A) :=
{ desc := λ s, ⟨s.X.2.op, comp_id _⟩,
  uniq' := λ s m w,
  begin
    simp_rw ← m.2,
    dsimp [elements.initial],
    simp,
  end }

/--
`extend_along_yoneda A` is an extension of `A` to the presheaf category along the yoneda embedding.
`unique_extension_along_yoneda` shows it is unique among functors preserving colimits with this
property (up to isomorphism).

The first part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 1 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
def is_extension_along_yoneda : (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ⋙ extend_along_yoneda A ≅ A :=
nat_iso.of_components
(λ X, (colimit.is_colimit _).cocone_point_unique_up_to_iso
      (colimit_of_diagram_terminal (terminal_op_of_initial (is_initial _)) _))
begin
  intros X Y f,
  change (colimit.desc _ ⟨_, _⟩ ≫ colimit.desc _ _) = colimit.desc _ _ ≫ _,
  apply colimit.hom_ext,
  intro j,
  rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc],
  change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _,
  rw [comp_id, colimit.ι_desc],
  dsimp,
  rw ← A.map_comp,
  congr' 1, refl
end

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
instance : preserves_colimits (extend_along_yoneda A) :=
(yoneda_adjunction A).left_adjoint_preserves_colimits

end colimit_adj

open colimit_adj

/--
Since `extend_along_yoneda A` is adjoint to `restricted_yoneda A`, if we use `A = yoneda`
then `restricted_yoneda A` is isomorphic to the identity, and so `extend_along_yoneda A` is as well.
-/
def extend_along_yoneda_yoneda : extend_along_yoneda (yoneda : C ⥤ _) ≅ 𝟭 _ :=
adjunction.nat_iso_of_right_adjoint_nat_iso
  (yoneda_adjunction _)
  adjunction.id
  restricted_yoneda_yoneda

/--
A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`cocone_of_representable` gives a cocone for this functor which is a colimit and has point `P`.
-/
-- Maybe this should be reducible or an abbreviation?
def functor_to_representables (P : Cᵒᵖ ⥤ Type u₁) :
  (P.elements)ᵒᵖ ⥤ Cᵒᵖ ⥤ Type u₁ :=
(category_of_elements.π P).left_op ⋙ yoneda

/--
This is a cocone with point `P` for the functor `functor_to_representables P`. It is shown in
`colimit_of_representable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
def cocone_of_representable (P : Cᵒᵖ ⥤ Type u₁) :
  cocone (functor_to_representables P) :=
cocone.extend (colimit.cocone _) (extend_along_yoneda_yoneda.hom.app P)

@[simp] lemma cocone_of_representable_X (P : Cᵒᵖ ⥤ Type u₁) :
  (cocone_of_representable P).X = P :=
rfl

/-- An explicit formula for the legs of the cocone `cocone_of_representable`. -/
-- Marking this as a simp lemma seems to make things more awkward.
lemma cocone_of_representable_ι_app (P : Cᵒᵖ ⥤ Type u₁) (j : (P.elements)ᵒᵖ):
  (cocone_of_representable P).ι.app j = (yoneda_sections_small _ _).inv j.unop.2 :=
colimit.ι_desc _ _

/-- The legs of the cocone `cocone_of_representable` are natural in the choice of presheaf. -/
lemma cocone_of_representable_naturality {P₁ P₂ : Cᵒᵖ ⥤ Type u₁} (α : P₁ ⟶ P₂)
  (j : (P₁.elements)ᵒᵖ) :
  (cocone_of_representable P₁).ι.app j ≫ α =
    (cocone_of_representable P₂).ι.app ((category_of_elements.map α).op.obj j) :=
begin
  ext T f,
  simpa [cocone_of_representable_ι_app] using functor_to_types.naturality _ _ α f.op _,
end

/--
The cocone with point `P` given by `the_cocone` is a colimit: that is, we have exhibited an
arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
def colimit_of_representable (P : Cᵒᵖ ⥤ Type u₁) : is_colimit (cocone_of_representable P) :=
begin
  apply is_colimit.of_point_iso (colimit.is_colimit (functor_to_representables P)),
  change is_iso (colimit.desc _ (cocone.extend _ _)),
  rw [colimit.desc_extend, colimit.desc_cocone],
  apply_instance,
end

/--
Given two functors L₁ and L₂ which preserve colimits, if they agree when restricted to the
representable presheaves then they agree everywhere.
-/
def nat_iso_of_nat_iso_on_representables (L₁ L₂ : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ)
  [preserves_colimits L₁] [preserves_colimits L₂]
  (h : yoneda ⋙ L₁ ≅ yoneda ⋙ L₂) : L₁ ≅ L₂ :=
begin
  apply nat_iso.of_components _ _,
  { intro P,
    refine (is_colimit_of_preserves L₁ (colimit_of_representable P)).cocone_points_iso_of_nat_iso
           (is_colimit_of_preserves L₂ (colimit_of_representable P)) _,
    apply functor.associator _ _ _ ≪≫ _,
    exact iso_whisker_left (category_of_elements.π P).left_op h },
  { intros P₁ P₂ f,
    apply (is_colimit_of_preserves L₁ (colimit_of_representable P₁)).hom_ext,
    intro j,
    dsimp only [id.def, is_colimit.cocone_points_iso_of_nat_iso_hom, iso_whisker_left_hom],
    have :
      (L₁.map_cocone (cocone_of_representable P₁)).ι.app j ≫ L₁.map f =
      (L₁.map_cocone (cocone_of_representable P₂)).ι.app ((category_of_elements.map f).op.obj j),
    { dsimp,
      rw [← L₁.map_comp, cocone_of_representable_naturality],
      refl },
    rw [reassoc_of this, is_colimit.ι_map_assoc, is_colimit.ι_map],
    dsimp,
    rw [← L₂.map_comp, cocone_of_representable_naturality],
    refl }
end

variable [has_colimits ℰ]

/--
Show that `extend_along_yoneda` is the unique colimit-preserving functor which extends `A` to
the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
def unique_extension_along_yoneda (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (hL : yoneda ⋙ L ≅ A)
  [preserves_colimits L] :
  L ≅ extend_along_yoneda A :=
nat_iso_of_nat_iso_on_representables _ _ (hL ≪≫ (is_extension_along_yoneda _).symm)

end category_theory
