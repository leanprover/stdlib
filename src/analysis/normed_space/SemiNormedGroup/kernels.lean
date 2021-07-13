/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin, Scott Morrison
-/
import analysis.normed_space.SemiNormedGroup
import analysis.normed_space.normed_group_quotient
import category_theory.limits.shapes.kernels

/-!
# Cokernels in SemiNormedGroup₁ and SemiNormedGroup

We show that `SemiNormedGroup₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGroup` has cokernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGroup` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGroup` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/

open category_theory
open category_theory.limits

namespace SemiNormedGroup₁

noncomputable theory

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernel_cocone {X Y : SemiNormedGroup₁} (f : X ⟶ Y) : cofork f 0 :=
cofork.of_π
  (@SemiNormedGroup₁.mk_hom
    _ (SemiNormedGroup.of (quotient_add_group.quotient (normed_group_hom.range f.1)))
    f.1.range.normed_mk
    (normed_group_hom.is_quotient_quotient _).norm_le)
  begin
    ext,
    simp only [comp_apply, limits.zero_comp, normed_group_hom.zero_apply,
      SemiNormedGroup₁.mk_hom_apply, SemiNormedGroup₁.zero_apply, ←normed_group_hom.mem_ker,
      f.1.range.ker_normed_mk, f.1.mem_range],
    use x,
    refl,
  end

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernel_lift {X Y : SemiNormedGroup₁} (f : X ⟶ Y) (s : cokernel_cofork f) :
  (cokernel_cocone f).X ⟶ s.X :=
begin
  fsplit,
  -- The lift itself:
  { apply normed_group_hom.lift _ s.π.1,
    rintro _ ⟨b, rfl⟩,
    change (f ≫ s.π) b = 0,
    simp, },
  -- The lift has norm at most one:
  exact normed_group_hom.lift_norm_noninc _ _ _ s.π.2,
end

instance : has_cokernels SemiNormedGroup₁ :=
{ has_colimit := λ X Y f, has_colimit.mk
  { cocone := cokernel_cocone f,
    is_colimit := is_colimit_aux _
      (cokernel_lift f)
      (λ s, begin
        ext,
        apply normed_group_hom.lift_mk f.1.range,
        rintro _ ⟨b, rfl⟩,
        change (f ≫ s.π) b = 0,
        simp,
      end)
      (λ s m w, subtype.eq
        (normed_group_hom.lift_unique f.1.range _ _ _ (congr_arg subtype.val w : _))), } }

end SemiNormedGroup₁

namespace SemiNormedGroup
-- PROJECT: can we reuse the work to construct cokernels in `SemiNormedGroup₁` here?
-- I don't see a way to do this that is less work than just repeating the relevant parts.

instance : has_cokernels SemiNormedGroup :=
{ has_colimit := λ X Y f, has_colimit.mk
  { cocone := @cofork.of_π _ _ _ _ _ _
      (SemiNormedGroup.of (quotient_add_group.quotient (normed_group_hom.range f)))
      f.range.normed_mk
      begin
        ext,
        simp only [comp_apply, limits.zero_comp, normed_group_hom.zero_apply,
          ←normed_group_hom.mem_ker, f.range.ker_normed_mk, f.mem_range, exists_apply_eq_apply],
      end,
    is_colimit := is_colimit_aux _
      (λ s, begin
        apply normed_group_hom.lift _ s.π,
        rintro _ ⟨b, rfl⟩,
        change (f ≫ s.π) b = 0,
        simp,
      end)
      (λ s, begin
        ext,
        apply normed_group_hom.lift_mk f.range,
        rintro _ ⟨b, rfl⟩,
        change (f ≫ s.π) b = 0,
        simp,
      end)
      (λ s m w, normed_group_hom.lift_unique f.range _ _ _ w), } }

end SemiNormedGroup
