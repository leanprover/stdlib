/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.preserves.shapes.pullbacks

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

## TODO

Dualise and apply to functor categories.

-/

universes v u₁ u₂

namespace category_theory
open category limits

variables {C : Type u₁} {D : Type u₂} [category.{v} C] [category.{v} D]
variables (F : C ⥤ D)

/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
instance preserves_mono {X Y : C} (f : X ⟶ Y) [preserves_limit (cospan f f) F] [mono f] :
  mono (F.map f) :=
begin
  have := is_limit_pullback_cone_map_of_is_limit F _ (pullback_cone.is_limit_mk_id_id f),
  simp_rw [F.map_id] at this,
  apply pullback_cone.mono_of_is_limit_mk_id_id _ this,
end

/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
lemma reflects_mono {X Y : C} (f : X ⟶ Y) [reflects_limit (cospan f f) F] [mono (F.map f)] :
  mono f :=
begin
  have := pullback_cone.is_limit_mk_id_id (F.map f),
  simp_rw [←F.map_id] at this,
  apply pullback_cone.mono_of_is_limit_mk_id_id _ (is_limit_of_is_limit_pullback_cone_map F _ this),
end

end category_theory
