/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read
-/

import category_theory.adjunction.basic
import category_theory.yoneda

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.
These constructions are used to show uniqueness of adjoints (up to natural isomorphism).

## Tags
adjunction, opposite, uniqueness
-/

open category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

namespace adjunction

/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
def adjoint_of_op_adjoint_op (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  ((h.hom_equiv (opposite.op Y) (opposite.op X)).trans (op_equiv _ _)).symm.trans (op_equiv _ _) }

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
def adjoint_unop_of_adjoint_op (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
adjoint_of_op_adjoint_op F G.unop (h.of_nat_iso_left G.op_unop_iso.symm)

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
def unop_adjoint_of_op_adjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
adjoint_of_op_adjoint_op _ _ (h.of_nat_iso_right F.op_unop_iso.symm)

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
def unop_adjoint_unop_of_adjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
adjoint_unop_of_adjoint_op F.unop G (h.of_nat_iso_right F.op_unop_iso.symm)

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
def op_adjoint_op_of_adjoint (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  (op_equiv _ Y).trans ((h.hom_equiv _ _).symm.trans (op_equiv X (opposite.op _)).symm) }

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
def adjoint_op_of_adjoint_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
(op_adjoint_op_of_adjoint F.unop _ h).of_nat_iso_left F.op_unop_iso

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
def op_adjoint_of_unop_adjoint (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
(op_adjoint_op_of_adjoint _ G.unop h).of_nat_iso_right G.op_unop_iso

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
def adjoint_of_unop_adjoint_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
(adjoint_op_of_adjoint_unop _ _ h).of_nat_iso_right G.op_unop_iso

/--
If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fully_faithful_cancel_right` to show left adjoints are unique.
-/
def left_adjoints_coyoneda_equiv {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G):
  F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
nat_iso.of_components
  (λ X, nat_iso.of_components
    (λ Y, ((adj1.hom_equiv X.unop Y).trans (adj2.hom_equiv X.unop Y).symm).to_iso)
    (by tidy))
  (by tidy)

/-- If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic. -/
def left_adjoint_uniq {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
nat_iso.remove_op (fully_faithful_cancel_right _ (left_adjoints_coyoneda_equiv adj2 adj1))

/-- If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphic. -/
def right_adjoint_uniq {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
nat_iso.remove_op
  (left_adjoint_uniq (op_adjoint_op_of_adjoint _ F adj2) (op_adjoint_op_of_adjoint _ _ adj1))

/--
Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.
-/
def nat_iso_of_left_adjoint_nat_iso {F F' : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') :
  G ≅ G' :=
right_adjoint_uniq adj1 (adj2.of_nat_iso_left l.symm)

/--
Given two adjunctions, if the right adjoints are naturally isomorphic, then so are the left
adjoints.
-/
def nat_iso_of_right_adjoint_nat_iso {F F' : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G') :
  F ≅ F' :=
left_adjoint_uniq adj1 (adj2.of_nat_iso_right r.symm)

end adjunction
