
/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/

import data.qpf.indexed.basic

/-!
# The quotients of QPFs is itself a QPF
The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `iqpf`
-/

universes u

namespace iqpf

variables {I J : Type u}
variables {F : fam I ⥤ fam J}

section repr

variables [q : iqpf F]
variables {G : fam I ⥤ fam J}
variable  {FG_abs  : F ⟶ G}
variable  {FG_repr : Π α, G.obj α ⟶ F.obj α}

/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `iqpf` instances by transporting them across a
natural transformations -/
def quotient_qpf
    (FG_abs_repr : Π α, FG_repr α ≫ FG_abs.app α = 𝟙 _) : iqpf G :=
{ P := q.P,
  abs := λ α, abs F α ≫ FG_abs.app _,
  repr := λ α, FG_repr α ≫ repr F α,
  abs_repr := λ α, by simp [abs_repr,FG_abs_repr],
  abs_map := λ α β f, by simp [abs_map_assoc] }

end repr

section rel

open fam category_theory

variables (R : ∀ α, Pred (F.obj α ⊗ F.obj α))

/-- Functorial quotient type -/
def quot1_obj (α : fam I) : fam J :=
quot (R α)

variables [q : iqpf F]
variables (Hfunc : ∀ ⦃X α β⦄ (x : X ⟶ F.obj α ⊗ F.obj α) (f : α ⟶ β),
  x ⊨ R α → x ≫ (F.map f ⊗ F.map f) ⊨ R β)

include Hfunc

/-- `map` of the `quot1` functor -/
def quot1_map ⦃α β⦄ (f : α ⟶ β) : quot1_obj.{u} R α ⟶ quot1_obj.{u} R β :=
fam.quot.lift _ (F.map f ≫ fam.quot.mk _) $
begin
  intros i a h₀,
  refine fam.quot.sound'' (a ≫ fam.prod.fst ≫ F.map f) (a ≫ fam.prod.snd ≫ F.map f) _ _ _,
  { simp only [diag_map_comp, diag_map_fst_snd_comp, Hfunc, h₀], },
  { simp only [category.assoc] },
  { simp only [category.assoc] },
end

/-- `quot1` is a functor if `R` is well-behaved (i.e. `Hfunc`) -/
@[simps]
def quot1 : fam I ⥤ fam J :=
{ obj := quot1_obj R,
  map := quot1_map R Hfunc,
  map_id' :=
    by intros; apply quot.lift_ext;
       simp only [quot1_map, quot.mk_lift_, category.id_comp, category_theory.functor.map_id];
       erw category_theory.category.comp_id,
  map_comp' :=
    by intros; apply quot.lift_ext;
       simp only [quot1_map, quot.lift_comp, quot.mk_lift_, category.assoc, functor.map_comp]
  }

/-- Natural transformation taking the quotient of `F` by `R` -/
@[simps]
def quot1.MK : F ⟶ quot1 R Hfunc :=
{ app := λ X, fam.quot.mk _,
  naturality' := by intros; simp [quot1_map] }

/-- `quot1` is a qpf -/
noncomputable def rel_quot : iqpf (quot1 R Hfunc)  :=
@quotient_qpf _ _ F q (quot1 R Hfunc) (quot1.MK _ Hfunc) (λ x, fam.quot.out _)
  (by intros; simp; refl)

end rel

end iqpf
