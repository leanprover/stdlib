/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.derivation_bundle

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivation for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `left_invariant_derivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

-/

noncomputable theory

open_locale lie_group manifold derivation

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(G : Type*) [topological_space G] [charted_space H G] [monoid G] [has_smooth_mul I G] (g h : G)

-- Generate trivial has_sizeof instance. It prevents weird type class inference timeout problems
local attribute [nolint instance_priority, instance, priority 10000]
private def disable_has_sizeof {α} : has_sizeof α := ⟨λ _, 0⟩

/--
Left-invariant global derivations.

A global derivation is left-invariant if it is equal to its pullback along left multiplication by
an arbitrary element of `G`.
-/
structure left_invariant_derivation extends derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ :=
(left_invariant'' : ∀ g, 𝒅ₕ(smooth_left_mul_one I g) (derivation.eval_at 1 to_derivation) =
  derivation.eval_at g to_derivation)

variables {I G}

namespace left_invariant_derivation

instance : has_coe (left_invariant_derivation I G) (derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯)
:= ⟨λ X, X.to_derivation⟩

instance : has_coe_to_fun (left_invariant_derivation I G) := ⟨_, λ X, X.to_derivation.to_fun⟩

variables
{M : Type*} [topological_space M] [charted_space H M] {x : M} {r : 𝕜}
{X Y : left_invariant_derivation I G} {f f' : C^∞⟮I, G; 𝕜⟯}

lemma to_fun_eq_coe : X.to_fun = ⇑X := rfl
lemma coe_to_linear_map : ⇑(X : C^∞⟮I, G; 𝕜⟯ →ₗ[𝕜] C^∞⟮I, G; 𝕜⟯) = X := rfl
@[simp] lemma to_derivation_eq_coe : X.to_derivation = X := rfl

lemma coe_injective :
  @function.injective (left_invariant_derivation I G) (_ → C^⊤⟮I, G; 𝕜⟯) coe_fn :=
λ X Y h, by { cases X, cases Y, congr', exact derivation.coe_injective h }

@[ext] theorem ext (h : ∀ f, X f = Y f) : X = Y :=
coe_injective $ funext h

variables (X Y f)

lemma coe_derivation :
  ⇑(X : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯) := rfl

lemma coe_derivation_injective : function.injective
  (coe : left_invariant_derivation I G → derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
λ X Y h, by { cases X, cases Y, congr, exact h }

/-- Premature version of the lemma. Prefer using `left_invariant` instead. -/
lemma left_invariant' :
  𝒅ₕ(smooth_left_mul_one I g) (derivation.eval_at (1 : G) ↑X) = derivation.eval_at g ↑X :=
by rw [←to_derivation_eq_coe]; exact left_invariant'' X g

@[simp] lemma map_add : X (f + f') = X f + X f' := derivation.map_add X f f'
@[simp] lemma map_zero : X 0 = 0 := derivation.map_zero X
@[simp] lemma map_neg : X (-f) = -X f := derivation.map_neg X f
@[simp] lemma map_sub : X (f - f') = X f - X f' := derivation.map_sub X f f'
@[simp] lemma map_smul : X (r • f) = r • X f := derivation.map_smul X r f
@[simp] lemma leibniz : X (f * f') = f • X f' + f' • X f := X.leibniz' _ _

instance : has_zero (left_invariant_derivation I G) :=
⟨⟨0, λ g, by simp only [linear_map.map_zero, derivation.coe_zero]⟩⟩

instance : inhabited (left_invariant_derivation I G) := ⟨0⟩

instance : has_add (left_invariant_derivation I G) :=
{ add := λ X Y, ⟨X + Y, λ g, by simp only [linear_map.map_add, derivation.coe_add,
    left_invariant', pi.add_apply]⟩ }

instance : has_neg (left_invariant_derivation I G) :=
{ neg := λ X, ⟨-X, λ g, by simp only [linear_map.map_neg, derivation.coe_neg, left_invariant',
    pi.neg_apply]⟩ }

instance : has_sub (left_invariant_derivation I G) :=
{ sub := λ X Y, ⟨X - Y, λ g, by simp only [linear_map.map_sub, derivation.coe_sub,
    left_invariant', pi.sub_apply]⟩ }

@[simp] lemma coe_add : ⇑(X + Y) = X + Y := rfl
@[simp] lemma coe_zero : ⇑(0 : left_invariant_derivation I G) = 0 := rfl
@[simp] lemma coe_neg : ⇑(-X) = -X := rfl
@[simp] lemma coe_sub : ⇑(X - Y) = X - Y := rfl
@[simp, norm_cast] lemma lift_add :
  (↑(X + Y) : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y := rfl
@[simp, norm_cast] lemma lift_zero :
  (↑(0 : left_invariant_derivation I G) : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0 := rfl

instance : add_comm_group (left_invariant_derivation I G) :=
coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub

instance : has_scalar 𝕜 (left_invariant_derivation I G) :=
{ smul := λ r X, ⟨r • X, λ g, by simp only [derivation.Rsmul_apply, algebra.id.smul_eq_mul,
            mul_eq_mul_left_iff, linear_map.map_smul, left_invariant']⟩ }

variables (r X)

@[simp] lemma coe_smul : ⇑(r • X) = r • X := rfl
@[simp] lemma lift_smul (k : 𝕜) : (↑(k • X) : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = k • X := rfl

variables (I G)

/-- The coercion to function is a monoid homomorphism. -/
@[simps] def coe_fn_add_monoid_hom :
  (left_invariant_derivation I G) →+ (C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯) :=
⟨λ X, X.to_derivation.to_fun, coe_zero, coe_add⟩

variables {I G}

instance : module 𝕜 (left_invariant_derivation I G) :=
coe_injective.module _ (coe_fn_add_monoid_hom I G) coe_smul

/-- Evaluation at a point for left invariant derivation. Same thing as for generic global
derivations (`derivation.eval_at`). -/
def eval_at : (left_invariant_derivation I G) →ₗ[𝕜] (point_derivation I g) :=
{ to_fun := λ X, derivation.eval_at g ↑X,
  map_add' := λ X Y, rfl,
  map_smul' := λ k X, rfl }

lemma eval_at_apply : eval_at g X f = (X f) g := rfl

@[simp] lemma eval_at_coe : derivation.eval_at g ↑X = eval_at g X := rfl

lemma left_invariant : 𝒅ₕ(smooth_left_mul_one I g) (eval_at (1 : G) X) = eval_at g X :=
(X.left_invariant'' g)

lemma eval_at_mul : eval_at (g * h) X = 𝒅ₕ(L_apply I g h) (eval_at h X) :=
by { ext f, rw [←left_invariant, apply_hfdifferential, apply_hfdifferential, L_mul,
  fdifferential_comp, apply_fdifferential, linear_map.comp_apply, apply_fdifferential,
  ←apply_hfdifferential, left_invariant] }

lemma comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g)) :=
by ext h; rw [times_cont_mdiff_map.comp_apply, L_apply, ←eval_at_apply, eval_at_mul,
  apply_hfdifferential, apply_fdifferential, eval_at_apply]

instance : has_bracket (left_invariant_derivation I G) (left_invariant_derivation I G) :=
{ bracket := λ X Y, ⟨⁅(X : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, λ g, begin
    ext f,
    have hX := derivation.congr_fun (left_invariant' g X) (Y f),
    have hY := derivation.congr_fun (left_invariant' g Y) (X f),
    rw [apply_hfdifferential, apply_fdifferential, derivation.eval_at_apply] at hX hY ⊢,
    rw comp_L at hX hY,
    rw [derivation.commutator_apply, smooth_map.coe_sub, pi.sub_apply, coe_derivation],
    rw coe_derivation at hX hY ⊢,
    rw [hX, hY],
    refl
  end⟩ }

@[simp] lemma commutator_coe_derivation :
  ⇑⁅X, Y⁆ = (⁅(X : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆ :
  derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) := rfl

lemma commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) := rfl

instance : lie_ring (left_invariant_derivation I G) :=
{ add_lie := λ X Y Z, by { ext1, simp only [commutator_apply, coe_add, pi.add_apply,
              linear_map.map_add, left_invariant_derivation.map_add], ring },
  lie_add := λ X Y Z, by { ext1, simp only [commutator_apply, coe_add, pi.add_apply,
              linear_map.map_add, left_invariant_derivation.map_add], ring },
  lie_self := λ X, by { ext1, simp only [commutator_apply, sub_self], refl },
  leibniz_lie := λ X Y Z, by { ext1, simp only [commutator_apply, coe_add, coe_sub, map_sub,
              pi.add_apply], ring, } }

instance : lie_algebra 𝕜 (left_invariant_derivation I G) :=
{ lie_smul := λ r Y Z, by { ext1, simp only [commutator_apply, map_smul, smul_sub, coe_smul,
              pi.smul_apply] } }

end left_invariant_derivation
