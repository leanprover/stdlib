/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.smooth_functions
import ring_theory.derivation

/-!

# Derivation bundle

In this file we define the derivations at a point of a manifold on the algebra of smooth fuctions.
Moreover, we define the differential of a function in terms of derivations.

The content of this file is not meant to be regarded as an alternative definition to the current
tangent bundle but rather as a purely algebraic theory that provides a purely algebraic definition
of the Lie algebra for a Lie group.

-/

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] (n : with_top ℕ)

open_locale manifold

-- the following two instances prevent poorly understood type class inference timeout problems
instance smooth_functions_algebra : algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := by apply_instance
instance smooth_functions_tower : is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := by apply_instance

/-- Type synonym, introduced to put a different `has_scalar` action on `C^n⟮I, M; 𝕜⟯`
which is defined as `f • r = f(x) * r`. -/
@[nolint unused_arguments] def pointed_smooth_map (x : M) := C^n⟮I, M; 𝕜⟯

localized "notation `C^` n `⟮` I `,` M `;` 𝕜 `⟯⟨` x `⟩` :=
  pointed_smooth_map 𝕜 I M n x" in derivation

variables {𝕜 M}

namespace pointed_smooth_map

instance {x : M} : has_coe_to_fun C^∞⟮I, M; 𝕜⟯⟨x⟩ := times_cont_mdiff_map.has_coe_to_fun
instance {x : M} : comm_ring C^∞⟮I, M; 𝕜⟯⟨x⟩ := smooth_map.comm_ring
instance {x : M} : algebra 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ := smooth_map.algebra
instance {x : M} : inhabited C^∞⟮I, M; 𝕜⟯⟨x⟩ := ⟨0⟩
instance {x : M} : algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ := algebra.id C^∞⟮I, M; 𝕜⟯
instance {x : M} : is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ := is_scalar_tower.right

variable {I}

/-- `smooth_map.eval_ring_hom` gives rise to an algebra structure of `C^∞⟮I, M; 𝕜⟯` on `𝕜`. -/
instance eval_algebra {x : M} : algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 :=
(smooth_map.eval_ring_hom x : C^∞⟮I, M; 𝕜⟯⟨x⟩ →+* 𝕜).to_algebra

/-- With the `eval_algebra` algebra structure evaluation is actually an algebra morphism. -/
def eval (x : M) : C^∞⟮I, M; 𝕜⟯ →ₐ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
algebra.of_id C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

lemma smul_def (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜) : f • k = f x * k := rfl

instance (x : M) : is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 :=
{ smul_assoc := λ k f h, by { simp only [smul_def, algebra.id.smul_eq_mul, smooth_map.coe_smul,
  pi.smul_apply, mul_assoc]} }

end pointed_smooth_map

open_locale derivation

/-- The derivations at a point of a manifold. Some regard this as a possible definition of the
tangent space -/
@[reducible] def point_derivation (x : M) := derivation 𝕜 (C^∞⟮I, M; 𝕜⟯⟨x⟩) 𝕜

section

variables (I) {M} (X Y : derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

/-- Evaluation at a point gives rise to a `C^∞⟮I, M; 𝕜⟯`-linear map between `C^∞⟮I, M; 𝕜⟯` and `𝕜`.
 -/
def smooth_function.eval_at (x : M) : C^∞⟮I, M; 𝕜⟯ →ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
(pointed_smooth_map.eval x).to_linear_map

namespace derivation

variable {I}

/-- The evaluation at a point as a linear map. -/
def eval_at (x : M) : (derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) →ₗ[𝕜] point_derivation I x :=
(smooth_function.eval_at I x).comp_der

lemma eval_at_apply (x : M) : eval_at x X f = (X f) x := rfl

end derivation

variables {I} {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']

/-- The heterogeneous differential as a linear map. Instead of taking a function as an argument this
differential takes `h : f x = y`. It is particularly handy to deal with situations where the points
on where it has to be evaluated are equal but not definitionally equal. -/
def hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) :
  point_derivation I x →ₗ[𝕜] point_derivation I' y :=
{ to_fun := λ v, { to_fun := λ g, v (g.comp f),
    map_add' := λ g g', by rw [smooth_map.add_comp, derivation.map_add],
    map_smul' := λ k g, by rw [smooth_map.smul_comp, derivation.map_smul],
    leibniz' := λ g g', by simp only [derivation.leibniz, smooth_map.mul_comp,
      pointed_smooth_map.smul_def, times_cont_mdiff_map.comp_apply, h] },
  map_smul' := λ k v, rfl,
  map_add' := λ v w, rfl }

/-- The homogeneous differential as a linear map. -/
def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) :
  point_derivation I x →ₗ[𝕜] point_derivation I' (f x) :=
hfdifferential (rfl : f x = f x)

/- Standard notation for the differential. The abbreviation is `MId`. -/
localized "notation `𝒅` := fdifferential" in manifold

/- Standard notation for the differential. The abbreviation is `MId`. -/
localized "notation `𝒅ₕ` := hfdifferential" in manifold

@[simp] lemma apply_fdifferential (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : point_derivation I x)
  (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅f x v g = v (g.comp f) := rfl

@[simp] lemma apply_hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
  (v : point_derivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕh v g = 𝒅f x v g := rfl

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']

@[simp] lemma fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
  𝒅(g.comp f) x = (𝒅g (f x)).comp (𝒅f x) := rfl

end
