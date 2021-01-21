/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel
-/
import data.complex.basic
import data.matrix.notation
import field_theory.tower

/-!
# Complex number as a vector space over `ℝ`

This file contains three instances:
* `ℂ` is an `ℝ` algebra;
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimesional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines three linear maps:

* `complex.linear_map.re`;
* `complex.linear_map.im`;
* `complex.linear_map.of_real`.

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as `ℝ`-linear maps.
-/
noncomputable theory

namespace complex

instance algebra_over_reals : algebra ℝ ℂ := (complex.of_real).to_algebra

@[simp] lemma coe_algebra_map : ⇑(algebra_map ℝ ℂ) = complex.of_real := rfl

@[simp] lemma re_smul (a : ℝ) (z : ℂ) : re (a • z) = a * re z := by simp [algebra.smul_def]

@[simp] lemma im_smul (a : ℝ) (z : ℂ) : im (a • z) = a * im z := by simp [algebra.smul_def]

open submodule finite_dimensional

lemma is_basis_one_I : is_basis ℝ ![1, I] :=
begin
  refine ⟨linear_independent_fin2.2 ⟨I_ne_zero, λ a, mt (congr_arg re) $ by simp⟩,
    eq_top_iff'.2 $ λ z, _⟩,
  suffices : ∃ a b, z = a • I + b • 1,
    by simpa [mem_span_insert, mem_span_singleton, -set.singleton_one],
  use [z.im, z.re],
  simp [algebra.smul_def, add_comm]
end

instance : finite_dimensional ℝ ℂ := of_fintype_basis is_basis_one_I

@[simp] lemma findim_real_complex : finite_dimensional.findim ℝ ℂ = 2 :=
by rw [findim_eq_card_basis is_basis_one_I, fintype.card_fin]

@[simp] lemma dim_real_complex : vector_space.dim ℝ ℂ = 2 :=
by simp [← findim_eq_dim, findim_real_complex]

lemma {u} dim_real_complex' : cardinal.lift.{0 u} (vector_space.dim ℝ ℂ) = 2 :=
by simp [← findim_eq_dim, findim_real_complex, bit0]

end complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
@[priority 900]
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
restrict_scalars.semimodule ℝ ℂ E

instance module.real_complex_tower (E : Type*) [add_comm_group E] [module ℂ E] :
  is_scalar_tower ℝ ℂ E :=
restrict_scalars.is_scalar_tower ℝ ℂ E

@[priority 100]
instance finite_dimensional.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E]
  [finite_dimensional ℂ E] : finite_dimensional ℝ E :=
finite_dimensional.trans ℝ ℂ E

lemma dim_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  vector_space.dim ℝ E = 2 * vector_space.dim ℂ E :=
cardinal.lift_inj.1 $
  by { rw [← dim_mul_dim' ℝ ℂ E, complex.dim_real_complex], simp [bit0] }

lemma findim_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  finite_dimensional.findim ℝ E = 2 * finite_dimensional.findim ℂ E :=
by rw [← finite_dimensional.findim_mul_findim ℝ ℂ E, complex.findim_real_complex]

namespace complex

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def linear_map.re : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  map_add' := add_re,
  map_smul' := re_smul }

@[simp] lemma linear_map.coe_re : ⇑linear_map.re = re := rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def linear_map.im : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  map_add' := add_im,
  map_smul' := im_smul }

@[simp] lemma linear_map.coe_im : ⇑linear_map.im = im := rfl

/-- Linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def linear_map.of_real : ℝ →ₗ[ℝ] ℂ :=
{ to_fun := coe,
  map_add' := of_real_add,
  map_smul' := λc x, by simp [algebra.smul_def] }

@[simp] lemma linear_map.coe_of_real : ⇑linear_map.of_real = coe := rfl

end complex
