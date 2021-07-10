/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
import analysis.complex.circle

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `linear_isometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/
noncomputable theory

open complex

local notation `|` x `|` := complex.abs x

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. This is an auxiliary construction; use `rotation`, which has more structure, by
preference. -/
def rotation_aux (a : circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
{ to_fun := λ z, a * z,
  map_add' := mul_add ↑a,
  map_smul' := λ t z, by { simp only [smul_coe], ring },
  inv_fun := λ z, a⁻¹ * z,
  left_inv := λ z, by { field_simp [nonzero_of_mem_circle], ring },
  right_inv := λ z, by { field_simp [nonzero_of_mem_circle], ring },
  norm_map' := by simp }

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. -/
def rotation : circle →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
{ to_fun := rotation_aux,
  map_one' := by { ext1, simp [rotation_aux] },
  map_mul' := λ a b, by { ext1, simp [rotation_aux] } }

@[simp] lemma rotation_apply (a : circle) (z : ℂ) : rotation a z = a * z := rfl

lemma linear_isometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
  (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re :=
by simpa [ext_iff, add_re, add_im, conj_re, conj_im, ←two_mul,
         (show (2 : ℝ) ≠ 0, by simp [two_ne_zero'])] using (h₃ z).symm

lemma linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
  (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) :
  (f z).im = z.im ∨ (f z).im = -z.im :=
begin
  have h₁ := f.norm_map z,
  simp only [complex.abs, norm_eq_abs] at h₁,
  rwa [real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁,
end

lemma linear_isometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
  z + conj z = f z + conj (f z) :=
begin
  have : ∥f z - 1∥ = ∥z - 1∥ := by rw [← f.norm_map (z - 1), f.map_sub, h],
  apply_fun λ x, x ^ 2 at this,
  simp only [norm_eq_abs, ←norm_sq_eq_abs] at this,
  rw [←of_real_inj, ←mul_conj, ←mul_conj] at this,
  rw [conj.map_sub, conj.map_sub] at this,
  simp only [sub_mul, mul_sub, one_mul, mul_one] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs, linear_isometry.norm_map] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs] at this,
  simp only [sub_sub, sub_right_inj, mul_one, of_real_pow, ring_hom.map_one, norm_eq_abs] at this,
  simp only [add_sub, sub_left_inj] at this,
  rw [add_comm, ←this, add_comm],
end

lemma linear_isometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re :=
begin
  apply linear_isometry.re_apply_eq_re_of_add_conj_eq,
  intro z,
  apply linear_isometry.im_apply_eq_im h,
end

lemma linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) :
  f = linear_isometry_equiv.refl ℝ ℂ ∨ f = conj_lie :=
begin
  have h0 : f I = I ∨ f I = -I,
  { have : |f I| = 1 := by simpa using f.norm_map complex.I,
    simp only [ext_iff, ←and_or_distrib_left, neg_re, I_re, neg_im, neg_zero],
    split,
    { rw ←I_re,
      exact @linear_isometry.re_apply_eq_re f.to_linear_isometry h I, },
    { apply @linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.to_linear_isometry,
      intro z, rw @linear_isometry.re_apply_eq_re f.to_linear_isometry h } },
  refine h0.imp (λ h' : f I = I, _) (λ h' : f I = -I, _);
  { apply linear_isometry_equiv.to_linear_equiv_injective,
    apply complex.basis_one_I.ext',
    intros i,
    fin_cases i; simp [h, h'] }
end

lemma linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
  ∃ a : circle, f = rotation a ∨ f = conj_lie.trans (rotation a) :=
begin
  let a : circle := ⟨f 1, by simpa using f.norm_map 1⟩,
  use a,
  have : (f.trans (rotation a).symm) 1 = 1,
  { simpa using rotation_apply a⁻¹ (f 1) },
  refine (linear_isometry_complex_aux this).imp (λ h₁, _) (λ h₂, _),
  { simpa using eq_mul_of_inv_mul_eq h₁ },
  { exact eq_mul_of_inv_mul_eq h₂ }
end
