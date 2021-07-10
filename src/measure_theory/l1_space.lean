/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import measure_theory.lp_space


/-!
# Integrable functions and `L¹` space

In the first part of this file, the predicate `integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `mem_ℒp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `mem_ℒp 1`

In the second part, we establish an API between `integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `measure_space` and `β` is a `normed_group`
  with a `second_countable_topology`. `f : α →ₘ β` is a "function" in `L¹`. In comments, `[f]` is
  also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `measure_space` and `β` a `normed_group`.
  Then `has_finite_integral f` means `(∫⁻ a, nnnorm (f a)) < ∞`.

* If `β` is moreover a `measurable_space` then `f` is called `integrable` if
  `f` is `measurable` and `has_finite_integral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`integrable.induction` in the file `set_integral`.

## Tags

integrable, function space, l1

-/

noncomputable theory
open_locale classical topological_space big_operators ennreal measure_theory nnreal

open set filter topological_space ennreal emetric measure_theory

variables {α β γ δ : Type*} [measurable_space α] {μ ν : measure α}
variables [normed_group β]
variables [normed_group γ]

namespace measure_theory

/-! ### Some results about the Lebesgue integral involving a normed group -/

lemma lintegral_nnnorm_eq_lintegral_edist (f : α → β) :
  ∫⁻ a, nnnorm (f a) ∂μ = ∫⁻ a, edist (f a) 0 ∂μ :=
by simp only [edist_eq_coe_nnnorm]

lemma lintegral_norm_eq_lintegral_edist (f : α → β) :
  ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ = ∫⁻ a, edist (f a) 0 ∂μ :=
by simp only [of_real_norm_eq_coe_nnnorm, edist_eq_coe_nnnorm]

lemma lintegral_edist_triangle [second_countable_topology β] [measurable_space β]
  [opens_measurable_space β] {f g h : α → β}
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) (hh : ae_measurable h μ) :
  ∫⁻ a, edist (f a) (g a) ∂μ ≤ ∫⁻ a, edist (f a) (h a) ∂μ + ∫⁻ a, edist (g a) (h a) ∂μ :=
begin
  rw ← lintegral_add' (hf.edist hh) (hg.edist hh),
  refine lintegral_mono (λ a, _),
  apply edist_triangle_right
end

lemma lintegral_nnnorm_zero : ∫⁻ a : α, nnnorm (0 : β) ∂μ = 0 := by simp

lemma lintegral_nnnorm_add [measurable_space β] [opens_measurable_space β]
  [measurable_space γ] [opens_measurable_space γ]
  {f : α → β} {g : α → γ} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ = ∫⁻ a, nnnorm (f a) ∂μ + ∫⁻ a, nnnorm (g a) ∂μ :=
lintegral_add' hf.ennnorm hg.ennnorm

lemma lintegral_nnnorm_neg {f : α → β} :
  ∫⁻ a, nnnorm ((-f) a) ∂μ = ∫⁻ a, nnnorm (f a) ∂μ :=
by simp only [pi.neg_apply, nnnorm_neg]

/-! ### The predicate `has_finite_integral` -/

/-- `has_finite_integral f μ` means that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `has_finite_integral f` means `has_finite_integral f volume`. -/
def has_finite_integral (f : α → β) (μ : measure α . volume_tac) : Prop :=
∫⁻ a, nnnorm (f a) ∂μ < ∞

lemma has_finite_integral_iff_norm (f : α → β) :
  has_finite_integral f μ ↔ ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ < ∞ :=
by simp only [has_finite_integral, of_real_norm_eq_coe_nnnorm]

lemma has_finite_integral_iff_edist (f : α → β) :
  has_finite_integral f μ ↔ ∫⁻ a, edist (f a) 0 ∂μ < ∞ :=
by simp only [has_finite_integral_iff_norm, edist_dist, dist_zero_right]

lemma has_finite_integral_iff_of_real {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
  has_finite_integral f μ ↔ ∫⁻ a, ennreal.of_real (f a) ∂μ < ∞ :=
have lintegral_eq : ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ = ∫⁻ a, ennreal.of_real (f a) ∂μ :=
begin
  refine lintegral_congr_ae (h.mono $ λ a h, _),
  rwa [real.norm_eq_abs, abs_of_nonneg]
end,
by rw [has_finite_integral_iff_norm, lintegral_eq]

lemma has_finite_integral_iff_of_nnreal {f : α → ℝ≥0} :
  has_finite_integral (λ x, (f x : ℝ)) μ ↔ ∫⁻ a, f a ∂μ < ∞ :=
by simp [has_finite_integral_iff_norm]

lemma has_finite_integral.mono {f : α → β} {g : α → γ} (hg : has_finite_integral g μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) : has_finite_integral f μ :=
begin
  simp only [has_finite_integral_iff_norm] at *,
  calc ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ ≤ ∫⁻ (a : α), (ennreal.of_real ∥g a∥) ∂μ :
    lintegral_mono_ae (h.mono $ assume a h, of_real_le_of_real h)
    ... < ∞ : hg
end

lemma has_finite_integral.mono' {f : α → β} {g : α → ℝ} (hg : has_finite_integral g μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ g a) : has_finite_integral f μ :=
hg.mono $ h.mono $ λ x hx, le_trans hx (le_abs_self _)

lemma has_finite_integral.congr' {f : α → β} {g : α → γ} (hf : has_finite_integral f μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) :
  has_finite_integral g μ :=
hf.mono $ eventually_eq.le $ eventually_eq.symm h

lemma has_finite_integral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) :
  has_finite_integral f μ ↔ has_finite_integral g μ :=
⟨λ hf, hf.congr' h, λ hg, hg.congr' $ eventually_eq.symm h⟩

lemma has_finite_integral.congr {f g : α → β} (hf : has_finite_integral f μ) (h : f =ᵐ[μ] g) :
  has_finite_integral g μ :=
hf.congr' $ h.fun_comp norm

lemma has_finite_integral_congr {f g : α → β} (h : f =ᵐ[μ] g) :
  has_finite_integral f μ ↔ has_finite_integral g μ :=
has_finite_integral_congr' $ h.fun_comp norm

lemma has_finite_integral_const_iff {c : β} :
  has_finite_integral (λ x : α, c) μ ↔ c = 0 ∨ μ univ < ∞ :=
begin
  simp only [has_finite_integral, lintegral_const],
  by_cases hc : c = 0,
  { simp [hc] },
  { simp only [hc, false_or],
    refine ⟨λ h, _, λ h, mul_lt_top coe_lt_top h⟩,
    replace h := mul_lt_top (@coe_lt_top $ (nnnorm c)⁻¹) h,
    rwa [← mul_assoc, ← coe_mul, _root_.inv_mul_cancel, coe_one, one_mul] at h,
    rwa [ne.def, nnnorm_eq_zero] }
end

lemma has_finite_integral_const [finite_measure μ] (c : β) : has_finite_integral (λ x : α, c) μ :=
has_finite_integral_const_iff.2 (or.inr $ measure_lt_top _ _)

lemma has_finite_integral_of_bounded [finite_measure μ] {f : α → β} {C : ℝ}
  (hC : ∀ᵐ a ∂μ, ∥f a∥ ≤ C) : has_finite_integral f μ :=
(has_finite_integral_const C).mono' hC

lemma has_finite_integral.mono_measure {f : α → β} (h : has_finite_integral f ν) (hμ : μ ≤ ν) :
  has_finite_integral f μ :=
lt_of_le_of_lt (lintegral_mono' hμ (le_refl _)) h

lemma has_finite_integral.add_measure {f : α → β} (hμ : has_finite_integral f μ)
  (hν : has_finite_integral f ν) : has_finite_integral f (μ + ν) :=
begin
  simp only [has_finite_integral, lintegral_add_measure] at *,
  exact add_lt_top.2 ⟨hμ, hν⟩
end

lemma has_finite_integral.left_of_add_measure {f : α → β} (h : has_finite_integral f (μ + ν)) :
  has_finite_integral f μ :=
h.mono_measure $ measure.le_add_right $ le_refl _

lemma has_finite_integral.right_of_add_measure {f : α → β} (h : has_finite_integral f (μ + ν)) :
  has_finite_integral f ν :=
h.mono_measure $ measure.le_add_left $ le_refl _

@[simp] lemma has_finite_integral_add_measure {f : α → β} :
  has_finite_integral f (μ + ν) ↔ has_finite_integral f μ ∧ has_finite_integral f ν :=
⟨λ h, ⟨h.left_of_add_measure, h.right_of_add_measure⟩, λ h, h.1.add_measure h.2⟩

lemma has_finite_integral.smul_measure {f : α → β} (h : has_finite_integral f μ) {c : ℝ≥0∞}
  (hc : c < ∞) : has_finite_integral f (c • μ) :=
begin
  simp only [has_finite_integral, lintegral_smul_measure] at *,
  exact mul_lt_top hc h
end

@[simp] lemma has_finite_integral_zero_measure (f : α → β) : has_finite_integral f 0 :=
by simp only [has_finite_integral, lintegral_zero_measure, with_top.zero_lt_top]

variables (α β μ)
@[simp] lemma has_finite_integral_zero : has_finite_integral (λa:α, (0:β)) μ :=
by simp [has_finite_integral]
variables {α β μ}

lemma has_finite_integral.neg {f : α → β} (hfi : has_finite_integral f μ) :
  has_finite_integral (-f) μ :=
by simpa [has_finite_integral] using hfi

@[simp] lemma has_finite_integral_neg_iff {f : α → β} :
  has_finite_integral (-f) μ ↔ has_finite_integral f μ :=
⟨λ h, neg_neg f ▸ h.neg, has_finite_integral.neg⟩

lemma has_finite_integral.norm {f : α → β} (hfi : has_finite_integral f μ) :
  has_finite_integral (λa, ∥f a∥) μ :=
have eq : (λa, (nnnorm ∥f a∥ : ℝ≥0∞)) = λa, (nnnorm (f a) : ℝ≥0∞),
  by { funext, rw nnnorm_norm },
by { rwa [has_finite_integral, eq] }

lemma has_finite_integral_norm_iff (f : α → β) :
  has_finite_integral (λa, ∥f a∥) μ ↔ has_finite_integral f μ :=
has_finite_integral_congr' $ eventually_of_forall $ λ x, norm_norm (f x)

section dominated_convergence

variables {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}

lemma all_ae_of_real_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a) :
  ∀ n, ∀ᵐ a ∂μ, ennreal.of_real ∥F n a∥ ≤ ennreal.of_real (bound a) :=
λn, (h n).mono $ λ a h, ennreal.of_real_le_of_real h

lemma all_ae_tendsto_of_real_norm (h : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top $ 𝓝 $ f a) :
  ∀ᵐ a ∂μ, tendsto (λn, ennreal.of_real ∥F n a∥) at_top $ 𝓝 $ ennreal.of_real ∥f a∥ :=
h.mono $
  λ a h, tendsto_of_real $ tendsto.comp (continuous.tendsto continuous_norm _) h

lemma all_ae_of_real_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  ∀ᵐ a ∂μ, ennreal.of_real ∥f a∥ ≤ ennreal.of_real (bound a) :=
begin
  have F_le_bound := all_ae_of_real_F_le_bound h_bound,
  rw ← ae_all_iff at F_le_bound,
  apply F_le_bound.mp ((all_ae_tendsto_of_real_norm h_lim).mono _),
  assume a tendsto_norm F_le_bound,
  exact le_of_tendsto' tendsto_norm (F_le_bound)
end

lemma has_finite_integral_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (bound_has_finite_integral : has_finite_integral bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  has_finite_integral f μ :=
/- `∥F n a∥ ≤ bound a` and `∥F n a∥ --> ∥f a∥` implies `∥f a∥ ≤ bound a`,
  and so `∫ ∥f∥ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
begin
  rw has_finite_integral_iff_norm,
  calc ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ ≤ ∫⁻ a, ennreal.of_real (bound a) ∂μ :
    lintegral_mono_ae $ all_ae_of_real_f_le_bound h_bound h_lim
    ... < ∞ :
    begin
      rw ← has_finite_integral_iff_of_real,
      { exact bound_has_finite_integral },
      exact (h_bound 0).mono (λ a h, le_trans (norm_nonneg _) h)
    end
end

lemma tendsto_lintegral_norm_of_dominated_convergence [measurable_space β]
  [borel_space β] [second_countable_topology β]
  {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (F_measurable : ∀ n, ae_measurable (F n) μ)
  (f_measurable : ae_measurable f μ)
  (bound_has_finite_integral : has_finite_integral bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, (ennreal.of_real ∥F n a - f a∥) ∂μ) at_top (𝓝 0) :=
let b := λa, 2 * ennreal.of_real (bound a) in
/- `∥F n a∥ ≤ bound a` and `F n a --> f a` implies `∥f a∥ ≤ bound a`, and thus by the
  triangle inequality, have `∥F n a - f a∥ ≤ 2 * (bound a). -/
have hb : ∀ n, ∀ᵐ a ∂μ, ennreal.of_real ∥F n a - f a∥ ≤ b a,
begin
  assume n,
  filter_upwards [all_ae_of_real_F_le_bound h_bound n, all_ae_of_real_f_le_bound h_bound h_lim],
  assume a h₁ h₂,
  calc ennreal.of_real ∥F n a - f a∥ ≤ (ennreal.of_real ∥F n a∥) + (ennreal.of_real ∥f a∥) :
  begin
    rw [← ennreal.of_real_add],
    apply of_real_le_of_real,
    { apply norm_sub_le }, { exact norm_nonneg _ }, { exact norm_nonneg _ }
  end
    ... ≤ (ennreal.of_real (bound a)) + (ennreal.of_real (bound a)) : add_le_add h₁ h₂
    ... = b a : by rw ← two_mul
end,
/- On the other hand, `F n a --> f a` implies that `∥F n a - f a∥ --> 0`  -/
have h : ∀ᵐ a ∂μ, tendsto (λ n, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 0),
begin
  rw ← ennreal.of_real_zero,
  refine h_lim.mono (λ a h, (continuous_of_real.tendsto _).comp _),
  rwa ← tendsto_iff_norm_tendsto_zero
end,
/- Therefore, by the dominated convergence theorem for nonnegative integration, have
  ` ∫ ∥f a - F n a∥ --> 0 ` -/
begin
  suffices h : tendsto (λn, ∫⁻ a, (ennreal.of_real ∥F n a - f a∥) ∂μ) at_top (𝓝 (∫⁻ (a:α), 0 ∂μ)),
  { rwa lintegral_zero at h },
  -- Using the dominated convergence theorem.
  refine tendsto_lintegral_of_dominated_convergence' _ _ hb _ _,
  -- Show `λa, ∥f a - F n a∥` is almost everywhere measurable for all `n`
  { exact λn, measurable_of_real.comp_ae_measurable ((F_measurable n).sub f_measurable).norm },
  -- Show `2 * bound` is has_finite_integral
  { rw has_finite_integral_iff_of_real at bound_has_finite_integral,
    { calc ∫⁻ a, b a ∂μ = 2 * ∫⁻ a, ennreal.of_real (bound a) ∂μ :
        by { rw lintegral_const_mul', exact coe_ne_top }
        ... < ∞ : mul_lt_top (coe_lt_top) bound_has_finite_integral },
    filter_upwards [h_bound 0] λ a h, le_trans (norm_nonneg _) h },
  -- Show `∥f a - F n a∥ --> 0`
  { exact h }
end

end dominated_convergence

section pos_part
/-! Lemmas used for defining the positive part of a `L¹` function -/

lemma has_finite_integral.max_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (λa, max (f a) 0) μ :=
hf.mono $ eventually_of_forall $ λ x, by simp [real.norm_eq_abs, abs_le, abs_nonneg, le_abs_self]

lemma has_finite_integral.min_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (λa, min (f a) 0) μ :=
hf.mono $ eventually_of_forall $ λ x,
  by simp [real.norm_eq_abs, abs_le, abs_nonneg, neg_le, neg_le_abs_self]

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma has_finite_integral.smul (c : 𝕜) {f : α → β} : has_finite_integral f μ →
  has_finite_integral (c • f) μ :=
begin
  simp only [has_finite_integral], assume hfi,
  calc
    ∫⁻ (a : α), nnnorm (c • f a) ∂μ = ∫⁻ (a : α), (nnnorm c) * nnnorm (f a) ∂μ :
      by simp only [nnnorm_smul, ennreal.coe_mul]
    ... < ∞ :
    begin
      rw lintegral_const_mul',
      exacts [mul_lt_top coe_lt_top hfi, coe_ne_top]
    end
end

lemma has_finite_integral_smul_iff {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
  has_finite_integral (c • f) μ ↔ has_finite_integral f μ :=
begin
  split,
  { assume h,
    simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.smul c⁻¹ },
  exact has_finite_integral.smul _
end

lemma has_finite_integral.const_mul {f : α → ℝ} (h : has_finite_integral f μ) (c : ℝ) :
  has_finite_integral (λ x, c * f x) μ :=
(has_finite_integral.smul c h : _)

lemma has_finite_integral.mul_const {f : α → ℝ} (h : has_finite_integral f μ) (c : ℝ) :
  has_finite_integral (λ x, f x * c) μ :=
by simp_rw [mul_comm, h.const_mul _]
end normed_space

/-! ### The predicate `integrable` -/

variables [measurable_space β] [measurable_space γ] [measurable_space δ]

/-- `integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `integrable f` means `integrable f volume`. -/
def integrable (f : α → β) (μ : measure α . volume_tac) : Prop :=
ae_measurable f μ ∧ has_finite_integral f μ

lemma integrable.ae_measurable {f : α → β} (hf : integrable f μ) : ae_measurable f μ := hf.1
lemma integrable.has_finite_integral {f : α → β} (hf : integrable f μ) : has_finite_integral f μ :=
hf.2

lemma integrable.mono {f : α → β} {g : α → γ} (hg : integrable g μ) (hf : ae_measurable f μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) : integrable f μ :=
⟨hf, hg.has_finite_integral.mono h⟩

lemma integrable.mono' {f : α → β} {g : α → ℝ} (hg : integrable g μ) (hf : ae_measurable f μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ g a) : integrable f μ :=
⟨hf, hg.has_finite_integral.mono' h⟩

lemma integrable.congr' {f : α → β} {g : α → γ} (hf : integrable f μ) (hg : ae_measurable g μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) : integrable g μ :=
⟨hg, hf.has_finite_integral.congr' h⟩

lemma integrable_congr' {f : α → β} {g : α → γ} (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) : integrable f μ ↔ integrable g μ :=
⟨λ h2f, h2f.congr' hg h, λ h2g, h2g.congr' hf $ eventually_eq.symm h⟩

lemma integrable.congr {f g : α → β} (hf : integrable f μ) (h : f =ᵐ[μ] g) :
  integrable g μ :=
⟨hf.1.congr h, hf.2.congr h⟩

lemma integrable_congr {f g : α → β} (h : f =ᵐ[μ] g) :
  integrable f μ ↔ integrable g μ :=
⟨λ hf, hf.congr h, λ hg, hg.congr h.symm⟩

lemma integrable_const_iff {c : β} : integrable (λ x : α, c) μ ↔ c = 0 ∨ μ univ < ∞ :=
begin
  have : ae_measurable (λ (x : α), c) μ := measurable_const.ae_measurable,
  rw [integrable, and_iff_right this, has_finite_integral_const_iff]
end

lemma integrable_const [finite_measure μ] (c : β) : integrable (λ x : α, c) μ :=
integrable_const_iff.2 $ or.inr $ measure_lt_top _ _

lemma integrable.mono_measure {f : α → β} (h : integrable f ν) (hμ : μ ≤ ν) : integrable f μ :=
⟨h.ae_measurable.mono_measure hμ, h.has_finite_integral.mono_measure hμ⟩

lemma integrable.add_measure {f : α → β} (hμ : integrable f μ) (hν : integrable f ν) :
  integrable f (μ + ν) :=
⟨hμ.ae_measurable.add_measure hν.ae_measurable,
  hμ.has_finite_integral.add_measure hν.has_finite_integral⟩

lemma integrable.left_of_add_measure {f : α → β} (h : integrable f (μ + ν)) : integrable f μ :=
h.mono_measure $ measure.le_add_right $ le_refl _

lemma integrable.right_of_add_measure {f : α → β} (h : integrable f (μ + ν)) : integrable f ν :=
h.mono_measure $ measure.le_add_left $ le_refl _

@[simp] lemma integrable_add_measure {f : α → β} :
  integrable f (μ + ν) ↔ integrable f μ ∧ integrable f ν :=
⟨λ h, ⟨h.left_of_add_measure, h.right_of_add_measure⟩, λ h, h.1.add_measure h.2⟩

lemma integrable.smul_measure {f : α → β} (h : integrable f μ) {c : ℝ≥0∞} (hc : c < ∞) :
  integrable f (c • μ) :=
⟨h.ae_measurable.smul_measure c, h.has_finite_integral.smul_measure hc⟩

lemma integrable_map_measure [opens_measurable_space β] {f : α → δ} {g : δ → β}
  (hg : ae_measurable g (measure.map f μ)) (hf : measurable f) :
  integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
by simp [integrable, hg, hg.comp_measurable hf, has_finite_integral, lintegral_map' hg.ennnorm hf]

lemma lintegral_edist_lt_top [second_countable_topology β] [opens_measurable_space β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) :
  ∫⁻ a, edist (f a) (g a) ∂μ < ∞ :=
lt_of_le_of_lt
  (lintegral_edist_triangle hf.ae_measurable hg.ae_measurable
    (measurable_const.ae_measurable : ae_measurable (λa, (0 : β)) μ))
  (ennreal.add_lt_top.2 $ by { simp_rw ← has_finite_integral_iff_edist,
                               exact ⟨hf.has_finite_integral, hg.has_finite_integral⟩ })

variables (α β μ)
@[simp] lemma integrable_zero : integrable (λ _, (0 : β)) μ :=
by simp [integrable, measurable_const.ae_measurable]
variables {α β μ}

lemma integrable.add' [opens_measurable_space β] {f g : α → β} (hf : integrable f μ)
  (hg : integrable g μ) :
  has_finite_integral (f + g) μ :=
calc ∫⁻ a, nnnorm (f a + g a) ∂μ ≤ ∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ :
  lintegral_mono (λ a, by exact_mod_cast nnnorm_add_le _ _)
... = _ : lintegral_nnnorm_add hf.ae_measurable hg.ae_measurable
... < ∞ : add_lt_top.2 ⟨hf.has_finite_integral, hg.has_finite_integral⟩

lemma integrable.add [borel_space β] [second_countable_topology β]
  {f g : α → β} (hf : integrable f μ) (hg : integrable g μ) : integrable (f + g) μ :=
⟨hf.ae_measurable.add hg.ae_measurable, hf.add' hg⟩

lemma integrable_finset_sum {ι} [borel_space β] [second_countable_topology β] (s : finset ι)
  {f : ι → α → β} (hf : ∀ i, integrable (f i) μ) : integrable (λ a, ∑ i in s, f i a) μ :=
begin
  refine finset.induction_on s _ _,
  { simp only [finset.sum_empty, integrable_zero] },
  { assume i s his ih, simp only [his, finset.sum_insert, not_false_iff],
    exact (hf _).add ih }
end

lemma integrable.neg [borel_space β] {f : α → β} (hf : integrable f μ) : integrable (-f) μ :=
⟨hf.ae_measurable.neg, hf.has_finite_integral.neg⟩

@[simp] lemma integrable_neg_iff [borel_space β] {f : α → β} : integrable (-f) μ ↔ integrable f μ :=
⟨λ h, neg_neg f ▸ h.neg, integrable.neg⟩

lemma integrable.sub' [opens_measurable_space β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) : has_finite_integral (f - g) μ :=
calc ∫⁻ a, nnnorm (f a - g a) ∂μ ≤ ∫⁻ a, nnnorm (f a) + nnnorm (-g a) ∂μ :
  lintegral_mono (assume a, by { simp only [sub_eq_add_neg], exact_mod_cast nnnorm_add_le _ _ } )
... = _ :
  by { simp only [nnnorm_neg], exact lintegral_nnnorm_add hf.ae_measurable hg.ae_measurable }
... < ∞ : add_lt_top.2 ⟨hf.has_finite_integral, hg.has_finite_integral⟩

lemma integrable.sub [borel_space β] [second_countable_topology β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) : integrable (f - g) μ :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma integrable.norm [opens_measurable_space β] {f : α → β} (hf : integrable f μ) :
  integrable (λa, ∥f a∥) μ :=
⟨hf.ae_measurable.norm, hf.has_finite_integral.norm⟩

lemma integrable_norm_iff [opens_measurable_space β] {f : α → β} (hf : ae_measurable f μ) :
  integrable (λa, ∥f a∥) μ ↔ integrable f μ :=
by simp_rw [integrable, and_iff_right hf, and_iff_right hf.norm, has_finite_integral_norm_iff]

lemma integrable_of_norm_sub_le [opens_measurable_space β] {f₀ f₁ : α → β} {g : α → ℝ}
  (hf₁_m : ae_measurable f₁ μ)
  (hf₀_i : integrable f₀ μ)
  (hg_i : integrable g μ)
  (h : ∀ᵐ a ∂μ, ∥f₀ a - f₁ a∥ ≤ g a) :
  integrable f₁ μ :=
begin
  have : ∀ᵐ a ∂μ, ∥f₁ a∥ ≤ ∥f₀ a∥ + g a,
  { apply h.mono,
    intros a ha,
    calc ∥f₁ a∥ ≤ ∥f₀ a∥ + ∥f₀ a - f₁ a∥ : norm_le_insert _ _
    ... ≤ ∥f₀ a∥ + g a : add_le_add_left ha _ },
  exact integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this
end

lemma integrable.prod_mk [opens_measurable_space β] [opens_measurable_space γ] {f : α → β}
  {g : α → γ} (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ x, (f x, g x)) μ :=
⟨hf.ae_measurable.prod_mk hg.ae_measurable,
  (hf.norm.add' hg.norm).mono $ eventually_of_forall $ λ x,
  calc max ∥f x∥ ∥g x∥ ≤ ∥f x∥ + ∥g x∥   : max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
                 ... ≤ ∥(∥f x∥ + ∥g x∥)∥ : le_abs_self _⟩

lemma mem_ℒp_one_iff_integrable {f : α → β} : mem_ℒp f 1 μ ↔ integrable f μ :=
by simp_rw [integrable, has_finite_integral, mem_ℒp, snorm_one_eq_lintegral_nnnorm]

lemma mem_ℒp.integrable [borel_space β] {q : ℝ≥0∞} (hq1 : 1 ≤ q) {f : α → β} [finite_measure μ]
  (hfq : mem_ℒp f q μ) : integrable f μ :=
mem_ℒp_one_iff_integrable.mp (hfq.mem_ℒp_of_exponent_le hq1)

lemma lipschitz_with.integrable_comp_iff_of_antilipschitz [complete_space β] [borel_space β]
  [borel_space γ] {K K'} {f : α → β} {g : β → γ} (hg : lipschitz_with K g)
  (hg' : antilipschitz_with K' g) (g0 : g 0 = 0) :
  integrable (g ∘ f) μ ↔ integrable f μ :=
by simp [← mem_ℒp_one_iff_integrable, hg.mem_ℒp_comp_iff_of_antilipschitz hg' g0]

lemma integrable.real_to_nnreal {f : α → ℝ} (hf : integrable f μ) :
  integrable (λ x, ((f x).to_nnreal : ℝ)) μ :=
begin
  refine ⟨hf.ae_measurable.real_to_nnreal.coe_nnreal_real, _⟩,
  rw has_finite_integral_iff_norm,
  refine lt_of_le_of_lt _ ((has_finite_integral_iff_norm _).1 hf.has_finite_integral),
  apply lintegral_mono,
  assume x,
  simp [real.norm_eq_abs, ennreal.of_real_le_of_real, abs_le, abs_nonneg, le_abs_self],
end

section pos_part
/-! ### Lemmas used for defining the positive part of a `L¹` function -/

lemma integrable.max_zero {f : α → ℝ} (hf : integrable f μ) : integrable (λa, max (f a) 0) μ :=
⟨hf.ae_measurable.max measurable_const.ae_measurable, hf.has_finite_integral.max_zero⟩

lemma integrable.min_zero {f : α → ℝ} (hf : integrable f μ) : integrable (λa, min (f a) 0) μ :=
⟨hf.ae_measurable.min measurable_const.ae_measurable, hf.has_finite_integral.min_zero⟩

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β] [measurable_space 𝕜]
  [opens_measurable_space 𝕜]

lemma integrable.smul [borel_space β] (c : 𝕜) {f : α → β}
  (hf : integrable f μ) : integrable (c • f) μ :=
⟨hf.ae_measurable.const_smul c, hf.has_finite_integral.smul c⟩

lemma integrable_smul_iff [borel_space β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
  integrable (c • f) μ ↔ integrable f μ :=
and_congr (ae_measurable_const_smul_iff' hc) (has_finite_integral_smul_iff hc f)

lemma integrable.const_mul {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, c * f x) μ :=
integrable.smul c h

lemma integrable.mul_const {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, f x * c) μ :=
by simp_rw [mul_comm, h.const_mul _]

end normed_space

section normed_space_over_complete_field
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜] [measurable_space 𝕜]
variables [borel_space 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E] [measurable_space E] [borel_space E]

lemma integrable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
  integrable (λ x, f x • c) μ ↔ integrable f μ :=
begin
  simp_rw [integrable, ae_measurable_smul_const hc, and.congr_right_iff, has_finite_integral,
    nnnorm_smul, ennreal.coe_mul],
  intro hf, rw [lintegral_mul_const' _ _ ennreal.coe_ne_top, ennreal.mul_lt_top_iff],
  have : ∀ x : ℝ≥0∞, x = 0 → x < ∞ := by simp,
  simp [hc, or_iff_left_of_imp (this _)]
end
end normed_space_over_complete_field

section trim

variables {H α' : Type*} [normed_group H] [measurable_space H]
  {m m0 : measurable_space α'} {μ' : measure α'}

lemma integrable.trim (hm : m ≤ m0) [opens_measurable_space H] {f : α' → H}
  (hf_int : integrable f μ') (hf : @measurable _ _ m _ f) :
  @integrable _ _ m _ _ f (μ'.trim hm) :=
begin
  refine ⟨@measurable.ae_measurable α' _ m _ f (μ'.trim hm) hf, _⟩,
  rw [has_finite_integral, lintegral_trim hm _],
  { exact hf_int.2, },
  { exact @measurable.coe_nnreal_ennreal α' m _ (@measurable.nnnorm _ α' _ _ _ m _ hf), },
end

lemma integrable_of_integrable_trim (hm : m ≤ m0) [opens_measurable_space H]
  {f : α' → H} (hf_int : @integrable α' H m _ _ f (μ'.trim hm)) :
  integrable f μ' :=
begin
  obtain ⟨hf_meas_ae, hf⟩ := hf_int,
  refine ⟨ae_measurable_of_ae_measurable_trim hm hf_meas_ae, _⟩,
  rw has_finite_integral at hf ⊢,
  rwa lintegral_trim_ae hm _ at hf,
  exact @ae_measurable.coe_nnreal_ennreal α' m _ _
    (@ae_measurable.nnnorm H α' _ _ _ m _ _ hf_meas_ae),
end

end trim

/-! ### The predicate `integrable` on measurable functions modulo a.e.-equality -/

namespace ae_eq_fun

section

/-- A class of almost everywhere equal functions is `integrable` if its function representative
is integrable. -/
def integrable (f : α →ₘ[μ] β) : Prop := integrable f μ

lemma integrable_mk {f : α → β} (hf : ae_measurable f μ ) :
  (integrable (mk f hf : α →ₘ[μ] β)) ↔ measure_theory.integrable f μ :=
begin
  simp [integrable],
  apply integrable_congr,
  exact coe_fn_mk f hf
end

lemma integrable_coe_fn {f : α →ₘ[μ] β} : (measure_theory.integrable f μ) ↔ integrable f :=
by rw [← integrable_mk, mk_coe_fn]

lemma integrable_zero : integrable (0 : α →ₘ[μ] β) :=
(integrable_zero α β μ).congr (coe_fn_mk _ _).symm

end

section

variables [borel_space β]

lemma integrable.neg {f : α →ₘ[μ] β} : integrable f → integrable (-f) :=
induction_on f $ λ f hfm hfi, (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section
variable [second_countable_topology β]

lemma integrable_iff_mem_L1 {f : α →ₘ[μ] β} : integrable f ↔ f ∈ (α →₁[μ] β) :=
by rw [← integrable_coe_fn, ← mem_ℒp_one_iff_integrable, Lp.mem_Lp_iff_mem_ℒp]

lemma integrable.add {f g : α →ₘ[μ] β} : integrable f → integrable g → integrable (f + g) :=
begin
  refine induction_on₂ f g (λ f hf g hg hfi hgi, _),
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢,
  exact hfi.add hgi
end

lemma integrable.sub {f g : α →ₘ[μ] β} (hf : integrable f) (hg : integrable g) :
  integrable (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β] [measurable_space 𝕜]
  [opens_measurable_space 𝕜]

lemma integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : integrable f → integrable (c • f) :=
induction_on f $ λ f hfm hfi, (integrable_mk _).2 $ ((integrable_mk hfm).1 hfi).smul _

end normed_space

end

end ae_eq_fun

namespace L1
variables [second_countable_topology β] [borel_space β]

lemma integrable_coe_fn (f : α →₁[μ] β) :
  integrable f μ :=
by { rw ← mem_ℒp_one_iff_integrable, exact Lp.mem_ℒp f }

lemma has_finite_integral_coe_fn (f : α →₁[μ] β) :
  has_finite_integral f μ :=
(integrable_coe_fn f).has_finite_integral

lemma measurable_coe_fn (f : α →₁[μ] β) :
  measurable f := Lp.measurable f

lemma ae_measurable_coe_fn (f : α →₁[μ] β) :
  ae_measurable f μ := Lp.ae_measurable f

lemma edist_def (f g : α →₁[μ] β) :
  edist f g = ∫⁻ a, edist (f a) (g a) ∂μ :=
by { simp [Lp.edist_def, snorm, snorm'], simp [edist_eq_coe_nnnorm_sub] }

lemma dist_def (f g : α →₁[μ] β) :
  dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).to_real :=
by { simp [Lp.dist_def, snorm, snorm'], simp [edist_eq_coe_nnnorm_sub] }

lemma norm_def (f : α →₁[μ] β) :
  ∥f∥ = (∫⁻ a, nnnorm (f a) ∂μ).to_real :=
by { simp [Lp.norm_def, snorm, snorm'] }

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
lemma norm_sub_eq_lintegral (f g : α →₁[μ] β) :
  ∥f - g∥ = (∫⁻ x, (nnnorm (f x - g x) : ℝ≥0∞) ∂μ).to_real :=
begin
  rw [norm_def],
  congr' 1,
  rw lintegral_congr_ae,
  filter_upwards [Lp.coe_fn_sub f g],
  assume a ha,
  simp only [ha, pi.sub_apply],
end

lemma of_real_norm_eq_lintegral (f : α →₁[μ] β) :
  ennreal.of_real ∥f∥ = ∫⁻ x, (nnnorm (f x) : ℝ≥0∞) ∂μ :=
by { rw [norm_def, ennreal.of_real_to_real], rw [← ennreal.lt_top_iff_ne_top],
  exact has_finite_integral_coe_fn f }

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `of_real_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
lemma of_real_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
  ennreal.of_real ∥f - g∥ = ∫⁻ x, (nnnorm (f x - g x) : ℝ≥0∞) ∂μ :=
begin
  simp_rw [of_real_norm_eq_lintegral, ← edist_eq_coe_nnnorm],
  apply lintegral_congr_ae,
  filter_upwards [Lp.coe_fn_sub f g],
  assume a ha,
  simp only [ha, pi.sub_apply],
end

end L1

namespace integrable

variables [second_countable_topology β] [borel_space β]

/-- Construct the equivalence class `[f]` of an integrable function `f`, as a member of the
space `L1 β 1 μ`. -/
def to_L1 (f : α → β) (hf : integrable f μ) : α →₁[μ] β :=
(mem_ℒp_one_iff_integrable.2 hf).to_Lp f

@[simp] lemma to_L1_coe_fn (f : α →₁[μ] β) (hf : integrable f μ) : hf.to_L1 f = f :=
by simp [integrable.to_L1]

lemma coe_fn_to_L1 {f : α → β} (hf : integrable f μ) : hf.to_L1 f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk _ _

@[simp] lemma to_L1_zero (h : integrable (0 : α → β) μ) : h.to_L1 0 = 0 := rfl

@[simp] lemma to_L1_eq_mk (f : α → β) (hf : integrable f μ) :
  (hf.to_L1 f : α →ₘ[μ] β) = ae_eq_fun.mk f hf.ae_measurable :=
rfl

@[simp] lemma to_L1_eq_to_L1_iff (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 f hf = to_L1 g hg ↔ f =ᵐ[μ] g :=
mem_ℒp.to_Lp_eq_to_Lp_iff _ _

lemma to_L1_add (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 (f + g) (hf.add hg) = to_L1 f hf + to_L1 g hg := rfl

lemma to_L1_neg (f : α → β) (hf : integrable f μ) :
  to_L1 (- f) (integrable.neg hf) = - to_L1 f hf := rfl

lemma to_L1_sub (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 (f - g) (hf.sub hg) = to_L1 f hf - to_L1 g hg := rfl

lemma norm_to_L1 (f : α → β) (hf : integrable f μ) :
  ∥hf.to_L1 f∥ = ennreal.to_real (∫⁻ a, edist (f a) 0 ∂μ) :=
by { simp [to_L1, snorm, snorm'], simp [edist_eq_coe_nnnorm] }

lemma norm_to_L1_eq_lintegral_norm (f : α → β) (hf : integrable f μ) :
  ∥hf.to_L1 f∥ = ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :=
by { rw [norm_to_L1, lintegral_norm_eq_lintegral_edist] }

@[simp] lemma edist_to_L1_to_L1 (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  edist (hf.to_L1 f) (hg.to_L1 g) = ∫⁻ a, edist (f a) (g a) ∂μ :=
by { simp [integrable.to_L1, snorm, snorm'], simp [edist_eq_coe_nnnorm_sub] }

@[simp] lemma edist_to_L1_zero (f : α → β) (hf : integrable f μ) :
  edist (hf.to_L1 f) 0 = ∫⁻ a, edist (f a) 0 ∂μ :=
by { simp [integrable.to_L1, snorm, snorm'], simp [edist_eq_coe_nnnorm] }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β] [measurable_space 𝕜]
  [opens_measurable_space 𝕜]

lemma to_L1_smul (f : α → β) (hf : integrable f μ) (k : 𝕜) :
  to_L1 (λa, k • f a) (hf.smul k) = k • to_L1 f hf := rfl

end integrable

end measure_theory

open measure_theory

lemma integrable_zero_measure [measurable_space β] {f : α → β} :
  integrable f 0 :=
begin
  apply (integrable_zero _ _ _).congr,
  change (0 : measure α) {x | 0 ≠ f x} = 0,
  refl,
end

variables {E : Type*} [normed_group E] [measurable_space E] [borel_space E] [normed_space ℝ E]
          {H : Type*} [normed_group H] [normed_space ℝ H]

lemma measure_theory.integrable.apply_continuous_linear_map {φ : α → H →L[ℝ] E}
  (φ_int : integrable φ μ) (v : H) : integrable (λ a, φ a v) μ :=
(φ_int.norm.mul_const ∥v∥).mono' (φ_int.ae_measurable.apply_continuous_linear_map v)
  (eventually_of_forall $ λ a, (φ a).le_op_norm v)

variables {𝕜 : Type*} [is_R_or_C 𝕜]
  {G : Type*} [normed_group G] [normed_space 𝕜 G] [measurable_space G] [borel_space G]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [measurable_space F] [opens_measurable_space F]

lemma continuous_linear_map.integrable_comp {φ : α → F} (L : F →L[𝕜] G)
  (φ_int : integrable φ μ) : integrable (λ (a : α), L (φ a)) μ :=
((integrable.norm φ_int).const_mul ∥L∥).mono' (L.measurable.comp_ae_measurable φ_int.ae_measurable)
  (eventually_of_forall $ λ a, L.le_op_norm (φ a))
