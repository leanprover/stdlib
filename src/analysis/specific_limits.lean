/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.geom_sum
import order.filter.archimedean
import order.iterate
import topology.instances.ennreal
import tactic.ring_exp
import analysis.asymptotics.asymptotics

/-!
# A collection of specific limit computations
-/

noncomputable theory
open classical set function filter finset metric asymptotics

open_locale classical topological_space nat big_operators uniformity nnreal ennreal

variables {α : Type*} {β : Type*} {ι : Type*}

lemma tendsto_norm_at_top_at_top : tendsto (norm : ℝ → ℝ) at_top at_top :=
tendsto_abs_at_top_at_top

lemma summable_of_absolute_convergence_real {f : ℕ → ℝ} :
  (∃r, tendsto (λn, (∑ i in range n, abs (f i))) at_top (𝓝 r)) → summable f
| ⟨r, hr⟩ :=
  begin
    refine summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩,
    exact assume i, norm_nonneg _,
    simpa only using hr
  end

lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ)⁻¹) at_top (𝓝 0) :=
tendsto_inv_at_top_zero.comp tendsto_coe_nat_at_top_at_top

lemma tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : tendsto (λ n : ℕ, C / n) at_top (𝓝 0) :=
by simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_inverse_at_top_nhds_0_nat

lemma nnreal.tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ≥0)⁻¹) at_top (𝓝 0) :=
by { rw ← nnreal.tendsto_coe, convert tendsto_inverse_at_top_nhds_0_nat, simp }

lemma nnreal.tendsto_const_div_at_top_nhds_0_nat (C : ℝ≥0) :
  tendsto (λ n : ℕ, C / n) at_top (𝓝 0) :=
by simpa using tendsto_const_nhds.mul nnreal.tendsto_inverse_at_top_nhds_0_nat

lemma tendsto_one_div_add_at_top_nhds_0_nat :
  tendsto (λ n : ℕ, 1 / ((n : ℝ) + 1)) at_top (𝓝 0) :=
suffices tendsto (λ n : ℕ, 1 / (↑(n + 1) : ℝ)) at_top (𝓝 0), by simpa,
(tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat 1)

/-! ### Powers -/

lemma tendsto_add_one_pow_at_top_at_top_of_pos [linear_ordered_semiring α] [archimedean α] {r : α}
  (h : 0 < r) :
  tendsto (λ n:ℕ, (r + 1)^n) at_top at_top :=
tendsto_at_top_at_top_of_monotone' (λ n m, pow_le_pow (le_add_of_nonneg_left (le_of_lt h))) $
  not_bdd_above_iff.2 $ λ x, set.exists_range_iff.2 $ add_one_pow_unbounded_of_pos _ h

lemma tendsto_pow_at_top_at_top_of_one_lt [linear_ordered_ring α] [archimedean α]
  {r : α} (h : 1 < r) :
  tendsto (λn:ℕ, r ^ n) at_top at_top :=
sub_add_cancel r 1 ▸ tendsto_add_one_pow_at_top_at_top_of_pos (sub_pos.2 h)

lemma nat.tendsto_pow_at_top_at_top_of_one_lt {m : ℕ} (h : 1 < m) :
  tendsto (λn:ℕ, m ^ n) at_top at_top :=
nat.sub_add_cancel (le_of_lt h) ▸
  tendsto_add_one_pow_at_top_at_top_of_pos (nat.sub_pos_of_lt h)

lemma tendsto_norm_zero' {𝕜 : Type*} [normed_group 𝕜] :
  tendsto (norm : 𝕜 → ℝ) (𝓝[{x | x ≠ 0}] 0) (𝓝[set.Ioi 0] 0) :=
tendsto_norm_zero.inf $ tendsto_principal_principal.2 $ λ x hx, norm_pos_iff.2 hx

lemma normed_field.tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type*} [normed_field 𝕜] :
  tendsto (λ x:𝕜, ∥x⁻¹∥) (𝓝[{x | x ≠ 0}] 0) at_top :=
(tendsto_inv_zero_at_top.comp tendsto_norm_zero').congr $ λ x, (normed_field.norm_inv x).symm

@[simp] lemma normed_field.continuous_at_inv_iff {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {x : 𝕜} :
  continuous_at (λx:𝕜, x⁻¹) x ↔ x ≠ 0 :=
begin
  refine ⟨_, λ t, continuous_at_inv' t⟩,
  rintros h rfl,
  apply not_tendsto_nhds_of_tendsto_at_top normed_field.tendsto_norm_inverse_nhds_within_0_at_top
    (∥(0:𝕜)⁻¹∥),
  convert (continuous_norm.continuous_at.comp h).tendsto.mono_left inf_le_left,
  exact normed_field.punctured_nhds_ne_bot 0
end

@[simp] lemma normed_field.continuous_at_fpow_iff
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {m : ℤ} {x : 𝕜} :
  continuous_at (λx:𝕜, x^m) x ↔ (x ≠ 0 ∨ 0 ≤ m) :=
begin
  have : ∀ m : ℤ, 0 < m → continuous_at (λx, x^m) x,
  { assume m hm,
    lift m to ℕ using (le_of_lt hm),
    exact (continuous_pow m).continuous_at },
  rcases lt_trichotomy m 0 with hm|hm|hm,
  { have : ¬ (0 ≤ m) := not_le.mpr hm,
    simp only [this, or_false, ne.def],
    lift -m to ℕ using le_of_lt (neg_pos.mpr hm) with k hk,
    have hk' : m = -↑k := eq_neg_of_eq_neg hk,
    suffices : continuous_at (λ x, (x ^ k)⁻¹) x ↔ x ≠ 0,
    { convert this,
      ext y,
      simp [hk'] },
    split,
    { rintros h rfl,
      suffices h' : tendsto (λ x : 𝕜, ∥(x ^ k)⁻¹∥) (𝓝[{0}ᶜ] 0) at_top,
      { haveI := normed_field.punctured_nhds_ne_bot (0:𝕜),
        apply not_tendsto_nhds_of_tendsto_at_top h' _,
        exact (continuous_norm.continuous_at.comp h).continuous_within_at.tendsto },
      refine normed_field.tendsto_norm_inverse_nhds_within_0_at_top.comp _,
      change tendsto _ _ (_ ⊓ _),
      rw filter.tendsto_inf,
      split,
      { apply tendsto_nhds_within_of_tendsto_nhds,
        convert (continuous_pow k).continuous_at.tendsto,
        { refine (zero_pow _).symm,
          rw hk' at hm,
          exact_mod_cast neg_lt_zero.mp hm },
        apply_instance },
      simp only [tendsto_principal],
      refine ⟨set.univ, univ_mem_sets, {(0:𝕜)}ᶜ, by simp [subset.rfl], _⟩,
      rw set.univ_inter,
      exact λ _, mt pow_eq_zero },
    { intros h,
      refine continuous_at.comp _ (continuous_pow k).continuous_at,
      refine continuous_at_inv' _,
      exact pow_ne_zero k h } },
  { simp [hm, fpow_zero, int.cast_zero, zero_mul, continuous_at_const, rfl.ge] },
  { simp [this m hm, le_of_lt hm] }
end

lemma tendsto_pow_at_top_nhds_0_of_lt_1 {𝕜 : Type*} [linear_ordered_field 𝕜] [archimedean 𝕜]
  [topological_space 𝕜] [order_topology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝 0) :=
h₁.eq_or_lt.elim
  (assume : 0 = r,
    (tendsto_add_at_top_iff_nat 1).mp $ by simp [pow_succ, ← this, tendsto_const_nhds])
  (assume : 0 < r,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (𝓝 0),
      from tendsto_inv_at_top_zero.comp
        (tendsto_pow_at_top_at_top_of_one_lt $ one_lt_inv this h₂),
    this.congr (λ n, by simp))

lemma tendsto_pow_at_top_nhds_within_0_of_lt_1 {𝕜 : Type*} [linear_ordered_field 𝕜] [archimedean 𝕜]
  [topological_space 𝕜] [order_topology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝[Ioi 0] 0) :=
tendsto_inf.2 ⟨tendsto_pow_at_top_nhds_0_of_lt_1 h₁.le h₂,
  tendsto_principal.2 $ eventually_of_forall $ λ n, pow_pos h₁ _⟩

lemma is_o_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
  is_o (λ n : ℕ, r₁ ^ n) (λ n, r₂ ^ n) at_top :=
have H : 0 < r₂ := h₁.trans_lt h₂,
is_o_of_tendsto (λ n hn, false.elim $ H.ne' $ pow_eq_zero hn) $
  (tendsto_pow_at_top_nhds_0_of_lt_1 (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr
    (λ n, div_pow _ _ _)

lemma is_O_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
  is_O (λ n : ℕ, r₁ ^ n) (λ n, r₂ ^ n) at_top :=
h₂.eq_or_lt.elim (λ h, h ▸ is_O_refl _ _) (λ h, (is_o_pow_pow_of_lt_left h₁ h).is_O)

lemma is_o_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : abs r₁ < abs r₂) :
  is_o (λ n : ℕ, r₁ ^ n) (λ n, r₂ ^ n) at_top :=
begin
  refine (is_o.of_norm_left _).of_norm_right,
  exact (is_o_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)
end

/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
     for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
lemma tfae_exists_lt_is_o_pow (f : ℕ → ℝ) (R : ℝ) :
  tfae [∃ a ∈ Ioo (-R) R, is_o f (pow a) at_top,
    ∃ a ∈ Ioo 0 R, is_o f (pow a) at_top,
    ∃ a ∈ Ioo (-R) R, is_O f (pow a) at_top,
    ∃ a ∈ Ioo 0 R, is_O f (pow a) at_top,
    ∃ (a < R) C (h₀ : 0 < C ∨ 0 < R), ∀ n, abs (f n) ≤ C * a ^ n,
    ∃ (a ∈ Ioo 0 R) (C > 0), ∀ n, abs (f n) ≤ C * a ^ n,
    ∃ a < R, ∀ᶠ n in at_top, abs (f n) ≤ a ^ n,
    ∃ a ∈ Ioo 0 R, ∀ᶠ n in at_top, abs (f n) ≤ a ^ n] :=
begin
  have A : Ico 0 R ⊆ Ioo (-R) R,
    from λ x hx, ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩,
  have B : Ioo 0 R ⊆ Ioo (-R) R := subset.trans Ioo_subset_Ico_self A,
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have : 1 → 3, from λ ⟨a, ha, H⟩, ⟨a, ha, H.is_O⟩,
  tfae_have : 2 → 1, from λ ⟨a, ha, H⟩, ⟨a, B ha, H⟩,
  tfae_have : 3 → 2,
  { rintro ⟨a, ha, H⟩,
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩,
    exact ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
      H.trans_is_o (is_o_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩ },
  tfae_have : 2 → 4, from λ ⟨a, ha, H⟩, ⟨a, ha, H.is_O⟩,
  tfae_have : 4 → 3, from λ ⟨a, ha, H⟩, ⟨a, B ha, H⟩,
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have : 4 → 6,
  { rintro ⟨a, ha, H⟩,
    rcases bound_of_is_O_nat_at_top H with ⟨C, hC₀, hC⟩,
    refine ⟨a, ha, C, hC₀, λ n, _⟩,
    simpa only [real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le]
      using hC (pow_ne_zero n ha.1.ne') },
  tfae_have : 6 → 5, from λ ⟨a, ha, C, H₀, H⟩, ⟨a, ha.2, C, or.inl H₀, H⟩,
  tfae_have : 5 → 3,
  { rintro ⟨a, ha, C, h₀, H⟩,
    rcases sign_cases_of_C_mul_pow_nonneg (λ n, (abs_nonneg _).trans (H n)) with rfl | ⟨hC₀, ha₀⟩,
    { obtain rfl : f = 0, by { ext n, simpa using H n },
      simp only [lt_irrefl, false_or] at h₀,
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, is_O_zero _ _⟩ },
    exact ⟨a, A ⟨ha₀, ha⟩,
      is_O_of_le' _ (λ n, (H n).trans $ mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le)⟩ },
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have : 2 → 8,
  { rintro ⟨a, ha, H⟩,
    refine ⟨a, ha, (H.def zero_lt_one).mono (λ n hn, _)⟩,
    rwa [real.norm_eq_abs, real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn },
  tfae_have : 8 → 7, from λ ⟨a, ha, H⟩, ⟨a, ha.2, H⟩,
  tfae_have : 7 → 3,
  { rintro ⟨a, ha, H⟩,
    have : 0 ≤ a, from nonneg_of_eventually_pow_nonneg (H.mono $ λ n, (abs_nonneg _).trans),
    refine ⟨a, A ⟨this, ha⟩, is_O.of_bound 1 _⟩,
    simpa only [real.norm_eq_abs, one_mul, abs_pow, abs_of_nonneg this] },
  tfae_finish
end

lemma uniformity_basis_dist_pow_of_lt_1 {α : Type*} [metric_space α]
  {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) :
  (𝓤 α).has_basis (λ k : ℕ, true) (λ k, {p : α × α | dist p.1 p.2 < r ^ k}) :=
metric.mk_uniformity_basis (λ i _, pow_pos h₀ _) $ λ ε ε0,
  (exists_pow_lt_of_lt_one ε0 h₁).imp $ λ k hk, ⟨trivial, hk.le⟩

lemma geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
  (h : ∀ k < n, c * u k < u (k + 1)) :
  c ^ n * u 0 < u n :=
begin
  refine (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h,
  { simp },
  { simp [pow_succ, mul_assoc, le_refl] }
end

lemma geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, c * u k ≤ u (k + 1)) :
  c ^ n * u 0 ≤ u n :=
by refine (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h; simp [pow_succ, mul_assoc, le_refl]

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
lemma is_o_pow_const_const_pow_of_one_lt {R : Type*} [normed_ring R] (k : ℕ) {r : ℝ} (hr : 1 < r) :
  is_o (λ n, n ^ k : ℕ → R) (λ n, r ^ n) at_top :=
begin
  have : tendsto (λ x : ℝ, x ^ k) (𝓝[Ioi 1] 1) (𝓝 1),
    from ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left,
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhds_within).exists,
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le,
  suffices : is_O _ (λ n : ℕ, (r' ^ k) ^ n) at_top,
    from this.trans_is_o (is_o_pow_pow_of_lt_left (pow_nonneg h0 _) hr'),
  conv in ((r' ^ _) ^ _) { rw [← pow_mul, mul_comm, pow_mul] },
  suffices : ∀ n : ℕ, ∥(n : R)∥ ≤ (r' - 1)⁻¹ * ∥(1 : R)∥ * ∥r' ^ n∥,
    from (is_O_of_le' _ this).pow _,
  intro n, rw mul_right_comm,
  refine n.norm_cast_le.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _)),
  simpa [div_eq_inv_mul, real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1
end

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
lemma is_o_coe_const_pow_of_one_lt {R : Type*} [normed_ring R] {r : ℝ} (hr : 1 < r) :
  is_o (coe : ℕ → R) (λ n, r ^ n) at_top :=
by simpa only [pow_one] using is_o_pow_const_const_pow_of_one_lt 1 hr

/-- If `∥r₁∥ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
lemma is_o_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [normed_ring R] (k : ℕ)
  {r₁ : R} {r₂ : ℝ} (h : ∥r₁∥ < r₂) :
  is_o (λ n, n ^ k * r₁ ^ n : ℕ → R) (λ n, r₂ ^ n) at_top :=
begin
  by_cases h0 : r₁ = 0,
  { refine (is_o_zero _ _).congr' (mem_at_top_sets.2 $ ⟨1, λ n hn, _⟩) eventually_eq.rfl,
    simp [zero_pow (zero_lt_one.trans_le hn), h0] },
  rw [← ne.def, ← norm_pos_iff] at h0,
  have A : is_o (λ n, n ^ k : ℕ → R) (λ n, (r₂ / ∥r₁∥) ^ n) at_top,
    from is_o_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h),
  suffices : is_O (λ n, r₁ ^ n) (λ n, ∥r₁∥ ^ n) at_top,
    by simpa [div_mul_cancel _ (pow_pos h0 _).ne'] using A.mul_is_O this,
  exact is_O.of_bound 1 (by simpa using eventually_norm_pow_le r₁)
end

lemma tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
  tendsto (λ n, n ^ k / r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
(is_o_pow_const_const_pow_of_one_lt k hr).tendsto_0

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
lemma tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : abs r < 1) :
  tendsto (λ n, n ^ k * r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
begin
  by_cases h0 : r = 0,
  { exact tendsto_const_nhds.congr'
      (mem_at_top_sets.2 ⟨1, λ n hn, by simp [zero_lt_one.trans_le hn, h0]⟩) },
  have hr' : 1 < (abs r)⁻¹, from one_lt_inv (abs_pos.2 h0) hr,
  rw tendsto_zero_iff_norm_tendsto_zero,
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'
end

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
lemma tendsto_at_top_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c)
  (hu : ∀ n, c * v n ≤ v (n + 1)) : tendsto v at_top at_top :=
tendsto_at_top_mono (λ n, geom_le (zero_le_one.trans hc.le) n (λ k hk, hu k)) $
  (tendsto_pow_at_top_at_top_of_one_lt hc).at_top_mul_const h₀

lemma nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0} (hr : r < 1) :
  tendsto (λ n:ℕ, r^n) at_top (𝓝 0) :=
nnreal.tendsto_coe.1 $ by simp only [nnreal.coe_pow, nnreal.coe_zero,
  tendsto_pow_at_top_nhds_0_of_lt_1 r.coe_nonneg hr]

lemma ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0∞} (hr : r < 1) :
  tendsto (λ n:ℕ, r^n) at_top (𝓝 0) :=
begin
  rcases ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩,
  rw [← ennreal.coe_zero],
  norm_cast at *,
  apply nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 hr
end

/-- In a normed ring, the powers of an element x with `∥x∥ < 1` tend to zero. -/
lemma tendsto_pow_at_top_nhds_0_of_norm_lt_1 {R : Type*} [normed_ring R] {x : R}
  (h : ∥x∥ < 1) : tendsto (λ (n : ℕ), x ^ n) at_top (𝓝 0) :=
begin
  apply squeeze_zero_norm' (eventually_norm_pow_le x),
  exact tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _) h,
end

lemma tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : abs r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝 0) :=
tendsto_pow_at_top_nhds_0_of_norm_lt_1 h

/-! ### Geometric series-/
section geometric

lemma has_sum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  has_sum (λn:ℕ, r ^ n) (1 - r)⁻¹ :=
have r ≠ 1, from ne_of_lt h₂,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (𝓝 ((0 - 1) * (r - 1)⁻¹)),
  from ((tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds,
have (λ n, (∑ i in range n, r ^ i)) = (λ n, geom_sum r n) := rfl,
(has_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr $
  by simp [neg_inv, geom_sum_eq, div_eq_mul_inv, *] at *

lemma summable_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, has_sum_geometric_of_lt_1 h₁ h₂⟩

lemma tsum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
(has_sum_geometric_of_lt_1 h₁ h₂).tsum_eq

lemma has_sum_geometric_two : has_sum (λn:ℕ, ((1:ℝ)/2) ^ n) 2 :=
by convert has_sum_geometric_of_lt_1 _ _; norm_num

lemma summable_geometric_two : summable (λn:ℕ, ((1:ℝ)/2) ^ n) :=
⟨_, has_sum_geometric_two⟩

lemma tsum_geometric_two : ∑'n:ℕ, ((1:ℝ)/2) ^ n = 2 :=
has_sum_geometric_two.tsum_eq

lemma sum_geometric_two_le (n : ℕ) : ∑ (i : ℕ) in range n, (1 / (2 : ℝ)) ^ i ≤ 2 :=
begin
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i,
  { intro i, apply pow_nonneg, norm_num },
  convert sum_le_tsum (range n) (λ i _, this i) summable_geometric_two,
  exact tsum_geometric_two.symm
end

lemma has_sum_geometric_two' (a : ℝ) : has_sum (λn:ℕ, (a / 2) / 2 ^ n) a :=
begin
  convert has_sum.mul_left (a / 2) (has_sum_geometric_of_lt_1
    (le_of_lt one_half_pos) one_half_lt_one),
  { funext n, simp, refl, },
  { norm_num }
end

lemma summable_geometric_two' (a : ℝ) : summable (λ n:ℕ, (a / 2) / 2 ^ n) :=
⟨a, has_sum_geometric_two' a⟩

lemma tsum_geometric_two' (a : ℝ) : ∑' n:ℕ, (a / 2) / 2^n = a :=
(has_sum_geometric_two' a).tsum_eq

lemma nnreal.has_sum_geometric {r : ℝ≥0} (hr : r < 1) :
  has_sum (λ n : ℕ, r ^ n) (1 - r)⁻¹ :=
begin
  apply nnreal.has_sum_coe.1,
  push_cast,
  rw [nnreal.coe_sub (le_of_lt hr)],
  exact has_sum_geometric_of_lt_1 r.coe_nonneg hr
end

lemma nnreal.summable_geometric {r : ℝ≥0} (hr : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, nnreal.has_sum_geometric hr⟩

lemma tsum_geometric_nnreal {r : ℝ≥0} (hr : r < 1) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
(nnreal.has_sum_geometric hr).tsum_eq

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
lemma ennreal.tsum_geometric (r : ℝ≥0∞) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
begin
  cases lt_or_le r 1 with hr hr,
  { rcases ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩,
    norm_cast at *,
    convert ennreal.tsum_coe_eq (nnreal.has_sum_geometric hr),
    rw [ennreal.coe_inv $ ne_of_gt $ nnreal.sub_pos.2 hr] },
  { rw [ennreal.sub_eq_zero_of_le hr, ennreal.inv_zero, ennreal.tsum_eq_supr_nat, supr_eq_top],
    refine λ a ha, (ennreal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp
      (λ n hn, lt_of_lt_of_le hn _),
    have : ∀ k:ℕ, 1 ≤ r^k, by simpa using canonically_ordered_semiring.pow_le_pow_of_le_left hr,
    calc (n:ℝ≥0∞) = (∑ i in range n, 1) : by rw [sum_const, nsmul_one, card_range]
    ... ≤ ∑ i in range n, r ^ i : sum_le_sum (λ k _, this k) }
end

variables {K : Type*} [normed_field K] {ξ : K}

lemma has_sum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : has_sum (λn:ℕ, ξ ^ n) (1 - ξ)⁻¹ :=
begin
  have xi_ne_one : ξ ≠ 1, by { contrapose! h, simp [h] },
  have A : tendsto (λn, (ξ ^ n - 1) * (ξ - 1)⁻¹) at_top (𝓝 ((0 - 1) * (ξ - 1)⁻¹)),
    from ((tendsto_pow_at_top_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds,
  have B : (λ n, (∑ i in range n, ξ ^ i)) = (λ n, geom_sum ξ n) := rfl,
  rw [has_sum_iff_tendsto_nat_of_summable_norm, B],
  { simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A },
  { simp [normed_field.norm_pow, summable_geometric_of_lt_1 (norm_nonneg _) h] }
end

lemma summable_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : summable (λn:ℕ, ξ ^ n) :=
⟨_, has_sum_geometric_of_norm_lt_1 h⟩

lemma tsum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : ∑'n:ℕ, ξ ^ n = (1 - ξ)⁻¹ :=
(has_sum_geometric_of_norm_lt_1 h).tsum_eq

lemma has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : has_sum (λn:ℕ, r ^ n) (1 - r)⁻¹ :=
has_sum_geometric_of_norm_lt_1 h

lemma summable_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : summable (λn:ℕ, r ^ n) :=
summable_geometric_of_norm_lt_1 h

lemma tsum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
tsum_geometric_of_norm_lt_1 h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp] lemma summable_geometric_iff_norm_lt_1 : summable (λ n : ℕ, ξ ^ n) ↔ ∥ξ∥ < 1 :=
begin
  refine ⟨λ h, _, summable_geometric_of_norm_lt_1⟩,
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists,
  simp only [normed_field.norm_pow, dist_zero_right] at hk,
  rw [← one_pow k] at hk,
  exact lt_of_pow_lt_pow _ zero_le_one hk
end

end geometric

section mul_geometric

lemma summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type*} [normed_ring R]
  (k : ℕ) {r : R} (hr : ∥r∥ < 1) : summable (λ n : ℕ, ∥(n ^ k * r ^ n : R)∥) :=
begin
  rcases exists_between hr with ⟨r', hrr', h⟩,
  exact summable_of_is_O_nat _ (summable_geometric_of_lt_1 ((norm_nonneg _).trans hrr'.le) h)
    (is_o_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').is_O.norm_left
end

lemma summable_pow_mul_geometric_of_norm_lt_1 {R : Type*} [normed_ring R] [complete_space R]
  (k : ℕ) {r : R} (hr : ∥r∥ < 1) : summable (λ n, n ^ k * r ^ n : ℕ → R) :=
summable_of_summable_norm $ summable_norm_pow_mul_geometric_of_norm_lt_1 _ hr

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
lemma has_sum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type*} [normed_field 𝕜] [complete_space 𝕜]
  {r : 𝕜} (hr : ∥r∥ < 1) : has_sum (λ n, n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) :=
begin
  have A : summable (λ n, n * r ^ n : ℕ → 𝕜),
    by simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hr,
  have B : has_sum (pow r : ℕ → 𝕜) (1 - r)⁻¹, from has_sum_geometric_of_norm_lt_1 hr,
  refine A.has_sum_iff.2 _,
  have hr' : r ≠ 1, by { rintro rfl, simpa [lt_irrefl] using hr },
  set s : 𝕜 := ∑' n : ℕ, n * r ^ n,
  calc s = (1 - r) * s / (1 - r) : (mul_div_cancel_left _ (sub_ne_zero.2 hr'.symm)).symm
  ... = (s - r * s) / (1 - r) : by rw [sub_mul, one_mul]
  ... = ((0 : ℕ) * r ^ 0 + (∑' n : ℕ, (n + 1) * r ^ (n + 1)) - r * s) / (1 - r) :
    by { congr, exact tsum_eq_zero_add A }
  ... = (r * (∑' n : ℕ, (n + 1) * r ^ n) - r * s) / (1 - r) :
    by simp [pow_succ, mul_left_comm _ r, tsum_mul_left]
  ... = r / (1 - r) ^ 2 :
    by simp [add_mul, tsum_add A B.summable, mul_add, B.tsum_eq, ← div_eq_mul_inv, pow_two,
      div_div_eq_div_mul]
end

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
lemma tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type*} [normed_field 𝕜] [complete_space 𝕜]
  {r : 𝕜} (hr : ∥r∥ < 1) :
  (∑' n : ℕ, n * r ^ n : 𝕜) = (r / (1 - r) ^ 2) :=
(has_sum_coe_mul_geometric_of_norm_lt_1 hr).tsum_eq

end mul_geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/
section edist_le_geometric

variables [emetric_space α] (r C : ℝ≥0∞) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀n, edist (f n) (f (n+1)) ≤ C * r^n)

include hr hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.-/
lemma cauchy_seq_of_edist_le_geometric : cauchy_seq f :=
begin
  refine cauchy_seq_of_edist_le_of_tsum_ne_top _ hu _,
  rw [ennreal.tsum_mul_left, ennreal.tsum_geometric],
  refine ennreal.mul_ne_top hC (ennreal.inv_ne_top.2 _),
  exact ne_of_gt (ennreal.zero_lt_sub_iff_lt.2 hr)
end

omit hr hC

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
lemma edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  edist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  convert edist_le_tsum_of_edist_le_of_tendsto _ hu ha _,
  simp only [pow_add, ennreal.tsum_mul_left, ennreal.tsum_geometric, div_eq_mul_inv, mul_assoc]
end

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
lemma edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  edist (f 0) a ≤ C / (1 - r) :=
by simpa only [pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end edist_le_geometric

section edist_le_geometric_two

variables [emetric_space α] (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀n, edist (f n) (f (n+1)) ≤ C / 2^n) {a : α} (ha : tendsto f at_top (𝓝 a))

include hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence.-/
lemma cauchy_seq_of_edist_le_geometric_two : cauchy_seq f :=
begin
  simp only [div_eq_mul_inv, ennreal.inv_pow] at hu,
  refine cauchy_seq_of_edist_le_geometric 2⁻¹ C _ hC hu,
  simp [ennreal.one_lt_two]
end

omit hC
include ha

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
lemma edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) :
  edist (f n) a ≤ 2 * C / 2^n :=
begin
  simp only [div_eq_mul_inv, ennreal.inv_pow] at *,
  rw [mul_assoc, mul_comm],
  convert edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n,
  rw [ennreal.one_sub_inv_two, ennreal.inv_inv]
end

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
lemma edist_le_of_edist_le_geometric_two_of_tendsto₀: edist (f 0) a ≤ 2 * C :=
by simpa only [pow_zero, div_eq_mul_inv, ennreal.inv_one, mul_one]
  using edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end edist_le_geometric_two

section le_geometric

variables [metric_space α] {r C : ℝ} (hr : r < 1) {f : ℕ → α}
  (hu : ∀n, dist (f n) (f (n+1)) ≤ C * r^n)

include hr hu

lemma aux_has_sum_of_le_geometric : has_sum (λ n : ℕ, C * r^n) (C / (1 - r)) :=
begin
  rcases sign_cases_of_C_mul_pow_nonneg (λ n, dist_nonneg.trans (hu n)) with rfl | ⟨C₀, r₀⟩,
  { simp [has_sum_zero] },
  { refine has_sum.mul_left C _,
    simpa using has_sum_geometric_of_lt_1 r₀ hr }
end

variables (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
lemma cauchy_seq_of_le_geometric : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
lemma dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C / (1 - r) :=
(aux_has_sum_of_le_geometric hr hu).tsum_eq ▸
  dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
lemma dist_le_of_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  have := aux_has_sum_of_le_geometric hr hu,
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n,
  simp only [pow_add, mul_left_comm C, mul_div_right_comm],
  rw [mul_comm],
  exact (this.mul_left _).tsum_eq.symm
end

omit hr hu

variable (hu₂ : ∀ n, dist (f n) (f (n+1)) ≤ (C / 2) / 2^n)

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
lemma cauchy_seq_of_le_geometric_two : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu₂ $ ⟨_, has_sum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
lemma dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C :=
(tsum_geometric_two' C) ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
lemma dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ C / 2^n :=
begin
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n,
  simp only [add_comm n, pow_add, ← div_div_eq_div_mul],
  symmetry,
  exact ((has_sum_geometric_two' C).div_const _).tsum_eq
end

end le_geometric

section summable_le_geometric

variables [normed_group α] {r C : ℝ} {f : ℕ → α}

lemma dist_partial_sum_le_of_le_geometric (hf : ∀n, ∥f n∥ ≤ C * r^n) (n : ℕ) :
  dist (∑ i in range n, f i) (∑ i in range (n+1), f i) ≤ C * r ^ n :=
begin
  rw [sum_range_succ, dist_eq_norm, ← norm_neg],
  convert hf n,
  rw [neg_sub, add_sub_cancel]
end

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
lemma cauchy_seq_finset_of_geometric_bound (hr : r < 1) (hf : ∀n, ∥f n∥ ≤ C * r^n) :
  cauchy_seq (λ s : finset (ℕ), ∑ x in s, f x) :=
cauchy_seq_finset_of_norm_bounded _
  (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
lemma norm_sub_le_of_geometric_bound_of_has_sum (hr : r < 1) (hf : ∀n, ∥f n∥ ≤ C * r^n)
  {a : α} (ha : has_sum f a) (n : ℕ) :
  ∥(∑ x in finset.range n, f x) - a∥ ≤ (C * r ^ n) / (1 - r) :=
begin
  rw ← dist_eq_norm,
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf),
  exact ha.tendsto_sum_nat
end

end summable_le_geometric

section normed_ring_geometric
variables {R : Type*} [normed_ring R] [complete_space R]

open normed_space

/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
lemma normed_ring.summable_geometric_of_norm_lt_1
  (x : R) (h : ∥x∥ < 1) : summable (λ (n:ℕ), x ^ n) :=
begin
  have h1 : summable (λ (n:ℕ), ∥x∥ ^ n) := summable_geometric_of_lt_1 (norm_nonneg _) h,
  refine summable_of_norm_bounded_eventually _ h1 _,
  rw nat.cofinite_eq_at_top,
  exact eventually_norm_pow_le x,
end

/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `∥1∥ = 1`. -/
lemma normed_ring.tsum_geometric_of_norm_lt_1
  (x : R) (h : ∥x∥ < 1) : ∥∑' n:ℕ, x ^ n∥ ≤ ∥(1:R)∥ - 1 + (1 - ∥x∥)⁻¹ :=
begin
  rw tsum_eq_zero_add (normed_ring.summable_geometric_of_norm_lt_1 x h),
  simp only [pow_zero],
  refine le_trans (norm_add_le _ _) _,
  have : ∥∑' b : ℕ, (λ n, x ^ (n + 1)) b∥ ≤ (1 - ∥x∥)⁻¹ - 1,
  { refine tsum_of_norm_bounded _ (λ b, norm_pow_le' _ (nat.succ_pos b)),
    convert (has_sum_nat_add_iff' 1).mpr (has_sum_geometric_of_lt_1 (norm_nonneg x) h),
    simp },
  linarith
end

lemma geom_series_mul_neg (x : R) (h : ∥x∥ < 1) :
  (∑' i:ℕ, x ^ i) * (1 - x) = 1 :=
begin
  have := ((normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_right (1 - x)),
  refine tendsto_nhds_unique this.tendsto_sum_nat _,
  have : tendsto (λ (n : ℕ), 1 - x ^ n) at_top (𝓝 1),
  { simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h) },
  convert ← this,
  ext n,
  rw [←geom_sum_mul_neg, geom_sum_def, finset.sum_mul],
end

lemma mul_neg_geom_series (x : R) (h : ∥x∥ < 1) :
  (1 - x) * ∑' i:ℕ, x ^ i = 1 :=
begin
  have := (normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_left (1 - x),
  refine tendsto_nhds_unique this.tendsto_sum_nat _,
  have : tendsto (λ (n : ℕ), 1 - x ^ n) at_top (nhds 1),
  { simpa using tendsto_const_nhds.sub
      (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h) },
  convert ← this,
  ext n,
  rw [←mul_neg_geom_sum, geom_sum_def, finset.mul_sum]
end

end normed_ring_geometric

/-! ### Positive sequences with small sums on encodable types -/

/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def pos_sum_of_encodable {ε : ℝ} (hε : 0 < ε)
  (ι) [encodable ι] : {ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, has_sum ε' c ∧ c ≤ ε} :=
begin
  let f := λ n, (ε / 2) / 2 ^ n,
  have hf : has_sum f ε := has_sum_geometric_two' _,
  have f0 : ∀ n, 0 < f n := λ n, div_pos (half_pos hε) (pow_pos zero_lt_two _),
  refine ⟨f ∘ encodable.encode, λ i, f0 _, _⟩,
  rcases hf.summable.comp_injective (@encodable.encode_injective ι _) with ⟨c, hg⟩,
  refine ⟨c, hg, has_sum_le_inj _ (@encodable.encode_injective ι _) _ _ hg hf⟩,
  { assume i _, exact le_of_lt (f0 _) },
  { assume n, exact le_refl _ }
end

namespace nnreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0} (hε : 0 < ε) (ι) [encodable ι] :
  ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∃c, has_sum ε' c ∧ c < ε :=
let ⟨a, a0, aε⟩ := exists_between hε in
let ⟨ε', hε', c, hc, hcε⟩ := pos_sum_of_encodable a0 ι in
⟨ λi, ⟨ε' i, le_of_lt $ hε' i⟩, assume i, nnreal.coe_lt_coe.2 $ hε' i,
  ⟨c, has_sum_le (assume i, le_of_lt $ hε' i) has_sum_zero hc ⟩, nnreal.has_sum_coe.1 hc,
   lt_of_le_of_lt (nnreal.coe_le_coe.1 hcε) aε ⟩

end nnreal

namespace ennreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0∞} (hε : 0 < ε) (ι) [encodable ι] :
  ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∑' i, (ε' i : ℝ≥0∞) < ε :=
begin
  rcases exists_between hε with ⟨r, h0r, hrε⟩,
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, hx⟩,
  rcases nnreal.exists_pos_sum_of_encodable (coe_lt_coe.1 h0r) ι with ⟨ε', hp, c, hc, hcr⟩,
  exact ⟨ε', hp, (ennreal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩
end

end ennreal

/-!
### Factorial
-/

lemma factorial_tendsto_at_top : tendsto nat.factorial at_top at_top :=
tendsto_at_top_at_top_of_monotone nat.monotone_factorial (λ n, ⟨n, n.self_le_factorial⟩)

lemma tendsto_factorial_div_pow_self_at_top : tendsto (λ n, n! / n^n : ℕ → ℝ) at_top (𝓝 0) :=
tendsto_of_tendsto_of_tendsto_of_le_of_le'
  tendsto_const_nhds
  (tendsto_const_div_at_top_nhds_0_nat 1)
  (eventually_of_forall $ λ n, div_nonneg (by exact_mod_cast n.factorial_pos.le)
    (pow_nonneg (by exact_mod_cast n.zero_le) _))
  begin
    refine (eventually_gt_at_top 0).mono (λ n hn, _),
    rcases nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩,
    rw [← prod_range_add_one_eq_factorial, pow_eq_prod_const, div_eq_mul_inv, ← inv_eq_one_div,
      prod_nat_cast, nat.cast_succ, ← prod_inv_distrib', ← prod_mul_distrib,
      finset.prod_range_succ'],
    simp only [prod_range_succ', one_mul, nat.cast_add, zero_add, nat.cast_one],
    refine mul_le_of_le_one_left (inv_nonneg.mpr $ by exact_mod_cast hn.le) (prod_le_one _ _);
      intros x hx; rw finset.mem_range at hx,
    { refine mul_nonneg _ (inv_nonneg.mpr _); norm_cast; linarith },
    { refine (div_le_one $ by exact_mod_cast hn).mpr _, norm_cast, linarith }
  end
