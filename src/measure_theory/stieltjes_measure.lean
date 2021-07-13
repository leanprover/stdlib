/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel
-/
import measure_theory.borel_space

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corrresponding measure, giving mass `f b - f a` to the interval `(a, b]`.

## Main definitions

* `stieltjes_function` is a structure containing a function from `ℝ → ℝ`, together with the
assertions that it is monotone and right-continuous. To `f : stieltjes_function`, one associates
a Borel measure `f.measure`.
* `f.left_lim x` is the limit of `f` to the left of `x`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = of_real (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = of_real (f.left_lim b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/

noncomputable theory
open classical set filter
open ennreal (of_real)
open_locale big_operators ennreal nnreal topological_space

/-! ### Basic properties of Stieltjes functions -/

/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure stieltjes_function :=
(to_fun : ℝ → ℝ)
(mono' : monotone to_fun)
(right_continuous' : ∀ x, continuous_within_at to_fun (Ici x) x)

namespace stieltjes_function

instance : has_coe_to_fun stieltjes_function := ⟨_, to_fun⟩

variable (f : stieltjes_function)

lemma mono : monotone f := f.mono'

lemma right_continuous (x : ℝ) : continuous_within_at f (Ici x) x := f.right_continuous' x

/-- The limit of a Stieltjes function to the left of `x` (it exists by monotonicity). The fact that
it is indeed a left limit is asserted in `tendsto_left_lim` -/
@[irreducible] def left_lim (x : ℝ) := Sup (f '' (Iio x))

lemma tendsto_left_lim (x : ℝ) : tendsto f (𝓝[Iio x] x) (𝓝 (f.left_lim x)) :=
by { rw left_lim, exact f.mono.tendsto_nhds_within_Iio x }

lemma left_lim_le {x y : ℝ} (h : x ≤ y) : f.left_lim x ≤ f y :=
begin
  apply le_of_tendsto (f.tendsto_left_lim x),
  filter_upwards [self_mem_nhds_within],
  assume z hz,
  exact (f.mono (le_of_lt hz)).trans (f.mono h)
end

lemma le_left_lim {x y : ℝ} (h : x < y) : f x ≤ f.left_lim y :=
begin
  apply ge_of_tendsto (f.tendsto_left_lim y),
  apply mem_nhds_within_Iio_iff_exists_Ioo_subset.2 ⟨x, h, _⟩,
  assume z hz,
  exact f.mono hz.1.le,
end

lemma left_lim_le_left_lim {x y : ℝ} (h : x ≤ y) : f.left_lim x ≤ f.left_lim y :=
begin
  rcases eq_or_lt_of_le h with rfl|hxy,
  { exact le_rfl },
  { exact (f.left_lim_le le_rfl).trans (f.le_left_lim hxy) }
end

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
protected def id : stieltjes_function :=
{ to_fun := id,
  mono' := λ x y, id,
  right_continuous' := λ x, continuous_within_at_id }

@[simp] lemma id_apply (x : ℝ) : stieltjes_function.id x = x := rfl

@[simp] lemma id_left_lim (x : ℝ) : stieltjes_function.id.left_lim x = x :=
tendsto_nhds_unique (stieltjes_function.id.tendsto_left_lim x) $
  (continuous_at_id).tendsto.mono_left nhds_within_le_nhds

instance : inhabited stieltjes_function := ⟨stieltjes_function.id⟩

/-! ### The outer measure associated to a Stieltjes function -/

/-- Length of an interval. This is the largest monotonic function which correctly
  measures all intervals. -/
def length (s : set ℝ) : ℝ≥0∞ := ⨅a b (h : s ⊆ Ioc a b), of_real (f b - f a)

@[simp] lemma length_empty : f.length ∅ = 0 :=
nonpos_iff_eq_zero.1 $ infi_le_of_le 0 $ infi_le_of_le 0 $ by simp

@[simp] lemma length_Ioc (a b : ℝ) :
  f.length (Ioc a b) = of_real (f b - f a) :=
begin
  refine le_antisymm (infi_le_of_le a $ binfi_le b (subset.refl _))
    (le_infi $ λ a', le_infi $ λ b', le_infi $ λ h, ennreal.coe_le_coe.2 _),
  cases le_or_lt b a with ab ab,
  { rw real.to_nnreal_of_nonpos (sub_nonpos.2 (f.mono ab)), apply zero_le, },
  cases (Ioc_subset_Ioc_iff ab).1 h with h₁ h₂,
  exact real.to_nnreal_le_to_nnreal (sub_le_sub (f.mono h₁) (f.mono h₂))
end

lemma length_mono {s₁ s₂ : set ℝ} (h : s₁ ⊆ s₂) :
  f.length s₁ ≤ f.length s₂ :=
infi_le_infi $ λ a, infi_le_infi $ λ b, infi_le_infi2 $ λ h', ⟨subset.trans h h', le_refl _⟩

open measure_theory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : outer_measure ℝ :=
outer_measure.of_function f.length f.length_empty

lemma outer_le_length (s : set ℝ) : f.outer s ≤ f.length s :=
outer_measure.of_function_le _

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
lemma length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ}
  (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
  of_real (f b - f a) ≤ ∑' i, of_real (f (d i) - f (c i)) :=
begin
  suffices : ∀ (s:finset ℕ) b
    (cv : Icc a b ⊆ ⋃ i ∈ (↑s:set ℕ), Ioo (c i) (d i)),
    (of_real (f b - f a) : ℝ≥0∞) ≤ ∑ i in s, of_real (f (d i) - f (c i)),
  { rcases is_compact_Icc.elim_finite_subcover_image (λ (i : ℕ) (_ : i ∈ univ),
      @is_open_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with ⟨s, su, hf, hs⟩,
    have e : (⋃ i ∈ (↑hf.to_finset:set ℕ), Ioo (c i) (d i)) = (⋃ i ∈ s, Ioo (c i) (d i)),
      by simp only [ext_iff, exists_prop, finset.set_bUnion_coe, mem_Union, forall_const, iff_self,
                    finite.mem_to_finset],
    rw ennreal.tsum_eq_supr_sum,
    refine le_trans _ (le_supr _ hf.to_finset),
    exact this hf.to_finset _ (by simpa only [e]) },
  clear ss b,
  refine λ s, finset.strong_induction_on s (λ s IH b cv, _),
  cases le_total b a with ab ab,
  { rw ennreal.of_real_eq_zero.2 (sub_nonpos.2 (f.mono ab)), exact zero_le _, },
  have := cv ⟨ab, le_refl _⟩, simp at this,
  rcases this with ⟨i, is, cb, bd⟩,
  rw [← finset.insert_erase is] at cv ⊢,
  rw [finset.coe_insert, bUnion_insert] at cv,
  rw [finset.sum_insert (finset.not_mem_erase _ _)],
  refine le_trans _ (add_le_add_left (IH _ (finset.erase_ssubset is) (c i) _) _),
  { refine le_trans (ennreal.of_real_le_of_real _) ennreal.of_real_add_le,
    rw sub_add_sub_cancel,
    exact sub_le_sub_right (f.mono bd.le) _ },
  { rintro x ⟨h₁, h₂⟩,
    refine (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left
      (mt and.left (not_lt_of_le h₂)) }
end

@[simp] lemma outer_Ioc (a b : ℝ) :
  f.outer (Ioc a b) = of_real (f b - f a) :=
begin
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
  by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
  intervals, while we would like to have a compact interval covered by open intervals to use
  compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use the
  right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is still
  covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a` (up to `ε/2`).
  Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
  very close to  that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
  slightly to the right, then the `f`-length will change very little by right continuity, and we
  will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
  of the `f`-length of `s i`. -/
  refine le_antisymm (by { rw ← f.length_Ioc, apply outer_le_length })
    (le_binfi $ λ s hs, ennreal.le_of_forall_pos_le_add $ λ ε εpos h, _),
  let δ := ε/2,
  have δpos : 0 < δ := nnreal.half_pos εpos,
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 δpos) ℕ with ⟨ε', ε'0, hε⟩,
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a',
  { have A : continuous_within_at (λ r, f r - f a) (Ioi a) a,
    { refine continuous_within_at.sub _ continuous_within_at_const,
      exact (f.right_continuous a).mono Ioi_subset_Ici_self },
    have B : f a - f a < δ, by rwa [sub_self],
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhds_within).exists },
  have : ∀ i, ∃ p:ℝ×ℝ, s i ⊆ Ioo p.1 p.2 ∧
                        (of_real (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i) + ε' i,
  { intro i,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum i) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 i))),
    conv at this { to_lhs, rw length },
    simp only [infi_lt_iff, exists_prop] at this,
    rcases this with ⟨p, q', spq, hq'⟩,
    have : continuous_within_at (λ r, of_real (f r - f p)) (Ioi q') q',
    { apply ennreal.continuous_of_real.continuous_at.comp_continuous_within_at,
      refine continuous_within_at.sub _ continuous_within_at_const,
      exact (f.right_continuous q').mono Ioi_subset_Ici_self },
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhds_within).exists with ⟨q, hq, q'q⟩,
    exact ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩ },
  choose g hg using this,
  have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 := calc
    Icc a' b ⊆ Ioc a b : λ x hx, ⟨aa'.trans_le hx.1, hx.2⟩
    ... ⊆ ⋃ i, s i : hs
    ... ⊆ ⋃ i, Ioo (g i).1 (g i).2 : Union_subset_Union (λ i, (hg i).1),
  calc of_real (f b - f a)
      = of_real ((f b - f a') + (f a' - f a)) : by rw sub_add_sub_cancel
  ... ≤ of_real (f b - f a') + of_real (f a' - f a) : ennreal.of_real_add_le
  ... ≤ (∑' i, of_real (f (g i).2 - f (g i).1)) + of_real δ :
    add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ennreal.of_real_le_of_real ha'.le)
  ... ≤ (∑' i, (f.length (s i) + ε' i)) + δ :
    add_le_add (ennreal.tsum_le_tsum (λ i, (hg i).2.le))
      (by simp only [ennreal.of_real_coe_nnreal, le_rfl])
  ... = (∑' i, f.length (s i)) + (∑' i, ε' i) + δ : by rw [ennreal.tsum_add]
  ... ≤ (∑' i, f.length (s i)) + δ + δ : add_le_add (add_le_add le_rfl hε.le) le_rfl
  ... = ∑' (i : ℕ), f.length (s i) + ε : by simp [add_assoc, ennreal.add_halves]
end

lemma measurable_set_Ioi {c : ℝ} :
  f.outer.caratheodory.measurable_set' (Ioi c) :=
begin
  apply outer_measure.of_function_caratheodory (λ t, _),
  refine le_infi (λ a, le_infi (λ b, le_infi (λ h, _))),
  refine le_trans (add_le_add
    (f.length_mono $ inter_subset_inter_left _ h)
    (f.length_mono $ diff_subset_diff_left h)) _,
  cases le_total a c with hac hac; cases le_total b c with hbc hbc,
  { simp only [Ioc_inter_Ioi, f.length_Ioc, hac, sup_eq_max, hbc, le_refl,
      Ioc_eq_empty, max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add] },
  { simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      sup_eq_max, ←ennreal.of_real_add, f.mono hac, f.mono hbc, sub_nonneg, sub_add_sub_cancel,
      le_refl, max_eq_right] },
  { simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi,
      f.length_empty, zero_add, or_true, le_sup_iff, f.length_Ioc] },
  { simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      sup_eq_max, le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty] }
end

theorem outer_trim : f.outer.trim = f.outer :=
begin
  refine le_antisymm (λ s, _) (outer_measure.le_trim _),
  rw outer_measure.trim_eq_infi,
  refine le_infi (λ t, le_infi $ λ ht,
    ennreal.le_of_forall_pos_le_add $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 ε0) ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left (le_of_lt hε) _),
  rw ← ennreal.tsum_add,
  choose g hg using show
    ∀ i, ∃ s, t i ⊆ s ∧ measurable_set s ∧
      f.outer s ≤ f.length (t i) + of_real (ε' i),
  { intro i,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum i) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 i))),
    conv at this {to_lhs, rw length},
    simp only [infi_lt_iff] at this,
    rcases this with ⟨a, b, h₁, h₂⟩,
    rw ← f.outer_Ioc at h₂,
    exact ⟨_, h₁, measurable_set_Ioc, le_of_lt $ by simpa using h₂⟩ },
  simp at hg,
  apply infi_le_of_le (Union g) _,
  apply infi_le_of_le (subset.trans ht $ Union_subset_Union (λ i, (hg i).1)) _,
  apply infi_le_of_le (measurable_set.Union (λ i, (hg i).2.1)) _,
  exact le_trans (f.outer.Union _) (ennreal.tsum_le_tsum $ λ i, (hg i).2.2)
end

lemma borel_le_measurable : borel ℝ ≤ f.outer.caratheodory :=
begin
  rw borel_eq_generate_Ioi,
  refine measurable_space.generate_from_le _,
  simp [f.measurable_set_Ioi] { contextual := tt }
end

/-! ### The measure associated to a Stieltjes function -/

/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
@[irreducible] protected def measure : measure ℝ :=
{ to_outer_measure := f.outer,
  m_Union := λ s hs, f.outer.Union_eq_of_caratheodory $
    λ i, f.borel_le_measurable _ (hs i),
  trimmed := f.outer_trim }

@[simp] lemma measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = of_real (f b - f a) :=
by { rw stieltjes_function.measure, exact f.outer_Ioc a b }

@[simp] lemma measure_singleton (a : ℝ) : f.measure {a} = of_real (f a - f.left_lim a) :=
begin
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ : ∃ (u : ℕ → ℝ), strict_mono u ∧ (∀ (n : ℕ), u n < a)
    ∧ tendsto u at_top (𝓝 a) := exists_seq_strict_mono_tendsto a,
  have A : {a} = ⋂ n, Ioc (u n) a,
  { refine subset.antisymm (λ x hx, by simp [mem_singleton_iff.1 hx, u_lt_a]) (λ x hx, _),
    simp at hx,
    have : a ≤ x := le_of_tendsto' u_lim (λ n, (hx n).1.le),
    simp [le_antisymm this (hx 0).2] },
  have L1 : tendsto (λ n, f.measure (Ioc (u n) a)) at_top (𝓝 (f.measure {a})),
  { rw A,
    refine tendsto_measure_Inter (λ n, measurable_set_Ioc) (λ m n hmn, _) _,
    { exact Ioc_subset_Ioc (u_mono.monotone hmn) le_rfl },
    { exact ⟨0, by simp only [measure_Ioc, ennreal.of_real_lt_top]⟩ } },
  have L2 : tendsto (λ n, f.measure (Ioc (u n) a)) at_top (𝓝 (of_real (f a - f.left_lim a))),
  { simp only [measure_Ioc],
    have : tendsto (λ n, f (u n)) at_top (𝓝 (f.left_lim a)),
    { apply (f.tendsto_left_lim a).comp,
      exact tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ u_lim
        (eventually_of_forall (λ n, u_lt_a n)) },
    exact ennreal.continuous_of_real.continuous_at.tendsto.comp (tendsto_const_nhds.sub this) },
  exact tendsto_nhds_unique L1 L2
end

@[simp] lemma measure_Icc (a b : ℝ) : f.measure (Icc a b) = of_real (f b - f.left_lim a) :=
begin
  rcases le_or_lt a b with hab|hab,
  { have A : disjoint {a} (Ioc a b), by simp,
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ennreal.of_real_add, f.left_lim_le,
      measure_union A (measurable_set_singleton a) measurable_set_Ioc, f.mono hab] },
  { simp only [hab, measure_empty, Icc_eq_empty],
    symmetry,
    simp [ennreal.of_real_eq_zero, f.le_left_lim hab] }
end

@[simp] lemma measure_Ioo {a b : ℝ} :
  f.measure (Ioo a b) = of_real (f.left_lim b - f a) :=
begin
  rcases le_or_lt b a with hab|hab,
  { simp only [hab, measure_empty, Ioo_eq_empty],
    symmetry,
    simp [ennreal.of_real_eq_zero, f.left_lim_le hab] },
  { have A : disjoint (Ioo a b) {b}, by simp,
    have D : f b - f a = (f b - f.left_lim b) + (f.left_lim b - f a), by abel,
    have := f.measure_Ioc a b,
    simp only [←Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A measurable_set_Ioo (measurable_set_singleton b), Icc_self] at this,
    rw [D, ennreal.of_real_add, add_comm] at this,
    { simpa only [ennreal.add_right_inj, ennreal.of_real_lt_top] },
    { simp only [f.left_lim_le, sub_nonneg] },
    { simp only [f.le_left_lim hab, sub_nonneg] } },
end

@[simp] lemma measure_Ico (a b : ℝ) : f.measure (Ico a b) = of_real (f.left_lim b - f.left_lim a) :=
begin
  rcases le_or_lt b a with hab|hab,
  { simp only [hab, measure_empty, Ico_eq_empty],
    symmetry,
    simp [ennreal.of_real_eq_zero, f.left_lim_le_left_lim hab] },
  { have A : disjoint {a} (Ioo a b) := by simp,
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, hab.ne, f.left_lim_le,
      measure_union A (measurable_set_singleton a) measurable_set_Ioo, f.le_left_lim hab,
      ← ennreal.of_real_add] }
end

end stieltjes_function
