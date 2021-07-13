/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import topology.instances.ennreal

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0` such that the values have (infinite) sum `1`.

This file features the monadic structure of `pmf` and the Bernoulli distribution

## Implementation Notes

This file is not yet connected to the `measure_theory` library in any way.
At some point we need to define a `measure` from a `pmf` and prove the appropriate lemmas about
that.

## Tags

probability mass function, discrete probability measure, bernoulli distribution
-/
noncomputable theory
variables {α : Type*} {β : Type*} {γ : Type*}
open_locale classical big_operators nnreal ennreal

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such that
  the values have (infinite) sum `1`. -/
def {u} pmf (α : Type u) : Type u := { f : α → ℝ≥0 // has_sum f 1 }

namespace pmf

instance : has_coe_to_fun (pmf α) := ⟨λ p, α → ℝ≥0, λ p a, p.1 a⟩

@[ext] protected lemma ext : ∀ {p q : pmf α}, (∀ a, p a = q a) → p = q
| ⟨f, hf⟩ ⟨g, hg⟩ eq :=  subtype.eq $ funext eq

lemma has_sum_coe_one (p : pmf α) : has_sum p 1 := p.2

lemma summable_coe (p : pmf α) : summable p := (p.has_sum_coe_one).summable

@[simp] lemma tsum_coe (p : pmf α) : ∑' a, p a = 1 := p.has_sum_coe_one.tsum_eq

/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : pmf α) : set α := {a | p.1 a ≠ 0}

@[simp] lemma mem_support_iff (p : pmf α) (a : α) :
  a ∈ p.support ↔ p a ≠ 0 := iff.rfl

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : pmf α := ⟨λ a', if a' = a then 1 else 0, has_sum_ite_eq _ _⟩

@[simp] lemma pure_apply (a a' : α) : pure a a' = (if a' = a then 1 else 0) := rfl

lemma mem_support_pure_iff (a a' : α) : a' ∈ (pure a).support ↔ a' = a :=
by simp

instance [inhabited α] : inhabited (pmf α) := ⟨pure (default α)⟩

lemma coe_le_one (p : pmf α) (a : α) : p a ≤ 1 :=
has_sum_le (by intro b; split_ifs; simp [h]; exact le_refl _) (has_sum_ite_eq a (p a)) p.2

protected lemma bind.summable (p : pmf α) (f : α → pmf β) (b : β) :
  summable (λ a : α, p a * f a b) :=
begin
  refine nnreal.summable_of_le (assume a, _) p.summable_coe,
  suffices : p a * f a b ≤ p a * 1, { simpa },
  exact mul_le_mul_of_nonneg_left ((f a).coe_le_one _) (p a).2
end

/-- The monadic bind operation for `pmf`. -/
def bind (p : pmf α) (f : α → pmf β) : pmf β :=
⟨λ b, ∑'a, p a * f a b,
  begin
    apply ennreal.has_sum_coe.1,
    simp only [ennreal.coe_tsum (bind.summable p f _)],
    rw [ennreal.summable.has_sum_iff, ennreal.tsum_comm],
    simp [ennreal.tsum_mul_left, (ennreal.coe_tsum (f _).summable_coe).symm,
      (ennreal.coe_tsum p.summable_coe).symm]
  end⟩

@[simp] lemma bind_apply (p : pmf α) (f : α → pmf β) (b : β) : p.bind f b = ∑'a, p a * f a b :=
rfl

lemma coe_bind_apply (p : pmf α) (f : α → pmf β) (b : β) :
  (p.bind f b : ℝ≥0∞) = ∑'a, p a * f a b :=
eq.trans (ennreal.coe_tsum $ bind.summable p f b) $ by simp

@[simp] lemma pure_bind (a : α) (f : α → pmf β) : (pure a).bind f = f a :=
have ∀ b a', ite (a' = a) 1 0 * f a' b = ite (a' = a) (f a b) 0, from
  assume b a', by split_ifs; simp; subst h; simp,
by ext b; simp [this]

@[simp] lemma bind_pure (p : pmf α) : p.bind pure = p :=
have ∀ a a', (p a * ite (a' = a) 1 0) = ite (a = a') (p a') 0, from
  assume a a', begin split_ifs; try { subst a }; try { subst a' }; simp * at * end,
by ext b; simp [this]

@[simp] lemma bind_bind (p : pmf α) (f : α → pmf β) (g : β → pmf γ) :
  (p.bind f).bind g = p.bind (λ a, (f a).bind g) :=
begin
  ext1 b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm,
             ennreal.tsum_mul_right.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

lemma bind_comm (p : pmf α) (q : pmf β) (f : α → β → pmf γ) :
  p.bind (λ a, q.bind (f a)) = q.bind (λ b, p.bind (λ a, f a b)) :=
begin
  ext1 b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm,
             ennreal.tsum_mul_right.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

protected lemma bind_on_support.summable (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  summable (λ a : α, p a * if h : p a = 0 then 0 else f a h b) :=
begin
  refine nnreal.summable_of_le (assume a, _) p.summable_coe,
  split_ifs,
  { refine (mul_zero (p a)).symm ▸ le_of_eq h.symm },
  { suffices : p a * f a h b ≤ p a * 1, { simpa },
    exact mul_le_mul_of_nonneg_left ((f a h).coe_le_one _) (p a).2 }
end

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bind_on_support (λ a _, f a)`, see `bind_on_support_eq_bind` -/
def bind_on_support (p : pmf α) (f : ∀ a ∈ p.support, pmf β) : pmf β :=
⟨λ b, ∑' a, p a * if h : p a = 0 then 0 else f a h b,
ennreal.has_sum_coe.1 begin
  simp only [ennreal.coe_tsum (bind_on_support.summable p f _)],
  rw [ennreal.summable.has_sum_iff, ennreal.tsum_comm],
  simp only [ennreal.coe_mul, ennreal.coe_one, ennreal.tsum_mul_left],
  have : ∑' (a : α), (p a : ennreal) = 1 :=
    by simp only [←ennreal.coe_tsum p.summable_coe, ennreal.coe_one, tsum_coe],
  refine trans (tsum_congr (λ a, _)) this,
  split_ifs with h,
  { simp [h] },
  { simp [← ennreal.coe_tsum (f a h).summable_coe, (f a h).tsum_coe] }
end⟩

@[simp] lemma bind_on_support_apply (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  p.bind_on_support f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b := rfl

/-- `bind_on_support` reduces to `bind` if `f` doesn't depend on the additional hypothesis -/
@[simp] lemma bind_on_support_eq_bind (p : pmf α) (f : α → pmf β) :
  p.bind_on_support (λ a _, f a) = p.bind f :=
begin
  ext b,
  simp only [p.bind_on_support_apply (λ a _, f a), p.bind_apply f,
    dite_eq_ite, nnreal.coe_eq, mul_ite, mul_zero],
  refine congr_arg _ (funext (λ a, _)),
  split_ifs with h; simp [h],
end

lemma coe_bind_on_support_apply (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  (p.bind_on_support f b : ℝ≥0∞) = ∑' a, p a * if h : p a = 0 then 0 else f a h b :=
by simp only [bind_on_support_apply, ennreal.coe_tsum (bind_on_support.summable p f b),
    dite_cast, ennreal.coe_mul, ennreal.coe_zero]

@[simp] lemma mem_support_bind_on_support_iff (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  b ∈ (p.bind_on_support f).support ↔ ∃ a (ha : p a ≠ 0), b ∈ (f a ha).support :=
begin
  simp only [mem_support_iff, bind_on_support_apply,
    tsum_ne_zero_iff (bind_on_support.summable p f b), mul_ne_zero_iff],
  split; { rintro ⟨a, ha, haf⟩, refine ⟨a, ha, ne_of_eq_of_ne _ haf⟩, simp [ha], },
end

lemma bind_on_support_eq_zero_iff (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  p.bind_on_support f b = 0 ↔ ∀ a (ha : p a ≠ 0), f a ha b = 0 :=
begin
  simp only [bind_on_support_apply, tsum_eq_zero_iff (bind_on_support.summable p f b),
    mul_eq_zero, or_iff_not_imp_left],
  exact ⟨λ h a ha, trans (dif_neg ha).symm (h a ha), λ h a ha, trans (dif_neg ha) (h a ha)⟩,
end

@[simp] lemma pure_bind_on_support (a : α) (f : ∀ (a' : α) (ha : a' ∈ (pure a).support), pmf β) :
  (pure a).bind_on_support f = f a ((mem_support_pure_iff a a).mpr rfl) :=
begin
  refine pmf.ext (λ b, _),
  simp only [nnreal.coe_eq, bind_on_support_apply, pure_apply],
  refine trans (tsum_congr (λ a', _)) (tsum_ite_eq a _),
  by_cases h : (a' = a); simp [h],
end

lemma bind_on_support_pure (p : pmf α) :
  p.bind_on_support (λ a _, pure a) = p :=
by simp only [pmf.bind_pure, pmf.bind_on_support_eq_bind]

@[simp] lemma bind_on_support_bind_on_support (p : pmf α)
  (f : ∀ a ∈ p.support, pmf β)
  (g : ∀ (b ∈ (p.bind_on_support f).support), pmf γ) :
  (p.bind_on_support f).bind_on_support g =
    p.bind_on_support (λ a ha, (f a ha).bind_on_support
      (λ b hb, g b ((p.mem_support_bind_on_support_iff f b).mpr ⟨a, ha, hb⟩))) :=
begin
  refine pmf.ext (λ a, _),
  simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm],
  refine trans (ennreal.tsum_comm) (tsum_congr (λ a', _)),
  split_ifs with h,
  { simp only [h, ennreal.coe_zero, zero_mul, tsum_zero] },
  { simp only [← ennreal.tsum_mul_left, ← mul_assoc],
    refine tsum_congr (λ b, _),
    split_ifs with h1 h2 h2,
    any_goals { ring1 },
    { rw bind_on_support_eq_zero_iff at h1,
      simp only [h1 a' h, ennreal.coe_zero, zero_mul, mul_zero] },
    { simp only [h2, ennreal.coe_zero, mul_zero, zero_mul] } }
end

lemma bind_on_support_comm (p : pmf α) (q : pmf β)
  (f : ∀ (a ∈ p.support) (b ∈ q.support), pmf γ) :
  p.bind_on_support (λ a ha, q.bind_on_support (f a ha)) =
    q.bind_on_support (λ b hb, p.bind_on_support (λ a ha, f a ha b hb)) :=
begin
  apply pmf.ext, rintro c,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm],
  refine trans (ennreal.tsum_comm) (tsum_congr (λ b, tsum_congr (λ a, _))),
  split_ifs with h1 h2 h2; ring,
end

/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : pmf α) : pmf β := bind p (pure ∘ f)

lemma bind_pure_comp (f : α → β) (p : pmf α) : bind p (pure ∘ f) = map f p := rfl

lemma map_id (p : pmf α) : map id p = p := by simp [map]

lemma map_comp (p : pmf α) (f : α → β) (g : β → γ) : (p.map f).map g = p.map (g ∘ f) :=
by simp [map]

lemma pure_map (a : α) (f : α → β) : (pure a).map f = pure (f a) :=
by simp [map]

/-- The monadic sequencing operation for `pmf`. -/
def seq (f : pmf (α → β)) (p : pmf α) : pmf β := f.bind (λ m, p.bind $ λ a, pure (m a))

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def of_multiset (s : multiset α) (hs : s ≠ 0) : pmf α :=
⟨λ a, s.count a / s.card,
  have ∑ a in s.to_finset, (s.count a : ℝ) / s.card = 1,
    by simp [div_eq_inv_mul, finset.mul_sum.symm, (nat.cast_sum _ _).symm, hs],
  have ∑ a in s.to_finset, (s.count a : ℝ≥0) / s.card = 1,
    by rw [← nnreal.eq_iff, nnreal.coe_one, ← this, nnreal.coe_sum]; simp,
  begin
    rw ← this,
    apply has_sum_sum_of_ne_finset_zero,
    simp {contextual := tt},
  end⟩

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype [fintype α] (f : α → ℝ≥0) (h : ∑ x, f x = 1) : pmf α :=
⟨f, h ▸ has_sum_sum_of_ne_finset_zero (by simp)⟩

/-- Given a `f` with non-zero sum, we get a `pmf` by normalizing `f` by its `tsum` -/
def normalize (f : α → ℝ≥0) (hf0 : tsum f ≠ 0) : pmf α :=
⟨λ a, f a * (∑' x, f x)⁻¹,
  (mul_inv_cancel hf0) ▸ has_sum.mul_right (∑' x, f x)⁻¹
    (not_not.mp (mt tsum_eq_zero_of_not_summable hf0 : ¬¬summable f)).has_sum⟩

lemma normalize_apply {f : α → ℝ≥0} (hf0 : tsum f ≠ 0) (a : α) :
  (normalize f hf0) a = f a * (∑' x, f x)⁻¹ := rfl

/-- Create new `pmf` by filtering on a set with non-zero measure and normalizing -/
def filter (p : pmf α) (s : set α) (h : ∃ a ∈ s, p a ≠ 0) : pmf α :=
pmf.normalize (s.indicator p) $ nnreal.tsum_indicator_ne_zero p.2.summable h

lemma filter_apply (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0) {a : α} :
  (p.filter s h) a = (s.indicator p a) * (∑' x, (s.indicator p) x)⁻¹ :=
by rw [filter, normalize_apply]

lemma filter_apply_eq_zero_of_not_mem (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0)
  {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 :=
by rw [filter_apply, set.indicator_apply_eq_zero.mpr (λ ha', absurd ha' ha), zero_mul]

lemma filter_apply_eq_zero_iff (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0) (a : α) :
  (p.filter s h) a = 0 ↔ a ∉ (p.support ∩ s) :=
begin
  rw [set.mem_inter_iff, p.mem_support_iff, not_and_distrib, not_not],
  split; intro ha,
  { rw [filter_apply, mul_eq_zero] at ha,
    refine ha.by_cases
      (λ ha, (em (a ∈ s)).by_cases (λ h, or.inl ((set.indicator_apply_eq_zero.mp ha) h)) or.inr)
      (λ ha, absurd (inv_eq_zero.1 ha) (nnreal.tsum_indicator_ne_zero p.2.summable h)) },
  { rw [filter_apply, set.indicator_apply_eq_zero.2 (λ h, ha.by_cases id (absurd h)), zero_mul] }
end

lemma filter_apply_ne_zero_iff (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0) (a : α) :
  (p.filter s h) a ≠ 0 ↔ a ∈ (p.support ∩ s) :=
by rw [← not_iff, filter_apply_eq_zero_iff, not_iff, not_not]

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : pmf bool :=
of_fintype (λ b, cond b p (1 - p)) (nnreal.eq $ by simp [h])

end pmf
