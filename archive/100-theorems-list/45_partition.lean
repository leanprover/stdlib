/-
Copyright (c) 2020 Bhavik Mehta, Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta, Aaron Anderson.
-/
import ring_theory.power_series.basic
import combinatorics.partition
import data.nat.parity
import data.finset.nat_antidiagonal
import tactic.interval_cases
import tactic.apply_fun

/-!
# Euler's Partition Theorem

This file proves Theorem 45 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem concerns the counting of integer partitions -- ways of
writing a positive integer `n` as a sum of positive integer parts.

Specifically, Euler proved that the number of integer partitions of `n`
into *distinct* parts equals the number of partitions of `n` into *odd*
parts.

## References
https://en.wikipedia.org/wiki/Partition_(number_theory)#Odd_parts_and_distinct_parts
-/

open power_series
noncomputable theory

variables {α : Type*}

open finset
open_locale big_operators
open_locale classical

/--
The partial product for the generating function for odd partitions.
TODO: As `n` tends to infinity, this converges (in the `X`-adic topology).

If `n` is sufficiently large, the `i`th coefficient gives the number of odd partitions of the
natural number `i`: proved in `odd_gf_prop`.
It is stated for an arbitrary field `α`, though it usually suffices to use `ℚ` or `ℝ`.
-/
def partial_odd_gf (n : ℕ) [field α] := ∏ i in range n, (1 - (X : power_series α)^(2*i+1))⁻¹

/--
The partial product for the generating function for distinct partitions.
TODO: As `n` tends to infinity, this converges (in the `X`-adic topology).

If `n` is sufficiently large, the `i`th coefficient gives the number of distinct partitions of the
natural number `i`: proved in `distinct_gf_prop`.
It is stated for an arbitrary commutative semiring `α`, though it usually suffices to use `ℕ`, `ℚ`
or `ℝ`.
-/
def partial_distinct_gf (n : ℕ) [comm_semiring α] :=
∏ i in range n, (1 + (X : power_series α)^(i+1))

/--
Functions defined only on `s`, which sum to `n`. In other words, a partition of `n` indexed by `s`.
Every function in here is finitely supported, and the support is a subset of `s`.
This should be thought of as a generalisation of `finset.nat.antidiagonal`, where
`antidiagonal n` is the same thing as `cut s n` if `s` has two elements.
-/
def cut {ι : Type*} (s : finset ι) (n : ℕ) : finset (ι → ℕ) :=
finset.filter (λ f, s.sum f = n) ((s.pi (λ _, range (n+1))).map
  ⟨λ f i, if h : i ∈ s then f i h else 0,
   λ f g h, by { ext i hi, simpa [dif_pos hi] using congr_fun h i }⟩)

lemma mem_cut {ι : Type*} (s : finset ι) (n : ℕ) (f : ι → ℕ) :
  f ∈ cut s n ↔ s.sum f = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [cut, mem_filter, and_comm, and_congr_right],
  intro h,
  rw [mem_map],
  simp only [exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_range, nat.lt_succ_iff, ← h],
      apply single_le_sum _ hi,
      simp },
    { ext,
      split_ifs with q,
      { refl },
      { apply (hf _ q).symm } } }
end

lemma cut_equiv_antidiag (n : ℕ) :
  equiv.finset_congr (equiv.bool_to_equiv_prod _) (cut univ n) = nat.antidiagonal n :=
begin
  ext ⟨x₁, x₂⟩,
  simp_rw [equiv.finset_congr_apply, mem_map, equiv.to_embedding, function.embedding.coe_fn_mk,
           ←equiv.eq_symm_apply],
  simp [mem_cut, add_comm],
end

/-- There is only one `cut` of 0. -/
@[simp]
lemma cut_zero {ι : Type*} (s : finset ι) :
  cut s 0 = {0} :=
begin
  -- In general it's nice to prove things using `mem_cut` but in this case it's easier to just
  -- use the definition.
  rw [cut, range_one, pi_const_singleton, map_singleton, function.embedding.coe_fn_mk,
      filter_singleton, if_pos, singleton_inj],
  { ext, split_ifs; refl },
  rw sum_eq_zero_iff,
  intros x hx,
  apply dif_pos hx,
end

@[simp]
lemma cut_empty_succ {ι : Type*} (n : ℕ) :
  cut (∅ : finset ι) (n+1) = ∅ :=
begin
  apply eq_empty_of_forall_not_mem,
  intros x hx,
  rw [mem_cut, sum_empty] at hx,
  cases hx.1,
end

lemma cut_insert {ι : Type*} (n : ℕ) (a : ι) (s : finset ι) (h : a ∉ s) :
  cut (insert a s) n =
  (nat.antidiagonal n).bUnion
    (λ (p : ℕ × ℕ), (cut s p.snd).map
      ⟨λ f, f + λ t, if t = a then p.fst else 0, add_left_injective _⟩) :=
begin
  ext f,
  rw [mem_cut, mem_bUnion, sum_insert h],
  split,
  { rintro ⟨rfl, h₁⟩,
    simp only [exists_prop, function.embedding.coe_fn_mk, mem_map,
               nat.mem_antidiagonal, prod.exists],
    refine ⟨f a, s.sum f, rfl, λ i, if i = a then 0 else f i, _, _⟩,
    { rw [mem_cut],
      refine ⟨_, _⟩,
      { rw [sum_ite],
        have : (filter (λ x, x ≠ a) s) = s,
          apply filter_true_of_mem,
          rintro i hi rfl,
          apply h hi,
        simp [this] },
      { intros i hi,
        split_ifs,
        { refl },
        { apply h₁ ,
          simpa [not_or_distrib, hi] } } },
    { ext,
      by_cases (x = a),
      { subst h, simp },
      { simp [if_neg h] } } },
  { simp only [mem_insert, function.embedding.coe_fn_mk, mem_map, nat.mem_antidiagonal, prod.exists,
               exists_prop, mem_cut, not_or_distrib],
    rintro ⟨p, q, rfl, g, ⟨rfl, hg₂⟩, rfl⟩,
    refine ⟨_, _⟩,
    { simp [sum_add_distrib, if_neg h, hg₂ _ h, add_comm] },
    { rintro i ⟨h₁, h₂⟩,
      simp [if_neg h₁, hg₂ _ h₂] } }
end

lemma coeff_prod_range
  [comm_semiring α] {ι : Type*} (s : finset ι) (f : ι → power_series α) (n : ℕ) :
  coeff α n (∏ j in s, f j) = ∑ l in cut s n, ∏ i in s, coeff α (l i) (f i) :=
begin
  revert n,
  apply finset.induction_on s,
    rintro ⟨_ | n⟩,
      simp,
    simp [cut_empty_succ, if_neg (nat.succ_ne_zero _)],
  intros a s hi ih n,
  rw [cut_insert _ _ _ hi, prod_insert hi, coeff_mul, sum_bUnion],
  { apply sum_congr rfl _,
    simp only [prod.forall, sum_map, pi.add_apply,
               function.embedding.coe_fn_mk, nat.mem_antidiagonal],
    rintro i j rfl,
    simp only [prod_insert hi, if_pos rfl],
    rw ih,
    rw mul_sum,
    apply sum_congr rfl _,
    intros x hx,
    rw mem_cut at hx,
    rw [hx.2 a hi, zero_add],
    congr' 1,
    apply prod_congr rfl,
    intros k hk,
    rw [if_neg, add_zero],
    rintro rfl,
    apply hi hk },
  { simp only [prod.forall, not_and, ne.def, nat.mem_antidiagonal, disjoint_left, mem_map,
               exists_prop, function.embedding.coe_fn_mk, exists_imp_distrib, not_exists],
    rintro p₁ q₁ rfl p₂ q₂ h t p q ⟨hq, rfl⟩ p hp z,
    rw mem_cut at hp hq,
    have := sum_congr (eq.refl s) (λ x _, function.funext_iff.1 z x),
    have : q₂ = q₁,
      simpa [sum_add_distrib, hp.1, hq.1, if_neg hi] using this,
    subst this,
    have : p₂ = p₁,
      simpa using h,
    subst this,
    apply t,
    refl }
end

/-- A convience constructor for the power series whose coefficients indicate a subset. -/
def indicator_series (α : Type*) [semiring α] (f : set ℕ) : power_series α :=
power_series.mk (λ n, if f n then 1 else 0)

lemma coeff_indicator (f : set ℕ) [semiring α] (n : ℕ) :
  coeff α n (indicator_series _ f) = if f n then 1 else 0 :=
coeff_mk _ _
lemma coeff_indicator_pos (f : set ℕ) [semiring α] (n : ℕ) (h : f n):
  coeff α n (indicator_series _ f) = 1 :=
by rw [coeff_indicator, if_pos h]
lemma coeff_indicator_neg (f : set ℕ) [semiring α] (n : ℕ) (h : ¬f n):
  coeff α n (indicator_series _ f) = 0 :=
by rw [coeff_indicator, if_neg h]
lemma constant_coeff_indicator (f : set ℕ) [semiring α] :
  constant_coeff α (indicator_series _ f) = if f 0 then 1 else 0 :=
rfl

lemma two_series (i : ℕ) [semiring α] :
  (1 + (X : power_series α)^i.succ) = indicator_series α {0, i.succ} :=
begin
  ext,
  simp [coeff_indicator, coeff_one, add_monoid_hom.map_add, coeff_X_pow,
        ← @set.mem_def _ _ {0, i.succ}, set.mem_insert_iff, set.mem_singleton_iff],
  cases n with d hd,
    { simp [(nat.succ_ne_zero i).symm, zero_pow] },
    { simp [(nat.succ_ne_zero d)], },
end

lemma num_series' [field α] (i : ℕ) :
  (1 - (X : power_series α)^(i+1))⁻¹ = indicator_series α (λ k, i + 1 ∣ k) :=
begin
  rw power_series.inv_eq_iff_mul_eq_one,
  { ext,
    cases n,
    { simp [mul_sub, zero_pow, constant_coeff_indicator] },
    { simp only [coeff_one, if_neg n.succ_ne_zero, mul_sub, mul_one,
                 coeff_indicator, linear_map.map_sub],
      simp_rw [coeff_mul, coeff_X_pow, coeff_indicator, boole_mul, sum_ite, filter_filter,
               sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one, sub_eq_iff_eq_add,
               zero_add, filter_congr_decidable],
      symmetry,
      split_ifs,
      { suffices :
        ((nat.antidiagonal n.succ).filter (λ (a : ℕ × ℕ), i + 1 ∣ a.fst ∧ a.snd = i + 1)).card = 1,
          rw this, norm_cast,
        rw card_eq_one,
        cases h with p hp,
        refine ⟨((i+1) * (p-1), i+1), _⟩,
        ext ⟨a₁, a₂⟩,
        simp only [mem_filter, prod.mk.inj_iff, nat.mem_antidiagonal, mem_singleton],
        split,
        { rintro ⟨a_left, ⟨a, rfl⟩, rfl⟩,
          refine ⟨_, rfl⟩,
          rw [nat.mul_sub_left_distrib, ← hp, ← a_left, mul_one, nat.add_sub_cancel] },
        { rintro ⟨rfl, rfl⟩,
          cases p,
            rw mul_zero at hp, cases hp,
          rw hp,
          simp [nat.succ_eq_add_one, mul_add] } },
      { suffices :
        (filter (λ (a : ℕ × ℕ), i + 1 ∣ a.fst ∧ a.snd = i + 1) (nat.antidiagonal n.succ)).card = 0,
          rw this, norm_cast,
        rw card_eq_zero,
        apply eq_empty_of_forall_not_mem,
        simp only [prod.forall, mem_filter, not_and, nat.mem_antidiagonal],
        rintro _ h₁ h₂ ⟨a, rfl⟩ rfl,
        apply h,
        simp [← h₂] } } },
  { simp [zero_pow] },
end

lemma card_eq_of_bijection {β : Type*} {s : finset α} {t : finset β}
  (f : α → β)
  (hf : ∀ a ∈ s, f a ∈ t)
  (hsurj : ∀ b ∈ t, ∃ (a ∈ s), f a = b)
  (hinj : ∀ a₁ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) :
s.card = t.card :=
finset.card_congr (λ a _, f a) hf hinj hsurj

-- TODO: name and move me
lemma auxy (n : ℕ) (a_blocks : multiset ℕ) (s : finset ℕ)
  (a_blocks_sum : a_blocks.sum = n)
  (hp : ∀ (i : ℕ), i ∈ a_blocks → i ∈ s) :
  ∑ (i : ℕ) in s, multiset.count i a_blocks * i = n :=
begin
  rw ← a_blocks_sum,
  rw sum_multiset_count,
  simp_rw nat.nsmul_eq_mul,
  symmetry,
  apply sum_subset_zero_on_sdiff,
  intros i hi,
  apply hp,
  simpa using hi,
  intros,
  rw mem_sdiff at H,
  simp only [multiset.mem_to_finset] at H,
  rw [multiset.count_eq_zero_of_not_mem H.2, zero_mul],
  intros, refl,
end

def mk_odd : ℕ ↪ ℕ := ⟨λ i, 2 * i + 1, λ x y h, by linarith⟩

-- TODO: move me
lemma sum_sum {β : Type*} [add_comm_monoid β] (f : α → multiset β) (s : finset α) :
  (∑ x in s, f x).sum = ∑ x in s, (f x).sum :=
(sum_hom s multiset.sum).symm

-- The main workhorse of the partition theorem proof.
lemma partial_gf_prop
  (α : Type*) [comm_semiring α] (n : ℕ) (s : finset ℕ)
  (hs : ∀ i ∈ s, 0 < i) (c : ℕ → set ℕ) (hc : ∀ i ∉ s, 0 ∈ c i) :
  (finset.card
    ((univ : finset (partition n)).filter
      (λ p, (∀ j, p.parts.count j ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s)) : α) =
        (coeff α n) (∏ (i : ℕ) in s, indicator_series α ((* i) '' c i)) :=
begin
  simp_rw [coeff_prod_range, coeff_indicator, prod_boole, sum_boole],
  congr' 1,
  refine card_eq_of_bijection _ _ _ _,
  { intros p i, apply multiset.count i p.parts * i },
  { simp only [mem_filter, mem_cut, mem_univ, true_and, exists_prop, and_assoc, and_imp,
               nat.mul_eq_zero, function.embedding.coe_fn_mk, exists_imp_distrib],
    rintro ⟨p, hp₁, hp₂⟩ hp₃ hp₄,
    refine ⟨_, _, _⟩,
    { rw auxy _ _ _ hp₂,
      apply hp₄ },
    { intros i hi,
      left,
      exact multiset.count_eq_zero_of_not_mem (mt (hp₄ i) hi) },
    { exact λ i hi, ⟨_, hp₃ i, rfl⟩ } },
  { simp only [mem_filter, mem_cut, mem_univ, exists_prop, true_and, and_assoc],
    rintros f ⟨hf₁, hf₂, hf₃⟩,
    refine ⟨⟨∑ i in s, multiset.repeat i (f i / i), _, _⟩, _, _, _⟩,
    { intros i hi,
      simp only [exists_prop, mem_sum, mem_map, function.embedding.coe_fn_mk] at hi,
      rcases hi with ⟨t, ht, z⟩,
      apply hs,
      rwa multiset.eq_of_mem_repeat z },
    { rw sum_sum,
      simp_rw [multiset.sum_repeat, nat.nsmul_eq_mul],
      have : ∀ i ∈ s, i ∣ f i,
      { intros i hi,
        rcases hf₃ i hi with ⟨w, hw, hw₂⟩,
        rw ← hw₂,
        apply dvd.intro_left _ rfl },
      { rw sum_congr rfl (λ i hi, nat.div_mul_cancel (this i hi)),
        apply hf₁ } },
    { intro i,
      rw ← sum_hom _ (multiset.count i),
      simp_rw [multiset.count_repeat, sum_ite_eq],
      split_ifs with h h,
      { rcases hf₃ i h with ⟨w, hw₁, hw₂⟩,
        rwa [← hw₂, nat.mul_div_cancel _ (hs i h)] },
      { apply hc _ h } },
    { intros i hi,
      rw mem_sum at hi,
      rcases hi with ⟨j, hj₁, hj₂⟩,
      rwa multiset.eq_of_mem_repeat hj₂ },
    { ext i,
      rw ← sum_hom _ (multiset.count i),
      simp_rw [multiset.count_repeat, sum_ite_eq],
      split_ifs,
      { apply nat.div_mul_cancel,
        rcases hf₃ i h with ⟨w, hw, hw₂⟩,
        apply dvd.intro_left _ hw₂ },
      { rw [zero_mul],
        apply (hf₂ i h).symm } } },
  { intros p₁ p₂ hp₁ hp₂ h,
    apply partition.ext,
    simp only [true_and, mem_univ, mem_filter] at hp₁ hp₂,
    ext i,
    rw function.funext_iff at h,
    specialize h i,
    cases i,
    { rw multiset.count_eq_zero_of_not_mem,
      rw multiset.count_eq_zero_of_not_mem,
      intro a, exact nat.lt_irrefl 0 (hs 0 (hp₂.2 0 a)),
      intro a, exact nat.lt_irrefl 0 (hs 0 (hp₁.2 0 a)) },
    { rwa nat.mul_left_inj i.succ_pos at h } },
end

lemma partial_odd_gf_prop [field α] (n m : ℕ) :
  (finset.card ((univ : finset (partition n)).filter
    (λ p, ∀ j ∈ p.parts, j ∈ (range m).map mk_odd)) : α) = coeff α n (partial_odd_gf m) :=
begin
  rw partial_odd_gf,
  convert partial_gf_prop α n ((range m).map mk_odd) _ (λ _, set.univ) (λ _ _, trivial) using 2,
  { congr' 2,
    simp only [true_and, forall_const, set.mem_univ] },
  { rw finset.prod_map,
    simp_rw num_series',
    apply prod_congr rfl,
    intros,
    congr' 1,
    ext k,
    split,
      rintro ⟨p, rfl⟩,
      refine ⟨p, ⟨⟩, _⟩,
      apply mul_comm,
    rintro ⟨a_w, _, rfl⟩,
    apply dvd.intro_left a_w rfl },
  { intro i,
    rw mem_map,
    rintro ⟨_, _, rfl⟩,
    apply nat.succ_pos },
end

/--  If m is big enough, the partial product's coefficient counts the number of odd partitions -/
theorem odd_gf_prop [field α] (n m : ℕ) (h : n < m * 2) :
  (finset.card (partition.odds n) : α) = coeff α n (partial_odd_gf m) :=
begin
  rw [← partial_odd_gf_prop],
  congr' 2,
  apply filter_congr,
  intros p hp,
  apply ball_congr,
  intros i hi,
  have : i ≤ n,
  { simpa [p.parts_sum] using multiset.single_le_sum (λ _ _, nat.zero_le _) _ hi },
  simp only [mk_odd, exists_prop, mem_range, function.embedding.coe_fn_mk, mem_map],
  split,
  { intro hi₂,
    have := nat.mod_add_div i 2,
    rw nat.not_even_iff at hi₂,
    rw [hi₂, add_comm] at this,
    refine ⟨i / 2, _, ‹_›⟩,
    rw nat.div_lt_iff_lt_mul,
    apply lt_of_le_of_lt ‹i ≤ n› h,
    norm_num },
  { rintro ⟨_, _, rfl⟩,
    apply nat.two_not_dvd_two_mul_add_one },
end

lemma partial_distinct_gf_prop [comm_semiring α] (n m : ℕ) :
  (finset.card
    ((univ : finset (partition n)).filter
      (λ p, p.parts.nodup ∧ ∀ j ∈ p.parts, j ∈ (range m).map ⟨nat.succ, nat.succ_injective⟩)) : α) =
  coeff α n (partial_distinct_gf m) :=
begin
  rw partial_distinct_gf,
  convert partial_gf_prop α n
    ((range m).map ⟨nat.succ, nat.succ_injective⟩) _ (λ _, {0, 1}) (λ _ _, or.inl rfl) using 2,
  { congr' 2,
    ext p,
    congr' 2,
    apply propext,
    rw multiset.nodup_iff_count_le_one,
    apply forall_congr,
    intro i,
    rw [set.mem_insert_iff, set.mem_singleton_iff],
    split,
    { intro hi,
      interval_cases (multiset.count i p.parts),
      left, assumption,
      right, assumption },
    { rintro (h | h);
        rw h,
      norm_num } },
  { rw finset.prod_map,
    apply prod_congr rfl,
    intros,
    rw two_series,
    congr' 1,
    simp [set.image_pair] },
  { simp only [mem_map, function.embedding.coe_fn_mk],
    rintro i ⟨_, _, rfl⟩,
    apply nat.succ_pos }
end

/--
If m is big enough, the partial product's coefficient counts the number of distinct partitions
-/
theorem distinct_gf_prop [comm_semiring α] (n m : ℕ) (h : n < m + 1) :
  ((partition.distincts n).card : α) = coeff α n (partial_distinct_gf m) :=
begin
  erw [← partial_distinct_gf_prop],
  congr' 2,
  apply filter_congr,
  intros p hp,
  apply (and_iff_left _).symm,
  intros i hi,
  have : i ≤ n,
    simpa [p.parts_sum] using multiset.single_le_sum (λ _ _, nat.zero_le _) _ hi,
  simp only [mk_odd, exists_prop, mem_range, function.embedding.coe_fn_mk, mem_map],
  refine ⟨i-1, _, _⟩,
  rw nat.sub_lt_right_iff_lt_add,
  apply lt_of_le_of_lt ‹i ≤ n› h,
  apply p.parts_pos hi,
  apply nat.succ_pred_eq_of_pos,
  apply p.parts_pos hi,
end

/--
The key proof idea for the partition theorem, showing that the generating functions for both
sequences are ultimately the same (since the factor converges to 0 as n tends to infinity).
It's enough to not take the limit though, and just consider large enough `n`.
-/
lemma same_gf [field α] (n : ℕ) :
  partial_odd_gf n * (range n).prod (λ i, (1 - (X : power_series α)^(n+i+1))) =
  partial_distinct_gf n :=
begin
  rw [partial_odd_gf, partial_distinct_gf],
  induction n with n ih,
  { simp },
  let Z : power_series α := ∏ (x : ℕ) in range n, (1 - X^(2*x+1))⁻¹,
  rw [prod_range_succ _ n, prod_range_succ _ n, prod_range_succ _ n, ← ih],
  clear ih,
  erw ← two_mul (n+1),
  have : 1 - (X : power_series α) ^ (2 * (n+1)) = (1 + X^(n+1)) * (1 - X^(n+1)),
    rw [← sq_sub_sq, one_pow, ← pow_mul, mul_comm],
  rw this, clear this,
  rw [mul_assoc, mul_assoc, ← mul_assoc Z, mul_left_comm _ (Z * _), mul_left_comm _ Z,
      ← mul_assoc Z],
  congr' 1,
  have := prod_range_succ' (λ x, 1 - (X : power_series α)^(n.succ + x)) n,
  dsimp at this,
  simp_rw [← add_assoc, add_zero, mul_comm _ (1 - X ^ n.succ)] at this,
  erw [← this],
  rw [prod_range_succ],
  simp_rw [nat.succ_eq_add_one, add_right_comm _ 1, ← two_mul, ← mul_assoc],
  rw [power_series.inv_mul, one_mul],
  simp [zero_pow],
end

lemma same_coeffs [field α] (n m : ℕ) (h : m ≤ n) :
  coeff α m (partial_odd_gf n) = coeff α m (partial_distinct_gf n) :=
begin
  rw ← same_gf,
  rw coeff_mul_prod_one_sub_of_lt_order,
  simp only [mem_range, order_X_pow],
  intros i hi,
  norm_cast,
  rw nat.lt_succ_iff,
  apply le_add_right,
  assumption,
end

theorem freek (n : ℕ) : (partition.odds n).card = (partition.distincts n).card :=
begin
  -- We need the counts to live in some field (which contains ℕ), so let's just use ℚ
  suffices : ((partition.odds n).card : ℚ) = (partition.distincts n).card,
    norm_cast at this, assumption,
  rw distinct_gf_prop n (n+1) (by linarith),
  rw odd_gf_prop n (n+1) (by linarith),
  apply same_coeffs (n+1) n (by linarith),
end
