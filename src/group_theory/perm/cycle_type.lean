/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import combinatorics.partition
import algebra.gcd_monoid.multiset
import tactic.linarith
import group_theory.perm.cycles
import group_theory.sylow

/-!
# Cycle Types

In this file we define the cycle type of a partition.

## Main definitions

- `σ.cycle_type` where `σ` is a permutation of a `fintype`
- `σ.partition` where `σ` is a permutation of a `fintype`

## Main results

- `sum_cycle_type` : The sum of `σ.cycle_type` equals `σ.support.card`
- `lcm_cycle_type` : The lcm of `σ.cycle_type` equals `order_of σ`
- `is_conj_iff_cycle_type_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
-/

namespace equiv.perm
open equiv list multiset

variables {α : Type*} [fintype α]

section cycle_type

variables [decidable_eq α]

/-- The cycle type of a permutation -/
def cycle_type (σ : perm α) : multiset ℕ :=
σ.trunc_cycle_factors.lift (λ l, l.1.map (finset.card ∘ support))
  (λ ⟨l₁, h₁l₁, h₂l₁, h₃l₁⟩ ⟨l₂, h₁l₂, h₂l₂, h₃l₂⟩, coe_eq_coe.mpr (perm.map _
  (list_cycles_perm_list_cycles (h₁l₁.trans h₁l₂.symm) h₂l₁ h₂l₂ h₃l₁ h₃l₂)))

lemma two_le_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 2 ≤ n :=
begin
  rw [cycle_type, ←σ.trunc_cycle_factors.out_eq] at h,
  obtain ⟨τ, hτ, rfl⟩ := list.mem_map.mp h,
  exact (σ.trunc_cycle_factors.out.2.2.1 τ hτ).two_le_card_support,
end

lemma one_lt_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 1 < n :=
two_le_of_mem_cycle_type h

lemma cycle_type_eq {σ : perm α} (l : list (perm α)) (h0 : l.prod = σ)
  (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle) (h2 : l.pairwise disjoint) :
  σ.cycle_type = l.map (finset.card ∘ support) :=
by rw [cycle_type, trunc.eq σ.trunc_cycle_factors (trunc.mk ⟨l, h0, h1, h2⟩), trunc.lift_mk]

lemma cycle_type_one : (1 : perm α).cycle_type = 0 :=
cycle_type_eq [] rfl (λ _, false.elim) pairwise.nil

lemma cycle_type_eq_zero {σ : perm α} : σ.cycle_type = 0 ↔ σ = 1 :=
begin
  split,
  { intro h,
    obtain ⟨l, h₁l, h₂l, h₃l⟩ := σ.trunc_cycle_factors.out,
    rw [cycle_type_eq l h₁l h₂l h₃l, coe_eq_zero, map_eq_nil] at h,
    exact h₁l.symm.trans (congr_arg _ h) },
  { exact λ h, by rw [h, cycle_type_one] },
end

lemma card_cycle_type_eq_zero {σ : perm α} : σ.cycle_type.card = 0 ↔ σ = 1 :=
by rw [card_eq_zero, cycle_type_eq_zero]

lemma is_cycle.cycle_type {σ : perm α} (hσ : is_cycle σ) : σ.cycle_type = [σ.support.card] :=
cycle_type_eq [σ] (mul_one σ) (λ τ hτ, (congr_arg is_cycle (list.mem_singleton.mp hτ)).mpr hσ)
  (pairwise_singleton disjoint σ)

lemma card_cycle_type_eq_one {σ : perm α} : σ.cycle_type.card = 1 ↔ σ.is_cycle :=
begin
  split,
  { intro hσ,
    obtain ⟨l, h₁l, h₂l, h₃l⟩ := σ.trunc_cycle_factors.out,
    rw [cycle_type_eq l h₁l h₂l h₃l, coe_card, length_map] at hσ,
    obtain ⟨τ, hτ⟩ := length_eq_one.mp hσ,
    rw [←h₁l, hτ, list.prod_singleton],
    apply h₂l,
    rw [hτ, list.mem_singleton] },
  { exact λ hσ, by rw [hσ.cycle_type, coe_card, length_singleton] },
end

lemma disjoint.cycle_type {σ τ : perm α} (h : disjoint σ τ) :
  (σ * τ).cycle_type = σ.cycle_type + τ.cycle_type :=
begin
  obtain ⟨l₁, h₁l₁, h₂l₁, h₃l₁⟩ := σ.trunc_cycle_factors.out,
  obtain ⟨l₂, h₁l₂, h₂l₂, h₃l₂⟩ := τ.trunc_cycle_factors.out,
  rw [cycle_type_eq l₁ h₁l₁ h₂l₁ h₃l₁, cycle_type_eq l₂ h₁l₂ h₂l₂ h₃l₂,
      cycle_type_eq (l₁ ++ l₂) _ _ _, map_append, ←coe_add],
  { rw [prod_append, h₁l₁, h₁l₂] },
  { exact λ f hf, (mem_append.mp hf).elim (h₂l₁ f) (h₂l₂ f) },
  { refine pairwise_append.mpr ⟨h₃l₁, h₃l₂, λ f hf g hg a, by_contra (λ H, _)⟩,
    rw not_or_distrib at H,
    rw [←ne.def, ←ne.def, ←mem_support, ←mem_support] at H,
    replace H : a ∈ l₁.prod.support ∧ a ∈ l₂.prod.support,
    { refine H.imp (λ H, _) (λ H, _);
      exact support_le_prod_of_mem ‹_› ‹_› H },
    rw [h₁l₁, h₁l₂] at H,
    exact h.disjoint_support (finset.mem_inter_of_mem H.left H.right) }
end

lemma cycle_type_inv (σ : perm α) : σ⁻¹.cycle_type = σ.cycle_type :=
cycle_induction_on (λ τ : perm α, τ⁻¹.cycle_type = τ.cycle_type) σ rfl
  (λ σ hσ, by rw [hσ.cycle_type, hσ.inv.cycle_type, support_inv])
  (λ σ τ hστ hc hσ hτ, by rw [mul_inv_rev, hστ.cycle_type, ←hσ, ←hτ, add_comm,
    disjoint.cycle_type (λ x, or.imp (λ h : τ x = x, inv_eq_iff_eq.mpr h.symm)
    (λ h : σ x = x, inv_eq_iff_eq.mpr h.symm) (hστ x).symm)])

lemma cycle_type_conj {σ τ : perm α} : (τ * σ * τ⁻¹).cycle_type = σ.cycle_type :=
begin
  revert τ,
  apply cycle_induction_on _ σ,
  { intro,
    simp },
  { intros σ hσ τ,
    rw [hσ.cycle_type, hσ.is_cycle_conj.cycle_type, card_support_conj] },
  { intros σ τ hd hc hσ hτ π,
    rw [← conj_mul, hd.cycle_type, disjoint.cycle_type, hσ, hτ],
    intro a,
    apply (hd (π⁻¹ a)).imp _ _;
    { intro h, rw [perm.mul_apply, perm.mul_apply, h, apply_inv_self] } }
end

lemma sum_cycle_type (σ : perm α) : σ.cycle_type.sum = σ.support.card :=
cycle_induction_on (λ τ : perm α, τ.cycle_type.sum = τ.support.card) σ
  (by rw [cycle_type_one, sum_zero, support_one, finset.card_empty])
  (λ σ hσ, by rw [hσ.cycle_type, coe_sum, list.sum_singleton])
  (λ σ τ hστ hc hσ hτ, by rw [hστ.cycle_type, sum_add, hσ, hτ, hστ.card_support_mul])

lemma sign_of_cycle_type (σ : perm α) :
  sign σ = (σ.cycle_type.map (λ n, -(-1 : units ℤ) ^ n)).prod :=
cycle_induction_on (λ τ : perm α, sign τ = (τ.cycle_type.map (λ n, -(-1 : units ℤ) ^ n)).prod) σ
  (by rw [sign_one, cycle_type_one, map_zero, prod_zero])
  (λ σ hσ, by rw [hσ.sign, hσ.cycle_type, coe_map, coe_prod,
    list.map_singleton, list.prod_singleton])
  (λ σ τ hστ hc hσ hτ, by rw [sign_mul, hσ, hτ, hστ.cycle_type, map_add, prod_add])

lemma lcm_cycle_type (σ : perm α) : σ.cycle_type.lcm = order_of σ :=
cycle_induction_on (λ τ : perm α, τ.cycle_type.lcm = order_of τ) σ
  (by rw [cycle_type_one, lcm_zero, order_of_one])
  (λ σ hσ, by rw [hσ.cycle_type, ←singleton_coe, lcm_singleton, order_of_is_cycle hσ,
    nat.normalize_eq])
  (λ σ τ hστ hc hσ hτ, by rw [hστ.cycle_type, lcm_add, nat.lcm_eq_lcm, hστ.order_of, hσ, hτ])

lemma dvd_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : n ∣ order_of σ :=
begin
  rw ← lcm_cycle_type,
  exact dvd_lcm h,
end

lemma two_dvd_card_support {σ : perm α} (hσ : σ ^ 2 = 1) : 2 ∣ σ.support.card :=
(congr_arg (has_dvd.dvd 2) σ.sum_cycle_type).mp
  (multiset.dvd_sum (λ n hn, by rw le_antisymm (nat.le_of_dvd zero_lt_two (dvd_trans
  (dvd_of_mem_cycle_type hn) (order_of_dvd_of_pow_eq_one hσ))) (two_le_of_mem_cycle_type hn)))

lemma cycle_type_prime_order {σ : perm α} (hσ : (order_of σ).prime) :
  ∃ n : ℕ, σ.cycle_type = repeat (order_of σ) (n + 1) :=
begin
  rw eq_repeat_of_mem (λ n hn, or_iff_not_imp_left.mp
    (hσ.2 n (dvd_of_mem_cycle_type hn)) (ne_of_gt (one_lt_of_mem_cycle_type hn))),
  use σ.cycle_type.card - 1,
  rw nat.sub_add_cancel,
  rw [nat.succ_le_iff, pos_iff_ne_zero, ne, card_cycle_type_eq_zero],
  rintro rfl,
  rw order_of_one at hσ,
  exact hσ.ne_one rfl,
end

lemma is_cycle_of_prime_order {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : σ.support.card < 2 * (order_of σ)) : σ.is_cycle :=
begin
  obtain ⟨n, hn⟩ := cycle_type_prime_order h1,
  rw [←σ.sum_cycle_type, hn, multiset.sum_repeat, nsmul_eq_mul, nat.cast_id, mul_lt_mul_right
      (order_of_pos σ), nat.succ_lt_succ_iff, nat.lt_succ_iff, nat.le_zero_iff] at h2,
  rw [←card_cycle_type_eq_one, hn, card_repeat, h2],
end

theorem is_conj_of_cycle_type_eq {σ τ : perm α} (h : cycle_type σ = cycle_type τ) : is_conj σ τ :=
begin
  revert τ,
  apply cycle_induction_on _ σ,
  { intros τ h,
    rw [cycle_type_one, eq_comm, cycle_type_eq_zero] at h,
    rw h },
  { intros σ hσ τ hστ,
    have hτ := card_cycle_type_eq_one.2 hσ,
    rw [hστ, card_cycle_type_eq_one] at hτ,
    apply hσ.is_conj hτ,
    rw [hσ.cycle_type, hτ.cycle_type, coe_eq_coe, singleton_perm] at hστ,
    simp only [and_true, eq_self_iff_true] at hστ,
    exact hστ },
  { intros σ τ hστ hσ h1 h2 π hπ,
    obtain ⟨l, rfl, hl1, hl2⟩ := trunc_cycle_factors π,
    rw [hστ.cycle_type, hσ.cycle_type, cycle_type_eq _ rfl hl1 hl2] at hπ,
    have h : σ.support.card ∈ map (finset.card ∘ perm.support) l,
    { rw [← multiset.mem_coe, ← hπ],
      simp },
    obtain ⟨σ', hσ'l, hσ'⟩ := list.mem_map.1 h,
    rw [disjoint_prod_perm hl2 (list.perm_cons_erase hσ'l), list.prod_cons],
    refine hστ.is_conj_mul (h1 _) (h2 _) _,
    { simp only [hσ.cycle_type, (hl1 _ hσ'l).cycle_type, ←hσ'] },
    { rw [← coe_map, coe_eq_coe.2 (list.perm_cons_erase hσ'l), singleton_add, ← cons_coe,
        multiset.map_cons, hσ', cons_inj_right, coe_map] at hπ,
      rw [hπ, cycle_type_eq (l.erase σ') rfl (λ f hf, hl1 f (list.erase_subset _ _ hf))
        (list.pairwise_of_sublist (list.erase_sublist _ _) hl2)] },
    { refine disjoint_prod_right _ (λ g hg, list.rel_of_pairwise_cons _ hg),
      refine (list.perm.pairwise_iff _ (list.perm_cons_erase hσ'l).symm).2 hl2,
      exact disjoint.symmetric } }
end

theorem is_conj_iff_cycle_type_eq {σ τ : perm α} :
  is_conj σ τ ↔ σ.cycle_type = τ.cycle_type :=
⟨λ h, begin
  obtain ⟨π, rfl⟩ := is_conj_iff.1 h,
  rw cycle_type_conj,
end, is_conj_of_cycle_type_eq⟩

@[simp] lemma cycle_type_extend_domain {β : Type*} [fintype β] [decidable_eq β]
  {p : β → Prop} [decidable_pred p] (f : α ≃ subtype p) {g : perm α} :
  cycle_type (g.extend_domain f) = cycle_type g :=
begin
  apply cycle_induction_on _ g,
  { rw [extend_domain_one, cycle_type_one, cycle_type_one] },
  { intros σ hσ,
    rw [(hσ.extend_domain f).cycle_type, hσ.cycle_type, card_support_extend_domain] },
  { intros σ τ hd hc hσ hτ,
    rw [hd.cycle_type, ← extend_domain_mul, (hd.extend_domain f).cycle_type, hσ, hτ] }
end

lemma mem_cycle_type_iff {n : ℕ} {σ : perm α} :
  n ∈ cycle_type σ ↔ ∃ c τ : perm α, σ = c * τ ∧ disjoint c τ ∧ is_cycle c ∧ c.support.card = n :=
begin
  split,
  { intro h,
    obtain ⟨l, rfl, hlc, hld⟩ := trunc_cycle_factors σ,
    rw cycle_type_eq _ rfl hlc hld at h,
    obtain ⟨c, cl, rfl⟩ := list.exists_of_mem_map h,
    rw (list.perm_cons_erase cl).pairwise_iff (λ _ _ hd, _) at hld,
    swap, { exact hd.symm },
    refine ⟨c, (l.erase c).prod, _, _, hlc _ cl, rfl⟩,
    { rw [← list.prod_cons,
        (list.perm_cons_erase cl).symm.prod_eq' (hld.imp (λ _ _, disjoint.commute))] },
    { exact disjoint_prod_right _ (λ g, list.rel_of_pairwise_cons hld) } },
  { rintros ⟨c, t, rfl, hd, hc, rfl⟩,
    simp [hd.cycle_type, hc.cycle_type] }
end

lemma le_card_support_of_mem_cycle_type {n : ℕ} {σ : perm α} (h : n ∈ cycle_type σ) :
  n ≤ σ.support.card :=
(le_sum_of_mem h).trans (le_of_eq σ.sum_cycle_type)

lemma cycle_type_of_card_le_mem_cycle_type_add_two {n : ℕ} {g : perm α}
  (hn2 : fintype.card α < n + 2) (hng : n ∈ g.cycle_type) :
  g.cycle_type = {n} :=
begin
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycle_type_iff.1 hng,
  by_cases g'1 : g' = 1,
  { rw [hd.cycle_type, hc.cycle_type, multiset.singleton_eq_singleton, multiset.singleton_coe,
      g'1, cycle_type_one, add_zero] },
  contrapose! hn2,
  apply le_trans _ (c * g').support.card_le_univ,
  rw [hd.card_support_mul],
  exact add_le_add_left (two_le_card_support_of_ne_one g'1) _,
end

end cycle_type

lemma is_cycle_of_prime_order' {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : fintype.card α < 2 * (order_of σ)) : σ.is_cycle :=
begin
  classical,
  exact is_cycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2),
end

lemma is_cycle_of_prime_order'' {σ : perm α} (h1 : (fintype.card α).prime)
  (h2 : order_of σ = fintype.card α) : σ.is_cycle :=
is_cycle_of_prime_order' ((congr_arg nat.prime h2).mpr h1)
begin
  classical,
  rw [←one_mul (fintype.card α), ←h2, mul_lt_mul_right (order_of_pos σ)],
  exact one_lt_two,
end

lemma subgroup_eq_top_of_swap_mem [decidable_eq α] {H : subgroup (perm α)}
  [d : decidable_pred (∈ H)] {τ : perm α} (h0 : (fintype.card α).prime)
  (h1 : fintype.card α ∣ fintype.card H) (h2 : τ ∈ H) (h3 : is_swap τ) :
  H = ⊤ :=
begin
  haveI : fact (fintype.card α).prime := ⟨h0⟩,
  obtain ⟨σ, hσ⟩ := sylow.exists_prime_order_of_dvd_card (fintype.card α) h1,
  have hσ1 : order_of (σ : perm α) = fintype.card α := (order_of_subgroup σ).trans hσ,
  have hσ2 : is_cycle ↑σ := is_cycle_of_prime_order'' h0 hσ1,
  have hσ3 : (σ : perm α).support = ⊤ :=
    finset.eq_univ_of_card (σ : perm α).support ((order_of_is_cycle hσ2).symm.trans hσ1),
  have hσ4 : subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3,
  rw [eq_top_iff, ←hσ4, subgroup.closure_le, set.insert_subset, set.singleton_subset_iff],
  exact ⟨subtype.mem σ, h2⟩,
end

section partition

variables [decidable_eq α]

/-- The partition corresponding to a permutation -/
def partition (σ : perm α) : partition (fintype.card α) :=
{ parts := σ.cycle_type + repeat 1 (fintype.card α - σ.support.card),
  parts_pos := λ n hn,
  begin
    cases mem_add.mp hn with hn hn,
    { exact zero_lt_one.trans (one_lt_of_mem_cycle_type hn) },
    { exact lt_of_lt_of_le zero_lt_one (ge_of_eq (multiset.eq_of_mem_repeat hn)) },
  end,
  parts_sum := by rw [sum_add, sum_cycle_type, multiset.sum_repeat, nsmul_eq_mul,
    nat.cast_id, mul_one, nat.add_sub_cancel' σ.support.card_le_univ] }

lemma parts_partition {σ : perm α} :
  σ.partition.parts = σ.cycle_type + repeat 1 (fintype.card α - σ.support.card) := rfl

lemma filter_parts_partition_eq_cycle_type {σ : perm α} :
  (partition σ).parts.filter (λ n, 2 ≤ n) = σ.cycle_type :=
begin
  rw [parts_partition, filter_add, multiset.filter_eq_self.2 (λ _, two_le_of_mem_cycle_type),
    multiset.filter_eq_nil.2 (λ a h, _), add_zero],
  rw multiset.eq_of_mem_repeat h,
  dec_trivial
end

lemma partition_eq_of_is_conj {σ τ : perm α} :
  is_conj σ τ ↔ σ.partition = τ.partition :=
begin
  rw [is_conj_iff_cycle_type_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { rw [partition.ext_iff, parts_partition, parts_partition,
      ← sum_cycle_type, ← sum_cycle_type, h] },
  { rw [← filter_parts_partition_eq_cycle_type, ← filter_parts_partition_eq_cycle_type, h] }
end

end partition

/-!
### 3-cycles
-/

/-- A three-cycle is a cycle of length 3. -/
def is_three_cycle [decidable_eq α] (σ : perm α) : Prop := σ.cycle_type = {3}

namespace is_three_cycle

variables [decidable_eq α] {σ : perm α}

lemma cycle_type (h : is_three_cycle σ) : σ.cycle_type = {3} := h

lemma card_support (h : is_three_cycle σ) : σ.support.card = 3 :=
by rw [←sum_cycle_type, h.cycle_type, singleton_eq_singleton, multiset.sum_cons, sum_zero]

lemma _root_.card_support_eq_three_iff : σ.support.card = 3 ↔ σ.is_three_cycle :=
begin
  refine ⟨λ h, _, is_three_cycle.card_support⟩,
  by_cases h0 : σ.cycle_type = 0,
  { rw [←sum_cycle_type, h0, sum_zero] at h,
    exact (ne_of_lt zero_lt_three h).elim },
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0,
  by_cases h1 : σ.cycle_type.erase n = 0,
  { rw [←sum_cycle_type, ←cons_erase hn, h1, multiset.sum_singleton] at h,
    rw [is_three_cycle, ←cons_erase hn, h1, h, singleton_eq_singleton] },
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1,
  rw [←sum_cycle_type, ←cons_erase hn, ←cons_erase hm, multiset.sum_cons, multiset.sum_cons] at h,
  linarith [two_le_of_mem_cycle_type hn, two_le_of_mem_cycle_type (mem_of_mem_erase hm)],
end

lemma is_cycle (h : is_three_cycle σ) : is_cycle σ :=
by rw [←card_cycle_type_eq_one, h.cycle_type, singleton_eq_singleton, card_singleton]

lemma sign (h : is_three_cycle σ) : sign σ = 1 :=
begin
  rw [sign_of_cycle_type, h.cycle_type],
  refl,
end

lemma inv {f : perm α} (h : is_three_cycle f) : is_three_cycle (f⁻¹) :=
by rwa [is_three_cycle, cycle_type_inv]

@[simp] lemma inv_iff {f : perm α} : is_three_cycle (f⁻¹) ↔ is_three_cycle f :=
⟨by { rw ← inv_inv f, apply inv }, inv⟩

lemma order_of {g : perm α} (ht : is_three_cycle g) :
  order_of g = 3 :=
by rw [←lcm_cycle_type, ht.cycle_type, multiset.singleton_eq_singleton,
  multiset.lcm_singleton, nat.normalize_eq]

lemma is_three_cycle_sq {g : perm α} (ht : is_three_cycle g) :
  is_three_cycle (g * g) :=
begin
  rw [←pow_two, ←card_support_eq_three_iff, support_pow_coprime, ht.card_support],
  rw [ht.order_of, nat.coprime_iff_gcd_eq_one],
  norm_num,
end

end is_three_cycle

section
variable [decidable_eq α]

lemma is_three_cycle_swap_mul_swap_same
  {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
  is_three_cycle (swap a b * swap a c) :=
begin
  suffices h : support (swap a b * swap a c) = {a, b, c},
  { rw [←card_support_eq_three_iff, h],
    simp [ab, ac, bc] },
  apply le_antisymm ((support_mul_le _ _).trans (λ x, _)) (λ x hx, _),
  { simp [ab, ac, bc] },
  { simp only [finset.mem_insert, finset.mem_singleton] at hx,
    rw mem_support,
    simp only [perm.coe_mul, function.comp_app, ne.def],
    obtain rfl | rfl | rfl := hx,
    { rw [swap_apply_left, swap_apply_of_ne_of_ne ac.symm bc.symm],
      exact ac.symm },
    { rw [swap_apply_of_ne_of_ne ab.symm bc, swap_apply_right],
      exact ab },
    { rw [swap_apply_right, swap_apply_left],
      exact bc } }
end

open subgroup

lemma swap_mul_swap_same_mem_closure_three_cycles
  {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
  (swap a b * swap a c) ∈ closure {σ : perm α | is_three_cycle σ } :=
begin
  by_cases bc : b = c,
  { subst bc,
    simp [one_mem] },
  exact subset_closure (is_three_cycle_swap_mul_swap_same ab ac bc)
end

lemma is_swap.mul_mem_closure_three_cycles {σ τ : perm α}
  (hσ : is_swap σ) (hτ : is_swap τ) :
  σ * τ ∈ closure {σ : perm α | is_three_cycle σ } :=
begin
  obtain ⟨a, b, ab, rfl⟩ := hσ,
  obtain ⟨c, d, cd, rfl⟩ := hτ,
  by_cases ac : a = c,
  { subst ac,
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd },
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d),
  { simp [swap_comm c a, mul_assoc] },
  rw h',
  exact mul_mem _ (swap_mul_swap_same_mem_closure_three_cycles ab ac)
    (swap_mul_swap_same_mem_closure_three_cycles (ne.symm ac) cd),
end

end

end equiv.perm
