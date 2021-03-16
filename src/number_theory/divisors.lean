/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.big_operators.order
import tactic
import data.nat.prime

/-!
# Divisor finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `nat` namespace:
 * `divisors n` is the `finset` of natural numbers that divide `n`.
 * `proper_divisors n` is the `finset` of natural numbers that divide `n`, other than `n`.
 * `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
 * `perfect n` is true when `n` is positive and the sum of `proper_divisors n` is `n`.

## Implementation details
 * `divisors 0`, `proper_divisors 0`, and `divisors_antidiagonal 0` are defined to be `∅`.

## Tags
divisors, perfect numbers

-/

open_locale classical
open_locale big_operators
open finset

namespace nat
variable (n : ℕ)

/-- `divisors n` is the `finset` of divisors of `n`. As a special case, `divisors 0 = ∅`. -/
def divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 (n + 1))

/-- `proper_divisors n` is the `finset` of divisors of `n`, other than `n`.
  As a special case, `proper_divisors 0 = ∅`. -/
def proper_divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 n)

/-- `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
  As a special case, `divisors_antidiagonal 0 = ∅`. -/
def divisors_antidiagonal : finset (ℕ × ℕ) :=
((finset.Ico 1 (n + 1)).product (finset.Ico 1 (n + 1))).filter (λ x, x.fst * x.snd = n)

variable {n}

lemma proper_divisors.not_self_mem : ¬ n ∈ proper_divisors n :=
begin
  rw proper_divisors,
  simp,
end

@[simp]
lemma mem_proper_divisors {m : ℕ} : n ∈ proper_divisors m ↔ n ∣ m ∧ n < m :=
begin
  rw [proper_divisors, finset.mem_filter, finset.Ico.mem, and_comm],
  apply and_congr_right,
  rw and_iff_right_iff_imp,
  intros hdvd hlt,
  apply nat.pos_of_ne_zero _,
  rintro rfl,
  rw zero_dvd_iff.1 hdvd at hlt,
  apply lt_irrefl 0 hlt,
end

lemma divisors_eq_proper_divisors_insert_self_of_pos (h : 0 < n):
  divisors n = has_insert.insert n (proper_divisors n) :=
by rw [divisors, proper_divisors, finset.Ico.succ_top h, finset.filter_insert, if_pos (dvd_refl n)]

@[simp]
lemma mem_divisors {m : ℕ} :
  n ∈ divisors m ↔ (n ∣ m ∧ m ≠ 0) :=
begin
  cases m,
  { simp [divisors] },
  simp only [divisors, finset.Ico.mem, ne.def, finset.mem_filter, succ_ne_zero, and_true,
             and_iff_right_iff_imp, not_false_iff],
  intro hdvd,
  split,
  { apply nat.pos_of_ne_zero,
    rintro rfl,
    apply nat.succ_ne_zero,
    rwa zero_dvd_iff at hdvd },
  { rw nat.lt_succ_iff,
    apply nat.le_of_dvd (nat.succ_pos m) hdvd }
end

lemma dvd_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : n ∣ m :=
begin
  cases m,
  { apply dvd_zero },
  { simp [mem_divisors.1 h], }
end

@[simp]
lemma mem_divisors_antidiagonal {x : ℕ × ℕ} :
  x ∈ divisors_antidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0 :=
begin
  simp only [divisors_antidiagonal, finset.Ico.mem, ne.def, finset.mem_filter, finset.mem_product],
  rw and_comm,
  apply and_congr_right,
  rintro rfl,
  split; intro h,
  { contrapose! h, simp [h], },
  { rw [nat.lt_add_one_iff, nat.lt_add_one_iff],
    rw [mul_eq_zero, decidable.not_or_iff_and_not] at h,
    simp only [succ_le_of_lt (nat.pos_of_ne_zero h.1), succ_le_of_lt (nat.pos_of_ne_zero h.2),
               true_and],
    exact ⟨le_mul_of_pos_right (nat.pos_of_ne_zero h.2),
      le_mul_of_pos_left (nat.pos_of_ne_zero h.1)⟩ }
end

variable {n}

lemma divisor_le {m : ℕ}:
n ∈ divisors m → n ≤ m :=
begin
  cases m,
  { simp },
  simp only [mem_divisors, m.succ_ne_zero, and_true, ne.def, not_false_iff],
  exact nat.le_of_dvd (nat.succ_pos m),
end

lemma divisors_subset_of_dvd {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
finset.subset_iff.2 $ λ x hx, nat.mem_divisors.mpr (⟨dvd.trans (nat.mem_divisors.mp hx).1 h, hzero⟩)

lemma divisors_subset_proper_divisors {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) (hdiff : m ≠ n) :
  divisors m ⊆ proper_divisors n :=
begin
  apply finset.subset_iff.2,
  intros x hx,
  exact nat.mem_proper_divisors.2 (⟨dvd.trans (nat.mem_divisors.1 hx).1 h,
    lt_of_le_of_lt (divisor_le hx) (lt_of_le_of_ne (divisor_le (nat.mem_divisors.2
    ⟨h, hzero⟩)) hdiff)⟩)
end

@[simp]
lemma divisors_zero : divisors 0 = ∅ := by { ext, simp }

@[simp]
lemma proper_divisors_zero : proper_divisors 0 = ∅ := by { ext, simp }

lemma proper_divisors_subset_divisors : proper_divisors n ⊆ divisors n :=
begin
  cases n,
  { simp },
  rw [divisors_eq_proper_divisors_insert_self_of_pos (nat.succ_pos _)],
  apply subset_insert,
end

@[simp]
lemma divisors_one : divisors 1 = {1} := by { ext, simp }

@[simp]
lemma proper_divisors_one : proper_divisors 1 = ∅ :=
begin
  ext,
  simp only [finset.not_mem_empty, nat.dvd_one, not_and, not_lt, mem_proper_divisors, iff_false],
  apply ge_of_eq,
end

lemma pos_of_mem_divisors {m : ℕ} (h : m ∈ n.divisors) : 0 < m :=
begin
  cases m,
  { rw [mem_divisors, zero_dvd_iff] at h,
    rcases h with ⟨rfl, h⟩,
    exfalso,
    apply h rfl },
  apply nat.succ_pos,
end

lemma pos_of_mem_proper_divisors {m : ℕ} (h : m ∈ n.proper_divisors) : 0 < m :=
pos_of_mem_divisors (proper_divisors_subset_divisors h)

lemma one_mem_proper_divisors_iff_one_lt :
  1 ∈ n.proper_divisors ↔ 1 < n :=
by rw [mem_proper_divisors, and_iff_right (one_dvd _)]

@[simp]
lemma divisors_antidiagonal_zero : divisors_antidiagonal 0 = ∅ := by { ext, simp }

@[simp]
lemma divisors_antidiagonal_one : divisors_antidiagonal 1 = {(1,1)} :=
by { ext, simp [nat.mul_eq_one_iff, prod.ext_iff], }

lemma swap_mem_divisors_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) :
  x.swap ∈ divisors_antidiagonal n :=
begin
  rw [mem_divisors_antidiagonal, mul_comm] at h,
  simp [h.1, h.2],
end

lemma fst_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) :
  x.fst ∈ divisors n :=
begin
  rw mem_divisors_antidiagonal at h,
  simp [dvd.intro _ h.1, h.2],
end

lemma snd_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) :
  x.snd ∈ divisors n :=
begin
  rw mem_divisors_antidiagonal at h,
  simp [dvd.intro_left _ h.1, h.2],
end

@[simp]
lemma map_swap_divisors_antidiagonal :
  (divisors_antidiagonal n).map ⟨prod.swap, prod.swap_right_inverse.injective⟩
  = divisors_antidiagonal n :=
begin
  ext,
  simp only [exists_prop, mem_divisors_antidiagonal, finset.mem_map, function.embedding.coe_fn_mk,
             ne.def, prod.swap_prod_mk, prod.exists],
  split,
  { rintros ⟨x, y, ⟨⟨rfl, h⟩, rfl⟩⟩,
    simp [mul_comm, h], },
  { rintros ⟨rfl, h⟩,
    use [a.snd, a.fst],
    rw mul_comm,
    simp [h] }
end

lemma sum_divisors_eq_sum_proper_divisors_add_self :
∑ i in divisors n, i = ∑ i in proper_divisors n, i + n :=
begin
  cases n,
  { simp },
  { rw [divisors_eq_proper_divisors_insert_self_of_pos (nat.succ_pos _),
        finset.sum_insert (proper_divisors.not_self_mem), add_comm] }
end

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and `n`
  is positive. -/
def perfect (n : ℕ) : Prop := (∑ i in proper_divisors n, i = n) ∧ 0 < n

theorem perfect_iff_sum_proper_divisors (h : 0 < n) :
  perfect n ↔ ∑ i in proper_divisors n, i = n := and_iff_left h

theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) :
  perfect n ↔ ∑ i in divisors n, i = 2 * n :=
begin
  rw [perfect_iff_sum_proper_divisors h, sum_divisors_eq_sum_proper_divisors_add_self, two_mul],
  split; intro h,
  { rw h },
  { apply add_right_cancel h }
end

lemma mem_divisors_prime_pow {p : ℕ} (pp : p.prime) (k : ℕ) {x : ℕ} :
  x ∈ divisors (p ^ k) ↔ ∃ (j : ℕ) (H : j ≤ k), x = p ^ j :=
by rw [mem_divisors, nat.dvd_prime_pow pp, and_iff_left (ne_of_gt (pow_pos pp.pos k))]

lemma prime.divisors {p : ℕ} (pp : p.prime) :
  divisors p = {1, p} :=
begin
  ext,
  simp only [pp.ne_zero, and_true, ne.def, not_false_iff, finset.mem_insert,
    finset.mem_singleton, mem_divisors],
  refine ⟨pp.2 a, λ h, _⟩,
  rcases h; subst h,
  apply one_dvd,
end

lemma prime.proper_divisors {p : ℕ} (pp : p.prime) :
  proper_divisors p = {1} :=
by rw [← erase_insert (proper_divisors.not_self_mem),
    ← divisors_eq_proper_divisors_insert_self_of_pos pp.pos,
    pp.divisors, insert_singleton_comm, erase_insert (λ con, pp.ne_one (mem_singleton.1 con))]

lemma divisors_prime_pow {p : ℕ} (pp : p.prime) (k : ℕ) :
  divisors (p ^ k) = (finset.range (k + 1)).map ⟨pow p, pow_right_injective pp.two_le⟩ :=
by { ext, simp [mem_divisors_prime_pow, pp, nat.lt_succ_iff, @eq_comm _ a] }

lemma eq_proper_divisors_of_subset_of_sum_eq_sum {s : finset ℕ} (hsub : s ⊆ n.proper_divisors) :
  ∑ x in s, x = ∑ x in n.proper_divisors, x → s = n.proper_divisors :=
begin
  cases n,
  { rw [proper_divisors_zero, subset_empty] at hsub,
    simp [hsub] },
  classical,
  rw [← sum_sdiff hsub],
  intros h,
  apply subset.antisymm hsub,
  rw [← sdiff_eq_empty_iff_subset],
  contrapose h,
  rw [← ne.def, ← nonempty_iff_ne_empty] at h,
  apply ne_of_lt,
  rw [← zero_add (∑ x in s, x), ← add_assoc, add_zero],
  apply add_lt_add_right,
  have hlt := sum_lt_sum_of_nonempty h (λ x hx, pos_of_mem_proper_divisors (sdiff_subset _ _ hx)),
  simp only [sum_const_zero] at hlt,
  apply hlt
end

lemma sum_proper_divisors_dvd (h : ∑ x in n.proper_divisors, x ∣ n) :
  (∑ x in n.proper_divisors, x = 1) ∨ (∑ x in n.proper_divisors, x = n) :=
begin
  cases n,
  { simp },
  cases n,
  { contrapose! h,
    simp, },
  rw or_iff_not_imp_right,
  intro ne_n,
  have hlt : ∑ x in n.succ.succ.proper_divisors, x < n.succ.succ :=
    lt_of_le_of_ne (nat.le_of_dvd (nat.succ_pos _) h) ne_n,
  symmetry,
  rw [← mem_singleton, eq_proper_divisors_of_subset_of_sum_eq_sum (singleton_subset_iff.2
        (mem_proper_divisors.2 ⟨h, hlt⟩)) sum_singleton, mem_proper_divisors],
  refine ⟨one_dvd _, nat.succ_lt_succ (nat.succ_pos _)⟩,
end

@[simp]
lemma prime.sum_proper_divisors {α : Type*} [add_comm_monoid α] {p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∑ x in p.proper_divisors, f x = f 1 :=
by simp [h.proper_divisors]

@[simp]
lemma prime.sum_divisors {α : Type*} [add_comm_monoid α] {p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∑ x in p.divisors, f x = f p + f 1 :=
by rw [divisors_eq_proper_divisors_insert_self_of_pos h.pos,
       sum_insert proper_divisors.not_self_mem, h.sum_proper_divisors]

lemma proper_divisors_eq_singleton_one_iff_prime :
  n.proper_divisors = {1} ↔ n.prime :=
⟨λ h, begin
  have h1 := mem_singleton.2 rfl,
  rw [← h, mem_proper_divisors] at h1,
  refine ⟨h1.2, _⟩,
  intros m hdvd,
  rw [← mem_singleton, ← h, mem_proper_divisors],
  cases lt_or_eq_of_le (nat.le_of_dvd (lt_trans (nat.succ_pos _) h1.2) hdvd),
  { left,
    exact ⟨hdvd, h_1⟩ },
  { right,
    exact h_1 }
end, prime.proper_divisors⟩

lemma sum_proper_divisors_eq_one_iff_prime :
  ∑ x in n.proper_divisors, x = 1 ↔ n.prime :=
begin
  cases n,
  { simp [nat.not_prime_zero] },
  cases n,
  { simp [nat.not_prime_one] },
  rw [← proper_divisors_eq_singleton_one_iff_prime],
  refine ⟨λ h, _, λ h, h.symm ▸ sum_singleton⟩,
  rw [@eq_comm (finset ℕ) _ _],
  apply eq_proper_divisors_of_subset_of_sum_eq_sum
    (singleton_subset_iff.2 (one_mem_proper_divisors_iff_one_lt.2 (succ_lt_succ (nat.succ_pos _))))
    (eq.trans sum_singleton h.symm)
end

@[simp]
lemma prod_divisors_prime {α : Type*} [comm_monoid α] {p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∏ x in p.divisors, f x = f p * f 1 :=
by simpa using congr_arg additive.to_mul (@prime.sum_divisors _ _ _ (additive.of_mul ∘ f) h)

@[simp]
lemma sum_divisors_prime_pow {α : Type*} [add_comm_monoid α] {k p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∑ x in (p ^ k).divisors, f x = ∑ x in range (k + 1), f (p ^ x) :=
by simp [h, divisors_prime_pow]

@[simp]
lemma prod_divisors_prime_pow {α : Type*} [comm_monoid α] {k p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∏ x in (p ^ k).divisors, f x = ∏ x in range (k + 1), f (p ^ x) :=
by simpa using congr_arg additive.to_mul (@sum_divisors_prime_pow _ _ _ _ (additive.of_mul ∘ f) h)

@[simp]
lemma filter_dvd_eq_divisors {n : ℕ} (h : n ≠ 0) :
  finset.filter (λ (x : ℕ), x ∣ n) (finset.range (n : ℕ).succ) = (n : ℕ).divisors :=
begin
  apply finset.ext,
  simp only [h, mem_filter, and_true, and_iff_right_iff_imp, cast_id, mem_range, ne.def,
  not_false_iff, mem_divisors],
  intros a ha,
  exact nat.lt_succ_of_le (nat.divisor_le (nat.mem_divisors.2 ⟨ha, h⟩))
end

end nat
