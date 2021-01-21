/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.polynomial.derivative
import logic.function.iterate
import data.finset.intervals
import tactic.linarith

/-!
# Theory of iterated derivative
We define and prove some lemmas about iterated (formal) derivative for polynomials over a semiring.
-/

noncomputable theory

open finset nat polynomial
open_locale big_operators

namespace polynomial
universes u
variable {R : Type u}

section semiring

variables [semiring R] (r : R) (f p q : polynomial R) (n k : ℕ)

/-- `iterated_deriv f n` is the `n`-th formal derivative of the polynomial `f` -/
def iterated_deriv : polynomial R := derivative ^[n] f

@[simp] lemma iterated_deriv_zero_right : iterated_deriv f 0 = f := rfl

lemma iterated_deriv_succ : iterated_deriv f (n + 1) = (iterated_deriv f n).derivative :=
by rw [iterated_deriv, iterated_deriv, function.iterate_succ']

@[simp] lemma iterated_deriv_zero_left : iterated_deriv (0 : polynomial R) n = 0 :=
begin
  induction n with n hn,
  { exact iterated_deriv_zero_right _ },
  { rw [iterated_deriv_succ, hn, derivative_zero] },
end

@[simp] lemma iterated_deriv_add : iterated_deriv (p + q) n = iterated_deriv p n + iterated_deriv q n :=
begin
  induction n with n ih,
  { simp only [iterated_deriv_zero_right], },
  { simp only [iterated_deriv_succ, ih, derivative_add] }
end

@[simp] lemma iterated_deriv_smul : iterated_deriv (r • p) n = r • iterated_deriv p n :=
begin
  induction n with n ih,
  { simp only [iterated_deriv_zero_right] },
  { simp only [iterated_deriv_succ, ih, derivative_smul] }
end

@[simp] lemma iterated_deriv_X_zero : iterated_deriv (X : polynomial R) 0 = X :=
by simp only [iterated_deriv_zero_right]

@[simp] lemma iterated_deriv_X_one : iterated_deriv (X : polynomial R) 1 = 1 :=
by simp only [iterated_deriv, derivative_X, function.iterate_one]

@[simp] lemma iterated_deriv_X (h : 1 < n) : iterated_deriv (X : polynomial R) n = 0 :=
begin
  induction n with n ih,
  { exfalso, exact not_lt_zero 1 h},
  { simp only [iterated_deriv_succ],
    by_cases H : n = 1,
    { rw H, simp only [iterated_deriv_X_one, derivative_one] },
    { replace h : 1 < n := array.push_back_idx h (ne.symm H),
      rw ih h, simp only [derivative_zero] } }
end


@[simp] lemma iterated_deriv_C_zero : iterated_deriv (C r) 0 = C r :=
  by simp only [iterated_deriv_zero_right]

@[simp] lemma iterated_deriv_C (h : 0 < n) : iterated_deriv (C r) n = 0 :=
begin
  induction n with n ih,
  { exfalso, exact nat.lt_asymm h h },
  { by_cases H : n = 0,
    { rw [iterated_deriv_succ, H], simp only [iterated_deriv_C_zero, derivative_C]},
    { replace h : 0 < n := nat.pos_of_ne_zero H,
      rw [iterated_deriv_succ, ih h], simp only [derivative_zero] } }
end

@[simp] lemma iterated_deriv_one_zero : iterated_deriv (1 : polynomial R) 0 = 1 :=
by simp only [iterated_deriv_zero_right]

@[simp] lemma iterated_deriv_one : 0 < n → iterated_deriv (1 : polynomial R) n = 0 := λ h,
begin
  have eq1 : (1 : polynomial R) = C 1 := by simp only [ring_hom.map_one],
  rw eq1, exact iterated_deriv_C _ _ h,
end

end semiring

section ring
variables [ring R] (p q : polynomial R) (n : ℕ)

@[simp] lemma iterated_deriv_neg : iterated_deriv (-p) n = - iterated_deriv p n :=
begin
  induction n with n ih,
  { simp only [iterated_deriv_zero_right] },
  { simp only [iterated_deriv_succ, ih, derivative_neg] }
end

@[simp] lemma iterated_deriv_sub : iterated_deriv (p - q) n = iterated_deriv p n - iterated_deriv q n :=
by rw [sub_eq_add_neg, iterated_deriv_add, iterated_deriv_neg, ←sub_eq_add_neg]


end ring

section comm_semiring
variable [comm_semiring R]
variables (f p q : polynomial R) (n k : ℕ)

lemma coeff_iterated_deriv_as_prod_Ico :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = (∏ i in Ico m.succ (m + k.succ), i) * (f.coeff (m+k)) :=
begin
  induction k with k ih,
  { simp only [add_zero, forall_const, one_mul, Ico.self_eq_empty, eq_self_iff_true,
      iterated_deriv_zero_right, prod_empty] },
  { intro m, rw [iterated_deriv_succ, coeff_derivative, ih (m+1), mul_right_comm],
    apply congr_arg2,
    { have set_eq : (Ico m.succ (m + k.succ.succ)) = (Ico (m + 1).succ (m + 1 + k.succ)) ∪ {m+1},
      { rw [union_comm, ←insert_eq, Ico.insert_succ_bot, add_succ, add_succ, add_succ _ k,
            ←succ_eq_add_one, succ_add],
        rw succ_eq_add_one,
        linarith },
      rw [set_eq, prod_union],
      apply congr_arg2,
      { refl },
      { simp only [prod_singleton], norm_cast },
      { simp only [succ_pos', disjoint_singleton, and_true, lt_add_iff_pos_right, not_le, Ico.mem],
        exact lt_add_one (m + 1) } },
    { exact congr_arg _ (succ_add m k) } },
end

lemma coeff_iterated_deriv_as_prod_range :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = f.coeff (m + k) * (∏ i in finset.range k, ↑(m + k - i)) :=
begin
  induction k with k ih,
  { simp },

  intro m,
  calc (f.iterated_deriv k.succ).coeff m
      = f.coeff (m + k.succ) * (∏ i in finset.range k, ↑(m + k.succ - i)) * (m + 1) :
    by rw [iterated_deriv_succ, coeff_derivative, ih m.succ, succ_add, add_succ]
  ... = f.coeff (m + k.succ) * (↑(m + 1) * (∏ (i : ℕ) in range k, ↑(m + k.succ - i))) :
    by { push_cast, ring }
  ... = f.coeff (m + k.succ) * (∏ (i : ℕ) in range k.succ, ↑(m + k.succ - i)) :
    by { rw [prod_range_succ, nat.add_sub_assoc (le_succ k), nat.succ_sub le_rfl, nat.sub_self] }
end

lemma iterated_deriv_eq_zero_of_nat_degree_lt (h : f.nat_degree < n) : iterated_deriv f n = 0 :=
begin
  ext m,
  rw [coeff_iterated_deriv_as_prod_range, coeff_zero, coeff_eq_zero_of_nat_degree_lt, zero_mul],
  linarith
end

lemma iterated_deriv_mul :
  iterated_deriv (p * q) n =
  ∑ k in range n.succ,
    (C (n.choose k : R)) * iterated_deriv p (n - k) * iterated_deriv q k :=
begin
  induction n with n IH,
  { simp },

  calc (p * q).iterated_deriv n.succ
      = (∑ (k : ℕ) in range n.succ,
           C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv k).derivative :
    by rw [iterated_deriv_succ, IH]
  ... = ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k + 1) * q.iterated_deriv k +
        ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) :
    by simp_rw [derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add,
                iterated_deriv_succ, sum_add_distrib]
  ... = (∑ (k : ℕ) in range n.succ,
            C ↑(n.choose k.succ) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) +
          C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0) +
        ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) : _
  ... = ∑ (k : ℕ) in range n.succ,
          C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) +
        ∑ (k : ℕ) in range n.succ,
            C ↑(n.choose k.succ) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) +
        C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0 :
    by ring
  ... = ∑ (i : ℕ) in range n.succ,
          C ↑(n.succ.choose (i + 1)) * p.iterated_deriv (n + 1 - (i + 1)) * q.iterated_deriv (i + 1) +
        C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0 :
    by simp_rw [choose_succ_succ, succ_sub_succ, cast_add, C.map_add, add_mul, sum_add_distrib]
  ... = ∑ (k : ℕ) in range n.succ.succ,
          C ↑(n.succ.choose k) * p.iterated_deriv (n.succ - k) * q.iterated_deriv k :
    by rw [sum_range_succ' _ n.succ, choose_zero_right, nat.sub_zero],

  congr,
  refine (sum_range_succ' _ _).trans (congr_arg2 (+) _ _),
  { rw [sum_range_succ, nat.choose_succ_self, cast_zero, C.map_zero, zero_mul, zero_mul, zero_add],
    refine sum_congr rfl (λ k hk, _),
    rw mem_range at hk,
    congr,
    rw [← nat.sub_add_comm (nat.succ_le_of_lt hk), nat.succ_sub_succ] },
  { rw [choose_zero_right, nat.sub_zero] },
end

end comm_semiring

end polynomial
