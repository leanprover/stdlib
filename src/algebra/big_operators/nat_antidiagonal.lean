/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import data.finset.nat_antidiagonal
import algebra.big_operators.basic

/-!
# Big operators for `nat_antidiagonal`

This file contains theorems relevant to big operators over `finset.nat.antidiagonal`.
-/

open_locale big_operators
open multiplicative additive

variables {M N : Type*} [comm_monoid M] [add_comm_monoid N]

namespace finset
namespace nat

lemma prod_antidiagonal_succ {n : ℕ} (f : ℕ × ℕ → M) :
  ∏ p in antidiagonal (n + 1), f p = f (0, n + 1) * ∏ p in antidiagonal n, f (p.1 + 1, p.2) :=
begin
  rw [antidiagonal_succ, prod_insert, prod_map], refl,
  intro con, rcases mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
  simp only [prod.mk.inj_iff, function.embedding.coe_prod_map, prod.map_mk] at h2,
  apply nat.succ_ne_zero a h2.1,
end

lemma sum_antidiagonal_succ {n : ℕ} (f : ℕ × ℕ → N) :
  ∑ p in antidiagonal (n + 1), f p = f (0, n + 1) + ∑ p in antidiagonal n, f (p.1 + 1, p.2) :=
by simpa using congr_arg to_add (prod_antidiagonal_succ (of_add ∘ f))

@[to_additive]
lemma prod_antidiagonal_swap {n : ℕ} (f : ℕ × ℕ → M) :
  ∏ p in antidiagonal n, f p.swap = ∏ p in antidiagonal n, f p :=
by { nth_rewrite 1 ← map_swap_antidiagonal, rw [prod_map], refl }

lemma prod_antidiagonal_succ' {n : ℕ} (f : ℕ × ℕ → M) :
  ∏ p in antidiagonal (n + 1), f p = f (n + 1, 0) * ∏ p in antidiagonal n, f (p.1, p.2 + 1) :=
begin
  rw [← prod_antidiagonal_swap, prod_antidiagonal_succ, ← prod_antidiagonal_swap],
  refl
end

lemma sum_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → N} :
  ∑ p in antidiagonal (n + 1), f p = f (n + 1, 0) + ∑ p in antidiagonal n, f (p.1, p.2 + 1) :=
by simpa using congr_arg to_add (prod_antidiagonal_succ' (of_add ∘ f))

@[to_additive]
lemma prod_antidiagonal_subst {n : ℕ} {f : ℕ × ℕ → ℕ → M} :
  ∏ p in antidiagonal n, f p n = ∏ p in antidiagonal n, f p (p.1 + p.2) :=
prod_congr rfl $ λ p hp, by rw [nat.mem_antidiagonal.1 hp]

@[to_additive]
lemma prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [comm_monoid M] (f : ℕ × ℕ → M) (n : ℕ) :
  ∏ ij in finset.nat.antidiagonal n, f ij = ∏ k in range n.succ, f (k, n - k) :=
begin
  convert prod_map _ ⟨λ i, (i, n - i), λ x y h, (prod.mk.inj h).1⟩ _,
  refl,
end

/-- This lemma matches more generally than `finset.nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ←`. -/
@[to_additive]
lemma prod_antidiagonal_eq_prod_range_succ {M : Type*} [comm_monoid M] (f : ℕ → ℕ → M) (n : ℕ) :
  ∏ ij in finset.nat.antidiagonal n, f ij.1 ij.2 = ∏ k in range n.succ, f k (n - k) :=
prod_antidiagonal_eq_prod_range_succ_mk _ _

end nat

end finset
