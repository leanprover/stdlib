/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.bitvec.core
import tactic.norm_num
import tactic.monotonicity

namespace bitvec

instance (n : ℕ) : preorder (bitvec n) :=
preorder.lift bitvec.to_nat

/-- convert `fin` to `bitvec` -/
def of_fin {n : ℕ} (i : fin $ 2^n) : bitvec n :=
bitvec.of_nat _ i.val

lemma of_fin_val {n : ℕ} (i : fin $ 2^n) : (of_fin i).to_nat = i.val :=
by rw [of_fin,to_nat_of_nat,nat.mod_eq_of_lt]; apply i.is_lt

/-- convert `bitvec` to `fin` -/
def to_fin {n : ℕ} (i : bitvec n) : fin $ 2^n :=
@fin.of_nat' _ (pow_pos (by norm_num) _) i.to_nat

lemma add_lsb_eq_twice_add_one {x b} :
  add_lsb x b = 2 * x + cond b 1 0 :=
by simp [add_lsb,two_mul]

lemma to_nat_eq_foldr_reverse {n : ℕ} (v : bitvec n) :
  v.to_nat = v.to_list.reverse.foldr (flip add_lsb) 0 :=
by rw [list.foldr_reverse, flip]; refl

lemma to_nat_lt {n : ℕ} (v : bitvec n) : v.to_nat < 2^n :=
begin
  suffices : v.to_nat + 1 ≤ 2 ^ n, { simpa },
  rw to_nat_eq_foldr_reverse,
  cases v with xs h,
  dsimp [bitvec.to_nat,bits_to_nat],
  rw ← list.length_reverse at h,
  generalize_hyp : xs.reverse = ys at ⊢ h, clear xs,
  induction ys generalizing n,
  { simp [← h] },
  { simp only [←h, pow_add, flip, list.length, list.foldr, pow_one],
    rw [add_lsb_eq_twice_add_one],
    transitivity 2 * list.foldr (λ (x : bool) (y : ℕ), add_lsb y x) 0 ys_tl + 2 * 1,
    { ac_mono, rw two_mul, mono, cases ys_hd; simp },
    { rw ← left_distrib, ac_mono, norm_num,
      apply ys_ih, refl } },
end

lemma add_lsb_div_two {x b} : add_lsb x b / 2 = x :=
by cases b; simp only [nat.add_mul_div_left, add_lsb, ←two_mul, add_comm, nat.succ_pos',
                       nat.mul_div_right, gt_iff_lt, zero_add, cond]; norm_num

lemma to_bool_add_lsb_mod_two {x b} : to_bool (add_lsb x b % 2 = 1) = b :=
by cases b; simp only [to_bool_iff, nat.add_mul_mod_self_left, add_lsb, ←two_mul, add_comm, bool.to_bool_false,
                       nat.mul_mod_right, zero_add, cond, zero_ne_one]; norm_num

lemma of_nat_to_nat  {n : ℕ} (v : bitvec n) : bitvec.of_nat _ v.to_nat = v :=
begin
  cases v with xs h,
  ext1,
  change vector.to_list _ = xs,
  dsimp [bitvec.to_nat,bits_to_nat],
  rw ← list.length_reverse at h,
  rw [← list.reverse_reverse xs,list.foldl_reverse],
  generalize_hyp : xs.reverse = ys at ⊢ h, clear xs,
  induction ys generalizing n,
  { cases h, simp [bitvec.of_nat] },
  { simp only [←nat.succ_eq_add_one, list.length] at h,
    cases h, simp only [bitvec.of_nat, vector.to_list_cons, vector.to_list_nil, list.reverse_cons, vector.to_list_append, list.foldr],
    erw [add_lsb_div_two,to_bool_add_lsb_mod_two],
    congr, apply ys_ih, refl }
end

lemma to_fin_val {n : ℕ} (v : bitvec n) : (to_fin v : ℕ) = v.to_nat :=
by rw [to_fin, fin.coe_of_nat_eq_mod', nat.mod_eq_of_lt]; apply to_nat_lt

lemma to_fin_le_to_fin_of_le {n} {v₀ v₁ : bitvec n} (h : v₀ ≤ v₁) : v₀.to_fin ≤ v₁.to_fin :=
show (v₀.to_fin : ℕ) ≤ v₁.to_fin,
by rw [to_fin_val,to_fin_val]; exact h

lemma of_fin_le_of_fin_of_le {n : ℕ} {i j : fin (2^n)} (h : i ≤ j) : of_fin i ≤ of_fin j :=
show (bitvec.of_nat n i).to_nat ≤ (bitvec.of_nat n j).to_nat,
by { simp only [to_nat_of_nat, nat.mod_eq_of_lt, fin.is_lt], exact h }

lemma to_fin_of_fin {n} (i : fin $ 2^n) : (of_fin i).to_fin = i :=
fin.eq_of_veq (by simp [to_fin_val, of_fin, to_nat_of_nat, nat.mod_eq_of_lt, i.is_lt])

lemma of_fin_to_fin {n} (v : bitvec n) : of_fin (to_fin v) = v :=
by dsimp [of_fin]; rw [to_fin_val, of_nat_to_nat]

end bitvec
