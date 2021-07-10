/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam, Mario Carneiro
-/
import data.int.modeq
import data.list.indexes
import tactic.interval_cases
import tactic.linarith

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

A basic `norm_digits` tactic is also provided for proving goals of the form
`nat.digits a b = l` where `a` and `b` are numerals.
-/

namespace nat

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux_0 : ℕ → list ℕ
| 0 := []
| (n+1) := [n+1]

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux_1 (n : ℕ) : list ℕ := list.repeat 1 n

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux (b : ℕ) (h : 2 ≤ b) : ℕ → list ℕ
| 0 := []
| (n+1) :=
  have (n+1)/b < n+1 := nat.div_lt_self (nat.succ_pos _) h,
  (n+1) % b :: digits_aux ((n+1)/b)

@[simp] lemma digits_aux_zero (b : ℕ) (h : 2 ≤ b) : digits_aux b h 0 = [] := by rw digits_aux

lemma digits_aux_def (b : ℕ) (h : 2 ≤ b) (n : ℕ) (w : 0 < n) :
  digits_aux b h n = n % b :: digits_aux b h (n/b) :=
begin
  cases n,
  { cases w, },
  { rw [digits_aux], }
end

/--
`digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `of_digits b L = L.foldr (λ x y, x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = list.repeat 1 n`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `nat.to_digits` in core, which is used for printing numerals.
In particular, `nat.to_digits b 0 = [0]`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → list ℕ
| 0 := digits_aux_0
| 1 := digits_aux_1
| (b+2) := digits_aux (b+2) (by norm_num)

@[simp] lemma digits_zero (b : ℕ) : digits b 0 = [] :=
by rcases b with _|⟨_|⟨_⟩⟩; simp [digits, digits_aux_0, digits_aux_1]

@[simp] lemma digits_zero_zero : digits 0 0 = [] := rfl

@[simp] lemma digits_zero_succ (n : ℕ) : digits 0 (n.succ) = [n+1] := rfl

theorem digits_zero_succ' : ∀ {n : ℕ} (w : 0 < n), digits 0 n = [n]
| 0 h := absurd h dec_trivial
| (n+1) _ := rfl

@[simp] lemma digits_one (n : ℕ) : digits 1 n = list.repeat 1 n := rfl

@[simp] lemma digits_one_succ (n : ℕ) : digits 1 (n + 1) = 1 :: digits 1 n := rfl

@[simp] lemma digits_add_two_add_one (b n : ℕ) :
  digits (b+2) (n+1) = (((n+1) % (b+2)) :: digits (b+2) ((n+1) / (b+2))) :=
by { rw [digits, digits_aux_def], exact succ_pos n }

theorem digits_def' : ∀ {b : ℕ} (h : 2 ≤ b) {n : ℕ} (w : 0 < n),
  digits b n = n % b :: digits b (n/b)
| 0 h := absurd h dec_trivial
| 1 h := absurd h dec_trivial
| (b+2) h := digits_aux_def _ _

@[simp]
lemma digits_of_lt (b x : ℕ) (w₁ : 0 < x) (w₂ : x < b) : digits b x = [x] :=
begin
  cases b,
  { cases w₂ },
  { cases b,
    { interval_cases x, },
    { cases x,
      { cases w₁, },
      { rw [digits_add_two_add_one, nat.div_eq_of_lt w₂, digits_zero, nat.mod_eq_of_lt w₂] } } }
end

lemma digits_add (b : ℕ) (h : 2 ≤ b) (x y : ℕ) (w : x < b) (w' : 0 < x ∨ 0 < y) :
  digits b (x + b * y) = x :: digits b y :=
begin
  cases b,
  { cases h, },
  { cases b,
    { norm_num at h, },
    { cases y,
      { norm_num at w',
        simp [w, w'], },
      dsimp [digits],
      rw digits_aux_def,
      { congr,
        { simp [nat.add_mod, nat.mod_eq_of_lt w], },
        { simp [mul_comm (b+2), nat.add_mul_div_right, nat.div_eq_of_lt w], }
      },
      { apply nat.succ_pos, }, }, },
end

/--
`of_digits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
-- If we had a function converting a list into a polynomial,
-- and appropriate lemmas about that function,
-- we could rewrite this in terms of that.
def of_digits {α : Type*} [semiring α] (b : α) : list ℕ → α
| [] := 0
| (h :: t) := h + b * of_digits t

lemma of_digits_eq_foldr {α : Type*} [semiring α] (b : α) (L : list ℕ) :
  of_digits b L = L.foldr (λ x y, x + b * y) 0 :=
begin
  induction L with d L ih,
  { refl, },
  { dsimp [of_digits], rw ih, },
end

lemma of_digits_eq_sum_map_with_index_aux (b : ℕ) (l : list ℕ) :
  ((list.range l.length).zip_with ((λ (i a : ℕ), a * b ^ i) ∘ succ) l).sum =
  b * ((list.range l.length).zip_with (λ i a, a * b ^ i) l).sum :=
begin
  suffices : (list.range l.length).zip_with (((λ (i a : ℕ), a * b ^ i) ∘ succ)) l =
      (list.range l.length).zip_with (λ i a, b * (a * b ^ i)) l,
    { simp [this] },
  congr,
  ext,
  simp [pow_succ],
  ring
end

lemma of_digits_eq_sum_map_with_index (b : ℕ) (L : list ℕ):
  of_digits b L = (L.map_with_index (λ i a, a * b ^ i)).sum :=
begin
  rw [list.map_with_index_eq_enum_map, list.enum_eq_zip_range,
      list.map_uncurry_zip_eq_zip_with, of_digits_eq_foldr],
  induction L with hd tl hl,
  { simp },
  { simpa [list.range_succ_eq_map, list.zip_with_map_left, of_digits_eq_sum_map_with_index_aux]
      using or.inl hl }
end

@[simp] lemma of_digits_singleton {b n : ℕ} : of_digits b [n] = n := by simp [of_digits]

@[simp] lemma of_digits_one_cons {α : Type*} [semiring α] (h : ℕ) (L : list ℕ) :
  of_digits (1 : α) (h :: L) = h + of_digits 1 L :=
by simp [of_digits]

lemma of_digits_append {b : ℕ} {l1 l2 : list ℕ} :
  of_digits b (l1 ++ l2) = of_digits b l1 + b^(l1.length) * of_digits b l2 :=
begin
  induction l1 with hd tl IH,
  { simp [of_digits] },
  { rw [of_digits, list.cons_append, of_digits, IH, list.length_cons, pow_succ'],
    ring }
end

@[norm_cast] lemma coe_of_digits (α : Type*) [semiring α] (b : ℕ) (L : list ℕ) :
  ((of_digits b L : ℕ) : α) = of_digits (b : α) L :=
begin
  induction L with d L ih,
  { refl, },
  { dsimp [of_digits], push_cast, rw ih, }
end

@[norm_cast] lemma coe_int_of_digits (b : ℕ) (L : list ℕ) :
  ((of_digits b L : ℕ) : ℤ) = of_digits (b : ℤ) L :=
begin
  induction L with d L ih,
  { refl, },
  { dsimp [of_digits], push_cast, rw ih, }
end

lemma digits_zero_of_eq_zero {b : ℕ} (h : 1 ≤ b) {L : list ℕ} (w : of_digits b L = 0) :
  ∀ l ∈ L, l = 0 :=
begin
  induction L with d L ih,
  { intros l m,
    cases m, },
  { intros l m,
    dsimp [of_digits] at w,
    rcases m with ⟨rfl⟩,
    { convert nat.eq_zero_of_add_eq_zero_right w, simp, },
    { exact ih ((nat.mul_right_inj h).mp (nat.eq_zero_of_add_eq_zero_left w)) _ m, }, }
end

lemma digits_of_digits
  (b : ℕ) (h : 2 ≤ b) (L : list ℕ)
  (w₁ : ∀ l ∈ L, l < b) (w₂ : ∀ (h : L ≠ []), L.last h ≠ 0) :
  digits b (of_digits b L) = L :=
begin
  induction L with d L ih,
  { dsimp [of_digits], simp },
  { dsimp [of_digits],
    replace w₂ := w₂ (by simp),
    rw digits_add b h,
    { rw ih,
      { simp, },
      { intros l m, apply w₁, exact list.mem_cons_of_mem _ m, },
      { intro h,
        { rw [list.last_cons _ h] at w₂,
            convert w₂, }}},
    { convert w₁ d (list.mem_cons_self _ _), simp, },
    { by_cases h' : L = [],
      { rcases h' with rfl,
        simp at w₂,
        left,
        apply nat.pos_of_ne_zero,
        convert w₂, simp, },
      { right,
        apply nat.pos_of_ne_zero,
        contrapose! w₂,
        apply digits_zero_of_eq_zero _ w₂,
        { rw list.last_cons _ h',
          exact list.last_mem h', },
        { exact le_of_lt h, }, }, }, },
end

lemma of_digits_digits (b n : ℕ) : of_digits b (digits b n) = n :=
begin
  cases b with b,
  { cases n with n,
    { refl, },
    { change of_digits 0 [n+1] = n+1,
      dsimp [of_digits],
      simp, } },
  { cases b with b,
    { induction n with n ih,
      { refl, },
      { simp only [ih, add_comm 1, of_digits_one_cons, nat.cast_id, digits_one_succ], } },
    { apply nat.strong_induction_on n _, clear n,
      intros n h,
      cases n,
      { rw digits_zero, refl, },
      { simp only [nat.succ_eq_add_one, digits_add_two_add_one],
        dsimp [of_digits],
        rw h _ (nat.div_lt_self' n b),
        rw [nat.cast_id, nat.mod_add_div], }, }, },
end

lemma of_digits_one (L : list ℕ) : of_digits 1 L = L.sum :=
begin
  induction L with d L ih,
  { refl, },
  { simp [of_digits, list.sum_cons, ih], }
end

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `of_digits`.
-/

lemma digits_eq_nil_iff_eq_zero {b n : ℕ} : digits b n = [] ↔ n = 0 :=
begin
  split,
  { intro h,
    have : of_digits b (digits b n) = of_digits b [], by rw h,
    convert this,
    rw of_digits_digits },
  { rintro rfl,
    simp }
end

lemma digits_ne_nil_iff_ne_zero {b n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
not_congr digits_eq_nil_iff_eq_zero

private lemma digits_last_aux {b n : ℕ} (h : 2 ≤ b) (w : 0 < n) :
  digits b n = ((n % b) :: digits b (n / b)) :=
begin
  rcases b with _|_|b,
  { finish },
  { norm_num at h },
  rcases n with _|n,
  { norm_num at w },
  simp,
end

lemma digits_last {b m : ℕ} (h : 2 ≤ b) (hm : 0 < m) (p q) :
  (digits b m).last p = (digits b (m/b)).last q :=
by { simp only [digits_last_aux h hm], rw list.last_cons }

lemma digits.injective (b : ℕ) : function.injective b.digits :=
function.left_inverse.injective (of_digits_digits b)

@[simp] lemma digits_inj_iff {b n m : ℕ} :
  b.digits n = b.digits m ↔ n = m :=
(digits.injective b).eq_iff

lemma last_digit_ne_zero (b : ℕ) {m : ℕ} (hm : m ≠ 0) :
  (digits b m).last (digits_ne_nil_iff_ne_zero.mpr hm) ≠ 0 :=
begin
  rcases b with _|_|b,
  { cases m; finish },
  { cases m, { finish },
    simp_rw [digits_one, list.last_repeat_succ 1 m],
    norm_num },
  revert hm,
  apply nat.strong_induction_on m,
  intros n IH hn,
  have hnpos : 0 < n := nat.pos_of_ne_zero hn,
  by_cases hnb : n < b + 2,
  { simp_rw [digits_of_lt b.succ.succ n hnpos hnb],
    exact pos_iff_ne_zero.mp hnpos },
  { rw digits_last (show 2 ≤ b + 2, from dec_trivial) hnpos,
    refine IH _ (nat.div_lt_self hnpos dec_trivial) _,
    { rw ←pos_iff_ne_zero,
      exact nat.div_pos (le_of_not_lt hnb) dec_trivial } },
end

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
lemma digits_lt_base' {b m : ℕ} : ∀ {d}, d ∈ digits (b+2) m → d < b+2 :=
begin
  apply nat.strong_induction_on m,
  intros n IH d hd,
  cases n with n,
  { rw digits_zero at hd, cases hd }, -- base b+2 expansion of 0 has no digits
  rw digits_add_two_add_one at hd,
  cases hd,
  { rw hd, exact n.succ.mod_lt (by linarith) },
  { exact IH _ (nat.div_lt_self (nat.succ_pos _) (by linarith)) hd }
end

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
lemma digits_lt_base {b m d : ℕ} (hb : 2 ≤ b) (hd : d ∈ digits b m) : d < b :=
begin
  rcases b with _ | _ | b; try {linarith},
  exact digits_lt_base' hd,
end

/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
lemma of_digits_lt_base_pow_length' {b : ℕ} {l : list ℕ} (hl : ∀ x ∈ l, x < b+2) :
  of_digits (b+2) l < (b+2)^(l.length) :=
begin
  induction l with hd tl IH,
  { simp [of_digits], },
  { rw [of_digits, list.length_cons, pow_succ],
    have : (of_digits (b + 2) tl + 1) * (b+2) ≤ (b + 2) ^ tl.length * (b+2) :=
      mul_le_mul (IH (λ x hx, hl _ (list.mem_cons_of_mem _ hx)))
                 (by refl) dec_trivial (nat.zero_le _),
    suffices : ↑hd < b + 2,
    { linarith },
    norm_cast,
    exact hl hd (list.mem_cons_self _ _) }
end

/-- an n-digit number in base b is less than b^n if b ≥ 2 -/
lemma of_digits_lt_base_pow_length {b : ℕ} {l : list ℕ} (hb : 2 ≤ b) (hl : ∀ x ∈ l, x < b) :
  of_digits b l < b^l.length :=
begin
  rcases b with _ | _ | b; try { linarith },
  exact of_digits_lt_base_pow_length' hl,
end

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
lemma lt_base_pow_length_digits' {b m : ℕ} : m < (b + 2) ^ (digits (b + 2) m).length :=
begin
  convert of_digits_lt_base_pow_length' (λ _, digits_lt_base'),
  rw of_digits_digits (b+2) m,
end

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
lemma lt_base_pow_length_digits {b m : ℕ} (hb : 2 ≤ b) : m < b^(digits b m).length :=
begin
  rcases b with _ | _ | b; try { linarith },
  exact lt_base_pow_length_digits',
end

lemma of_digits_digits_append_digits {b m n : ℕ} :
  of_digits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m:=
by rw [of_digits_append, of_digits_digits, of_digits_digits]

lemma digits_len_le_digits_len_succ (b n : ℕ) : (digits b n).length ≤ (digits b (n + 1)).length :=
begin
  cases b,
  { -- base 0
    cases n; simp },
  { cases b,
    { -- base 1
      simp },
    { -- base >= 2
      apply nat.strong_induction_on n,
      clear n,
      intros n IH,
      cases n,
      { simp },
      { rw [digits_add_two_add_one, digits_add_two_add_one],
        by_cases hdvd : (b.succ.succ) ∣ (n.succ+1),
        { rw [nat.succ_div_of_dvd hdvd, list.length_cons, list.length_cons, nat.succ_le_succ_iff],
          apply IH,
          exact nat.div_lt_self (by linarith) (by linarith) },
        { rw nat.succ_div_of_not_dvd hdvd,
          refl } } } }
end

lemma le_digits_len_le (b n m : ℕ) (h : n ≤ m) : (digits b n).length ≤ (digits b m).length :=
monotone_of_monotone_nat (digits_len_le_digits_len_succ b) h

lemma pow_length_le_mul_of_digits {b : ℕ} {l : list ℕ} (hl : l ≠ []) (hl2 : l.last hl ≠ 0):
  (b + 2) ^ l.length ≤ (b + 2) * of_digits (b+2) l :=
begin
  rw [←list.init_append_last hl],
  simp only [list.length_append, list.length, zero_add, list.length_init, of_digits_append,
    list.length_init, of_digits_singleton, add_comm (l.length - 1), pow_add, pow_one],
  apply nat.mul_le_mul_left,
  refine le_trans _ (nat.le_add_left _ _),
  have : 0 < l.last hl, { rwa [pos_iff_ne_zero] },
  convert nat.mul_le_mul_left _ this, rw [mul_one]
end

/--
Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
lemma base_pow_length_digits_le' (b m : ℕ) (hm : m ≠ 0) :
  (b + 2) ^ ((digits (b + 2) m).length) ≤ (b + 2) * m :=
begin
  have : digits (b + 2) m ≠ [], from digits_ne_nil_iff_ne_zero.mpr hm,
  convert pow_length_le_mul_of_digits this (last_digit_ne_zero _ hm),
  rwa of_digits_digits,
end

/--
Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
lemma base_pow_length_digits_le (b m : ℕ) (hb : 2 ≤ b): m ≠ 0 → b ^ ((digits b m).length) ≤ b * m :=
begin
  rcases b with _ | _ | b; try { linarith },
  exact base_pow_length_digits_le' b m,
end

/-! ### Modular Arithmetic -/

-- This is really a theorem about polynomials.
lemma dvd_of_digits_sub_of_digits {α : Type*} [comm_ring α]
  {a b k : α} (h : k ∣ a - b) (L : list ℕ) :
  k ∣ of_digits a L - of_digits b L :=
begin
  induction L with d L ih,
  { change k ∣ 0 - 0, simp, },
  { simp only [of_digits, add_sub_add_left_eq_sub],
    exact dvd_mul_sub_mul h ih, }
end

lemma of_digits_modeq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : list ℕ) :
  of_digits b L ≡ of_digits b' L [MOD k] :=
begin
  induction L with d L ih,
  { refl, },
  { dsimp [of_digits],
    dsimp [nat.modeq] at *,
    conv_lhs { rw [nat.add_mod, nat.mul_mod, h, ih], },
    conv_rhs { rw [nat.add_mod, nat.mul_mod], }, }
end

lemma of_digits_modeq (b k : ℕ) (L : list ℕ) : of_digits b L ≡ of_digits (b % k) L [MOD k] :=
of_digits_modeq' b (b % k) k (nat.modeq.symm (nat.modeq.mod_modeq b k)) L

lemma of_digits_mod (b k : ℕ) (L : list ℕ) : of_digits b L % k = of_digits (b % k) L % k :=
of_digits_modeq b k L

lemma of_digits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : list ℕ) :
  of_digits b L ≡ of_digits b' L [ZMOD k] :=
begin
  induction L with d L ih,
  { refl, },
  { dsimp [of_digits],
    dsimp [int.modeq] at *,
    conv_lhs { rw [int.add_mod, int.mul_mod, h, ih], },
    conv_rhs { rw [int.add_mod, int.mul_mod], }, }
end

lemma of_digits_zmodeq (b : ℤ) (k : ℕ) (L : list ℕ) :
  of_digits b L ≡ of_digits (b % k) L [ZMOD k] :=
of_digits_zmodeq' b (b % k) k (int.modeq.symm (int.modeq.mod_modeq b ↑k)) L

lemma of_digits_zmod (b : ℤ) (k : ℕ) (L : list ℕ) :
  of_digits b L % k = of_digits (b % k) L % k :=
of_digits_zmodeq b k L

lemma modeq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
   n ≡ (digits b' n).sum [MOD b] :=
begin
  rw ←of_digits_one,
  conv { congr, skip, rw ←(of_digits_digits b' n) },
  convert of_digits_modeq _ _ _,
  exact h.symm,
end

lemma modeq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 3] :=
modeq_digits_sum 3 10 (by norm_num) n

lemma modeq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 9] :=
modeq_digits_sum 9 10 (by norm_num) n

lemma zmodeq_of_digits_digits (b b' : ℕ) (c : ℤ) (h : b' ≡ c [ZMOD b]) (n : ℕ) :
  n ≡ of_digits c (digits b' n) [ZMOD b] :=
begin
  conv { congr, skip, rw ←(of_digits_digits b' n) },
  rw coe_int_of_digits,
  apply of_digits_zmodeq' _ _ _ h,
end

lemma of_digits_neg_one : Π (L : list ℕ),
  of_digits (-1 : ℤ) L = (L.map (λ n : ℕ, (n : ℤ))).alternating_sum
| [] := rfl
| [n] := by simp [of_digits, list.alternating_sum]
| (a :: b :: t) :=
  begin
    simp only [of_digits, list.alternating_sum, list.map_cons, of_digits_neg_one t],
    push_cast,
    ring,
  end

lemma modeq_eleven_digits_sum (n : ℕ) :
  n ≡ ((digits 10 n).map (λ n : ℕ, (n : ℤ))).alternating_sum [ZMOD 11] :=
begin
  have t := zmodeq_of_digits_digits 11 10 (-1 : ℤ) (by unfold int.modeq; norm_num) n,
  rwa of_digits_neg_one at t
end

/-! ## Divisibility  -/

lemma dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
  b ∣ n ↔ b ∣ (digits b' n).sum :=
begin
  rw ←of_digits_one,
  conv_lhs { rw ←(of_digits_digits b' n) },
  rw [nat.dvd_iff_mod_eq_zero, nat.dvd_iff_mod_eq_zero, of_digits_mod, h],
end

/-- **Divisibility by 3 Rule** -/
lemma three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum :=
dvd_iff_dvd_digits_sum 3 10 (by norm_num) n

lemma nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum :=
dvd_iff_dvd_digits_sum 9 10 (by norm_num) n


lemma dvd_iff_dvd_of_digits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
  b ∣ n ↔ (b : ℤ) ∣ of_digits c (digits b' n) :=
begin
  rw ←int.coe_nat_dvd,
  exact dvd_iff_dvd_of_dvd_sub
    (int.modeq.modeq_iff_dvd.1
      (zmodeq_of_digits_digits b b' c (int.modeq.modeq_iff_dvd.2 h).symm _).symm),
end

lemma eleven_dvd_iff (n : ℕ) :
  11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n).map (λ n : ℕ, (n : ℤ))).alternating_sum :=
begin
  have t := dvd_iff_dvd_of_digits 11 10 (-1 : ℤ) (by norm_num) n,
  rw of_digits_neg_one at t,
  exact t,
end

/-! ### `norm_digits` tactic -/

namespace norm_digits

theorem digits_succ
  (b n m r l)
  (e : r + b * m = n)
  (hr : r < b)
  (h : nat.digits b m = l ∧ 2 ≤ b ∧ 0 < m) :
  nat.digits b n = r :: l ∧ 2 ≤ b ∧ 0 < n :=
begin
  rcases h with ⟨h, b2, m0⟩,
  have b0 : 0 < b := by linarith,
  have n0 : 0 < n := by linarith [mul_pos b0 m0],
  refine ⟨_, b2, n0⟩,
  obtain ⟨rfl, rfl⟩ := (nat.div_mod_unique b0).2 ⟨e, hr⟩,
  subst h, exact nat.digits_def' b2 n0,
end

theorem digits_one
  (b n) (n0 : 0 < n) (nb : n < b) :
  nat.digits b n = [n] ∧ 2 ≤ b ∧ 0 < n :=
begin
  have b2 : 2 ≤ b := by linarith,
  refine ⟨_, b2, n0⟩,
  rw [nat.digits_def' b2 n0, nat.mod_eq_of_lt nb,
    (nat.div_eq_zero_iff (by linarith : 0 < b)).2 nb, nat.digits_zero],
end

open tactic

/-- Helper function for the `norm_digits` tactic. -/
meta def eval_aux (eb : expr) (b : ℕ) :
  expr → ℕ → instance_cache → tactic (instance_cache × expr × expr)
| en n ic := do
  let m := n / b,
  let r := n % b,
  (ic, er) ← ic.of_nat r,
  (ic, pr) ← norm_num.prove_lt_nat ic er eb,
  if m = 0 then do
    (_, pn0) ← norm_num.prove_pos ic en,
    return (ic, `([%%en] : list nat), `(digits_one %%eb %%en %%pn0 %%pr))
  else do
    em ← expr.of_nat `(ℕ) m,
    (_, pe) ← norm_num.derive `(%%er + %%eb * %%em : ℕ),
    (ic, el, p) ← eval_aux em m ic,
    return (ic, `(@list.cons ℕ %%er %%el),
      `(digits_succ %%eb %%en %%em %%er %%el %%pe %%pr %%p))

/--
A tactic for normalizing expressions of the form `nat.digits a b = l` where
`a` and `b` are numerals.

```
example : nat.digits 10 123 = [3,2,1] := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr)
| `(nat.digits %%eb %%en) := do
  b ← expr.to_nat eb,
  n ← expr.to_nat en,
  if n = 0 then return (`([] : list ℕ), `(nat.digits_zero %%eb))
  else if b = 0 then do
    ic ← mk_instance_cache `(ℕ),
    (_, pn0) ← norm_num.prove_pos ic en,
    return (`([%%en] : list ℕ), `(@nat.digits_zero_succ' %%en %%pn0))
  else if b = 1 then do
    ic ← mk_instance_cache `(ℕ),
    (_, pn0) ← norm_num.prove_pos ic en,
    s ← simp_lemmas.add_simp simp_lemmas.mk `list.repeat,
    (rhs, p2, _) ← simplify s [] `(list.repeat 1 %%en),
    p ← mk_eq_trans `(nat.digits_one %%en) p2,
    return (rhs, p)
  else do
    ic ← mk_instance_cache `(ℕ),
    (_, l, p) ← eval_aux eb b en n ic,
    p ← mk_app ``and.left [p],
    return (l, p)
| _ := failed

end norm_digits

end nat
