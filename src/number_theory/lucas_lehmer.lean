/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Scott Morrison, Ainsley Pahljina
-/
import tactic.ring_exp
import tactic.interval_cases
import data.nat.parity
import data.zmod.basic
import ring_theory.fintype

/-!
# The Lucas-Lehmer test for Mersenne primes.

We define `lucas_lehmer_residue : Π p : ℕ, zmod (2^p - 1)`, and
prove `lucas_lehmer_residue p = 0 → prime (mersenne p)`.

We construct a tactic `lucas_lehmer.run_test`, which iteratively certifies the arithmetic
required to calculate the residue, and enables us to prove

```
example : prime (mersenne 127) :=
lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test)
```

## TODO

- Show reverse implication.
- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Scott Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
-/

/-- The Mersenne numbers, 2^p - 1. -/
def mersenne (p : ℕ) : ℕ := 2^p - 1

lemma mersenne_pos {p : ℕ} (h : 0 < p) : 0 < mersenne p :=
begin
  dsimp [mersenne],
  calc 0 < 2^1 - 1 : by norm_num
     ... ≤ 2^p - 1 : nat.pred_le_pred (nat.pow_le_pow_of_le_right (nat.succ_pos 1) h)
end

@[simp]
lemma succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k :=
begin
  rw [mersenne, nat.sub_add_cancel],
  exact one_le_pow_of_one_le (by norm_num) k
end

namespace lucas_lehmer

open nat

/-!
We now define three(!) different versions of the recurrence
`s (i+1) = (s i)^2 - 2`.

These versions take values either in `ℤ`, in `zmod (2^p - 1)`, or
in `ℤ` but applying `% (2^p - 1)` at each step.

They are each useful at different points in the proof,
so we take a moment setting up the lemmas relating them.
-/

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ℤ`. -/
def s : ℕ → ℤ
| 0 := 4
| (i+1) := (s i)^2 - 2

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `zmod (2^p - 1)`. -/
def s_zmod (p : ℕ) : ℕ → zmod (2^p - 1)
| 0 := 4
| (i+1) := (s_zmod i)^2 - 2

/-- The recurrence `s (i+1) = ((s i)^2 - 2) % (2^p - 1)` in `ℤ`. -/
def s_mod (p : ℕ) : ℕ → ℤ
| 0 := 4 % (2^p - 1)
| (i+1) := ((s_mod i)^2 - 2) % (2^p - 1)

lemma mersenne_int_ne_zero (p : ℕ) (w : 0 < p) : (2^p - 1 : ℤ) ≠ 0 :=
begin
  apply ne_of_gt, simp only [gt_iff_lt, sub_pos],
  exact_mod_cast nat.one_lt_two_pow p w,
end

lemma s_mod_nonneg (p : ℕ) (w : 0 < p) (i : ℕ) : 0 ≤ s_mod p i :=
begin
  cases i; dsimp [s_mod],
  { exact sup_eq_left.mp rfl },
  { apply int.mod_nonneg, exact mersenne_int_ne_zero p w },
end

lemma s_mod_mod (p i : ℕ) : s_mod p i % (2^p - 1) = s_mod p i :=
by cases i; simp [s_mod]

lemma s_mod_lt (p : ℕ) (w : 0 < p) (i : ℕ) : s_mod p i < 2^p - 1 :=
begin
  rw ←s_mod_mod,
  convert int.mod_lt _ _,
  { refine (abs_of_nonneg _).symm,
    simp only [sub_nonneg, ge_iff_le],
    exact_mod_cast nat.one_le_two_pow p, },
  { exact mersenne_int_ne_zero p w, },
end

lemma s_zmod_eq_s (p' : ℕ) (i : ℕ) : s_zmod (p'+2) i = (s i : zmod (2^(p'+2) - 1)):=
begin
  induction i with i ih,
  { dsimp [s, s_zmod], norm_num, },
  { push_cast [s, s_zmod, ih] },
end

-- These next two don't make good `norm_cast` lemmas.
lemma int.coe_nat_pow_pred (b p : ℕ) (w : 0 < b) : ((b^p - 1 : ℕ) : ℤ) = (b^p - 1 : ℤ) :=
begin
  have : 1 ≤ b^p := nat.one_le_pow p b w,
  push_cast [this],
end

lemma int.coe_nat_two_pow_pred (p : ℕ) : ((2^p - 1 : ℕ) : ℤ) = (2^p - 1 : ℤ) :=
int.coe_nat_pow_pred 2 p dec_trivial

lemma s_zmod_eq_s_mod (p : ℕ) (i : ℕ) : s_zmod p i = (s_mod p i : zmod (2^p - 1)) :=
by induction i; push_cast [←int.coe_nat_two_pow_pred p, s_mod, s_zmod, *]

/-- The Lucas-Lehmer residue is `s p (p-2)` in `zmod (2^p - 1)`. -/
def lucas_lehmer_residue (p : ℕ) : zmod (2^p - 1) := s_zmod p (p-2)

lemma residue_eq_zero_iff_s_mod_eq_zero (p : ℕ) (w : 1 < p) :
  lucas_lehmer_residue p = 0 ↔ s_mod p (p-2) = 0 :=
begin
  dsimp [lucas_lehmer_residue],
  rw s_zmod_eq_s_mod p,
  split,
  { -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h,
    simp [zmod.int_coe_zmod_eq_zero_iff_dvd] at h,
    apply int.eq_zero_of_dvd_of_nonneg_of_lt _ _ h; clear h,
    apply s_mod_nonneg _ (nat.lt_of_succ_lt w),
    convert s_mod_lt _ (nat.lt_of_succ_lt w) (p-2),
    push_cast [nat.one_le_two_pow p],
    refl, },
  { intro h, rw h, simp, },
end

/--
A Mersenne number `2^p-1` is prime if and only if
the Lucas-Lehmer residue `s p (p-2) % (2^p - 1)` is zero.
-/
@[derive decidable_pred]
def lucas_lehmer_test (p : ℕ) : Prop := lucas_lehmer_residue p = 0

/-- `q` is defined as the minimum factor of `mersenne p`, bundled as an `ℕ+`. -/
def q (p : ℕ) : ℕ+ := ⟨nat.min_fac (mersenne p), nat.min_fac_pos (mersenne p)⟩

instance fact_pnat_pos (q : ℕ+) : fact (0 < (q : ℕ)) :=
q.2

/-- We construct the ring `X q` as ℤ/qℤ + √3 ℤ/qℤ. -/
-- It would be nice to define this as (ℤ/qℤ)[x] / (x^2 - 3),
-- obtaining the ring structure for free,
-- but that seems to be more trouble than it's worth;
-- if it were easy to make the definition,
-- cardinality calculations would be somewhat more involved, too.
@[derive [add_comm_group, decidable_eq, fintype, inhabited]]
def X (q : ℕ+) : Type := (zmod q) × (zmod q)

namespace X
variable {q : ℕ+}

@[ext]
lemma ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
begin
  cases x, cases y,
  congr; assumption
end

@[simp] lemma add_fst (x y : X q) : (x + y).1 = x.1 + y.1 := rfl
@[simp] lemma add_snd (x y : X q) : (x + y).2 = x.2 + y.2 := rfl

@[simp] lemma neg_fst (x : X q) : (-x).1 = -x.1 := rfl
@[simp] lemma neg_snd (x : X q) : (-x).2 = -x.2 := rfl

instance : has_mul (X q) :=
{ mul := λ x y, (x.1*y.1 + 3*x.2*y.2, x.1*y.2 + x.2*y.1) }

@[simp] lemma mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 := rfl
@[simp] lemma mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 := rfl

instance : has_one (X q) :=
{ one := ⟨1,0⟩ }

@[simp] lemma one_fst : (1 : X q).1 = 1 := rfl
@[simp] lemma one_snd : (1 : X q).2 = 0 := rfl

@[simp] lemma bit0_fst (x : X q) : (bit0 x).1 = bit0 x.1 := rfl
@[simp] lemma bit0_snd (x : X q) : (bit0 x).2 = bit0 x.2 := rfl
@[simp] lemma bit1_fst (x : X q) : (bit1 x).1 = bit1 x.1 := rfl
@[simp] lemma bit1_snd (x : X q) : (bit1 x).2 = bit0 x.2 := by { dsimp [bit1], simp, }

instance : monoid (X q) :=
{ mul_assoc := λ x y z, by { ext; { dsimp, ring }, },
  one := ⟨1,0⟩,
  one_mul := λ x, by { ext; simp, },
  mul_one := λ x, by { ext; simp, },
  ..(infer_instance : has_mul (X q)) }

lemma left_distrib (x y z : X q) : x * (y + z) = x * y + x * z :=
by { ext; { dsimp, ring }, }

lemma right_distrib (x y z : X q) : (x + y) * z = x * z + y * z :=
by { ext; { dsimp, ring }, }

instance : ring (X q) :=
{ left_distrib := left_distrib,
  right_distrib := right_distrib,
  ..(infer_instance : add_comm_group (X q)),
  ..(infer_instance : monoid (X q)) }

instance : comm_ring (X q) :=
{ mul_comm := λ x y, by { ext; { dsimp, ring }, },
  ..(infer_instance : ring (X q))}

instance [fact (1 < (q : ℕ))] : nontrivial (X q) :=
⟨⟨0, 1, λ h, by { injection h with h1 _, exact zero_ne_one h1 } ⟩⟩

@[simp]
lemma nat_coe_fst (n : ℕ) : (n : X q).fst = (n : zmod q) :=
begin
  induction n,
  { refl, },
  { dsimp, simp only [add_left_inj], exact n_ih, }
end
@[simp]
lemma nat_coe_snd (n : ℕ) : (n : X q).snd = (0 : zmod q) :=
begin
  induction n,
  { refl, },
  { dsimp, simp only [add_zero], exact n_ih, }
end

@[simp]
lemma int_coe_fst (n : ℤ) : (n : X q).fst = (n : zmod q) :=
by { induction n; simp, }
@[simp]
lemma int_coe_snd (n : ℤ) : (n : X q).snd = (0 : zmod q) :=
by { induction n; simp, }

@[norm_cast]
lemma coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) :=
by { ext; simp; ring }

@[norm_cast]
lemma coe_nat (n : ℕ) : ((n : ℤ) : X q) = (n : X q) :=
by { ext; simp, }

/-- The cardinality of `X` is `q^2`. -/
lemma X_card : fintype.card (X q) = q^2 :=
begin
  dsimp [X],
  rw [fintype.card_prod, zmod.card q],
  ring,
end

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
lemma units_card (w : 1 < q) : fintype.card (units (X q)) < q^2 :=
begin
  haveI : fact (1 < (q : ℕ)) := w,
  convert card_units_lt (X q),
  rw X_card,
end

/-- We define `ω = 2 + √3`. -/
def ω : X q := (2, 1)
/-- We define `ωb = 2 - √3`, which is the inverse of `ω`. -/
def ωb : X q := (2, -1)

lemma ω_mul_ωb (q : ℕ+) : (ω : X q) * ωb = 1 :=
begin
  dsimp [ω, ωb],
  ext; simp; ring,
end

lemma ωb_mul_ω (q : ℕ+) : (ωb : X q) * ω = 1 :=
begin
  dsimp [ω, ωb],
  ext; simp; ring,
end

/-- A closed form for the recurrence relation. -/
lemma closed_form (i : ℕ) : (s i : X q) = (ω : X q)^(2^i) + (ωb : X q)^(2^i) :=
begin
  induction i with i ih,
  { dsimp [s, ω, ωb],
    ext; { simp; refl, }, },
  { calc (s (i + 1) : X q) = ((s i)^2 - 2 : ℤ) : rfl
    ... = ((s i : X q)^2 - 2) : by push_cast
    ... = (ω^(2^i) + ωb^(2^i))^2 - 2 : by rw ih
    ... = (ω^(2^i))^2 + (ωb^(2^i))^2 + 2*(ωb^(2^i)*ω^(2^i)) - 2 : by ring
    ... = (ω^(2^i))^2 + (ωb^(2^i))^2 :
            by rw [←mul_pow ωb ω, ωb_mul_ω, one_pow, mul_one, add_sub_cancel]
    ... = ω^(2^(i+1)) + ωb^(2^(i+1)) : by rw [←pow_mul, ←pow_mul, pow_succ'] }
end


end X

open X

/-!
Here and below, we introduce `p' = p - 2`, in order to avoid using subtraction in `ℕ`.
-/

/-- If `1 < p`, then `q p`, the smallest prime factor of `mersenne p`, is more than 2. -/
lemma two_lt_q (p' : ℕ) : 2 < q (p'+2) := begin
  by_contradiction H,
  simp at H,
  interval_cases q (p'+2); clear H,
  { -- If q = 1, we get a contradiction from 2^p = 2
    dsimp [q] at h, injection h with h', clear h,
    simp [mersenne] at h',
    exact lt_irrefl 2
    (calc 2 ≤ p'+2    : nat.le_add_left _ _
      ...  < 2^(p'+2) : nat.lt_two_pow _
      ...  = 2        : nat.pred_inj (nat.one_le_two_pow _) dec_trivial h'), },
  { -- If q = 2, we get a contradiction from 2 ∣ 2^p - 1
    dsimp [q] at h, injection h with h', clear h,
    rw [mersenne, pnat.one_coe, nat.min_fac_eq_two_iff, pow_succ] at h',
    exact nat.two_not_dvd_two_mul_sub_one (nat.one_le_two_pow _) h', }
end

theorem ω_pow_formula (p' : ℕ) (h : lucas_lehmer_residue (p'+2) = 0) :
  ∃ (k : ℤ), (ω : X (q (p'+2)))^(2^(p'+1)) =
    k * (mersenne (p'+2)) * ((ω : X (q (p'+2)))^(2^p')) - 1 :=
begin
  dsimp [lucas_lehmer_residue] at h,
  rw s_zmod_eq_s p' at h,
  simp [zmod.int_coe_zmod_eq_zero_iff_dvd] at h,
  cases h with k h,
  use k,
  replace h := congr_arg (λ (n : ℤ), (n : X (q (p'+2)))) h, -- coercion from ℤ to X q
  dsimp at h,
  rw closed_form at h,
  replace h := congr_arg (λ x, ω^2^p' * x) h,
  dsimp at h,
  have t : 2^p' + 2^p' = 2^(p'+1) := by ring_exp,
  rw [mul_add, ←pow_add ω, t, ←mul_pow ω ωb (2^p'), ω_mul_ωb, one_pow] at h,
  rw [mul_comm, coe_mul] at h,
  rw [mul_comm _ (k : X (q (p'+2)))] at h,
  replace h := eq_sub_of_add_eq h,
  exact_mod_cast h,
end

/-- `q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`. -/
theorem mersenne_coe_X (p : ℕ) : (mersenne p : X (q p)) = 0 :=
begin
  ext; simp [mersenne, q, zmod.nat_coe_zmod_eq_zero_iff_dvd, -pow_pos],
  apply nat.min_fac_dvd,
end

theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucas_lehmer_residue (p'+2) = 0) :
  (ω : X (q (p'+2)))^(2^(p'+1)) = -1 :=
begin
  cases ω_pow_formula p' h with k w,
  rw [mersenne_coe_X] at w,
  simpa using w,
end

theorem ω_pow_eq_one (p' : ℕ) (h : lucas_lehmer_residue (p'+2) = 0) :
  (ω : X (q (p'+2)))^(2^(p'+2)) = 1 :=
calc (ω : X (q (p'+2)))^2^(p'+2)
        = (ω^(2^(p'+1)))^2 : by rw [←pow_mul, ←pow_succ']
    ... = (-1)^2           : by rw ω_pow_eq_neg_one p' h
    ... = 1                : by simp

/-- `ω` as an element of the group of units. -/
def ω_unit (p : ℕ) : units (X (q p)) :=
{ val := ω,
  inv := ωb,
  val_inv := by simp [ω_mul_ωb],
  inv_val := by simp [ωb_mul_ω], }

@[simp] lemma ω_unit_coe (p : ℕ) : (ω_unit p : X (q p)) = ω := rfl

/-- The order of `ω` in the unit group is exactly `2^p`. -/
theorem order_ω (p' : ℕ) (h : lucas_lehmer_residue (p'+2) = 0) :
  order_of (ω_unit (p'+2)) = 2^(p'+2) :=
begin
  apply nat.eq_prime_pow_of_dvd_least_prime_pow, -- the order of ω divides 2^p
  { norm_num, },
  { intro o,
    have ω_pow := order_of_dvd_iff_pow_eq_one.1 o,
    replace ω_pow := congr_arg (units.coe_hom (X (q (p'+2))) : units (X (q (p'+2))) → X (q (p'+2))) ω_pow,
    simp at ω_pow,
    have h : (1 : zmod (q (p'+2))) = -1 :=
      congr_arg (prod.fst) ((ω_pow.symm).trans (ω_pow_eq_neg_one p' h)),
    haveI : fact (2 < (q (p'+2) : ℕ)) := two_lt_q _,
    apply zmod.neg_one_ne_one h.symm, },
  { apply order_of_dvd_iff_pow_eq_one.2,
    apply units.ext,
    push_cast,
    exact ω_pow_eq_one p' h, }
end

lemma order_ineq (p' : ℕ) (h : lucas_lehmer_residue (p'+2) = 0) : 2^(p'+2) < (q (p'+2) : ℕ)^2 :=
calc 2^(p'+2) = order_of (ω_unit (p'+2)) : (order_ω p' h).symm
     ... ≤ fintype.card (units (X _))    : order_of_le_card_univ
     ... < (q (p'+2) : ℕ)^2              : units_card (nat.lt_of_succ_lt (two_lt_q _))

end lucas_lehmer

export lucas_lehmer (lucas_lehmer_test lucas_lehmer_residue)

open lucas_lehmer

theorem lucas_lehmer_sufficiency (p : ℕ) (w : 1 < p) : lucas_lehmer_test p → (mersenne p).prime :=
begin
  let p' := p - 2,
  have z : p = p' + 2 := (nat.sub_eq_iff_eq_add w).mp rfl,
  have w : 1 < p' + 2 := (nat.lt_of_sub_eq_succ rfl),
  contrapose,
  intros a t,
  rw z at a,
  rw z at t,
  have h₁ := order_ineq p' t,
  have h₂ := nat.min_fac_sq_le_self (mersenne_pos (nat.lt_of_succ_lt w)) a,
  have h := lt_of_lt_of_le h₁ h₂,
  exact not_lt_of_ge (nat.sub_le _ _) h,
end

-- Here we calculate the residue, very inefficiently, using `dec_trivial`. We can do much better.
example : (mersenne 5).prime := lucas_lehmer_sufficiency 5 (by norm_num) dec_trivial

-- Next we use `norm_num` to calculate each `s p i`.
namespace lucas_lehmer
open tactic

meta instance nat_pexpr : has_to_pexpr ℕ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩
meta instance int_pexpr : has_to_pexpr ℤ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩

lemma s_mod_succ {p a i b c}
  (h1 : (2^p - 1 : ℤ) = a)
  (h2 : s_mod p i = b)
  (h3 : (b * b - 2) % a = c) :
  s_mod p (i+1) = c :=
by { dsimp [s_mod, mersenne], rw [h1, h2, pow_two, h3] }

/--
Given a goal of the form `lucas_lehmer_test p`,
attempt to do the calculation using `norm_num` to certify each step.
-/
meta def run_test : tactic unit :=
do `(lucas_lehmer_test %%p) ← target,
   `[dsimp [lucas_lehmer_test]],
   `[rw lucas_lehmer.residue_eq_zero_iff_s_mod_eq_zero, swap, norm_num],
   p ← eval_expr ℕ p,
   -- Calculate the candidate Mersenne prime
   let M : ℤ := 2^p - 1,
   t ← to_expr ``(2^%%p - 1 = %%M),
   v ← to_expr ``(by norm_num : 2^%%p - 1 = %%M),
   w ← assertv `w t v,
   -- Unfortunately this creates something like `w : 2^5 - 1 = int.of_nat 31`.
   -- We could make a better `has_to_pexpr ℤ` instance, or just:
   `[simp only [int.coe_nat_zero, int.coe_nat_succ,
       int.of_nat_eq_coe, zero_add, int.coe_nat_bit1] at w],
   -- base case
   t ← to_expr ``(s_mod %%p 0 = 4),
   v ← to_expr ``(by norm_num [lucas_lehmer.s_mod] : s_mod %%p 0 = 4),
   h ← assertv `h t v,
   -- step case, repeated p-2 times
   iterate_exactly (p-2) `[replace h := lucas_lehmer.s_mod_succ w h (by { norm_num, refl })],
   -- now close the goal
   h ← get_local `h,
   exact h

end lucas_lehmer

/-- We verify that the tactic works to prove `127.prime`. -/
example : (mersenne 7).prime := lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test).

/-!
This implementation works successfully to prove `(2^127 - 1).prime`,
and all the Mersenne primes up to this point appear in [archive/examples/mersenne_primes.lean].

`(2^127 - 1).prime` takes about 5 minutes to run (depending on your CPU!),
and unfortunately the next Mersenne prime `(2^521 - 1)`,
which was the first "computer era" prime,
is out of reach with the current implementation.

There's still low hanging fruit available to do faster computations
based on the formula
  n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]
and the fact that `% 2^p` and `/ 2^p` can be very efficient on the binary representation.
Someone should do this, too!
-/

lemma modeq_mersenne (n k : ℕ) : k ≡ ((k / 2^n) + (k % 2^n)) [MOD 2^n - 1] :=
-- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
begin
  conv in k {rw [← nat.mod_add_div k (2^n), add_comm]},
  refine nat.modeq.modeq_add _ (by refl),
  conv {congr, skip, skip, rw ← one_mul (k/2^n)},
  refine nat.modeq.modeq_mul _ (by refl),
  symmetry,
  rw [nat.modeq.modeq_iff_dvd, int.coe_nat_sub],
  exact pow_pos (show 0 < 2, from dec_trivial) _
end

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, I think it's the squaring operation in `s`.
