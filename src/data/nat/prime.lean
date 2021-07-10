/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

-/
import data.nat.sqrt
import data.nat.gcd
import data.list.sort
import algebra.group_power
import tactic.wlog
import tactic.norm_num

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

All the following declarations exist in the namespace `nat`.

- `prime`: the predicate that expresses that a natural number `p` is prime
- `primes`: the subtype of natural numbers that are prime
- `min_fac n`: the minimal prime factor of a natural number `n ≠ 1`
- `exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers
- `factors n`: the prime factorization of `n`
- `factors_unique`: uniqueness of the prime factorisation

-/

open bool subtype
open_locale nat

namespace nat

/-- `prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
@[pp_nodot]
def prime (p : ℕ) := 2 ≤ p ∧ ∀ m ∣ p, m = 1 ∨ m = p

theorem prime.two_le {p : ℕ} : prime p → 2 ≤ p := and.left

theorem prime.one_lt {p : ℕ} : prime p → 1 < p := prime.two_le

instance prime.one_lt' (p : ℕ) [hp : _root_.fact p.prime] : _root_.fact (1 < p) := ⟨hp.1.one_lt⟩

lemma prime.ne_one {p : ℕ} (hp : p.prime) : p ≠ 1 :=
ne.symm $ ne_of_lt hp.one_lt

theorem prime_def_lt {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 :=
and_congr_right $ λ p2, forall_congr $ λ m,
⟨λ h l d, (h d).resolve_right (ne_of_lt l),
 λ h d, (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left (λ l, h l d)⟩

theorem prime_def_lt' {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬ m ∣ p :=
prime_def_lt.trans $ and_congr_right $ λ p2, forall_congr $ λ m,
⟨λ h m2 l d, not_lt_of_ge m2 ((h l d).symm ▸ dec_trivial),
λ h l d, begin
  rcases m with _|_|m,
  { rw eq_zero_of_zero_dvd d at p2, revert p2, exact dec_trivial },
  { refl },
  { exact (h dec_trivial l).elim d }
end⟩

theorem prime_def_le_sqrt {p : ℕ} : prime p ↔ 2 ≤ p ∧
  ∀ m, 2 ≤ m → m ≤ sqrt p → ¬ m ∣ p :=
prime_def_lt'.trans $ and_congr_right $ λ p2,
⟨λ a m m2 l, a m m2 $ lt_of_le_of_lt l $ sqrt_lt_self p2,
 λ a, have ∀ {m k}, m ≤ k → 1 < m → p ≠ m * k, from
  λ m k mk m1 e, a m m1
    (le_sqrt.2 (e.symm ▸ mul_le_mul_left m mk)) ⟨k, e⟩,
  λ m m2 l ⟨k, e⟩, begin
    cases (le_total m k) with mk km,
    { exact this mk m2 e },
    { rw [mul_comm] at e,
      refine this km (lt_of_mul_lt_mul_right _ (zero_le m)) e,
      rwa [one_mul, ← e] }
  end⟩

section

/--
  This instance is slower than the instance `decidable_prime` defined below,
  but has the advantage that it works in the kernel for small values.

  If you need to prove that a particular number is prime, in any case
  you should not use `dec_trivial`, but rather `by norm_num`, which is
  much faster.
  -/
local attribute [instance]
def decidable_prime_1 (p : ℕ) : decidable (prime p) :=
decidable_of_iff' _ prime_def_lt'

lemma prime.ne_zero {n : ℕ} (h : prime n) : n ≠ 0 :=
by { rintro rfl, revert h, dec_trivial }

theorem prime.pos {p : ℕ} (pp : prime p) : 0 < p :=
lt_of_succ_lt pp.one_lt

theorem not_prime_zero : ¬ prime 0 := by simp [prime]

theorem not_prime_one : ¬ prime 1 := by simp [prime]

theorem prime_two : prime 2 := dec_trivial

end

theorem prime.pred_pos {p : ℕ} (pp : prime p) : 0 < pred p :=
lt_pred_iff.2 pp.one_lt

theorem succ_pred_prime {p : ℕ} (pp : prime p) : succ (pred p) = p :=
succ_pred_eq_of_pos pp.pos

theorem dvd_prime {p m : ℕ} (pp : prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
⟨λ d, pp.2 m d, λ h, h.elim (λ e, e.symm ▸ one_dvd _) (λ e, e.symm ▸ dvd_refl _)⟩

theorem dvd_prime_two_le {p m : ℕ} (pp : prime p) (H : 2 ≤ m) : m ∣ p ↔ m = p :=
(dvd_prime pp).trans $ or_iff_right_of_imp $ not.elim $ ne_of_gt H

theorem prime_dvd_prime_iff_eq {p q : ℕ} (pp : p.prime) (qp : q.prime) : p ∣ q ↔ p = q :=
dvd_prime_two_le qp (prime.two_le pp)

theorem prime.not_dvd_one {p : ℕ} (pp : prime p) : ¬ p ∣ 1
| d := (not_le_of_gt pp.one_lt) $ le_of_dvd dec_trivial d

theorem not_prime_mul {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b) : ¬ prime (a * b) :=
λ h, ne_of_lt (nat.mul_lt_mul_of_pos_left b1 (lt_of_succ_lt a1)) $
by simpa using (dvd_prime_two_le h a1).1 (dvd_mul_right _ _)

lemma not_prime_mul' {a b n : ℕ} (h : a * b = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬ prime n :=
by { rw ← h, exact not_prime_mul h₁ h₂ }

section min_fac
  private lemma min_fac_lemma (n k : ℕ) (h : ¬ n < k * k) :
    sqrt n - k < sqrt n + 2 - k :=
  (nat.sub_lt_sub_right_iff $ le_sqrt.2 $ le_of_not_gt h).2 $
  nat.lt_add_of_pos_right dec_trivial

  /-- If `n < k * k`, then `min_fac_aux n k = n`, if `k | n`, then `min_fac_aux n k = k`.
    Otherwise, `min_fac_aux n k = min_fac_aux n (k+2)` using well-founded recursion.
    If `n` is odd and `1 < n`, then then `min_fac_aux n 3` is the smallest prime factor of `n`. -/
  def min_fac_aux (n : ℕ) : ℕ → ℕ | k :=
  if h : n < k * k then n else
  if k ∣ n then k else
  have _, from min_fac_lemma n k h,
  min_fac_aux (k + 2)
  using_well_founded {rel_tac :=
    λ _ _, `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}

  /-- Returns the smallest prime factor of `n ≠ 1`. -/
  def min_fac : ℕ → ℕ
  | 0 := 2
  | 1 := 1
  | (n+2) := if 2 ∣ n then 2 else min_fac_aux (n + 2) 3

  @[simp] theorem min_fac_zero : min_fac 0 = 2 := rfl
  @[simp] theorem min_fac_one : min_fac 1 = 1 := rfl

  theorem min_fac_eq : ∀ n, min_fac n = if 2 ∣ n then 2 else min_fac_aux n 3
  | 0     := by simp
  | 1     := by simp [show 2≠1, from dec_trivial]; rw min_fac_aux; refl
  | (n+2) :=
    have 2 ∣ n + 2 ↔ 2 ∣ n, from
      (nat.dvd_add_iff_left (by refl)).symm,
    by simp [min_fac, this]; congr

  private def min_fac_prop (n k : ℕ) :=
    2 ≤ k ∧ k ∣ n ∧ ∀ m, 2 ≤ m → m ∣ n → k ≤ m

  theorem min_fac_aux_has_prop {n : ℕ} (n2 : 2 ≤ n) (nd2 : ¬ 2 ∣ n) :
    ∀ k i, k = 2*i+3 → (∀ m, 2 ≤ m → m ∣ n → k ≤ m) → min_fac_prop n (min_fac_aux n k)
  | k := λ i e a, begin
    rw min_fac_aux,
    by_cases h : n < k*k; simp [h],
    { have pp : prime n :=
        prime_def_le_sqrt.2 ⟨n2, λ m m2 l d,
          not_lt_of_ge l $ lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩,
      from ⟨n2, dvd_refl _, λ m m2 d, le_of_eq
        ((dvd_prime_two_le pp m2).1 d).symm⟩ },
    have k2 : 2 ≤ k, { subst e, exact dec_trivial },
    by_cases dk : k ∣ n; simp [dk],
    { exact ⟨k2, dk, a⟩ },
    { refine have _, from min_fac_lemma n k h,
        min_fac_aux_has_prop (k+2) (i+1)
          (by simp [e, left_distrib]) (λ m m2 d, _),
      cases nat.eq_or_lt_of_le (a m m2 d) with me ml,
      { subst me, contradiction },
      apply (nat.eq_or_lt_of_le ml).resolve_left, intro me,
      rw [← me, e] at d, change 2 * (i + 2) ∣ n at d,
      have := dvd_of_mul_right_dvd d, contradiction }
  end
  using_well_founded {rel_tac :=
    λ _ _, `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}

  theorem min_fac_has_prop {n : ℕ} (n1 : n ≠ 1) :
    min_fac_prop n (min_fac n) :=
  begin
    by_cases n0 : n = 0, {simp [n0, min_fac_prop, ge]},
    have n2 : 2 ≤ n, { revert n0 n1, rcases n with _|_|_; exact dec_trivial },
    simp [min_fac_eq],
    by_cases d2 : 2 ∣ n; simp [d2],
    { exact ⟨le_refl _, d2, λ k k2 d, k2⟩ },
    { refine min_fac_aux_has_prop n2 d2 3 0 rfl
        (λ m m2 d, (nat.eq_or_lt_of_le m2).resolve_left (mt _ d2)),
      exact λ e, e.symm ▸ d }
  end

  theorem min_fac_dvd (n : ℕ) : min_fac n ∣ n :=
  if n1 : n = 1 then by simp [n1] else (min_fac_has_prop n1).2.1

  theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : prime (min_fac n) :=
  let ⟨f2, fd, a⟩ := min_fac_has_prop n1 in
  prime_def_lt'.2 ⟨f2, λ m m2 l d, not_le_of_gt l (a m m2 (dvd_trans d fd))⟩

  theorem min_fac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → min_fac n ≤ m :=
  by by_cases n1 : n = 1;
    [exact λ m m2 d, n1.symm ▸ le_trans dec_trivial m2,
     exact (min_fac_has_prop n1).2.2]

  theorem min_fac_pos (n : ℕ) : 0 < min_fac n :=
  by by_cases n1 : n = 1;
     [exact n1.symm ▸ dec_trivial, exact (min_fac_prime n1).pos]

  theorem min_fac_le {n : ℕ} (H : 0 < n) : min_fac n ≤ n :=
  le_of_dvd H (min_fac_dvd n)

  theorem le_min_fac {m n : ℕ} : n = 1 ∨ m ≤ min_fac n ↔ ∀ p, prime p → p ∣ n → m ≤ p :=
  ⟨λ h p pp d, h.elim
    (by rintro rfl; cases pp.not_dvd_one d)
    (λ h, le_trans h $ min_fac_le_of_dvd pp.two_le d),
   λ H, or_iff_not_imp_left.2 $ λ n1, H _ (min_fac_prime n1) (min_fac_dvd _)⟩

  theorem le_min_fac' {m n : ℕ} : n = 1 ∨ m ≤ min_fac n ↔ ∀ p, 2 ≤ p → p ∣ n → m ≤ p :=
  ⟨λ h p (pp:1<p) d, h.elim
    (by rintro rfl; cases not_le_of_lt pp (le_of_dvd dec_trivial d))
    (λ h, le_trans h $ min_fac_le_of_dvd pp d),
   λ H, le_min_fac.2 (λ p pp d, H p pp.two_le d)⟩

  theorem prime_def_min_fac {p : ℕ} : prime p ↔ 2 ≤ p ∧ min_fac p = p :=
  ⟨λ pp, ⟨pp.two_le,
    let ⟨f2, fd, a⟩ := min_fac_has_prop $ ne_of_gt pp.one_lt in
    ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
   λ ⟨p2, e⟩, e ▸ min_fac_prime (ne_of_gt p2)⟩

  /--
  This instance is faster in the virtual machine than `decidable_prime_1`,
  but slower in the kernel.

  If you need to prove that a particular number is prime, in any case
  you should not use `dec_trivial`, but rather `by norm_num`, which is
  much faster.
  -/
  instance decidable_prime (p : ℕ) : decidable (prime p) :=
  decidable_of_iff' _ prime_def_min_fac

  theorem not_prime_iff_min_fac_lt {n : ℕ} (n2 : 2 ≤ n) : ¬ prime n ↔ min_fac n < n :=
  (not_congr $ prime_def_min_fac.trans $ and_iff_right n2).trans $
    (lt_iff_le_and_ne.trans $ and_iff_right $ min_fac_le $ le_of_succ_le n2).symm

  lemma min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬ prime n) : min_fac n ≤ n / min_fac n :=
  match min_fac_dvd n with
  | ⟨0, h0⟩     := absurd pos $ by rw [h0, mul_zero]; exact dec_trivial
  | ⟨1, h1⟩     :=
    begin
      rw mul_one at h1,
      rw [prime_def_min_fac, not_and_distrib, ← h1, eq_self_iff_true, not_true, or_false,
        not_le] at np,
      rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos), min_fac_one, nat.div_one]
    end
  | ⟨(x+2), hx⟩ :=
    begin
      conv_rhs { congr, rw hx },
      rw [nat.mul_div_cancel_left _ (min_fac_pos _)],
      exact min_fac_le_of_dvd dec_trivial ⟨min_fac n, by rwa mul_comm⟩
    end
  end

  /--
  The square of the smallest prime factor of a composite number `n` is at most `n`.
  -/
  lemma min_fac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬ prime n) : (min_fac n)^2 ≤ n :=
  have t : (min_fac n) ≤ (n/min_fac n) := min_fac_le_div w h,
  calc
  (min_fac n)^2 = (min_fac n) * (min_fac n)   : sq (min_fac n)
            ... ≤ (n/min_fac n) * (min_fac n) : mul_le_mul_right (min_fac n) t
            ... ≤ n                           : div_mul_le_self n (min_fac n)

  @[simp]
  lemma min_fac_eq_one_iff {n : ℕ} : min_fac n = 1 ↔ n = 1 :=
  begin
    split,
    { intro h,
      by_contradiction hn,
      have := min_fac_prime hn,
      rw h at this,
      exact not_prime_one this, },
    { rintro rfl, refl, }
  end

  @[simp]
  lemma min_fac_eq_two_iff (n : ℕ) : min_fac n = 2 ↔ 2 ∣ n :=
  begin
    split,
    { intro h,
      convert min_fac_dvd _,
      rw h, },
    { intro h,
      have ub := min_fac_le_of_dvd (le_refl 2) h,
      have lb := min_fac_pos n,
      -- If `interval_cases` and `norm_num` were already available here,
      -- this would be easy and pleasant.
      -- But they aren't, so it isn't.
      cases h : n.min_fac with m,
      { rw h at lb, cases lb, },
      { cases m with m,
        { simp at h, subst h, cases h with n h, cases n; cases h, },
        { cases m with m,
          { refl, },
          { rw h at ub,
            cases ub with _ ub, cases ub with _ ub, cases ub, } } } }
  end

end min_fac

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬ prime n) :
  ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
⟨min_fac n, min_fac_dvd _, ne_of_gt (min_fac_prime (ne_of_gt n2)).one_lt,
  ne_of_lt $ (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬ prime n) :
  ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
⟨min_fac n, min_fac_dvd _, (min_fac_prime (ne_of_gt n2)).two_le,
  (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_prime_and_dvd {n : ℕ} (n2 : 2 ≤ n) : ∃ p, prime p ∧ p ∣ n :=
⟨min_fac n, min_fac_prime (ne_of_gt n2), min_fac_dvd _⟩

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
let p := min_fac (n! + 1) in
have f1 : n! + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ factorial_pos _,
have pp : prime p, from min_fac_prime f1,
have np : n ≤ p, from le_of_not_ge $ λ h,
  have h₁ : p ∣ n!, from dvd_factorial (min_fac_pos _) h,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  pp.not_dvd_one h₂,
⟨p, np, pp⟩

lemma prime.eq_two_or_odd {p : ℕ} (hp : prime p) : p = 2 ∨ p % 2 = 1 :=
(nat.mod_two_eq_zero_or_one p).elim
  (λ h, or.inl ((hp.2 2 (dvd_of_mod_eq_zero h)).resolve_left dec_trivial).symm)
  or.inr

theorem coprime_of_dvd {m n : ℕ} (H : ∀ k, prime k → k ∣ m → ¬ k ∣ n) : coprime m n :=
begin
  cases eq_zero_or_pos (gcd m n) with g0 g1,
  { rw [eq_zero_of_gcd_eq_zero_left g0, eq_zero_of_gcd_eq_zero_right g0] at H,
    exfalso,
    exact H 2 prime_two (dvd_zero _) (dvd_zero _) },
  apply eq.symm,
  change 1 ≤ _ at g1,
  apply (lt_or_eq_of_le g1).resolve_left,
  intro g2,
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2,
  apply H p hp; apply dvd_trans hpdvd,
  { exact gcd_dvd_left _ _ },
  { exact gcd_dvd_right _ _ }
end

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, prime k → k ∣ m → k ∣ n → k ∣ 1) : coprime m n :=
coprime_of_dvd $ λk kp km kn, not_le_of_gt kp.one_lt $ le_of_dvd zero_lt_one $ H k kp km kn

theorem factors_lemma {k} : (k+2) / min_fac (k+2) < k+2 :=
div_lt_self dec_trivial (min_fac_prime dec_trivial).one_lt

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → list ℕ
| 0 := []
| 1 := []
| n@(k+2) :=
  let m := min_fac n in have n / m < n := factors_lemma,
  m :: factors (n / m)

@[simp] lemma factors_zero : factors 0 = [] := by rw factors
@[simp] lemma factors_one : factors 1 = [] := by rw factors

lemma prime_of_mem_factors : ∀ {n p}, p ∈ factors n → prime p
| 0       := by simp
| 1       := by simp
| n@(k+2) := λ p h,
  let m := min_fac n in have n / m < n := factors_lemma,
  have h₁ : p = m ∨ p ∈ (factors (n / m)) :=
    (list.mem_cons_iff _ _ _).1 (by rwa [factors] at h),
  or.cases_on h₁ (λ h₂, h₂.symm ▸ min_fac_prime dec_trivial)
    prime_of_mem_factors

lemma prod_factors : ∀ {n}, 0 < n → list.prod (factors n) = n
| 0       := by simp
| 1       := by simp
| n@(k+2) := λ h,
  let m := min_fac n in have n / m < n := factors_lemma,
  show (factors n).prod = n, from
  have h₁ : 0 < n / m :=
    nat.pos_of_ne_zero $ λ h,
    have n = 0 * m := (nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h,
    by rw zero_mul at this; exact (show k + 2 ≠ 0, from dec_trivial) this,
  by rw [factors, list.prod_cons, prod_factors h₁, nat.mul_div_cancel' (min_fac_dvd _)]

lemma factors_prime {p : ℕ} (hp : nat.prime p) : p.factors = [p] :=
begin
  have : p = (p - 2) + 2 := (nat.sub_eq_iff_eq_add hp.1).mp rfl,
  rw [this, nat.factors],
  simp only [eq.symm this],
  have : nat.min_fac p = p := (nat.prime_def_min_fac.mp hp).2,
  split,
  { exact this, },
  { simp only [this, nat.factors, nat.div_self (nat.prime.pos hp)], },
end

lemma factors_chain : ∀ {n a}, (∀ p, prime p → p ∣ n → a ≤ p) → list.chain (≤) a (factors n)
| 0       := λ a h, by simp
| 1       := λ a h, by simp
| n@(k+2) := λ a h,
  let m := min_fac n in have n / m < n := factors_lemma,
  begin
    rw factors,
    refine list.chain.cons ((le_min_fac.2 h).resolve_left dec_trivial) (factors_chain _),
    exact λ p pp d, min_fac_le_of_dvd pp.two_le (dvd_trans d $ div_dvd_of_dvd $ min_fac_dvd _),
  end

lemma factors_chain_2 (n) : list.chain (≤) 2 (factors n) := factors_chain $ λ p pp _, pp.two_le

lemma factors_chain' (n) : list.chain' (≤) (factors n) :=
@list.chain'.tail _ _ (_::_) (factors_chain_2 _)

lemma factors_sorted (n : ℕ) : list.sorted (≤) (factors n) :=
(list.chain'_iff_pairwise (@le_trans _ _)).1 (factors_chain' _)

/-- `factors` can be constructed inductively by extracting `min_fac`, for sufficiently large `n`. -/
lemma factors_add_two (n : ℕ) :
  factors (n+2) = min_fac (n+2) :: factors ((n+2) / min_fac (n+2)) :=
by rw factors

@[simp]
lemma factors_eq_nil (n : ℕ) : n.factors = [] ↔ n = 0 ∨ n = 1 :=
begin
  split; intro h,
  { rcases n with (_ | _ | n),
    { exact or.inl rfl },
    { exact or.inr rfl },
    { rw factors at h, injection h }, },
  { rcases h with (rfl | rfl),
    { exact factors_zero },
    { exact factors_one }, }
end

theorem prime.coprime_iff_not_dvd {p n : ℕ} (pp : prime p) : coprime p n ↔ ¬ p ∣ n :=
⟨λ co d, pp.not_dvd_one $ co.dvd_of_dvd_mul_left (by simp [d]),
 λ nd, coprime_of_dvd $ λ m m2 mp, ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

theorem prime.dvd_iff_not_coprime {p n : ℕ} (pp : prime p) : p ∣ n ↔ ¬ coprime p n :=
iff_not_comm.2 pp.coprime_iff_not_dvd

theorem prime.not_coprime_iff_dvd {m n : ℕ} :
  ¬ coprime m n ↔ ∃p, prime p ∧ p ∣ m ∧ p ∣ n :=
begin
  apply iff.intro,
  { intro h,
    exact ⟨min_fac (gcd m n), min_fac_prime h,
      (dvd.trans (min_fac_dvd (gcd m n)) (gcd_dvd_left m n)),
      (dvd.trans (min_fac_dvd (gcd m n)) (gcd_dvd_right m n))⟩ },
  { intro h,
    cases h with p hp,
    apply nat.not_coprime_of_dvd_of_dvd (prime.one_lt hp.1) hp.2.1 hp.2.2 }
end

theorem prime.dvd_mul {p m n : ℕ} (pp : prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
⟨λ H, or_iff_not_imp_left.2 $ λ h,
  (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
 or.rec (λ h, dvd_mul_of_dvd_left h _) (λ h, dvd_mul_of_dvd_right h _)⟩

theorem prime.not_dvd_mul {p m n : ℕ} (pp : prime p)
  (Hm : ¬ p ∣ m) (Hn : ¬ p ∣ n) : ¬ p ∣ m * n :=
mt pp.dvd_mul.1 $ by simp [Hm, Hn]

theorem prime.dvd_of_dvd_pow {p m n : ℕ} (pp : prime p) (h : p ∣ m^n) : p ∣ m :=
by induction n with n IH;
   [exact pp.not_dvd_one.elim h,
    by { rw pow_succ at h, exact (pp.dvd_mul.1 h).elim id IH } ]

lemma prime.pow_not_prime {x n : ℕ} (hn : 2 ≤ n) : ¬ (x ^ n).prime :=
λ hp, (hp.2 x $ dvd_trans ⟨x, sq _⟩ (pow_dvd_pow _ hn)).elim
  (λ hx1, hp.ne_one $ hx1.symm ▸ one_pow _)
  (λ hxn, lt_irrefl x $ calc x = x ^ 1 : (pow_one _).symm
     ... < x ^ n : nat.pow_right_strict_mono (hxn.symm ▸ hp.two_le) hn
     ... = x : hxn.symm)

lemma prime.mul_eq_prime_sq_iff {x y p : ℕ} (hp : p.prime) (hx : x ≠ 1) (hy : y ≠ 1) :
  x * y = p ^ 2 ↔ x = p ∧ y = p :=
⟨λ h, have pdvdxy : p ∣ x * y, by rw h; simp [sq],
begin
  wlog := hp.dvd_mul.1 pdvdxy using x y,
  cases case with a ha,
  have hap : a ∣ p, from ⟨y, by rwa [ha, sq,
        mul_assoc, nat.mul_right_inj hp.pos, eq_comm] at h⟩,
  exact ((nat.dvd_prime hp).1 hap).elim
    (λ _, by clear_aux_decl; simp [*, sq, nat.mul_right_inj hp.pos] at *
      {contextual := tt})
    (λ _, by clear_aux_decl; simp [*, sq, mul_comm, mul_assoc,
      nat.mul_right_inj hp.pos, nat.mul_right_eq_self_iff hp.pos] at *
      {contextual := tt})
end,
λ ⟨h₁, h₂⟩, h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩

lemma prime.dvd_factorial : ∀ {n p : ℕ} (hp : prime p), p ∣ n! ↔ p ≤ n
| 0 p hp := iff_of_false hp.not_dvd_one (not_le_of_lt hp.pos)
| (n+1) p hp := begin
  rw [factorial_succ, hp.dvd_mul, prime.dvd_factorial hp],
  exact ⟨λ h, h.elim (le_of_dvd (succ_pos _)) le_succ_of_le,
    λ h, (_root_.lt_or_eq_of_le h).elim (or.inr ∘ le_of_lt_succ)
      (λ h, or.inl $ by rw h)⟩
end

theorem prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : prime p) (h : ¬ p ∣ a) : coprime a (p^m) :=
(pp.coprime_iff_not_dvd.2 h).symm.pow_right _

theorem coprime_primes {p q : ℕ} (pp : prime p) (pq : prime q) : coprime p q ↔ p ≠ q :=
pp.coprime_iff_not_dvd.trans $ not_congr $ dvd_prime_two_le pq pp.two_le

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : prime p) (pq : prime q) (h : p ≠ q) :
  coprime (p^n) (q^m) :=
((coprime_primes pp pq).2 h).pow _ _

theorem coprime_or_dvd_of_prime {p} (pp : prime p) (i : ℕ) : coprime p i ∨ p ∣ i :=
by rw [pp.dvd_iff_not_coprime]; apply em

theorem dvd_prime_pow {p : ℕ} (pp : prime p) {m i : ℕ} : i ∣ (p^m) ↔ ∃ k ≤ m, i = p^k :=
begin
  induction m with m IH generalizing i, {simp [pow_succ, le_zero_iff] at *},
  by_cases p ∣ i,
  { cases h with a e, subst e,
    rw [pow_succ, nat.mul_dvd_mul_iff_left pp.pos, IH],
    split; intro h; rcases h with ⟨k, h, e⟩,
    { exact ⟨succ k, succ_le_succ h, by rw [e, pow_succ]; refl⟩ },
    cases k with k,
    { apply pp.not_dvd_one.elim,
      simp at e, rw ← e, apply dvd_mul_right },
    { refine ⟨k, le_of_succ_le_succ h, _⟩,
      rwa [mul_comm, pow_succ', nat.mul_left_inj pp.pos] at e } },
  { split; intro d,
    { rw (pp.coprime_pow_of_not_dvd h).eq_one_of_dvd d,
      exact ⟨0, zero_le _, rfl⟩ },
    { rcases d with ⟨k, l, e⟩,
      rw e, exact pow_dvd_pow _ l } }
end

/--
If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
lemma eq_prime_pow_of_dvd_least_prime_pow
  {a p k : ℕ} (pp : prime p) (h₁ : ¬(a ∣ p^k)) (h₂ : a ∣ p^(k+1)) :
  a = p^(k+1) :=
begin
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂,
  congr,
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (prime.one_lt pp))).1 h₁)),
end

section
open list

lemma mem_list_primes_of_dvd_prod {p : ℕ} (hp : prime p) :
  ∀ {l : list ℕ}, (∀ p ∈ l, prime p) → p ∣ prod l → p ∈ l
| []       := λ h₁ h₂, absurd h₂ (prime.not_dvd_one hp)
| (q :: l) := λ h₁ h₂,
  have h₃ : p ∣ q * prod l := @prod_cons _ _ l q ▸ h₂,
  have hq : prime q := h₁ q (mem_cons_self _ _),
  or.cases_on ((prime.dvd_mul hp).1 h₃)
    (λ h, by rw [prime.dvd_iff_not_coprime hp, coprime_primes hp hq, ne.def, not_not] at h;
      exact h ▸ mem_cons_self _ _)
    (λ h, have hl : ∀ p ∈ l, prime p := λ p hlp, h₁ p ((mem_cons_iff _ _ _).2 (or.inr hlp)),
    (mem_cons_iff _ _ _).2 (or.inr (mem_list_primes_of_dvd_prod hl h)))

lemma mem_factors_iff_dvd {n p : ℕ} (hn : 0 < n) (hp : prime p) : p ∈ factors n ↔ p ∣ n :=
⟨λ h, prod_factors hn ▸ list.dvd_prod h,
 λ h, mem_list_primes_of_dvd_prod hp (@prime_of_mem_factors n) ((prod_factors hn).symm ▸ h)⟩

lemma mem_factors {n p} (hn : 0 < n) : p ∈ factors n ↔ prime p ∧ p ∣ n :=
⟨λ h, ⟨prime_of_mem_factors h, (mem_factors_iff_dvd hn $ prime_of_mem_factors h).mp h⟩,
 λ ⟨hprime, hdvd⟩, (mem_factors_iff_dvd hn hprime).mpr hdvd⟩

lemma perm_of_prod_eq_prod : ∀ {l₁ l₂ : list ℕ}, prod l₁ = prod l₂ →
  (∀ p ∈ l₁, prime p) → (∀ p ∈ l₂, prime p) → l₁ ~ l₂
| []        []        _  _  _  := perm.nil
| []        (a :: l)  h₁ h₂ h₃ :=
  have ha : a ∣ 1 := @prod_nil ℕ _ ▸ h₁.symm ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _,
  absurd ha (prime.not_dvd_one (h₃ a (mem_cons_self _ _)))
| (a :: l)  []        h₁ h₂ h₃ :=
  have ha : a ∣ 1 := @prod_nil ℕ _ ▸ h₁ ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _,
  absurd ha (prime.not_dvd_one (h₂ a (mem_cons_self _ _)))
| (a :: l₁) (b :: l₂) h hl₁ hl₂ :=
  have hl₁' : ∀ p ∈ l₁, prime p := λ p hp, hl₁ p (mem_cons_of_mem _ hp),
  have hl₂' : ∀ p ∈ (b :: l₂).erase a, prime p := λ p hp, hl₂ p (mem_of_mem_erase hp),
  have ha : a ∈ (b :: l₂) := mem_list_primes_of_dvd_prod (hl₁ a (mem_cons_self _ _)) hl₂
    (h ▸ by rw prod_cons; exact dvd_mul_right _ _),
  have hb : b :: l₂ ~ a :: (b :: l₂).erase a := perm_cons_erase ha,
  have hl : prod l₁ = prod ((b :: l₂).erase a) :=
  (nat.mul_right_inj (prime.pos (hl₁ a (mem_cons_self _ _)))).1 $
    by rwa [← prod_cons, ← prod_cons, ← hb.prod_eq],
  perm.trans ((perm_of_prod_eq_prod hl hl₁' hl₂').cons _) hb.symm

/-- **Fundamental theorem of arithmetic**-/
lemma factors_unique {n : ℕ} {l : list ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, prime p) :
  l ~ factors n :=
have hn : 0 < n := nat.pos_of_ne_zero $ λ h, begin
  rw h at *, clear h,
  induction l with a l hi,
  { exact absurd h₁ dec_trivial },
  { rw prod_cons at h₁,
    exact nat.mul_ne_zero (ne_of_lt (prime.pos (h₂ a (mem_cons_self _ _)))).symm
      (hi (λ p hp, h₂ p (mem_cons_of_mem _ hp))) h₁ }
end,
perm_of_prod_eq_prod (by rwa prod_factors hn) h₂ (@prime_of_mem_factors _)

end

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : prime p) {m n k l : ℕ}
      (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k+l+1) ∣ m*n) :
      p ^ (k+1) ∣ m ∨ p ^ (l+1) ∣ n :=
have hpd : p^(k+l)*p ∣ m*n, by rwa pow_succ' at hpmn,
have hpd2 : p ∣ (m*n) / p ^ (k+l), from dvd_div_of_mul_dvd hpd,
have hpd3 : p ∣ (m*n) / (p^k * p^l), by simpa [pow_add] using hpd2,
have hpd4 : p ∣ (m / p^k) * (n / p^l), by simpa [nat.div_mul_div hpm hpn] using hpd3,
have hpd5 : p ∣ (m / p^k) ∨ p ∣ (n / p^l), from (prime.dvd_mul p_prime).1 hpd4,
suffices p^k*p ∣ m ∨ p^l*p ∣ n, by rwa [pow_succ', pow_succ'],
  hpd5.elim
    (assume : p ∣ m / p ^ k, or.inl $ mul_dvd_of_dvd_div hpm this)
    (assume : p ∣ n / p ^ l, or.inr $ mul_dvd_of_dvd_div hpn this)

/-- The type of prime numbers -/
def primes := {p : ℕ // p.prime}

namespace primes

instance : has_repr nat.primes := ⟨λ p, repr p.val⟩
instance inhabited_primes : inhabited primes := ⟨⟨2, prime_two⟩⟩

instance coe_nat : has_coe nat.primes ℕ := ⟨subtype.val⟩

theorem coe_nat_inj (p q : nat.primes) : (p : ℕ) = (q : ℕ) → p = q :=
λ h, subtype.eq h

end primes

instance monoid.prime_pow {α : Type*} [monoid α] : has_pow α primes := ⟨λ x p, x^p.val⟩

end nat

/-! ### Primality prover -/

namespace tactic
namespace norm_num
open norm_num

lemma is_prime_helper (n : ℕ)
  (h₁ : 1 < n) (h₂ : nat.min_fac n = n) : nat.prime n :=
nat.prime_def_min_fac.2 ⟨h₁, h₂⟩

lemma min_fac_bit0 (n : ℕ) : nat.min_fac (bit0 n) = 2 :=
by simp [nat.min_fac_eq, show 2 ∣ bit0 n, by simp [bit0_eq_two_mul n]]

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def min_fac_helper (n k : ℕ) : Prop :=
0 < k ∧ bit1 k ≤ nat.min_fac (bit1 n)

theorem min_fac_helper.n_pos {n k : ℕ} (h : min_fac_helper n k) : 0 < n :=
pos_iff_ne_zero.2 $ λ e,
by rw e at h; exact not_le_of_lt (nat.bit1_lt h.1) h.2

lemma min_fac_ne_bit0 {n k : ℕ} : nat.min_fac (bit1 n) ≠ bit0 k :=
by rw bit0_eq_two_mul; exact λ e, absurd
  ((nat.dvd_add_iff_right (by simp [bit0_eq_two_mul n])).2
    (dvd_trans ⟨_, e⟩ (nat.min_fac_dvd _)))
  (by norm_num)

lemma min_fac_helper_0 (n : ℕ) (h : 0 < n) : min_fac_helper n 1 :=
begin
  refine ⟨zero_lt_one, lt_of_le_of_ne _ min_fac_ne_bit0.symm⟩,
  refine @lt_of_le_of_ne ℕ _ _ _ (nat.min_fac_pos _) _,
  intro e,
  have := nat.min_fac_prime _,
  { rw ← e at this, exact nat.not_prime_one this },
  { exact ne_of_gt (nat.bit1_lt h) }
end

lemma min_fac_helper_1 {n k k' : ℕ} (e : k + 1 = k')
  (np : nat.min_fac (bit1 n) ≠ bit1 k)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  rw ← e,
  refine ⟨nat.succ_pos _,
    (lt_of_le_of_ne (lt_of_le_of_ne _ _ : k+1+k < _)
      min_fac_ne_bit0.symm : bit0 (k+1) < _)⟩,
  { rw add_right_comm, exact h.2 },
  { rw add_right_comm, exact np.symm }
end

lemma min_fac_helper_2 (n k k' : ℕ) (e : k + 1 = k')
  (np : ¬ nat.prime (bit1 k)) (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  intro e₁, rw ← e₁ at np,
  exact np (nat.min_fac_prime $ ne_of_gt $ nat.bit1_lt h.n_pos)
end

lemma min_fac_helper_3 (n k k' c : ℕ) (e : k + 1 = k')
  (nc : bit1 n % bit1 k = c) (c0 : 0 < c)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  refine mt _ (ne_of_gt c0), intro e₁,
  rw [← nc, ← nat.dvd_iff_mod_eq_zero, ← e₁],
  apply nat.min_fac_dvd
end

lemma min_fac_helper_4 (n k : ℕ) (hd : bit1 n % bit1 k = 0)
  (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 k :=
by rw ← nat.dvd_iff_mod_eq_zero at hd; exact
le_antisymm (nat.min_fac_le_of_dvd (nat.bit1_lt h.1) hd) h.2

lemma min_fac_helper_5 (n k k' : ℕ) (e : bit1 k * bit1 k = k')
  (hd : bit1 n < k') (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 n :=
begin
  refine (nat.prime_def_min_fac.1 (nat.prime_def_le_sqrt.2
    ⟨nat.bit1_lt h.n_pos, _⟩)).2,
  rw ← e at hd,
  intros m m2 hm md,
  have := le_trans h.2 (le_trans (nat.min_fac_le_of_dvd m2 md) hm),
  rw nat.le_sqrt at this,
  exact not_le_of_lt hd this
end

/-- Given `e` a natural numeral and `d : nat` a factor of it, return `⊢ ¬ prime e`. -/
meta def prove_non_prime (e : expr) (n d₁ : ℕ) : tactic expr :=
do let e₁ := reflect d₁,
  c ← mk_instance_cache `(nat),
  (c, p₁) ← prove_lt_nat c `(1) e₁,
  let d₂ := n / d₁, let e₂ := reflect d₂,
  (c, e', p) ← prove_mul_nat c e₁ e₂,
  guard (e' =ₐ e),
  (c, p₂) ← prove_lt_nat c `(1) e₂,
  return $ `(@nat.not_prime_mul').mk_app [e₁, e₂, e, p, p₁, p₂]

/-- Given `a`,`a1 := bit1 a`, `n1` the value of `a1`, `b` and `p : min_fac_helper a b`,
  returns `(c, ⊢ min_fac a1 = c)`. -/
meta def prove_min_fac_aux (a a1 : expr) (n1 : ℕ) :
  instance_cache → expr → expr → tactic (instance_cache × expr × expr)
| ic b p := do
  k ← b.to_nat,
  let k1 := bit1 k,
  let b1 := `(bit1:ℕ→ℕ).mk_app [b],
  if n1 < k1*k1 then do
    (ic, e', p₁) ← prove_mul_nat ic b1 b1,
    (ic, p₂) ← prove_lt_nat ic a1 e',
    return (ic, a1, `(min_fac_helper_5).mk_app [a, b, e', p₁, p₂, p])
  else let d := k1.min_fac in
  if to_bool (d < k1) then do
    let k' := k+1, let e' := reflect k',
    (ic, p₁) ← prove_succ ic b e',
    p₂ ← prove_non_prime b1 k1 d,
    prove_min_fac_aux ic e' $ `(min_fac_helper_2).mk_app [a, b, e', p₁, p₂, p]
  else do
    let nc := n1 % k1,
    (ic, c, pc) ← prove_div_mod ic a1 b1 tt,
    if nc = 0 then
      return (ic, b1, `(min_fac_helper_4).mk_app [a, b, pc, p])
    else do
      (ic, p₀) ← prove_pos ic c,
      let k' := k+1, let e' := reflect k',
      (ic, p₁) ← prove_succ ic b e',
      prove_min_fac_aux ic e' $ `(min_fac_helper_3).mk_app [a, b, e', c, p₁, pc, p₀, p]

/-- Given `a` a natural numeral, returns `(b, ⊢ min_fac a = b)`. -/
meta def prove_min_fac (ic : instance_cache) (e : expr) : tactic (instance_cache × expr × expr) :=
match match_numeral e with
| match_numeral_result.zero := return (ic, `(2:ℕ), `(nat.min_fac_zero))
| match_numeral_result.one := return (ic, `(1:ℕ), `(nat.min_fac_one))
| match_numeral_result.bit0 e := return (ic, `(2), `(min_fac_bit0).mk_app [e])
| match_numeral_result.bit1 e := do
  n ← e.to_nat,
  c ← mk_instance_cache `(nat),
  (c, p) ← prove_pos c e,
  let a1 := `(bit1:ℕ→ℕ).mk_app [e],
  prove_min_fac_aux e a1 (bit1 n) c `(1) (`(min_fac_helper_0).mk_app [e, p])
| _ := failed
end

/-- A partial proof of `factors`. Asserts that `l` is a sorted list of primes, lower bounded by a
prime `p`, which multiplies to `n`. -/
def factors_helper (n p : ℕ) (l : list ℕ) : Prop :=
p.prime → list.chain (≤) p l ∧ (∀ a ∈ l, nat.prime a) ∧ list.prod l = n

lemma factors_helper_nil (a : ℕ) : factors_helper 1 a [] :=
λ pa, ⟨list.chain.nil, by rintro _ ⟨⟩, list.prod_nil⟩

lemma factors_helper_cons' (n m a b : ℕ) (l : list ℕ)
  (h₁ : b * m = n) (h₂ : a ≤ b) (h₃ : nat.min_fac b = b)
  (H : factors_helper m b l) : factors_helper n a (b :: l) :=
λ pa,
  have pb : b.prime, from nat.prime_def_min_fac.2 ⟨le_trans pa.two_le h₂, h₃⟩,
  let ⟨f₁, f₂, f₃⟩ := H pb in
  ⟨list.chain.cons h₂ f₁, λ c h, h.elim (λ e, e.symm ▸ pb) (f₂ _),
   by rw [list.prod_cons, f₃, h₁]⟩

lemma factors_helper_cons (n m a b : ℕ) (l : list ℕ)
  (h₁ : b * m = n) (h₂ : a < b) (h₃ : nat.min_fac b = b)
  (H : factors_helper m b l) : factors_helper n a (b :: l) :=
factors_helper_cons' _ _ _ _ _ h₁ h₂.le h₃ H

lemma factors_helper_sn (n a : ℕ) (h₁ : a < n) (h₂ : nat.min_fac n = n) : factors_helper n a [n] :=
factors_helper_cons _ _ _ _ _ (mul_one _) h₁ h₂ (factors_helper_nil _)

lemma factors_helper_same (n m a : ℕ) (l : list ℕ) (h : a * m = n)
  (H : factors_helper m a l) : factors_helper n a (a :: l) :=
λ pa, factors_helper_cons' _ _ _ _ _ h (le_refl _) (nat.prime_def_min_fac.1 pa).2 H pa

lemma factors_helper_same_sn (a : ℕ) : factors_helper a a [a] :=
factors_helper_same _ _ _ _ (mul_one _) (factors_helper_nil _)

lemma factors_helper_end (n : ℕ) (l : list ℕ) (H : factors_helper n 2 l) : nat.factors n = l :=
let ⟨h₁, h₂, h₃⟩ := H nat.prime_two in
have _, from (list.chain'_iff_pairwise (@le_trans _ _)).1 (@list.chain'.tail _ _ (_::_) h₁),
(list.eq_of_perm_of_sorted (nat.factors_unique h₃ h₂) this (nat.factors_sorted _)).symm

/-- Given `n` and `a` natural numerals, returns `(l, ⊢ factors_helper n a l)`. -/
meta def prove_factors_aux :
  instance_cache → expr → expr → ℕ → ℕ → tactic (instance_cache × expr × expr)
| c en ea n a :=
  let b := n.min_fac in
  if b < n then do
    let m := n / b,
    (c, em) ← c.of_nat m,
    if b = a then do
      (c, _, p₁) ← prove_mul_nat c ea em,
      (c, l, p₂) ← prove_factors_aux c em ea m a,
      pure (c, `(%%ea::%%l:list ℕ), `(factors_helper_same).mk_app [en, em, ea, l, p₁, p₂])
    else do
      (c, eb) ← c.of_nat b,
      (c, _, p₁) ← prove_mul_nat c eb em,
      (c, p₂) ← prove_lt_nat c ea eb,
      (c, _, p₃) ← prove_min_fac c eb,
      (c, l, p₄) ← prove_factors_aux c em eb m b,
      pure (c, `(%%eb::%%l : list ℕ),
        `(factors_helper_cons).mk_app [en, em, ea, eb, l, p₁, p₂, p₃, p₄])
  else if b = a then
    pure (c, `([%%ea] : list ℕ), `(factors_helper_same_sn).mk_app [ea])
  else do
    (c, p₁) ← prove_lt_nat c ea en,
    (c, _, p₂) ← prove_min_fac c en,
    pure (c, `([%%en] : list ℕ), `(factors_helper_sn).mk_app [en, ea, p₁, p₂])

/-- Evaluates the `prime` and `min_fac` functions. -/
@[norm_num] meta def eval_prime : expr → tactic (expr × expr)
| `(nat.prime %%e) := do
  n ← e.to_nat,
  match n with
  | 0 := false_intro `(nat.not_prime_zero)
  | 1 := false_intro `(nat.not_prime_one)
  | _ := let d₁ := n.min_fac in
    if d₁ < n then prove_non_prime e n d₁ >>= false_intro
    else do
      let e₁ := reflect d₁,
      c ← mk_instance_cache `(ℕ),
      (c, p₁) ← prove_lt_nat c `(1) e₁,
      (c, e₁, p) ← prove_min_fac c e,
      true_intro $ `(is_prime_helper).mk_app [e, p₁, p]
  end
| `(nat.min_fac %%e) := do
  ic ← mk_instance_cache `(ℕ),
  prod.snd <$> prove_min_fac ic e
| `(nat.factors %%e) := do
  n ← e.to_nat,
  match n with
  | 0 := pure (`(@list.nil ℕ), `(nat.factors_zero))
  | 1 := pure (`(@list.nil ℕ), `(nat.factors_one))
  | _ := do
    c ← mk_instance_cache `(ℕ),
    (c, l, p) ← prove_factors_aux c e `(2) n 2,
    pure (l, `(factors_helper_end).mk_app [e, l, p])
  end
| _ := failed

end norm_num
end tactic

namespace nat

theorem prime_three : prime 3 := by norm_num

end nat
