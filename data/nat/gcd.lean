/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Definitions and properties of gcd, lcm, and coprime.
-/
import data.nat.basic data.int.basic

namespace nat

/- gcd -/

theorem gcd_dvd (m n : ℕ) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) :=
gcd.induction m n
  (λn, by rw gcd_zero_left; exact ⟨dvd_zero n, dvd_refl n⟩)
  (λm n npos, by rw ←gcd_rec; exact λ ⟨IH₁, IH₂⟩, ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩)

theorem gcd_dvd_left (m n : ℕ) : gcd m n ∣ m := (gcd_dvd m n).left

theorem gcd_dvd_right (m n : ℕ) : gcd m n ∣ n := (gcd_dvd m n).right

theorem dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n :=
gcd.induction m n (λn _ kn, by rw gcd_zero_left; exact kn)
  (λn m mpos IH H1 H2, by rw gcd_rec; exact IH ((dvd_mod_iff H1).2 H2) H1)

theorem gcd_comm (m n : ℕ) : gcd m n = gcd n m :=
dvd_antisymm
  (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
  (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))

theorem gcd_assoc (m n k : ℕ) : gcd (gcd m n) k = gcd m (gcd n k) :=
dvd_antisymm
  (dvd_gcd
    (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_left m n))
    (dvd_gcd (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
  (dvd_gcd
    (dvd_gcd (gcd_dvd_left m (gcd n k)) (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_left n k)))
    (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_right n k)))

@[simp] theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 :=
eq.trans (gcd_comm n 1) $ gcd_one_left n

theorem gcd_mul_left (m n k : ℕ) : gcd (m * n) (m * k) = m * gcd n k :=
gcd.induction n k
  (λk, by repeat {rw mul_zero <|> rw gcd_zero_left})
  (λk n H IH, by rwa [←mul_mod_mul_left, ←gcd_rec, ←gcd_rec] at IH)

theorem gcd_mul_right (m n k : ℕ) : gcd (m * n) (k * n) = gcd m k * n :=
by rw [mul_comm m n, mul_comm k n, mul_comm (gcd m k) n, gcd_mul_left]

theorem gcd_pos_of_pos_left {m : ℕ} (n : ℕ) (mpos : m > 0) : gcd m n > 0 :=
pos_of_dvd_of_pos (gcd_dvd_left m n) mpos

theorem gcd_pos_of_pos_right (m : ℕ) {n : ℕ} (npos : n > 0) : gcd m n > 0 :=
pos_of_dvd_of_pos (gcd_dvd_right m n) npos

theorem eq_zero_of_gcd_eq_zero_left {m n : ℕ} (H : gcd m n = 0) : m = 0 :=
or.elim (eq_zero_or_pos m) id
  (assume H1 : m > 0, absurd (eq.symm H) (ne_of_lt (gcd_pos_of_pos_left _ H1)))

theorem eq_zero_of_gcd_eq_zero_right {m n : ℕ} (H : gcd m n = 0) : n = 0 :=
by rw gcd_comm at H; exact eq_zero_of_gcd_eq_zero_left H

theorem gcd_div {m n k : ℕ} (H1 : k ∣ m) (H2 : k ∣ n) :
  gcd (m / k) (n / k) = gcd m n / k :=
or.elim (eq_zero_or_pos k)
  (λk0, by rw [k0, nat.div_zero, nat.div_zero, nat.div_zero, gcd_zero_right])
  (λH3, nat.eq_of_mul_eq_mul_right H3 $ by rw [
    nat.div_mul_cancel (dvd_gcd H1 H2), ←gcd_mul_right,
    nat.div_mul_cancel H1, nat.div_mul_cancel H2])

theorem gcd_dvd_gcd_of_dvd_left {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd m n ∣ gcd k n :=
dvd_gcd (dvd.trans (gcd_dvd_left m n) H) (gcd_dvd_right m n)

theorem gcd_dvd_gcd_of_dvd_right {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd n m ∣ gcd n k :=
dvd_gcd (gcd_dvd_left n m) (dvd.trans (gcd_dvd_right n m) H)

theorem gcd_dvd_gcd_mul_left (m n k : ℕ) : gcd m n ∣ gcd (k * m) n :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (m n k : ℕ) : gcd m n ∣ gcd (m * k) n :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (m n k : ℕ) : gcd m n ∣ gcd m (k * n) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : ℕ) : gcd m n ∣ gcd m (n * k) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)

theorem gcd_eq_left {m n : ℕ} (H : m ∣ n) : gcd m n = m :=
dvd_antisymm (gcd_dvd_left _ _) (dvd_gcd (dvd_refl _) H)

theorem gcd_eq_right {m n : ℕ} (H : n ∣ m) : gcd m n = n :=
by rw [gcd_comm, gcd_eq_left H]

/- extended euclidean algorithm -/

def xgcd_aux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
| 0          s t r' s' t' := (r', s', t')
| r@(succ _) s t r' s' t' :=
  have r' % r < r, from mod_lt _ $ succ_pos _,
  let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp] theorem xgcd_zero_left {s t r' s' t'} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
by simp [xgcd_aux]

@[simp] theorem xgcd_aux_rec {r s t r' s' t'} (h : 0 < r) : xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
by cases r; [exact absurd h (lt_irrefl _), {simp only [xgcd_aux], refl}]

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : ℕ) : ℤ × ℤ := (xgcd_aux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a (x y : ℕ) : ℤ := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b (x y : ℕ) : ℤ := (xgcd x y).2

@[simp] theorem xgcd_aux_fst (x y) : ∀ s t s' t',
  (xgcd_aux x s t y s' t').1 = gcd x y :=
gcd.induction x y (by simp) (λ x y h IH s t s' t', by simp [h, IH]; rw ← gcd_rec)

theorem xgcd_aux_val (x y) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1]; cases xgcd_aux x 1 0 y 0 1; refl

theorem xgcd_val (x y) : xgcd x y = (gcd_a x y, gcd_b x y) :=
by unfold gcd_a gcd_b; cases xgcd x y; refl

section
parameters (a b : ℕ)

private def P : ℕ × ℤ × ℤ → Prop | (r, s, t) := (r : ℤ) = a * s + b * t

theorem xgcd_aux_P {r r'} : ∀ {s t s' t'}, P (r, s, t) → P (r', s', t') → P (xgcd_aux r s t r' s' t') :=
gcd.induction r r' (by simp) $ λ x y h IH s t s' t' p p', begin
  rw [xgcd_aux_rec h], refine IH _ p, dsimp [P] at *,
  rw [int.mod_def], generalize : (y / x : ℤ) = k,
  rw [p, p'], simp [mul_add, mul_comm, mul_left_comm]
end

theorem gcd_eq_gcd_ab : (gcd a b : ℤ) = a * gcd_a a b + b * gcd_b a b :=
by have := @xgcd_aux_P a b a b 1 0 0 1 (by simp [P]) (by simp [P]);
   rwa [xgcd_aux_val, xgcd_val] at this
end

/- lcm -/

theorem lcm_comm (m n : ℕ) : lcm m n = lcm n m :=
by delta lcm; rw [mul_comm, gcd_comm]

theorem lcm_zero_left (m : ℕ) : lcm 0 m = 0 :=
by delta lcm; rw [zero_mul, nat.zero_div]

theorem lcm_zero_right (m : ℕ) : lcm m 0 = 0 := lcm_comm 0 m ▸ lcm_zero_left m

theorem lcm_one_left (m : ℕ) : lcm 1 m = m :=
by delta lcm; rw [one_mul, gcd_one_left, nat.div_one]

theorem lcm_one_right (m : ℕ) : lcm m 1 = m := lcm_comm 1 m ▸ lcm_one_left m

theorem lcm_self (m : ℕ) : lcm m m = m :=
or.elim (eq_zero_or_pos m)
  (λh, by rw [h, lcm_zero_left])
  (λh, by delta lcm; rw [gcd_self, nat.mul_div_cancel _ h])

theorem dvd_lcm_left (m n : ℕ) : m ∣ lcm m n :=
dvd.intro (n / gcd m n) (nat.mul_div_assoc _ $ gcd_dvd_right m n).symm

theorem dvd_lcm_right (m n : ℕ) : n ∣ lcm m n :=
lcm_comm n m ▸ dvd_lcm_left n m

theorem gcd_mul_lcm (m n : ℕ) : gcd m n * lcm m n = m * n :=
by delta lcm; rw [nat.mul_div_cancel' (dvd.trans (gcd_dvd_left m n) (dvd_mul_right m n))]

theorem lcm_dvd {m n k : ℕ} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k :=
or.elim (eq_zero_or_pos k)
  (λh, by rw h; exact dvd_zero _)
  (λkpos, dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos)) $
    by rw [gcd_mul_lcm, ←gcd_mul_right, mul_comm n k];
       exact dvd_gcd (mul_dvd_mul_left _ H2) (mul_dvd_mul_right H1 _))

theorem lcm_assoc (m n k : ℕ) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd_antisymm
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left m (lcm n k)) (dvd.trans (dvd_lcm_left n k) (dvd_lcm_right m (lcm n k))))
    (dvd.trans (dvd_lcm_right n k) (dvd_lcm_right m (lcm n k))))
  (lcm_dvd
    (dvd.trans (dvd_lcm_left m n) (dvd_lcm_left (lcm m n) k))
    (lcm_dvd (dvd.trans (dvd_lcm_right m n) (dvd_lcm_left (lcm m n) k)) (dvd_lcm_right (lcm m n) k)))

/- coprime -/

instance (m n : ℕ) : decidable (coprime m n) := by unfold coprime; apply_instance

theorem coprime.gcd_eq_one {m n : ℕ} : coprime m n → gcd m n = 1 := id

theorem coprime.symm {m n : ℕ} : coprime n m → coprime m n := (gcd_comm m n).trans

theorem coprime_of_dvd {m n : ℕ} (H : ∀ k > 1, k ∣ m → ¬ k ∣ n) : coprime m n :=
or.elim (eq_zero_or_pos (gcd m n))
  (λg0, by rw [eq_zero_of_gcd_eq_zero_left g0, eq_zero_of_gcd_eq_zero_right g0] at H; exact false.elim
    (H 2 dec_trivial (dvd_zero _) (dvd_zero _)))
  (λ(g1 : 1 ≤ _), eq.symm $ (lt_or_eq_of_le g1).resolve_left $ λg2,
    H _ g2 (gcd_dvd_left _ _) (gcd_dvd_right _ _))

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, k ∣ m → k ∣ n → k ∣ 1) : coprime m n :=
coprime_of_dvd $ λk kl km kn, not_le_of_gt kl $ le_of_dvd zero_lt_one (H k km kn)

theorem coprime.dvd_of_dvd_mul_right {m n k : ℕ} (H1 : coprime k n) (H2 : k ∣ m * n) : k ∣ m :=
let t := dvd_gcd (dvd_mul_left k m) H2 in
by rwa [gcd_mul_left, H1.gcd_eq_one, mul_one] at t

theorem coprime.dvd_of_dvd_mul_left {m n k : ℕ} (H1 : coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
by rw mul_comm at H2; exact H1.dvd_of_dvd_mul_right H2

theorem coprime.gcd_mul_left_cancel {k : ℕ} (m : ℕ) {n : ℕ} (H : coprime k n) :
   gcd (k * m) n = gcd m n :=
have H1 : coprime (gcd (k * m) n) k,
by rw [coprime, gcd_assoc, H.symm.gcd_eq_one, gcd_one_right],
dvd_antisymm
  (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
  (gcd_dvd_gcd_mul_left _ _ _)

theorem coprime.gcd_mul_right_cancel (m : ℕ) {k n : ℕ} (H : coprime k n) :
   gcd (m * k) n = gcd m n :=
by rw [mul_comm m k, H.gcd_mul_left_cancel m]

theorem coprime.gcd_mul_left_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (k * n) = gcd m n :=
by rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem coprime.gcd_mul_right_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (n * k) = gcd m n :=
by rw [mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd {m n : ℕ} (H : gcd m n > 0) :
  coprime (m / gcd m n) (n / gcd m n) :=
by delta coprime; rw [gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), nat.div_self H]

theorem not_coprime_of_dvd_of_dvd {m n d : ℕ} (dgt1 : d > 1) (Hm : d ∣ m) (Hn : d ∣ n) :
  ¬ coprime m n :=
λ (co : gcd m n = 1),
not_lt_of_ge (le_of_dvd zero_lt_one $ by rw ←co; exact dvd_gcd Hm Hn) dgt1

theorem exists_coprime {m n : ℕ} (H : gcd m n > 0) :
  ∃ m' n', coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
⟨_, _, coprime_div_gcd_div_gcd H,
  (nat.div_mul_cancel (gcd_dvd_left m n)).symm,
  (nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' {m n : ℕ} (H : gcd m n > 0) :
  ∃ g m' n', 0 < g ∧ coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
let ⟨m', n', h⟩ := exists_coprime H in ⟨_, m', n', H, h⟩

theorem coprime.mul {m n k : ℕ} (H1 : coprime m k) (H2 : coprime n k) : coprime (m * n) k :=
(H1.gcd_mul_left_cancel n).trans H2

theorem coprime.mul_right {k m n : ℕ} (H1 : coprime k m) (H2 : coprime k n) : coprime k (m * n) :=
(H1.symm.mul H2.symm).symm

theorem coprime.coprime_dvd_left {m k n : ℕ} (H1 : m ∣ k) (H2 : coprime k n) : coprime m n :=
eq_one_of_dvd_one (by delta coprime at H2; rw ← H2; exact gcd_dvd_gcd_of_dvd_left _ H1)

theorem coprime.coprime_dvd_right {m k n : ℕ} (H1 : n ∣ m) (H2 : coprime k m) : coprime k n :=
(H2.symm.coprime_dvd_left H1).symm

theorem coprime.coprime_mul_left {k m n : ℕ} (H : coprime (k * m) n) : coprime m n :=
H.coprime_dvd_left (dvd_mul_left _ _)

theorem coprime.coprime_mul_right {k m n : ℕ} (H : coprime (m * k) n) : coprime m n :=
H.coprime_dvd_left (dvd_mul_right _ _)

theorem coprime.coprime_mul_left_right {k m n : ℕ} (H : coprime m (k * n)) : coprime m n :=
H.coprime_dvd_right (dvd_mul_left _ _)

theorem coprime.coprime_mul_right_right {k m n : ℕ} (H : coprime m (n * k)) : coprime m n :=
H.coprime_dvd_right (dvd_mul_right _ _)

theorem coprime_one_left : ∀ n, coprime 1 n := gcd_one_left

theorem coprime_one_right : ∀ n, coprime n 1 := gcd_one_right

theorem coprime.pow_left {m k : ℕ} (n : ℕ) (H1 : coprime m k) : coprime (m ^ n) k :=
nat.rec_on n (coprime_one_left _) (λn IH, IH.mul H1)

theorem coprime.pow_right {m k : ℕ} (n : ℕ) (H1 : coprime k m) : coprime k (m ^ n) :=
(H1.symm.pow_left n).symm

theorem coprime.pow {k l : ℕ} (m n : ℕ) (H1 : coprime k l) : coprime (k ^ m) (l ^ n) :=
(H1.pow_left _).pow_right _

theorem coprime.eq_one_of_dvd {k m : ℕ} (H : coprime k m) (d : k ∣ m) : k = 1 :=
by rw [← H.gcd_eq_one, gcd_eq_left d]

theorem exists_eq_prod_and_dvd_and_dvd {m n k : ℕ} (H : k ∣ m * n) :
  ∃ m' n', k = m' * n' ∧ m' ∣ m ∧ n' ∣ n :=
or.elim (eq_zero_or_pos (gcd k m))
  (λg0, ⟨0, n,
    by rw [zero_mul, eq_zero_of_gcd_eq_zero_left g0],
    by rw [eq_zero_of_gcd_eq_zero_right g0]; apply dvd_zero, dvd_refl _⟩)
  (λgpos, let hd := (nat.mul_div_cancel' (gcd_dvd_left k m)).symm in
     ⟨_, _, hd, gcd_dvd_right _ _,
    dvd_of_mul_dvd_mul_left gpos $ by rw [←hd, ←gcd_mul_right]; exact
      dvd_gcd (dvd_mul_right _ _) H⟩)

theorem pow_dvd_pow_iff {a b n : ℕ} (n0 : 0 < n) : a ^ n ∣ b ^ n ↔ a ∣ b :=
begin
  refine ⟨λ h, _, λ h, pow_dvd_pow_of_dvd h _⟩,
  cases eq_zero_or_pos (gcd a b) with g0 g0,
  { simp [eq_zero_of_gcd_eq_zero_right g0] },
  rcases exists_coprime' g0 with ⟨g, a', b', g0', co, rfl, rfl⟩,
  rw [mul_pow, mul_pow] at h,
  replace h := dvd_of_mul_dvd_mul_right (pos_pow_of_pos _ g0') h,
  have := pow_dvd_pow a' n0,
  rw [pow_one, (co.pow n n).eq_one_of_dvd h] at this,
  simp [eq_one_of_dvd_one this]
end

end nat
