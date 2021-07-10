/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/

import data.nat.choose
import data.int.modeq
import algebra.iterate_hom
import group_theory.order_of_element
/-!
# Characteristic of semirings
-/

universes u v

variables (R : Type u)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R -/
class char_p [add_monoid R] [has_one R] (p : ℕ) : Prop :=
(cast_eq_zero_iff [] : ∀ x:ℕ, (x:R) = 0 ↔ p ∣ x)

theorem char_p.cast_eq_zero [add_monoid R] [has_one R] (p : ℕ) [char_p R p] :
  (p:R) = 0 :=
(char_p.cast_eq_zero_iff R p p).2 (dvd_refl p)

@[simp] lemma char_p.cast_card_eq_zero [add_group R] [has_one R] [fintype R] :
  (fintype.card R : R) = 0 :=
by rw [← nsmul_one, card_nsmul_eq_zero]

lemma char_p.int_cast_eq_zero_iff [add_group R] [has_one R] (p : ℕ) [char_p R p]
  (a : ℤ) :
  (a : R) = 0 ↔ (p:ℤ) ∣ a :=
begin
  rcases lt_trichotomy a 0 with h|rfl|h,
  { rw [← neg_eq_zero, ← int.cast_neg, ← dvd_neg],
    lift -a to ℕ using neg_nonneg.mpr (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] },
  { simp only [int.cast_zero, eq_self_iff_true, dvd_zero] },
  { lift a to ℕ using (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] }
end

lemma char_p.int_coe_eq_int_coe_iff [add_group R] [has_one R] (p : ℕ) [char_p R p] (a b : ℤ) :
  (a : R) = (b : R) ↔ a ≡ b [ZMOD p] :=
by rw [eq_comm, ←sub_eq_zero, ←int.cast_sub,
       char_p.int_cast_eq_zero_iff R p, int.modeq.modeq_iff_dvd]

theorem char_p.eq [add_monoid R] [has_one R] {p q : ℕ} (c1 : char_p R p) (c2 : char_p R q) :
  p = q :=
nat.dvd_antisymm
  ((char_p.cast_eq_zero_iff R p q).1 (char_p.cast_eq_zero _ _))
  ((char_p.cast_eq_zero_iff R q p).1 (char_p.cast_eq_zero _ _))

instance char_p.of_char_zero [add_monoid R] [has_one R] [char_zero R] : char_p R 0 :=
⟨λ x, by rw [zero_dvd_iff, ← nat.cast_zero, nat.cast_inj]⟩

theorem char_p.exists [non_assoc_semiring R] : ∃ p, char_p R p :=
by letI := classical.dec_eq R; exact
classical.by_cases
  (assume H : ∀ p:ℕ, (p:R) = 0 → p = 0, ⟨0,
    ⟨λ x, by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; refl⟩⟩⟩)
  (λ H, ⟨nat.find (not_forall.1 H), ⟨λ x,
    ⟨λ H1, nat.dvd_of_mod_eq_zero (by_contradiction $ λ H2,
      nat.find_min (not_forall.1 H)
        (nat.mod_lt x $ nat.pos_of_ne_zero $ not_of_not_imp $
          nat.find_spec (not_forall.1 H))
        (not_imp_of_and_not ⟨by rwa [← nat.mod_add_div x (nat.find (not_forall.1 H)),
          nat.cast_add, nat.cast_mul, of_not_not (not_not_of_not_imp $ nat.find_spec
            (not_forall.1 H)),
          zero_mul, add_zero] at H1, H2⟩)),
    λ H1, by rw [← nat.mul_div_cancel' H1, nat.cast_mul,
      of_not_not (not_not_of_not_imp $ nat.find_spec (not_forall.1 H)), zero_mul]⟩⟩⟩)

theorem char_p.exists_unique [non_assoc_semiring R] : ∃! p, char_p R p :=
let ⟨c, H⟩ := char_p.exists R in ⟨c, H, λ y H2, char_p.eq R H2 H⟩

theorem char_p.congr {R : Type u} [add_monoid R] [has_one R] {p : ℕ} (q : ℕ) [hq : char_p R q]
  (h : q = p) :
  char_p R p :=
h ▸ hq

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ring_char [non_assoc_semiring R] : ℕ :=
classical.some (char_p.exists_unique R)

namespace ring_char
variables [non_assoc_semiring R]

theorem spec : ∀ x:ℕ, (x:R) = 0 ↔ ring_char R ∣ x :=
by letI := (classical.some_spec (char_p.exists_unique R)).1;
unfold ring_char; exact char_p.cast_eq_zero_iff R (ring_char R)

theorem eq {p : ℕ} (C : char_p R p) : p = ring_char R :=
(classical.some_spec (char_p.exists_unique R)).2 p C

instance char_p : char_p R (ring_char R) :=
⟨spec R⟩

variables {R}

theorem of_eq {p : ℕ} (h : ring_char R = p) : char_p R p :=
char_p.congr (ring_char R) h

theorem eq_iff {p : ℕ} : ring_char R = p ↔ char_p R p :=
⟨of_eq, eq.symm ∘ eq R⟩

theorem dvd {x : ℕ} (hx : (x : R) = 0) : ring_char R ∣ x :=
(spec R x).1 hx

@[simp]
lemma eq_zero [char_zero R] : ring_char R = 0 := (eq R (char_p.of_char_zero R)).symm

end ring_char

theorem add_pow_char_of_commute [semiring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) (h : commute x y) :
  (x + y)^p = x^p + y^p :=
begin
  rw [commute.add_pow h, finset.sum_range_succ_comm, nat.sub_self, pow_zero, nat.choose_self],
  rw [nat.cast_one, mul_one, mul_one], congr' 1,
  convert finset.sum_eq_single 0 _ _,
  { simp only [mul_one, one_mul, nat.choose_zero_right, nat.sub_zero, nat.cast_one, pow_zero] },
  { intros b h1 h2,
    suffices : (p.choose b : R) = 0, { rw this, simp },
    rw char_p.cast_eq_zero_iff R p,
    refine nat.prime.dvd_choose_self (pos_iff_ne_zero.mpr h2) _ (fact.out _),
    rwa ← finset.mem_range },
  { intro h1,
    contrapose! h1,
    rw finset.mem_range,
    exact nat.prime.pos (fact.out _) }
end

theorem add_pow_char_pow_of_commute [semiring R] {p : ℕ} [fact p.prime]
  [char_p R p] {n : ℕ} (x y : R) (h : commute x y) :
  (x + y) ^ (p ^ n) = x ^ (p ^ n) + y ^ (p ^ n) :=
begin
  induction n, { simp, },
  rw [pow_succ', pow_mul, pow_mul, pow_mul, n_ih],
  apply add_pow_char_of_commute, apply commute.pow_pow h,
end

theorem sub_pow_char_of_commute [ring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) (h : commute x y) :
  (x - y)^p = x^p - y^p :=
begin
  rw [eq_sub_iff_add_eq, ← add_pow_char_of_commute _ _ _ (commute.sub_left h rfl)],
  simp, repeat {apply_instance},
end

theorem sub_pow_char_pow_of_commute [ring R] {p : ℕ} [fact p.prime]
  [char_p R p] {n : ℕ} (x y : R) (h : commute x y) :
  (x - y) ^ (p ^ n) = x ^ (p ^ n) - y ^ (p ^ n) :=
begin
  induction n, { simp, },
  rw [pow_succ', pow_mul, pow_mul, pow_mul, n_ih],
  apply sub_pow_char_of_commute, apply commute.pow_pow h,
end

theorem add_pow_char [comm_semiring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) : (x + y)^p = x^p + y^p :=
add_pow_char_of_commute _ _ _ (commute.all _ _)

theorem add_pow_char_pow [comm_semiring R] {p : ℕ} [fact p.prime]
  [char_p R p] {n : ℕ} (x y : R) :
  (x + y) ^ (p ^ n) = x ^ (p ^ n) + y ^ (p ^ n) :=
add_pow_char_pow_of_commute _ _ _ (commute.all _ _)

theorem sub_pow_char [comm_ring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) : (x - y)^p = x^p - y^p :=
sub_pow_char_of_commute _ _ _ (commute.all _ _)

theorem sub_pow_char_pow [comm_ring R] {p : ℕ} [fact p.prime]
  [char_p R p] {n : ℕ} (x y : R) :
  (x - y) ^ (p ^ n) = x ^ (p ^ n) - y ^ (p ^ n) :=
sub_pow_char_pow_of_commute _ _ _ (commute.all _ _)

lemma eq_iff_modeq_int [ring R] (p : ℕ) [char_p R p] (a b : ℤ) :
  (a : R) = b ↔ a ≡ b [ZMOD p] :=
by rw [eq_comm, ←sub_eq_zero, ←int.cast_sub,
       char_p.int_cast_eq_zero_iff R p, int.modeq.modeq_iff_dvd]

lemma char_p.neg_one_ne_one [ring R] (p : ℕ) [char_p R p] [fact (2 < p)] :
  (-1 : R) ≠ (1 : R) :=
begin
  suffices : (2 : R) ≠ 0,
  { symmetry, rw [ne.def, ← sub_eq_zero, sub_neg_eq_add], exact this },
  assume h,
  rw [show (2 : R) = (2 : ℕ), by norm_cast] at h,
  have := (char_p.cast_eq_zero_iff R p 2).mp h,
  have := nat.le_of_dvd dec_trivial this,
  rw fact_iff at *, linarith,
end

lemma ring_hom.char_p_iff_char_p {K L : Type*} [field K] [field L] (f : K →+* L) (p : ℕ) :
  char_p K p ↔ char_p L p :=
begin
  split;
  { introI _c, constructor, intro n,
    rw [← @char_p.cast_eq_zero_iff _ _ _ p _c n, ← f.injective.eq_iff, f.map_nat_cast, f.map_zero] }
end

section frobenius

section comm_semiring

variables [comm_semiring R] {S : Type v} [comm_semiring S] (f : R →* S) (g : R →+* S)
  (p : ℕ) [fact p.prime] [char_p R p]  [char_p S p] (x y : R)

/-- The frobenius map that sends x to x^p -/
def frobenius : R →+* R :=
{ to_fun := λ x, x^p,
  map_one' := one_pow p,
  map_mul' := λ x y, mul_pow x y p,
  map_zero' := zero_pow (lt_trans zero_lt_one (fact.out (nat.prime p)).one_lt),
  map_add' := add_pow_char R }

variable {R}

theorem frobenius_def : frobenius R p x = x ^ p := rfl

theorem iterate_frobenius (n : ℕ) : (frobenius R p)^[n] x = x ^ p ^ n :=
begin
  induction n, {simp},
  rw [function.iterate_succ', pow_succ', pow_mul, function.comp_apply, frobenius_def, n_ih]
end

theorem frobenius_mul : frobenius R p (x * y) = frobenius R p x * frobenius R p y :=
(frobenius R p).map_mul x y

theorem frobenius_one : frobenius R p 1 = 1 := one_pow _

theorem monoid_hom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) :=
f.map_pow x p

theorem ring_hom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) :=
g.map_pow x p

theorem monoid_hom.map_iterate_frobenius (n : ℕ) :
  f (frobenius R p^[n] x) = (frobenius S p^[n] (f x)) :=
function.semiconj.iterate_right (f.map_frobenius p) n x

theorem ring_hom.map_iterate_frobenius (n : ℕ) :
  g (frobenius R p^[n] x) = (frobenius S p^[n] (g x)) :=
g.to_monoid_hom.map_iterate_frobenius p x n

theorem monoid_hom.iterate_map_frobenius (f : R →* R) (p : ℕ) [fact p.prime] [char_p R p] (n : ℕ) :
  f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
f.iterate_map_pow _ _ _

theorem ring_hom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [fact p.prime] [char_p R p] (n : ℕ) :
  f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
f.iterate_map_pow _ _ _

variable (R)

theorem frobenius_zero : frobenius R p 0 = 0 := (frobenius R p).map_zero

theorem frobenius_add : frobenius R p (x + y) = frobenius R p x + frobenius R p y :=
(frobenius R p).map_add x y

theorem frobenius_nat_cast (n : ℕ) : frobenius R p n = n := (frobenius R p).map_nat_cast n

end comm_semiring

section comm_ring

variables [comm_ring R] {S : Type v} [comm_ring S] (f : R →* S) (g : R →+* S)
  (p : ℕ) [fact p.prime] [char_p R p]  [char_p S p] (x y : R)

theorem frobenius_neg : frobenius R p (-x) = -frobenius R p x := (frobenius R p).map_neg x

theorem frobenius_sub : frobenius R p (x - y) = frobenius R p x - frobenius R p y :=
(frobenius R p).map_sub x y

end comm_ring

end frobenius

theorem frobenius_inj [comm_ring R] [no_zero_divisors R]
  (p : ℕ) [fact p.prime] [char_p R p] :
  function.injective (frobenius R p) :=
λ x h H, by { rw ← sub_eq_zero at H ⊢, rw ← frobenius_sub at H, exact pow_eq_zero H }

namespace char_p

section
variables [ring R]

lemma char_p_to_char_zero [char_p R 0] : char_zero R :=
char_zero_of_inj_zero $
  λ n h0, eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

lemma cast_eq_mod (p : ℕ) [char_p R p] (k : ℕ) : (k : R) = (k % p : ℕ) :=
calc (k : R) = ↑(k % p + p * (k / p)) : by rw [nat.mod_add_div]
         ... = ↑(k % p)               : by simp[cast_eq_zero]

theorem char_ne_zero_of_fintype (p : ℕ) [hc : char_p R p] [fintype R] : p ≠ 0 :=
assume h : p = 0,
have char_zero R := @char_p_to_char_zero R _ (h ▸ hc),
absurd (@nat.cast_injective R _ _ this) (not_injective_infinite_fintype coe)

end

section semiring
open nat

variables [non_assoc_semiring R]

theorem char_ne_one [nontrivial R] (p : ℕ) [hc : char_p R p] : p ≠ 1 :=
assume hp : p = 1,
have ( 1 : R) = 0, by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p),
absurd this one_ne_zero

section no_zero_divisors

variable [no_zero_divisors R]

theorem char_is_prime_of_two_le (p : ℕ) [hc : char_p R p] (hp : 2 ≤ p) : nat.prime p :=
suffices ∀d ∣ p, d = 1 ∨ d = p, from ⟨hp, this⟩,
assume (d : ℕ) (hdvd : ∃ e, p = d * e),
let ⟨e, hmul⟩ := hdvd in
have (p : R) = 0, from (cast_eq_zero_iff R p p).mpr (dvd_refl p),
have (d : R) * e = 0, from (@cast_mul R _ d e) ▸ (hmul ▸ this),
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
  (assume hd : (d : R) = 0,
  have p ∣ d, from (cast_eq_zero_iff R p d).mp hd,
  show d = 1 ∨ d = p, from or.inr (dvd_antisymm ⟨e, hmul⟩ this))
  (assume he : (e : R) = 0,
  have p ∣ e, from (cast_eq_zero_iff R p e).mp he,
  have e ∣ p, from dvd_of_mul_left_eq d (eq.symm hmul),
  have e = p, from dvd_antisymm ‹e ∣ p› ‹p ∣ e›,
  have h₀ : p > 0, from gt_of_ge_of_gt hp (nat.zero_lt_succ 1),
  have d * p = 1 * p, by rw ‹e = p› at hmul; rw [one_mul]; exact eq.symm hmul,
  show d = 1 ∨ d = p, from or.inl (eq_of_mul_eq_mul_right h₀ this))

section nontrivial

variables [nontrivial R]

theorem char_is_prime_or_zero (p : ℕ) [hc : char_p R p] : nat.prime p ∨ p = 0 :=
match p, hc with
| 0,     _  := or.inr rfl
| 1,     hc := absurd (eq.refl (1 : ℕ)) (@char_ne_one R _ _ (1 : ℕ) hc)
| (m+2), hc := or.inl (@char_is_prime_of_two_le R _ _ (m+2) hc (nat.le_add_left 2 m))
end

lemma char_is_prime_of_pos (p : ℕ) [h : fact (0 < p)] [char_p R p] : fact p.prime :=
⟨(char_p.char_is_prime_or_zero R _).resolve_right (pos_iff_ne_zero.1 h.1)⟩

end nontrivial

end no_zero_divisors

end semiring

section ring

variables (R) [ring R] [no_zero_divisors R] [nontrivial R] [fintype R]

theorem char_is_prime (p : ℕ) [char_p R p] :
  p.prime :=
or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_fintype R p)

end ring

section char_one

variables {R} [non_assoc_semiring R]

@[priority 100]  -- see Note [lower instance priority]
instance [char_p R 1] : subsingleton R :=
subsingleton.intro $
suffices ∀ (r : R), r = 0,
  from assume a b, show a = b, by rw [this a, this b],
assume r,
calc r = 1 * r       : by rw one_mul
   ... = (1 : ℕ) * r : by rw nat.cast_one
   ... = 0 * r       : by rw char_p.cast_eq_zero
   ... = 0           : by rw zero_mul

lemma false_of_nontrivial_of_char_one [nontrivial R] [char_p R 1] : false :=
false_of_nontrivial_of_subsingleton R

lemma ring_char_ne_one [nontrivial R] : ring_char R ≠ 1 :=
by { intros h, apply @zero_ne_one R, symmetry, rw [←nat.cast_one, ring_char.spec, h], }

lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : char_p R v] :
  nontrivial R :=
⟨⟨(1 : ℕ), 0, λ h, hv $ by rwa [char_p.cast_eq_zero_iff _ v, nat.dvd_one] at h; assumption ⟩⟩

end char_one

end char_p

section

variables (R) [comm_ring R] [fintype R] (n : ℕ)

lemma char_p_of_ne_zero (hn : fintype.card R = n) (hR : ∀ i < n, (i : R) = 0 → i = 0) :
  char_p R n :=
{ cast_eq_zero_iff :=
  begin
    have H : (n : R) = 0, by { rw [← hn, char_p.cast_card_eq_zero] },
    intro k,
    split,
    { intro h,
      rw [← nat.mod_add_div k n, nat.cast_add, nat.cast_mul, H, zero_mul, add_zero] at h,
      rw nat.dvd_iff_mod_eq_zero,
      apply hR _ (nat.mod_lt _ _) h,
      rw [← hn, fintype.card_pos_iff],
      exact ⟨0⟩, },
    { rintro ⟨k, rfl⟩, rw [nat.cast_mul, H, zero_mul] }
  end }

lemma char_p_of_prime_pow_injective (p : ℕ) [hp : fact p.prime] (n : ℕ)
  (hn : fintype.card R = p ^ n) (hR : ∀ i ≤ n, (p ^ i : R) = 0 → i = n) :
  char_p R (p ^ n) :=
begin
  obtain ⟨c, hc⟩ := char_p.exists R, resetI,
  have hcpn : c ∣ p ^ n,
  { rw [← char_p.cast_eq_zero_iff R c, ← hn, char_p.cast_card_eq_zero], },
  obtain ⟨i, hi, hc⟩ : ∃ i ≤ n, c = p ^ i, by rwa nat.dvd_prime_pow hp.1 at hcpn,
  obtain rfl : i = n,
  { apply hR i hi, rw [← nat.cast_pow, ← hc, char_p.cast_eq_zero] },
  rwa ← hc
end

end
