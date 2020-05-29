/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Neil Strickland
-/
import data.nat.prime

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def pnat := {n : ℕ // 0 < n}
notation `ℕ+` := pnat

instance coe_pnat_nat : has_coe ℕ+ ℕ := ⟨subtype.val⟩
instance : has_repr ℕ+ := ⟨λ n, repr n.1⟩

namespace nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def to_pnat (n : ℕ) (h : 0 < n . tactic.exact_dec_trivial) : ℕ+ := ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succ_pnat (n : ℕ) : ℕ+ := ⟨succ n, succ_pos n⟩

@[simp] theorem succ_pnat_coe (n : ℕ) : (succ_pnat n : ℕ) = succ n := rfl

theorem succ_pnat_inj {n m : ℕ} : succ_pnat n = succ_pnat m → n = m :=
λ h, by { let h' := congr_arg (coe : ℕ+ → ℕ) h, exact nat.succ_inj h' }

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def to_pnat' (n : ℕ) : ℕ+ := succ_pnat (pred n)

@[simp] theorem to_pnat'_coe : ∀ (n : ℕ),
 ((to_pnat' n) : ℕ) = ite (0 < n) n 1
| 0 := rfl
| (m + 1) := by {rw [if_pos (succ_pos m)], refl}

namespace primes
instance coe_pnat : has_coe nat.primes ℕ+ := ⟨λ p, ⟨(p : ℕ), p.property.pos⟩⟩
theorem coe_pnat_nat (p : nat.primes) : ((p : ℕ+) : ℕ) = p := rfl

theorem coe_pnat_inj (p q : nat.primes) : (p : ℕ+) = (q : ℕ+) → p = q := λ h,
begin
  replace h : ((p : ℕ+) : ℕ) = ((q : ℕ+) : ℕ) := congr_arg subtype.val h,
  rw [coe_pnat_nat, coe_pnat_nat] at h,
  exact subtype.eq h,
end

end primes
end nat

namespace pnat

open nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/

instance : decidable_eq ℕ+ := λ (a b : ℕ+), by apply_instance

instance : decidable_linear_order ℕ+ :=
subtype.decidable_linear_order _

@[simp] lemma mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
  (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k := iff.rfl

@[simp] lemma mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
  (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k := iff.rfl

@[simp, norm_cast] lemma coe_le_coe (n k : ℕ+) : (n:ℕ) ≤ k ↔ n ≤ k := iff.rfl

@[simp, norm_cast] lemma coe_lt_coe (n k : ℕ+) : (n:ℕ) < k ↔ n < k := iff.rfl

@[simp] theorem pos (n : ℕ+) : 0 < (n : ℕ) := n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n := subtype.eq

@[simp] theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n := rfl

instance : add_comm_semigroup ℕ+ :=
{ add       := λ a b, ⟨(a  + b : ℕ), add_pos a.pos b.pos⟩,
  add_comm  := λ a b, subtype.eq (add_comm a b),
  add_assoc := λ a b c, subtype.eq (add_assoc a b c) }

@[simp] theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n := rfl
instance coe_add_hom : is_add_hom (coe : ℕ+ → ℕ) := ⟨add_coe⟩

instance : add_left_cancel_semigroup ℕ+ :=
{ add_left_cancel := λ a b c h, by {
    replace h := congr_arg (coe : ℕ+ → ℕ) h,
    rw [add_coe, add_coe] at h,
    exact eq ((add_right_inj (a : ℕ)).mp h)},
  .. (pnat.add_comm_semigroup) }

instance : add_right_cancel_semigroup ℕ+ :=
{ add_right_cancel := λ a b c h, by {
    replace h := congr_arg (coe : ℕ+ → ℕ) h,
    rw [add_coe, add_coe] at h,
    exact eq ((add_left_inj (b : ℕ)).mp h)},
  .. (pnat.add_comm_semigroup) }

@[simp] theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 := ne_of_gt n.2

theorem to_pnat'_coe {n : ℕ} : 0 < n → (n.to_pnat' : ℕ) = n := succ_pred_eq_of_pos

@[simp] theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).to_pnat' = n := eq (to_pnat'_coe n.pos)

instance : comm_monoid ℕ+ :=
{ mul       := λ m n, ⟨m.1 * n.1, mul_pos m.2 n.2⟩,
  mul_assoc := λ a b c, subtype.eq (mul_assoc _ _ _),
  one       := succ_pnat 0,
  one_mul   := λ a, subtype.eq (one_mul _),
  mul_comm  := λ a b, subtype.eq (mul_comm _ _) }

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b :=
λ a b, nat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b :=
λ a b, nat.add_one_le_iff

@[simp] lemma one_le (n : ℕ+) : (1 : ℕ+) ≤ n := n.2

instance : order_bot ℕ+ :=
{ bot := 1,
  bot_le := λ a, a.property,
  ..(by apply_instance : partial_order ℕ+) }

@[simp] lemma bot_eq_zero : (⊥ : ℕ+) = 1 := rfl

instance : inhabited ℕ+ := ⟨1⟩

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp] lemma mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) := rfl
@[simp] lemma mk_bit0 (n) {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, pos_of_bit0_pos h⟩ : ℕ+) := rfl
@[simp] lemma mk_bit1 (n) {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) := rfl

-- Some lemmas that rewrite inequalities between explicit numerals in `pnat`
-- into the corresponding inequalities in `nat`.
-- TODO: perhaps this should not be attempted by `simp`,
-- and instead we should expect `norm_num` to take care of these directly?
-- TODO: these lemmas are perhaps incomplete:
-- * 1 is not represented as a bit0 or bit1
-- * strict inequalities?
@[simp] lemma bit0_le_bit0 (n m : ℕ+) : (bit0 n) ≤ (bit0 m) ↔ (bit0 (n : ℕ)) ≤ (bit0 (m : ℕ)) := iff.refl _
@[simp] lemma bit0_le_bit1 (n m : ℕ+) : (bit0 n) ≤ (bit1 m) ↔ (bit0 (n : ℕ)) ≤ (bit1 (m : ℕ)) := iff.refl _
@[simp] lemma bit1_le_bit0 (n m : ℕ+) : (bit1 n) ≤ (bit0 m) ↔ (bit1 (n : ℕ)) ≤ (bit0 (m : ℕ)) := iff.refl _
@[simp] lemma bit1_le_bit1 (n m : ℕ+) : (bit1 n) ≤ (bit1 m) ↔ (bit1 (n : ℕ)) ≤ (bit1 (m : ℕ)) := iff.refl _

@[simp] theorem one_coe : ((1 : ℕ+) : ℕ) = 1 := rfl
@[simp] theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n := rfl
instance coe_mul_hom : is_monoid_hom (coe : ℕ+ → ℕ) :=
 {map_one := one_coe, map_mul := mul_coe}

@[simp] lemma coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) := rfl
@[simp] lemma coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) := rfl

@[simp] theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
by induction n with n ih;
 [refl, rw [nat.pow_succ, _root_.pow_succ, mul_coe, mul_comm, ih]]

instance : left_cancel_semigroup ℕ+ :=
{ mul_left_cancel := λ a b c h, by {
   replace h := congr_arg (coe : ℕ+ → ℕ) h,
   exact eq ((nat.mul_right_inj a.pos).mp h)},
  .. (pnat.comm_monoid) }

instance : right_cancel_semigroup ℕ+ :=
{ mul_right_cancel := λ a b c h, by {
   replace h := congr_arg (coe : ℕ+ → ℕ) h,
   exact eq ((nat.mul_left_inj b.pos).mp h)},
  .. (pnat.comm_monoid) }

instance : distrib ℕ+ :=
{ left_distrib  := λ a b c, eq (mul_add a b c),
  right_distrib := λ a b c, eq (add_mul a b c),
  ..(pnat.add_comm_semigroup), ..(pnat.comm_monoid) }

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : has_sub ℕ+ := ⟨λ a b, to_pnat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 :=
begin
  change ((to_pnat' ((a : ℕ) - (b :  ℕ)) : ℕ)) =
    ite ((a : ℕ) > (b : ℕ)) ((a : ℕ) - (b : ℕ)) 1,
  split_ifs with h,
  { exact to_pnat'_coe (nat.sub_pos_of_lt h) },
  { rw [nat.sub_eq_zero_iff_le.mpr (le_of_not_gt h)], refl }
end

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b :=
 λ h, eq $ by { rw [add_coe, sub_coe, if_pos h],
                exact nat.add_sub_of_le (le_of_lt h) }

/-- We define m % k and m / k in the same way as for nat
  except that when m = n * k we take m % k = k and
  m / k = n - 1.  This ensures that m % k is always positive
  and m = (m % k) + k * (m / k) in all cases.  Later we
  define a function div_exact which gives the usual m / k
  in the case where k divides m.
-/

def mod_div_aux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
| k 0 q := ⟨k, q.pred⟩
| k (r + 1) q := ⟨⟨r + 1, nat.succ_pos r⟩, q⟩

lemma mod_div_aux_spec : ∀ (k : ℕ+) (r q : ℕ) (h : ¬ (r = 0 ∧ q = 0)),
 (((mod_div_aux k r q).1 : ℕ) + k * (mod_div_aux k r q).2 = (r + k * q))
| k 0 0 h := (h ⟨rfl, rfl⟩).elim
| k 0 (q + 1) h := by {
  change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1),
  rw [nat.pred_succ, nat.mul_succ, zero_add, add_comm]}
| k (r + 1) q h := rfl

def mod_div (m k : ℕ+) : ℕ+ × ℕ := mod_div_aux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

def mod (m k : ℕ+) : ℕ+ := (mod_div m k).1
def div (m k : ℕ+) : ℕ  := (mod_div m k).2

theorem mod_add_div (m k : ℕ+) : (m : ℕ) = (mod m k) + k * (div m k) :=
begin
  let h₀ := nat.mod_add_div (m : ℕ) (k : ℕ),
  have : ¬ ((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0),
  by { rintro ⟨hr, hq⟩, rw [hr, hq, mul_zero, zero_add] at h₀,
       exact (m.ne_zero h₀.symm).elim },
  have := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this,
  exact (this.trans h₀).symm,
end

theorem mod_coe (m k : ℕ+) :
 ((mod m k) : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) :=
begin
  dsimp [mod, mod_div],
  cases (m : ℕ) % (k : ℕ),
  { rw [if_pos rfl], refl },
  { rw [if_neg n.succ_ne_zero], refl }
end

theorem div_coe (m k : ℕ+) :
 ((div m k) : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) :=
begin
  dsimp [div, mod_div],
  cases (m : ℕ) % (k : ℕ),
  { rw [if_pos rfl], refl },
  { rw [if_neg n.succ_ne_zero], refl }
end

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k :=
begin
  change ((mod m k) : ℕ) ≤ (m : ℕ) ∧ ((mod m k) : ℕ) ≤ (k : ℕ),
  rw [mod_coe], split_ifs,
  { have hm : (m : ℕ) > 0 := m.pos,
    rw [← nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm ⊢,
    by_cases h' : ((m : ℕ) / (k : ℕ)) = 0,
    { rw [h', mul_zero] at hm, exact (lt_irrefl _ hm).elim},
    { let h' := nat.mul_le_mul_left (k : ℕ)
             (nat.succ_le_of_lt (nat.pos_of_ne_zero h')),
      rw [mul_one] at h', exact ⟨h', le_refl (k : ℕ)⟩ } },
  { exact ⟨nat.mod_le (m : ℕ) (k : ℕ), le_of_lt (nat.mod_lt (m : ℕ) k.pos)⟩ }
end

instance : has_dvd ℕ+ := ⟨λ k m, (k : ℕ) ∣ (m : ℕ)⟩

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by {refl}

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k :=
begin
  change (k : ℕ) ∣ (m : ℕ) ↔ mod m k = k,
  rw [nat.dvd_iff_mod_eq_zero], split,
  { intro h, apply eq, rw [mod_coe, if_pos h] },
  { intro h, by_cases h' : (m : ℕ) % (k : ℕ) = 0,
    { exact h'},
    { replace h : ((mod m k) : ℕ) = (k : ℕ) := congr_arg _ h,
      rw [mod_coe, if_neg h'] at h,
      exact (ne_of_lt (nat.mod_lt (m : ℕ) k.pos) h).elim } }
end

def div_exact {m k : ℕ+} (h : k ∣ m) : ℕ+ :=
 ⟨(div m k).succ, nat.succ_pos _⟩

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * (div_exact h) = m :=
begin
 apply eq, rw [mul_coe],
 change (k : ℕ) * (div m k).succ = m,
 rw [mod_add_div m k, dvd_iff'.mp h, nat.mul_succ, add_comm],
end

theorem dvd_iff'' {k n : ℕ+} : k ∣ n ↔ ∃ m, k * m = n :=
⟨λ h, ⟨div_exact h, mul_div_exact h⟩,
 λ ⟨m, h⟩, dvd.intro (m : ℕ)
          ((mul_coe k m).symm.trans (congr_arg subtype.val h))⟩

theorem dvd_intro {k n : ℕ+} (m : ℕ+) (h : k * m = n) : k ∣ n :=
 dvd_iff''.mpr ⟨m, h⟩

theorem dvd_refl (m : ℕ+) : m ∣ m := dvd_intro 1 (mul_one m)

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n :=
λ hmn hnm, subtype.eq (nat.dvd_antisymm hmn hnm)

protected theorem dvd_trans {k m n : ℕ+} : k ∣ m → m ∣ n → k ∣ n :=
@dvd_trans ℕ _ (k : ℕ) (m : ℕ) (n : ℕ)

theorem one_dvd (n : ℕ+) : 1 ∣ n := dvd_intro n (one_mul n)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
 ⟨λ h, dvd_antisymm h (one_dvd n), λ h, h.symm ▸ (dvd_refl 1)⟩

def gcd (n m : ℕ+) : ℕ+ :=
 ⟨nat.gcd (n : ℕ) (m : ℕ), nat.gcd_pos_of_pos_left (m : ℕ) n.pos⟩

def lcm (n m : ℕ+) : ℕ+ :=
 ⟨nat.lcm (n : ℕ) (m : ℕ),
  by { let h := mul_pos n.pos m.pos,
       rw [← gcd_mul_lcm (n : ℕ) (m : ℕ), mul_comm] at h,
       exact pos_of_dvd_of_pos (dvd.intro (nat.gcd (n : ℕ) (m : ℕ)) rfl) h }⟩

@[simp] theorem gcd_coe (n m : ℕ+) : ((gcd n m) : ℕ) = nat.gcd n m := rfl

@[simp] theorem lcm_coe (n m : ℕ+) : ((lcm n m) : ℕ) = nat.lcm n m := rfl

theorem gcd_dvd_left (n m : ℕ+) : (gcd n m) ∣ n := nat.gcd_dvd_left (n : ℕ) (m : ℕ)

theorem gcd_dvd_right (n m : ℕ+) : (gcd n m) ∣ m := nat.gcd_dvd_right (n : ℕ) (m : ℕ)

theorem dvd_gcd {m n k : ℕ+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
 @nat.dvd_gcd (m : ℕ) (n : ℕ) (k : ℕ) hm hn

theorem dvd_lcm_left  (n m : ℕ+) : n ∣ lcm n m := nat.dvd_lcm_left  (n : ℕ) (m : ℕ)

theorem dvd_lcm_right (n m : ℕ+) : m ∣ lcm n m := nat.dvd_lcm_right (n : ℕ) (m : ℕ)

theorem lcm_dvd {m n k : ℕ+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
 @nat.lcm_dvd (m : ℕ) (n : ℕ) (k : ℕ) hm hn

theorem gcd_mul_lcm (n m : ℕ+) : (gcd n m) * (lcm n m) = n * m :=
 subtype.eq (nat.gcd_mul_lcm (n : ℕ) (m : ℕ))

def prime (p : ℕ+) : Prop := (p : ℕ).prime

end pnat
