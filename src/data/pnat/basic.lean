/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import data.nat.basic
import algebra.group_power.basic

/-!
# The positive natural numbers

This file defines the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
-/

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def pnat := {n : ℕ // 0 < n}
notation `ℕ+` := pnat

instance coe_pnat_nat : has_coe ℕ+ ℕ := ⟨subtype.val⟩
instance : has_repr ℕ+ := ⟨λ n, repr n.1⟩

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def pnat.nat_pred (i : ℕ+) : ℕ := i - 1

namespace nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def to_pnat (n : ℕ) (h : 0 < n . tactic.exact_dec_trivial) : ℕ+ := ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succ_pnat (n : ℕ) : ℕ+ := ⟨succ n, succ_pos n⟩

@[simp] theorem succ_pnat_coe (n : ℕ) : (succ_pnat n : ℕ) = succ n := rfl

theorem succ_pnat_inj {n m : ℕ} : succ_pnat n = succ_pnat m → n = m :=
λ h, by { let h' := congr_arg (coe : ℕ+ → ℕ) h, exact nat.succ.inj h' }

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def to_pnat' (n : ℕ) : ℕ+ := succ_pnat (pred n)

@[simp] theorem to_pnat'_coe : ∀ (n : ℕ),
 ((to_pnat' n) : ℕ) = ite (0 < n) n 1
| 0 := rfl
| (m + 1) := by {rw [if_pos (succ_pos m)], refl}

end nat

namespace pnat

open nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/

instance : decidable_eq ℕ+ := λ (a b : ℕ+), by apply_instance

instance : linear_order ℕ+ :=
subtype.linear_order _

@[simp] lemma mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
  (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k := iff.rfl

@[simp] lemma mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
  (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k := iff.rfl

@[simp, norm_cast] lemma coe_le_coe (n k : ℕ+) : (n:ℕ) ≤ k ↔ n ≤ k := iff.rfl

@[simp, norm_cast] lemma coe_lt_coe (n k : ℕ+) : (n:ℕ) < k ↔ n < k := iff.rfl

@[simp] theorem pos (n : ℕ+) : 0 < (n : ℕ) := n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n := subtype.eq

@[simp] lemma coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n := set_coe.ext_iff

lemma coe_injective : function.injective (coe : ℕ+ → ℕ) := subtype.coe_injective

@[simp] theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n := rfl

instance : has_add ℕ+ := ⟨λ a b, ⟨(a  + b : ℕ), add_pos a.pos b.pos⟩⟩

instance : add_comm_semigroup ℕ+ := coe_injective.add_comm_semigroup coe (λ _ _, rfl)

@[simp] theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n := rfl
instance coe_add_hom : is_add_hom (coe : ℕ+ → ℕ) := ⟨add_coe⟩

instance : add_left_cancel_semigroup ℕ+ :=
coe_injective.add_left_cancel_semigroup coe (λ _ _, rfl)

instance : add_right_cancel_semigroup ℕ+ :=
coe_injective.add_right_cancel_semigroup coe (λ _ _, rfl)

@[simp] theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 := ne_of_gt n.2

theorem to_pnat'_coe {n : ℕ} : 0 < n → (n.to_pnat' : ℕ) = n := succ_pred_eq_of_pos

@[simp] theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).to_pnat' = n := eq (to_pnat'_coe n.pos)

instance : has_mul ℕ+ := ⟨λ m n, ⟨m.1 * n.1, mul_pos m.2 n.2⟩⟩
instance : has_one ℕ+ := ⟨succ_pnat 0⟩

instance : comm_monoid ℕ+ := coe_injective.comm_monoid coe rfl (λ _ _, rfl)

instance : has_lt_iff_add_one_le ℕ+ :=
{ lt_iff_add_one_le := λ a b, iff.rfl }

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b :=
λ a b, nat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b :=
λ a b, nat.add_one_le_iff

@[simp] lemma one_le (n : ℕ+) : (1 : ℕ+) ≤ n := n.2

instance : order_bot ℕ+ :=
{ bot := 1,
  bot_le := λ a, a.property,
  .. pnat.linear_order }

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
@[simp] lemma bit0_le_bit0 (n m : ℕ+) : (bit0 n) ≤ (bit0 m) ↔ (bit0 (n : ℕ)) ≤ (bit0 (m : ℕ)) :=
iff.rfl
@[simp] lemma bit0_le_bit1 (n m : ℕ+) : (bit0 n) ≤ (bit1 m) ↔ (bit0 (n : ℕ)) ≤ (bit1 (m : ℕ)) :=
iff.rfl
@[simp] lemma bit1_le_bit0 (n m : ℕ+) : (bit1 n) ≤ (bit0 m) ↔ (bit1 (n : ℕ)) ≤ (bit0 (m : ℕ)) :=
iff.rfl
@[simp] lemma bit1_le_bit1 (n m : ℕ+) : (bit1 n) ≤ (bit1 m) ↔ (bit1 (n : ℕ)) ≤ (bit1 (m : ℕ)) :=
iff.rfl

@[simp] theorem one_coe : ((1 : ℕ+) : ℕ) = 1 := rfl
@[simp] theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n := rfl
instance coe_mul_hom : is_monoid_hom (coe : ℕ+ → ℕ) :=
 {map_one := one_coe, map_mul := mul_coe}

 @[simp]
lemma coe_eq_one_iff {m : ℕ+} :
(m : ℕ) = 1 ↔ m = 1 := by { split; intro h; try { apply pnat.eq}; rw h; simp }


@[simp] lemma coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) := rfl
@[simp] lemma coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) := rfl

@[simp] theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
by induction n with n ih;
 [refl, rw [pow_succ', pow_succ, mul_coe, mul_comm, ih]]

instance : ordered_cancel_comm_monoid ℕ+ :=
{ mul_le_mul_left := by { intros, apply nat.mul_le_mul_left, assumption },
  le_of_mul_le_mul_left := by { intros a b c h, apply nat.le_of_mul_le_mul_left h a.property, },
  mul_left_cancel := λ a b c h, by {
   replace h := congr_arg (coe : ℕ+ → ℕ) h,
   exact eq ((nat.mul_right_inj a.pos).mp h)},
  .. pnat.comm_monoid,
  .. pnat.linear_order }

instance : distrib ℕ+ := coe_injective.distrib coe (λ _ _, rfl) (λ _ _, rfl)

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

instance : has_well_founded ℕ+ := ⟨(<), measure_wf coe⟩

/-- Strong induction on `pnat`. -/
lemma strong_induction_on {p : pnat → Prop} : ∀ (n : pnat) (h : ∀ k, (∀ m, m < k → p m) → p k), p n
| n := λ IH, IH _ (λ a h, strong_induction_on a IH)
using_well_founded { dec_tac := `[assumption] }

/-- If `(n : pnat)` is different from `1`, then it is the successor of some `(k : pnat)`. -/
lemma exists_eq_succ_of_ne_one : ∀ {n : pnat} (h1 : n ≠ 1), ∃ (k : pnat), n = k + 1
| ⟨1, _⟩ h1 := false.elim $ h1 rfl
| ⟨n+2, _⟩ _ := ⟨⟨n+1, by simp⟩, rfl⟩

lemma case_strong_induction_on {p : pnat → Prop} (a : pnat) (hz : p 1)
  (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a :=
begin
  apply strong_induction_on a,
  intros k hk,
  by_cases h1 : k = 1, { rwa h1 },
  obtain ⟨b, rfl⟩ := exists_eq_succ_of_ne_one h1,
  simp only [lt_add_one_iff] at hk,
  exact hi b hk
end

/-- An induction principle for `pnat`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_eliminator]
def rec_on (n : pnat) {p : pnat → Sort*} (p1 : p 1) (hp : ∀ n, p n → p (n + 1)) : p n :=
begin
  rcases n with ⟨n, h⟩,
  induction n with n IH,
  { exact absurd h dec_trivial },
  { cases n with n,
    { exact p1 },
    { exact hp _ (IH n.succ_pos) } }
end

@[simp] theorem rec_on_one {p} (p1 hp) : @pnat.rec_on 1 p p1 hp = p1 := rfl

@[simp] theorem rec_on_succ (n : pnat) {p : pnat → Sort*} (p1 hp) :
  @pnat.rec_on (n + 1) p p1 hp = hp n (@pnat.rec_on n p p1 hp) :=
by { cases n with n h, cases n; [exact absurd h dec_trivial, refl] }

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
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

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def mod_div (m k : ℕ+) : ℕ+ × ℕ := mod_div_aux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ := (mod_div m k).1

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ  := (mod_div m k).2

theorem mod_add_div (m k : ℕ+) : ((mod m k) + k * (div m k) : ℕ) = m :=
begin
  let h₀ := nat.mod_add_div (m : ℕ) (k : ℕ),
  have : ¬ ((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0),
  by { rintro ⟨hr, hq⟩, rw [hr, hq, mul_zero, zero_add] at h₀,
       exact (m.ne_zero h₀.symm).elim },
  have := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this,
  exact (this.trans h₀),
end

theorem div_add_mod (m k : ℕ+) : (k * (div m k) + mod m k : ℕ) = m :=
(add_comm _ _).trans (mod_add_div _ _)

lemma mod_add_div' (m k : ℕ+) : ((mod m k) + (div m k) * k : ℕ) = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : ℕ+) : ((div m k) * k + mod m k : ℕ) = m :=
by { rw mul_comm, exact div_add_mod _ _ }

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

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) :=
begin
  split; intro h, rcases h with ⟨_, rfl⟩, apply dvd_mul_right,
  rcases h with ⟨a, h⟩, cases a, { contrapose h, apply ne_zero, },
  use a.succ, apply nat.succ_pos, rw [← coe_inj, h, mul_coe, mk_coe],
end

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k :=
begin
  rw dvd_iff,
  rw [nat.dvd_iff_mod_eq_zero], split,
  { intro h, apply eq, rw [mod_coe, if_pos h] },
  { intro h, by_cases h' : (m : ℕ) % (k : ℕ) = 0,
    { exact h'},
    { replace h : ((mod m k) : ℕ) = (k : ℕ) := congr_arg _ h,
      rw [mod_coe, if_neg h'] at h,
      exact (ne_of_lt (nat.mod_lt (m : ℕ) k.pos) h).elim } }
end

lemma le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n :=
by { rw dvd_iff', intro h, rw ← h, apply (mod_le n m).left }

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def div_exact (m k : ℕ+) : ℕ+ :=
 ⟨(div m k).succ, nat.succ_pos _⟩

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * (div_exact m k) = m :=
begin
 apply eq, rw [mul_coe],
 change (k : ℕ) * (div m k).succ = m,
 rw [← div_add_mod m k, dvd_iff'.mp h, nat.mul_succ]
end

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n :=
λ hmn hnm, le_antisymm (le_of_dvd hmn) (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
 ⟨λ h, dvd_antisymm h (one_dvd n), λ h, h.symm ▸ (dvd_refl 1)⟩

lemma pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a :=
begin
  apply pos_iff_ne_zero.2,
  intro hzero,
  rw hzero at h,
  exact pnat.ne_zero n (eq_zero_of_zero_dvd h)
end

end pnat

section can_lift

instance nat.can_lift_pnat : can_lift ℕ ℕ+ :=
⟨coe, λ n, 0 < n, λ n hn, ⟨nat.to_pnat' n, pnat.to_pnat'_coe hn⟩⟩

instance int.can_lift_pnat : can_lift ℤ ℕ+ :=
⟨coe, λ n, 0 < n, λ n hn, ⟨nat.to_pnat' (int.nat_abs n),
  by rw [coe_coe, nat.to_pnat'_coe, if_pos (int.nat_abs_pos_of_ne_zero (ne_of_gt hn)),
    int.nat_abs_of_nonneg hn.le]⟩⟩

end can_lift
