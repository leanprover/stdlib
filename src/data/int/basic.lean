/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import data.nat.pow
import algebra.order_functions

open nat

namespace int

instance : inhabited ℤ := ⟨int.zero⟩

instance : nontrivial ℤ :=
⟨⟨0, 1, int.zero_ne_one⟩⟩

instance : comm_ring int :=
{ add            := int.add,
  add_assoc      := int.add_assoc,
  zero           := int.zero,
  zero_add       := int.zero_add,
  add_zero       := int.add_zero,
  neg            := int.neg,
  add_left_neg   := int.add_left_neg,
  add_comm       := int.add_comm,
  mul            := int.mul,
  mul_assoc      := int.mul_assoc,
  one            := int.one,
  one_mul        := int.one_mul,
  mul_one        := int.mul_one,
  sub            := int.sub,
  left_distrib   := int.distrib_left,
  right_distrib  := int.distrib_right,
  mul_comm       := int.mul_comm,
  gsmul          := (*),
  gsmul_zero'    := int.zero_mul,
  gsmul_succ'    := λ n x, by rw [succ_eq_one_add, of_nat_add, int.distrib_right, of_nat_one,
                                  int.one_mul],
  gsmul_neg'     := λ n x, neg_mul_eq_neg_mul_symm (n.succ : ℤ) x }

/-! ### Extra instances to short-circuit type class resolution -/
-- instance : has_sub int            := by apply_instance -- This is in core
instance : add_comm_monoid int    := by apply_instance
instance : add_monoid int         := by apply_instance
instance : monoid int             := by apply_instance
instance : comm_monoid int        := by apply_instance
instance : comm_semigroup int     := by apply_instance
instance : semigroup int          := by apply_instance
instance : add_comm_semigroup int := by apply_instance
instance : add_semigroup int      := by apply_instance
instance : comm_semiring int      := by apply_instance
instance : semiring int           := by apply_instance
instance : ring int               := by apply_instance
instance : distrib int            := by apply_instance

instance : linear_ordered_comm_ring int :=
{ add_le_add_left := @int.add_le_add_left,
  mul_pos         := @int.mul_pos,
  zero_le_one     := le_of_lt int.zero_lt_one,
  .. int.comm_ring, .. int.linear_order, .. int.nontrivial }

instance : linear_ordered_add_comm_group int :=
by apply_instance

@[simp] lemma add_neg_one (i : ℤ) : i + -1 = i - 1 := rfl

theorem abs_eq_nat_abs : ∀ a : ℤ, abs a = nat_abs a
| (n : ℕ) := abs_of_nonneg $ coe_zero_le _
| -[1+ n] := abs_of_nonpos $ le_of_lt $ neg_succ_lt_zero _

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
by rw [abs_eq_nat_abs]; refl

theorem sign_mul_abs (a : ℤ) : sign a * abs a = a :=
by rw [abs_eq_nat_abs, sign_mul_nat_abs]

@[simp] lemma default_eq_zero : default ℤ = 0 := rfl

meta instance : has_to_format ℤ := ⟨λ z, to_string z⟩
meta instance : has_reflect ℤ := by tactic.mk_has_reflect_instance

attribute [simp] int.coe_nat_add int.coe_nat_mul int.coe_nat_zero int.coe_nat_one int.coe_nat_succ
attribute [simp] int.of_nat_eq_coe int.bodd

@[simp] theorem add_def {a b : ℤ} : int.add a b = a + b := rfl
@[simp] theorem mul_def {a b : ℤ} : int.mul a b = a * b := rfl

@[simp] lemma neg_succ_not_nonneg (n : ℕ) : 0 ≤ -[1+ n] ↔ false :=
by { simp only [not_le, iff_false], exact int.neg_succ_lt_zero n, }

@[simp] lemma neg_succ_not_pos (n : ℕ) : 0 < -[1+ n] ↔ false :=
by simp only [not_lt, iff_false]

@[simp] lemma neg_succ_sub_one (n : ℕ) : -[1+ n] - 1 = -[1+ (n+1)] := rfl
@[simp] theorem coe_nat_mul_neg_succ (m n : ℕ) : (m : ℤ) * -[1+ n] = -(m * succ n) := rfl
@[simp] theorem neg_succ_mul_coe_nat (m n : ℕ) : -[1+ m] * n = -(succ m * n) := rfl
@[simp] theorem neg_succ_mul_neg_succ (m n : ℕ) : -[1+ m] * -[1+ n] = succ m * succ n := rfl

@[simp, norm_cast]
theorem coe_nat_le {m n : ℕ} : (↑m : ℤ) ≤ ↑n ↔ m ≤ n := coe_nat_le_coe_nat_iff m n
@[simp, norm_cast]
theorem coe_nat_lt {m n : ℕ} : (↑m : ℤ) < ↑n ↔ m < n := coe_nat_lt_coe_nat_iff m n
@[simp, norm_cast]
theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n := int.coe_nat_eq_coe_nat_iff m n

@[simp] theorem coe_nat_pos {n : ℕ} : (0 : ℤ) < n ↔ 0 < n :=
by rw [← int.coe_nat_zero, coe_nat_lt]

@[simp] theorem coe_nat_eq_zero {n : ℕ} : (n : ℤ) = 0 ↔ n = 0 :=
by rw [← int.coe_nat_zero, coe_nat_inj']

theorem coe_nat_ne_zero {n : ℕ} : (n : ℤ) ≠ 0 ↔ n ≠ 0 :=
not_congr coe_nat_eq_zero

@[simp] lemma coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := coe_nat_le.2 (nat.zero_le _)

lemma coe_nat_ne_zero_iff_pos {n : ℕ} : (n : ℤ) ≠ 0 ↔ 0 < n :=
⟨λ h, nat.pos_of_ne_zero (coe_nat_ne_zero.1 h),
λ h, (ne_of_lt (coe_nat_lt.2 h)).symm⟩

lemma coe_nat_succ_pos (n : ℕ) : 0 < (n.succ : ℤ) := int.coe_nat_pos.2 (succ_pos n)

@[simp, norm_cast] theorem coe_nat_abs (n : ℕ) : abs (n : ℤ) = n :=
abs_of_nonneg (coe_nat_nonneg n)

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1

theorem nat_succ_eq_int_succ (n : ℕ) : (nat.succ n : ℤ) = int.succ n := rfl

theorem pred_succ (a : ℤ) : pred (succ a) = a := add_sub_cancel _ _

theorem succ_pred (a : ℤ) : succ (pred a) = a := sub_add_cancel _ _

theorem neg_succ (a : ℤ) : -succ a = pred (-a) := neg_add _ _

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
by rw [neg_succ, succ_pred]

theorem neg_pred (a : ℤ) : -pred a = succ (-a) :=
by rw [eq_neg_of_eq_neg (neg_succ (-a)).symm, neg_neg]

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
by rw [neg_pred, pred_succ]

theorem pred_nat_succ (n : ℕ) : pred (nat.succ n) = n := pred_succ n

theorem neg_nat_succ (n : ℕ) : -(nat.succ n : ℤ) = pred (-n) := neg_succ n

theorem succ_neg_nat_succ (n : ℕ) : succ (-nat.succ n) = -n := succ_neg_succ n

theorem lt_succ_self (a : ℤ) : a < succ a :=
lt_add_of_pos_right _ zero_lt_one

theorem pred_self_lt (a : ℤ) : pred a < a :=
sub_lt_self _ zero_lt_one

theorem add_one_le_iff {a b : ℤ} : a + 1 ≤ b ↔ a < b := iff.rfl

theorem lt_add_one_iff {a b : ℤ} : a < b + 1 ↔ a ≤ b :=
add_le_add_iff_right _

@[simp] lemma succ_coe_nat_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
lt_add_one_iff.mpr (by simp)

@[norm_cast] lemma coe_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 :=
by { cases n, cases h, simp, }

lemma le_add_one {a b : ℤ} (h : a ≤ b) : a ≤ b + 1 :=
le_of_lt (int.lt_add_one_iff.mpr h)

theorem sub_one_lt_iff {a b : ℤ} : a - 1 < b ↔ a ≤ b :=
sub_lt_iff_lt_add.trans lt_add_one_iff

theorem le_sub_one_iff {a b : ℤ} : a ≤ b - 1 ↔ a < b :=
le_sub_iff_add_le

@[simp] lemma eq_zero_iff_abs_lt_one {a : ℤ} : abs a < 1 ↔ a = 0 :=
⟨λ a0, let ⟨hn, hp⟩ := abs_lt.mp a0 in (le_of_lt_add_one (by exact hp)).antisymm hn,
  λ a0, (abs_eq_zero.mpr a0).le.trans_lt zero_lt_one⟩

@[elab_as_eliminator] protected lemma induction_on {p : ℤ → Prop}
  (i : ℤ) (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i :=
begin
  induction i,
  { induction i,
    { exact hz },
    { exact hp _ i_ih } },
  { have : ∀ n:ℕ, p (- n),
    { intro n, induction n,
      { simp [hz] },
      { convert hn _ n_ih using 1, simp [sub_eq_neg_add] } },
    exact this (i + 1) }
end

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
  than `b`, and the `pred` of a number less than `b`. -/
protected def induction_on' {C : ℤ → Sort*} (z : ℤ) (b : ℤ) :
  C b → (∀ k, b ≤ k → C k → C (k + 1)) → (∀ k ≤ b, C k → C (k - 1)) → C z :=
λ H0 Hs Hp,
begin
  rw ←sub_add_cancel z b,
  induction (z - b) with n n,
  { induction n with n ih, { rwa [of_nat_zero, zero_add] },
    rw [of_nat_succ, add_assoc, add_comm 1 b, ←add_assoc],
    exact Hs _ (le_add_of_nonneg_left (of_nat_nonneg _)) ih },
  { induction n with n ih,
    { rw [neg_succ_of_nat_eq, ←of_nat_eq_coe, of_nat_zero, zero_add, neg_add_eq_sub],
      exact Hp _ (le_refl _) H0 },
    { rw [neg_succ_of_nat_coe', nat.succ_eq_add_one, ←neg_succ_of_nat_coe, sub_add_eq_add_sub],
      exact Hp _ (le_of_lt (add_lt_of_neg_of_le (neg_succ_lt_zero _) (le_refl _))) ih } }
end

/-! ### nat abs -/

attribute [simp] nat_abs nat_abs_of_nat nat_abs_zero nat_abs_one

theorem nat_abs_add_le (a b : ℤ) : nat_abs (a + b) ≤ nat_abs a + nat_abs b :=
begin
  have : ∀ (a b : ℕ), nat_abs (sub_nat_nat a (nat.succ b)) ≤ nat.succ (a + b),
  { refine (λ a b : ℕ, sub_nat_nat_elim a b.succ
      (λ m n i, n = b.succ → nat_abs i ≤ (m + b).succ) _ _ rfl);
    intros i n e,
    { subst e, rw [add_comm _ i, add_assoc],
      exact nat.le_add_right i (b.succ + b).succ },
    { apply succ_le_succ,
      rw [← succ.inj e, ← add_assoc, add_comm],
      apply nat.le_add_right } },
  cases a; cases b with b b; simp [nat_abs, nat.succ_add];
  try {refl}; [skip, rw add_comm a b]; apply this
end

lemma nat_abs_sub_le (a b : ℤ) : nat_abs (a - b) ≤ nat_abs a + nat_abs b :=
by { rw [sub_eq_add_neg, ← int.nat_abs_neg b], apply nat_abs_add_le }

theorem nat_abs_neg_of_nat (n : ℕ) : nat_abs (neg_of_nat n) = n :=
by cases n; refl

theorem nat_abs_mul (a b : ℤ) : nat_abs (a * b) = (nat_abs a) * (nat_abs b) :=
by cases a; cases b;
  simp only [← int.mul_def, int.mul, nat_abs_neg_of_nat, eq_self_iff_true, int.nat_abs]

lemma nat_abs_mul_nat_abs_eq {a b : ℤ} {c : ℕ} (h : a * b = (c : ℤ)) :
  a.nat_abs * b.nat_abs = c :=
by rw [← nat_abs_mul, h, nat_abs_of_nat]

@[simp] lemma nat_abs_mul_self' (a : ℤ) : (nat_abs a * nat_abs a : ℤ) = a * a :=
by rw [← int.coe_nat_mul, nat_abs_mul_self]

theorem neg_succ_of_nat_eq' (m : ℕ) : -[1+ m] = -m - 1 :=
by simp [neg_succ_of_nat_eq, sub_eq_neg_add]

lemma nat_abs_ne_zero_of_ne_zero {z : ℤ} (hz : z ≠ 0) : z.nat_abs ≠ 0 :=
λ h, hz $ int.eq_zero_of_nat_abs_eq_zero h

@[simp] lemma nat_abs_eq_zero {a : ℤ} : a.nat_abs = 0 ↔ a = 0 :=
⟨int.eq_zero_of_nat_abs_eq_zero, λ h, h.symm ▸ rfl⟩

lemma nat_abs_ne_zero {a : ℤ} : a.nat_abs ≠ 0 ↔ a ≠ 0 := not_congr int.nat_abs_eq_zero

lemma nat_abs_lt_nat_abs_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) :
  a.nat_abs < b.nat_abs :=
begin
  lift b to ℕ using le_trans w₁ (le_of_lt w₂),
  lift a to ℕ using w₁,
  simpa using w₂,
end

lemma nat_abs_eq_nat_abs_iff {a b : ℤ} : a.nat_abs = b.nat_abs ↔ a = b ∨ a = -b :=
begin
  split; intro h,
  { cases int.nat_abs_eq a with h₁ h₁; cases int.nat_abs_eq b with h₂ h₂;
    rw [h₁, h₂]; simp [h], },
  { cases h; rw h, rw int.nat_abs_neg, },
end

lemma nat_abs_eq_iff {a : ℤ} {n : ℕ} : a.nat_abs = n ↔ a = n ∨ a = -n :=
by rw [←int.nat_abs_eq_nat_abs_iff, int.nat_abs_of_nat]

lemma nat_abs_eq_iff_mul_self_eq {a b : ℤ} : a.nat_abs = b.nat_abs ↔ a * a = b * b :=
begin
  rw [← abs_eq_iff_mul_self_eq, abs_eq_nat_abs, abs_eq_nat_abs],
  exact int.coe_nat_inj'.symm
end

lemma nat_abs_lt_iff_mul_self_lt {a b : ℤ} : a.nat_abs < b.nat_abs ↔ a * a < b * b :=
begin
  rw [← abs_lt_iff_mul_self_lt, abs_eq_nat_abs, abs_eq_nat_abs],
  exact int.coe_nat_lt.symm
end

lemma nat_abs_le_iff_mul_self_le {a b : ℤ} : a.nat_abs ≤ b.nat_abs ↔ a * a ≤ b * b :=
begin
  rw [← abs_le_iff_mul_self_le, abs_eq_nat_abs, abs_eq_nat_abs],
  exact int.coe_nat_le.symm
end

lemma nat_abs_eq_iff_sq_eq {a b : ℤ} : a.nat_abs = b.nat_abs ↔ a ^ 2 = b ^ 2 :=
by { rw [sq, sq], exact nat_abs_eq_iff_mul_self_eq }

lemma nat_abs_lt_iff_sq_lt {a b : ℤ} : a.nat_abs < b.nat_abs ↔ a ^ 2 < b ^ 2 :=
by { rw [sq, sq], exact nat_abs_lt_iff_mul_self_lt }

lemma nat_abs_le_iff_sq_le {a b : ℤ} : a.nat_abs ≤ b.nat_abs ↔ a ^ 2 ≤ b ^ 2 :=
by { rw [sq, sq], exact nat_abs_le_iff_mul_self_le }

/-! ### `/`  -/

@[simp] theorem of_nat_div (m n : ℕ) : of_nat (m / n) = (of_nat m) / (of_nat n) := rfl

@[simp, norm_cast] theorem coe_nat_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := rfl

theorem neg_succ_of_nat_div (m : ℕ) {b : ℤ} (H : 0 < b) :
  -[1+m] / b = -(m / b + 1) :=
match b, eq_succ_of_zero_lt H with ._, ⟨n, rfl⟩ := rfl end

-- Will be generalized to Euclidean domains.
local attribute [simp]
protected theorem zero_div : ∀ (b : ℤ), 0 / b = 0
| 0       := show of_nat _ = _, by simp
| (n+1:ℕ) := show of_nat _ = _, by simp
| -[1+ n] := show -of_nat _ = _, by simp

local attribute [simp] -- Will be generalized to Euclidean domains.
protected theorem div_zero : ∀ (a : ℤ), a / 0 = 0
| 0       := show of_nat _ = _, by simp
| (n+1:ℕ) := show of_nat _ = _, by simp
| -[1+ n] := rfl

@[simp] protected theorem div_neg : ∀ (a b : ℤ), a / -b = -(a / b)
| (m : ℕ) 0       := show of_nat (m / 0) = -(m / 0 : ℕ), by rw nat.div_zero; refl
| (m : ℕ) (n+1:ℕ) := rfl
| 0       -[1+ n] := by simp
| (m+1:ℕ) -[1+ n] := (neg_neg _).symm
| -[1+ m] 0       := rfl
| -[1+ m] (n+1:ℕ) := rfl
| -[1+ m] -[1+ n] := rfl


theorem div_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b = -((-a - 1) / b + 1) :=
match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ :=
  by change (- -[1+ m] : ℤ) with (m+1 : ℤ); rw add_sub_cancel; refl
end

protected theorem div_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b :=
match a, b, eq_coe_of_zero_le Ha, eq_coe_of_zero_le Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ := coe_zero_le _
end

protected theorem div_nonpos {a b : ℤ} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a / b ≤ 0 :=
nonpos_of_neg_nonneg $ by rw [← int.div_neg]; exact int.div_nonneg Ha (neg_nonneg_of_nonpos Hb)

theorem div_neg' {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 :=
match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ := neg_succ_lt_zero _
end

@[simp] protected theorem div_one : ∀ (a : ℤ), a / 1 = a
| 0       := show of_nat _ = _, by simp
| (n+1:ℕ) := congr_arg of_nat (nat.div_one _)
| -[1+ n] := congr_arg neg_succ_of_nat (nat.div_one _)

theorem div_eq_zero_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
match a, b, eq_coe_of_zero_le H1, eq_succ_of_zero_lt (lt_of_le_of_lt H1 H2), H2  with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 :=
  congr_arg of_nat $ nat.div_eq_of_lt $ lt_of_coe_nat_lt_coe_nat H2
end

theorem div_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < abs b) : a / b = 0 :=
match b, abs b, abs_eq_nat_abs b, H2 with
| (n : ℕ), ._, rfl, H2 := div_eq_zero_of_lt H1 H2
| -[1+ n], ._, rfl, H2 := neg_injective $ by rw [← int.div_neg]; exact div_eq_zero_of_lt H1 H2
end

protected theorem add_mul_div_right (a b : ℤ) {c : ℤ} (H : c ≠ 0) :
  (a + b * c) / c = a / c + b :=
have ∀ {k n : ℕ} {a : ℤ}, (a + n * k.succ) / k.succ = a / k.succ + n, from
λ k n a, match a with
| (m : ℕ) := congr_arg of_nat $ nat.add_mul_div_right _ _ k.succ_pos
| -[1+ m] := show ((n * k.succ:ℕ) - m.succ : ℤ) / k.succ =
                  n - (m / k.succ + 1 : ℕ), begin
  cases lt_or_ge m (n*k.succ) with h h,
  { rw [← int.coe_nat_sub h,
        ← int.coe_nat_sub ((nat.div_lt_iff_lt_mul _ _ k.succ_pos).2 h)],
    apply congr_arg of_nat,
    rw [mul_comm, nat.mul_sub_div], rwa mul_comm },
  { change (↑(n * nat.succ k) - (m + 1) : ℤ) / ↑(nat.succ k) =
           ↑n - ((m / nat.succ k : ℕ) + 1),
    rw [← sub_sub, ← sub_sub, ← neg_sub (m:ℤ), ← neg_sub _ (n:ℤ),
        ← int.coe_nat_sub h,
        ← int.coe_nat_sub ((nat.le_div_iff_mul_le _ _ k.succ_pos).2 h),
        ← neg_succ_of_nat_coe', ← neg_succ_of_nat_coe'],
    { apply congr_arg neg_succ_of_nat,
      rw [mul_comm, nat.sub_mul_div], rwa mul_comm } }
  end
end,
have ∀ {a b c : ℤ}, 0 < c → (a + b * c) / c = a / c + b, from
λ a b c H, match c, eq_succ_of_zero_lt H, b with
| ._, ⟨k, rfl⟩, (n : ℕ) := this
| ._, ⟨k, rfl⟩, -[1+ n] :=
  show (a - n.succ * k.succ) / k.succ = (a / k.succ) - n.succ, from
  eq_sub_of_add_eq $ by rw [← this, sub_add_cancel]
end,
match lt_trichotomy c 0 with
| or.inl hlt          := neg_inj.1 $ by rw [← int.div_neg, neg_add, ← int.div_neg, ← neg_mul_neg];
                         apply this (neg_pos_of_neg hlt)
| or.inr (or.inl heq) := absurd heq H
| or.inr (or.inr hgt) := this hgt
end

protected theorem add_mul_div_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b ≠ 0) :
    (a + b * c) / b = a / b + c :=
by rw [mul_comm, int.add_mul_div_right _ _ H]

protected theorem add_div_of_dvd_right {a b c : ℤ} (H : c ∣ b) :
  (a + b) / c = a / c + b / c :=
begin
  by_cases h1 : c = 0,
  { simp [h1] },
  cases H with k hk,
  rw hk,
  change c ≠ 0 at h1,
  rw [mul_comm c k, int.add_mul_div_right _ _ h1, ←zero_add (k * c), int.add_mul_div_right _ _ h1,
      int.zero_div, zero_add]
end

protected theorem add_div_of_dvd_left {a b c : ℤ} (H : c ∣ a) :
  (a + b) / c = a / c + b / c :=
by rw [add_comm, int.add_div_of_dvd_right H, add_comm]

@[simp] protected theorem mul_div_cancel (a : ℤ) {b : ℤ} (H : b ≠ 0) : a * b / b = a :=
by have := int.add_mul_div_right 0 a H;
   rwa [zero_add, int.zero_div, zero_add] at this

@[simp] protected theorem mul_div_cancel_left {a : ℤ} (b : ℤ) (H : a ≠ 0) : a * b / a = b :=
by rw [mul_comm, int.mul_div_cancel _ H]

@[simp] protected theorem div_self {a : ℤ} (H : a ≠ 0) : a / a = 1 :=
by have := int.mul_div_cancel 1 H; rwa one_mul at this

/-! ### mod -/

theorem of_nat_mod (m n : nat) : (m % n : ℤ) = of_nat (m % n) := rfl

@[simp, norm_cast] theorem coe_nat_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl

theorem neg_succ_of_nat_mod (m : ℕ) {b : ℤ} (bpos : 0 < b) :
  -[1+m] % b = b - 1 - m % b :=
by rw [sub_sub, add_comm]; exact
match b, eq_succ_of_zero_lt bpos with ._, ⟨n, rfl⟩ := rfl end

@[simp] theorem mod_neg : ∀ (a b : ℤ), a % -b = a % b
| (m : ℕ) n := @congr_arg ℕ ℤ _ _ (λ i, ↑(m % i)) (nat_abs_neg _)
| -[1+ m] n := @congr_arg ℕ ℤ _ _ (λ i, sub_nat_nat i (nat.succ (m % i))) (nat_abs_neg _)

@[simp] theorem mod_abs (a b : ℤ) : a % (abs b) = a % b :=
abs_by_cases (λ i, a % i = a % b) rfl (mod_neg _ _)

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem zero_mod (b : ℤ) : 0 % b = 0 := rfl

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem mod_zero : ∀ (a : ℤ), a % 0 = a
| (m : ℕ) := congr_arg of_nat $ nat.mod_zero _
| -[1+ m] := congr_arg neg_succ_of_nat $ nat.mod_zero _

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem mod_one : ∀ (a : ℤ), a % 1 = 0
| (m : ℕ) := congr_arg of_nat $ nat.mod_one _
| -[1+ m] := show (1 - (m % 1).succ : ℤ) = 0, by rw nat.mod_one; refl

theorem mod_eq_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
match a, b, eq_coe_of_zero_le H1, eq_coe_of_zero_le (le_trans H1 (le_of_lt H2)), H2 with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 :=
  congr_arg of_nat $ nat.mod_eq_of_lt (lt_of_coe_nat_lt_coe_nat H2)
end

theorem mod_nonneg : ∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
| (m : ℕ) n H := coe_zero_le _
| -[1+ m] n H :=
  sub_nonneg_of_le $ coe_nat_le_coe_nat_of_le $ nat.mod_lt _ (nat_abs_pos_of_ne_zero H)

theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : 0 < b) : a % b < b :=
match a, b, eq_succ_of_zero_lt H with
| (m : ℕ), ._, ⟨n, rfl⟩ := coe_nat_lt_coe_nat_of_lt (nat.mod_lt _ (nat.succ_pos _))
| -[1+ m], ._, ⟨n, rfl⟩ := sub_lt_self _ (coe_nat_lt_coe_nat_of_lt $ nat.succ_pos _)
end

theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < abs b :=
by rw [← mod_abs]; exact mod_lt_of_pos _ (abs_pos.2 H)

theorem mod_add_div_aux (m n : ℕ) : (n - (m % n + 1) - (n * (m / n) + n) : ℤ) = -[1+ m] :=
begin
  rw [← sub_sub, neg_succ_of_nat_coe, sub_sub (n:ℤ)],
  apply eq_neg_of_eq_neg,
  rw [neg_sub, sub_sub_self, add_right_comm],
  exact @congr_arg ℕ ℤ _ _ (λi, (i + 1 : ℤ)) (nat.mod_add_div _ _).symm
end

theorem mod_add_div : ∀ (a b : ℤ), a % b + b * (a / b) = a
| (m : ℕ) 0       := congr_arg of_nat (nat.mod_add_div _ _)
| (m : ℕ) (n+1:ℕ) := congr_arg of_nat (nat.mod_add_div _ _)
| 0       -[1+ n] := by simp
| (m+1:ℕ) -[1+ n] := show (_ + -(n+1) * -((m + 1) / (n + 1) : ℕ) : ℤ) = _,
  by rw [neg_mul_neg]; exact congr_arg of_nat (nat.mod_add_div _ _)
| -[1+ m] 0       := by rw [mod_zero, int.div_zero]; refl
| -[1+ m] (n+1:ℕ) := mod_add_div_aux m n.succ
| -[1+ m] -[1+ n] := mod_add_div_aux m n.succ

theorem div_add_mod (a b : ℤ) : b * (a / b) + a % b = a :=
(add_comm _ _).trans (mod_add_div _ _)

lemma mod_add_div' (m k : ℤ) : m % k + (m / k) * k = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : ℤ) : (m / k) * k + m % k = m :=
by { rw mul_comm, exact div_add_mod _ _ }

theorem mod_def (a b : ℤ) : a % b = a - b * (a / b) :=
eq_sub_of_add_eq (mod_add_div _ _)

@[simp] theorem add_mul_mod_self {a b c : ℤ} : (a + b * c) % c = a % c :=
if cz : c = 0 then by rw [cz, mul_zero, add_zero] else
by rw [mod_def, mod_def, int.add_mul_div_right _ _ cz,
       mul_add, mul_comm, add_sub_add_right_eq_sub]

@[simp] theorem add_mul_mod_self_left (a b c : ℤ) : (a + b * c) % b = a % b :=
by rw [mul_comm, add_mul_mod_self]

@[simp] theorem add_mod_self {a b : ℤ} : (a + b) % b = a % b :=
by have := add_mul_mod_self_left a b 1; rwa mul_one at this

@[simp] theorem add_mod_self_left {a b : ℤ} : (a + b) % a = b % a :=
by rw [add_comm, add_mod_self]

@[simp] theorem mod_add_mod (m n k : ℤ) : (m % n + k) % n = (m + k) % n :=
by have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm;
   rwa [add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : ℤ) : (m + n % k) % k = (m + n) % k :=
by rw [add_comm, mod_add_mod, add_comm]

lemma add_mod (a b n : ℤ) : (a + b) % n = ((a % n) + (b % n)) % n :=
by rw [add_mod_mod, mod_add_mod]

theorem add_mod_eq_add_mod_right {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (m + i) % n = (k + i) % n :=
by rw [← mod_add_mod, ← mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (i + m) % n = (i + k) % n :=
by rw [add_comm, add_mod_eq_add_mod_right _ H, add_comm]

theorem mod_add_cancel_right {m n k : ℤ} (i) : (m + i) % n = (k + i) % n ↔
  m % n = k % n :=
⟨λ H, by have := add_mod_eq_add_mod_right (-i) H;
      rwa [add_neg_cancel_right, add_neg_cancel_right] at this,
 add_mod_eq_add_mod_right _⟩

theorem mod_add_cancel_left {m n k i : ℤ} :
  (i + m) % n = (i + k) % n ↔ m % n = k % n :=
by rw [add_comm, add_comm i, mod_add_cancel_right]

theorem mod_sub_cancel_right {m n k : ℤ} (i) : (m - i) % n = (k - i) % n ↔
  m % n = k % n :=
mod_add_cancel_right _

theorem mod_eq_mod_iff_mod_sub_eq_zero {m n k : ℤ} : m % n = k % n ↔ (m - k) % n = 0 :=
(mod_sub_cancel_right k).symm.trans $ by simp

@[simp] theorem mul_mod_left (a b : ℤ) : (a * b) % b = 0 :=
by rw [← zero_add (a * b), add_mul_mod_self, zero_mod]

@[simp] theorem mul_mod_right (a b : ℤ) : (a * b) % a = 0 :=
by rw [mul_comm, mul_mod_left]

lemma mul_mod (a b n : ℤ) : (a * b) % n = ((a % n) * (b % n)) % n :=
begin
  conv_lhs {
    rw [←mod_add_div a n, ←mod_add_div' b n, right_distrib, left_distrib, left_distrib,
        mul_assoc, mul_assoc, ←left_distrib n _ _, add_mul_mod_self_left, ← mul_assoc,
        add_mul_mod_self] }
end

@[simp] lemma neg_mod_two (i : ℤ) : (-i) % 2 = i % 2 :=
begin
  apply int.mod_eq_mod_iff_mod_sub_eq_zero.mpr,
  convert int.mul_mod_right 2 (-i),
  simp only [two_mul, sub_eq_add_neg]
end

local attribute [simp] -- Will be generalized to Euclidean domains.
theorem mod_self {a : ℤ} : a % a = 0 :=
by have := mul_mod_left 1 a; rwa one_mul at this

@[simp] theorem mod_mod_of_dvd (n : ℤ) {m k : ℤ} (h : m ∣ k) : n % k % m = n % m :=
begin
  conv { to_rhs, rw ←mod_add_div n k },
  rcases h with ⟨t, rfl⟩, rw [mul_assoc, add_mul_mod_self_left]
end

@[simp] theorem mod_mod (a b : ℤ) : a % b % b = a % b :=
by conv {to_rhs, rw [← mod_add_div a b, add_mul_mod_self_left]}

lemma sub_mod (a b n : ℤ) : (a - b) % n = ((a % n) - (b % n)) % n :=
begin
  apply (mod_add_cancel_right b).mp,
  rw [sub_add_cancel, ← add_mod_mod, sub_add_cancel, mod_mod]
end

/-! ### properties of `/` and `%` -/

@[simp] theorem mul_div_mul_of_pos {a : ℤ} (b c : ℤ) (H : 0 < a) : a * b / (a * c) = b / c :=
suffices ∀ (m k : ℕ) (b : ℤ), (m.succ * b / (m.succ * k) : ℤ) = b / k, from
match a, eq_succ_of_zero_lt H, c, eq_coe_or_neg c with
| ._, ⟨m, rfl⟩, ._, ⟨k, or.inl rfl⟩ := this _ _ _
| ._, ⟨m, rfl⟩, ._, ⟨k, or.inr rfl⟩ :=
  by rw [← neg_mul_eq_mul_neg, int.div_neg, int.div_neg];
     apply congr_arg has_neg.neg; apply this
end,
λ m k b, match b, k with
| (n : ℕ), k   := congr_arg of_nat (nat.mul_div_mul _ _ m.succ_pos)
| -[1+ n], 0   := by rw [int.coe_nat_zero, mul_zero, int.div_zero, int.div_zero]
| -[1+ n], k+1 := congr_arg neg_succ_of_nat $
  show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ, begin
    apply nat.div_eq_of_lt_le,
    { refine le_trans _ (nat.le_add_right _ _),
      rw [← nat.mul_div_mul _ _ m.succ_pos],
      apply nat.div_mul_le_self },
    { change m.succ * n.succ ≤ _,
      rw [mul_left_comm],
      apply nat.mul_le_mul_left,
      apply (nat.div_lt_iff_lt_mul _ _ k.succ_pos).1,
      apply nat.lt_succ_self }
  end
end

@[simp] theorem mul_div_mul_of_pos_left (a : ℤ) {b : ℤ} (H : 0 < b) (c : ℤ) :
  a * b / (c * b) = a / c :=
by rw [mul_comm, mul_comm c, mul_div_mul_of_pos _ _ H]

@[simp] theorem mul_mod_mul_of_pos {a : ℤ} (H : 0 < a) (b c : ℤ) : a * b % (a * c) = a * (b % c) :=
by rw [mod_def, mod_def, mul_div_mul_of_pos _ _ H, mul_sub_left_distrib, mul_assoc]

theorem lt_div_add_one_mul_self (a : ℤ) {b : ℤ} (H : 0 < b) : a < (a / b + 1) * b :=
by { rw [add_mul, one_mul, mul_comm, ← sub_lt_iff_lt_add', ← mod_def],
  exact mod_lt_of_pos _ H }

theorem abs_div_le_abs : ∀ (a b : ℤ), abs (a / b) ≤ abs a :=
suffices ∀ (a : ℤ) (n : ℕ), abs (a / n) ≤ abs a, from
λ a b, match b, eq_coe_or_neg b with
| ._, ⟨n, or.inl rfl⟩ := this _ _
| ._, ⟨n, or.inr rfl⟩ := by rw [int.div_neg, abs_neg]; apply this
end,
λ a n, by rw [abs_eq_nat_abs, abs_eq_nat_abs]; exact
coe_nat_le_coe_nat_of_le (match a, n with
| (m : ℕ), n := nat.div_le_self _ _
| -[1+ m], 0 := nat.zero_le _
| -[1+ m], n+1 := nat.succ_le_succ (nat.div_le_self _ _)
end)

theorem div_le_self {a : ℤ} (b : ℤ) (Ha : 0 ≤ a) : a / b ≤ a :=
by have := le_trans (le_abs_self _) (abs_div_le_abs a b);
   rwa [abs_of_nonneg Ha] at this

theorem mul_div_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : b * (a / b) = a :=
by have := mod_add_div a b; rwa [H, zero_add] at this

theorem div_mul_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : a / b * b = a :=
by rw [mul_comm, mul_div_cancel_of_mod_eq_zero H]

lemma mod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
have h : n % 2 < 2 := abs_of_nonneg (show 0 ≤ (2 : ℤ), from dec_trivial) ▸ int.mod_lt _ dec_trivial,
have h₁ : 0 ≤ n % 2 := int.mod_nonneg _ dec_trivial,
match (n % 2), h, h₁ with
| (0 : ℕ) := λ _ _, or.inl rfl
| (1 : ℕ) := λ _ _, or.inr rfl
| (k + 2 : ℕ) := λ h _, absurd h dec_trivial
| -[1+ a] := λ _ h₁, absurd h₁ dec_trivial
end

/-! ### dvd -/

@[norm_cast] theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
⟨λ ⟨a, ae⟩, m.eq_zero_or_pos.elim
  (λm0, by simp [m0] at ae; simp [ae, m0])
  (λm0l, by {
    cases eq_coe_of_zero_le (@nonneg_of_mul_nonneg_left ℤ _ m a
      (by simp [ae.symm]) (by simpa using m0l)) with k e,
    subst a, exact ⟨k, int.coe_nat_inj ae⟩ }),
 λ ⟨k, e⟩, dvd.intro k $ by rw [e, int.coe_nat_mul]⟩

theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.nat_abs :=
by rcases nat_abs_eq z with eq | eq; rw eq; simp [coe_nat_dvd]

theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.nat_abs ∣ n :=
by rcases nat_abs_eq z with eq | eq; rw eq; simp [coe_nat_dvd]

theorem dvd_antisymm {a b : ℤ} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b :=
begin
  rw [← abs_of_nonneg H1, ← abs_of_nonneg H2, abs_eq_nat_abs, abs_eq_nat_abs],
  rw [coe_nat_dvd, coe_nat_dvd, coe_nat_inj'],
  apply nat.dvd_antisymm
end

theorem dvd_of_mod_eq_zero {a b : ℤ} (H : b % a = 0) : a ∣ b :=
⟨b / a, (mul_div_cancel_of_mod_eq_zero H).symm⟩

theorem mod_eq_zero_of_dvd : ∀ {a b : ℤ}, a ∣ b → b % a = 0
| a ._ ⟨c, rfl⟩ := mul_mod_right _ _

theorem dvd_iff_mod_eq_zero (a b : ℤ) : a ∣ b ↔ b % a = 0 :=
⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

/-- If `a % b = c` then `b` divides `a - c`. -/
lemma dvd_sub_of_mod_eq {a b c : ℤ} (h : a % b = c) : b ∣ a - c :=
begin
  have hx : a % b % b = c % b, { rw h },
  rw [mod_mod, ←mod_sub_cancel_right c, sub_self, zero_mod] at hx,
  exact dvd_of_mod_eq_zero hx
end

theorem nat_abs_dvd {a b : ℤ} : (a.nat_abs : ℤ) ∣ b ↔ a ∣ b :=
(nat_abs_eq a).elim (λ e, by rw ← e) (λ e, by rw [← neg_dvd_iff_dvd, ← e])

theorem dvd_nat_abs {a b : ℤ} : a ∣ b.nat_abs ↔ a ∣ b :=
(nat_abs_eq b).elim (λ e, by rw ← e) (λ e, by rw [← dvd_neg_iff_dvd, ← e])

instance decidable_dvd : @decidable_rel ℤ (∣) :=
assume a n, decidable_of_decidable_of_iff (by apply_instance) (dvd_iff_mod_eq_zero _ _).symm

protected theorem div_mul_cancel {a b : ℤ} (H : b ∣ a) : a / b * b = a :=
div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

protected theorem mul_div_cancel' {a b : ℤ} (H : a ∣ b) : a * (b / a) = b :=
by rw [mul_comm, int.div_mul_cancel H]

protected theorem mul_div_assoc (a : ℤ) : ∀ {b c : ℤ}, c ∣ b → (a * b) / c = a * (b / c)
| ._ c ⟨d, rfl⟩ := if cz : c = 0 then by simp [cz] else
  by rw [mul_left_comm, int.mul_div_cancel_left _ cz, int.mul_div_cancel_left _ cz]

protected theorem mul_div_assoc' (b : ℤ) {a c : ℤ} (h : c ∣ a) : a * b / c = a / c * b :=
by rw [mul_comm, int.mul_div_assoc _ h, mul_comm]

theorem div_dvd_div : ∀ {a b c : ℤ} (H1 : a ∣ b) (H2 : b ∣ c), b / a ∣ c / a
| a ._ ._ ⟨b, rfl⟩ ⟨c, rfl⟩ := if az : a = 0 then by simp [az] else
  by rw [int.mul_div_cancel_left _ az, mul_assoc, int.mul_div_cancel_left _ az];
     apply dvd_mul_right

protected theorem eq_mul_of_div_eq_right {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = b * c :=
by rw [← H2, int.mul_div_cancel' H1]

protected theorem div_eq_of_eq_mul_right {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = b * c) :
  a / b = c :=
by rw [H2, int.mul_div_cancel_left _ H1]

protected theorem eq_div_of_mul_eq_right {a b c : ℤ} (H1 : a ≠ 0) (H2 : a * b = c) :
  b = c / a :=
eq.symm $ int.div_eq_of_eq_mul_right H1 H2.symm

protected theorem div_eq_iff_eq_mul_right {a b c : ℤ} (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = b * c :=
⟨int.eq_mul_of_div_eq_right H', int.div_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : ℤ} (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = c * b :=
by rw mul_comm; exact int.div_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_left {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = c * b :=
by rw [mul_comm, int.eq_mul_of_div_eq_right H1 H2]

protected theorem div_eq_of_eq_mul_left {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = c * b) :
  a / b = c :=
int.div_eq_of_eq_mul_right H1 (by rw [mul_comm, H2])

protected lemma eq_zero_of_div_eq_zero {d n : ℤ} (h : d ∣ n) (H : n / d = 0) : n = 0 :=
by rw [← int.mul_div_cancel' h, H, mul_zero]

theorem neg_div_of_dvd : ∀ {a b : ℤ} (H : b ∣ a), -a / b = -(a / b)
| ._ b ⟨c, rfl⟩ := if bz : b = 0 then by simp [bz] else
  by rw [neg_mul_eq_mul_neg, int.mul_div_cancel_left _ bz, int.mul_div_cancel_left _ bz]

lemma sub_div_of_dvd (a : ℤ) {b c : ℤ} (hcb : c ∣ b) : (a - b) / c = a / c - b / c :=
begin
  rw [sub_eq_add_neg, sub_eq_add_neg, int.add_div_of_dvd_right ((dvd_neg c b).mpr hcb)],
  congr,
  exact neg_div_of_dvd hcb,
end

lemma sub_div_of_dvd_sub {a b c : ℤ} (hcab : c ∣ (a - b)) : (a - b) / c = a / c - b / c :=
by rw [eq_sub_iff_add_eq, ← int.add_div_of_dvd_left hcab, sub_add_cancel]

theorem div_sign : ∀ a b, a / sign b = a * sign b
| a (n+1:ℕ) := by unfold sign; simp
| a 0       := by simp [sign]
| a -[1+ n] := by simp [sign]

@[simp] theorem sign_mul : ∀ a b, sign (a * b) = sign a * sign b
| a       0       := by simp
| 0       b       := by simp
| (m+1:ℕ) (n+1:ℕ) := rfl
| (m+1:ℕ) -[1+ n] := rfl
| -[1+ m] (n+1:ℕ) := rfl
| -[1+ m] -[1+ n] := rfl

protected theorem sign_eq_div_abs (a : ℤ) : sign a = a / (abs a) :=
if az : a = 0 then by simp [az] else
(int.div_eq_of_eq_mul_left (mt abs_eq_zero.1 az)
  (sign_mul_abs _).symm).symm

theorem mul_sign : ∀ (i : ℤ), i * sign i = nat_abs i
| (n+1:ℕ) := mul_one _
| 0       := mul_zero _
| -[1+ n] := mul_neg_one _

@[simp]
theorem sign_pow_bit1 (k : ℕ) : ∀ n : ℤ, n.sign ^ (bit1 k) = n.sign
| (n+1:ℕ) := one_pow (bit1 k)
| 0       := zero_pow (nat.zero_lt_bit1 k)
| -[1+ n] := (neg_pow_bit1 1 k).trans (congr_arg (λ x, -x) (one_pow (bit1 k)))

theorem le_of_dvd {a b : ℤ} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
match a, b, eq_succ_of_zero_lt bpos, H with
| (m : ℕ), ._, ⟨n, rfl⟩, H := coe_nat_le_coe_nat_of_le $
  nat.le_of_dvd n.succ_pos $ coe_nat_dvd.1 H
| -[1+ m], ._, ⟨n, rfl⟩, _ :=
  le_trans (le_of_lt $ neg_succ_lt_zero _) (coe_zero_le _)
end

theorem eq_one_of_dvd_one {a : ℤ} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
match a, eq_coe_of_zero_le H, H' with
| ._, ⟨n, rfl⟩, H' := congr_arg coe $
  nat.eq_one_of_dvd_one $ coe_nat_dvd.1 H'
end

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
eq_one_of_dvd_one H ⟨b, H'.symm⟩

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (by rw [mul_comm, H'])

lemma of_nat_dvd_of_dvd_nat_abs {a : ℕ} : ∀ {z : ℤ} (haz : a ∣ z.nat_abs), ↑a ∣ z
| (int.of_nat _) haz := int.coe_nat_dvd.2 haz
| -[1+k] haz :=
  begin
    change ↑a ∣ -(k+1 : ℤ),
    apply dvd_neg_of_dvd,
    apply int.coe_nat_dvd.2,
    exact haz
  end

lemma dvd_nat_abs_of_of_nat_dvd {a : ℕ} : ∀ {z : ℤ} (haz : ↑a ∣ z), a ∣ z.nat_abs
| (int.of_nat _) haz := int.coe_nat_dvd.1 (int.dvd_nat_abs.2 haz)
| -[1+k] haz :=
  have haz' : (↑a:ℤ) ∣ (↑(k+1):ℤ), from dvd_of_dvd_neg haz,
  int.coe_nat_dvd.1 haz'

lemma pow_dvd_of_le_of_pow_dvd {p m n : ℕ} {k : ℤ} (hmn : m ≤ n) (hdiv : ↑(p ^ n) ∣ k) :
  ↑(p ^ m) ∣ k :=
begin
  induction k,
  { apply int.coe_nat_dvd.2,
    apply pow_dvd_of_le_of_pow_dvd hmn,
    apply int.coe_nat_dvd.1 hdiv },
  change -[1+k] with -(↑(k+1) : ℤ),
  apply dvd_neg_of_dvd,
  apply int.coe_nat_dvd.2,
  apply pow_dvd_of_le_of_pow_dvd hmn,
  apply int.coe_nat_dvd.1,
  apply dvd_of_dvd_neg,
  exact hdiv,
end

lemma dvd_of_pow_dvd {p k : ℕ} {m : ℤ} (hk : 1 ≤ k) (hpk : ↑(p^k) ∣ m) : ↑p ∣ m :=
by rw ←pow_one p; exact pow_dvd_of_le_of_pow_dvd hk hpk

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) {n : ℤ} (hn : 0 < n) :
  (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬ n ∣ m :=
begin
  split,
  { rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩, rw [mul_lt_mul_left hn] at h1k h2k,
    rw [lt_add_one_iff, ← not_lt] at h2k, exact h2k h1k },
  { intro h, rw [dvd_iff_mod_eq_zero, ← ne.def] at h,
    have := (mod_nonneg m hn.ne.symm).lt_of_ne h.symm,
    simp only [← mod_add_div m n] {single_pass := tt},
    refine ⟨m / n, lt_add_of_pos_left _ this, _⟩,
    rw [add_comm _ (1 : ℤ), left_distrib, mul_one], exact add_lt_add_right (mod_lt_of_pos _ hn) _ }
end

/-! ### `/` and ordering -/

protected theorem div_mul_le (a : ℤ) {b : ℤ} (H : b ≠ 0) : a / b * b ≤ a :=
le_of_sub_nonneg $ by rw [mul_comm, ← mod_def]; apply mod_nonneg _ H

protected theorem div_le_of_le_mul {a b c : ℤ} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b :=
le_of_mul_le_mul_right (le_trans (int.div_mul_le _ (ne_of_gt H)) H') H

protected theorem mul_lt_of_lt_div {a b c : ℤ} (H : 0 < c) (H3 : a < b / c) : a * c < b :=
lt_of_not_ge $ mt (int.div_le_of_le_mul H) (not_le_of_gt H3)

protected theorem mul_le_of_le_div {a b c : ℤ} (H1 : 0 < c) (H2 : a ≤ b / c) : a * c ≤ b :=
le_trans (decidable.mul_le_mul_of_nonneg_right H2 (le_of_lt H1)) (int.div_mul_le _ (ne_of_gt H1))

protected theorem le_div_of_mul_le {a b c : ℤ} (H1 : 0 < c) (H2 : a * c ≤ b) : a ≤ b / c :=
le_of_lt_add_one $ lt_of_mul_lt_mul_right
  (lt_of_le_of_lt H2 (lt_div_add_one_mul_self _ H1)) (le_of_lt H1)

protected theorem le_div_iff_mul_le {a b c : ℤ} (H : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
⟨int.mul_le_of_le_div H, int.le_div_of_mul_le H⟩

protected theorem div_le_div {a b c : ℤ} (H : 0 < c) (H' : a ≤ b) : a / c ≤ b / c :=
int.le_div_of_mul_le H (le_trans (int.div_mul_le _ (ne_of_gt H)) H')

protected theorem div_lt_of_lt_mul {a b c : ℤ} (H : 0 < c) (H' : a < b * c) : a / c < b :=
lt_of_not_ge $ mt (int.mul_le_of_le_div H) (not_le_of_gt H')

protected theorem lt_mul_of_div_lt {a b c : ℤ} (H1 : 0 < c) (H2 : a / c < b) : a < b * c :=
lt_of_not_ge $ mt (int.le_div_of_mul_le H1) (not_le_of_gt H2)

protected theorem div_lt_iff_lt_mul {a b c : ℤ} (H : 0 < c) : a / c < b ↔ a < b * c :=
⟨int.lt_mul_of_div_lt H, int.div_lt_of_lt_mul H⟩

protected theorem le_mul_of_div_le {a b c : ℤ} (H1 : 0 ≤ b) (H2 : b ∣ a) (H3 : a / b ≤ c) :
  a ≤ c * b :=
by rw [← int.div_mul_cancel H2]; exact decidable.mul_le_mul_of_nonneg_right H3 H1

protected theorem lt_div_of_mul_lt {a b c : ℤ} (H1 : 0 ≤ b) (H2 : b ∣ c) (H3 : a * b < c) :
  a < c / b :=
lt_of_not_ge $ mt (int.le_mul_of_div_le H1 H2) (not_le_of_gt H3)

protected theorem lt_div_iff_mul_lt {a b : ℤ} (c : ℤ) (H : 0 < c) (H' : c ∣ b) :
  a < b / c ↔ a * c < b :=
⟨int.mul_lt_of_lt_div H, int.lt_div_of_mul_lt (le_of_lt H) H'⟩

theorem div_pos_of_pos_of_dvd {a b : ℤ} (H1 : 0 < a) (H2 : 0 ≤ b) (H3 : b ∣ a) : 0 < a / b :=
int.lt_div_of_mul_lt H2 H3 (by rwa zero_mul)

theorem div_eq_div_of_mul_eq_mul {a b c d : ℤ} (H2 : d ∣ c) (H3 : b ≠ 0)
    (H4 : d ≠ 0) (H5 : a * d = b * c) :
  a / b = c / d :=
int.div_eq_of_eq_mul_right H3 $
by rw [← int.mul_div_assoc _ H2]; exact
(int.div_eq_of_eq_mul_left H4 H5.symm).symm

theorem eq_mul_div_of_mul_eq_mul_of_dvd_left {a b c d : ℤ} (hb : b ≠ 0) (hbc : b ∣ c)
    (h : b * a = c * d) :
  a = c / b * d :=
begin
  cases hbc with k hk,
  subst hk,
  rw [int.mul_div_cancel_left _ hb],
  rw mul_assoc at h,
  apply mul_left_cancel' hb h
end

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
lemma eq_zero_of_dvd_of_nat_abs_lt_nat_abs {a b : ℤ} (w : a ∣ b) (h : nat_abs b < nat_abs a) :
  b = 0 :=
begin
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at w,
  rw ←nat_abs_eq_zero,
  exact eq_zero_of_dvd_of_lt w h
end

lemma eq_zero_of_dvd_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
eq_zero_of_dvd_of_nat_abs_lt_nat_abs h (nat_abs_lt_nat_abs_of_nonneg_of_lt w₁ w₂)

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
lemma eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs {a b c : ℤ} (h1 : a % b = c)
    (h2 : nat_abs (a - c) < nat_abs b) :
  a = c :=
eq_of_sub_eq_zero (eq_zero_of_dvd_of_nat_abs_lt_nat_abs (dvd_sub_of_mod_eq h1) h2)

theorem of_nat_add_neg_succ_of_nat_of_lt {m n : ℕ} (h : m < n.succ) :
  of_nat m + -[1+n] = -[1+ n - m] :=
begin
  change sub_nat_nat _ _ = _,
  have h' : n.succ - m = (n - m).succ,
  apply succ_sub,
  apply le_of_lt_succ h,
  simp [*, sub_nat_nat]
end

theorem of_nat_add_neg_succ_of_nat_of_ge {m n : ℕ}
  (h : n.succ ≤ m) : of_nat m + -[1+n] = of_nat (m - n.succ) :=
begin
  change sub_nat_nat _ _ = _,
  have h' : n.succ - m = 0,
  apply sub_eq_zero_of_le h,
  simp [*, sub_nat_nat]
end

@[simp] theorem neg_add_neg (m n : ℕ) : -[1+m] + -[1+n] = -[1+nat.succ(m+n)] := rfl

/-! ### to_nat -/

theorem to_nat_eq_max : ∀ (a : ℤ), (to_nat a : ℤ) = max a 0
| (n : ℕ) := (max_eq_left (coe_zero_le n)).symm
| -[1+ n] := (max_eq_right (le_of_lt (neg_succ_lt_zero n))).symm

@[simp] lemma to_nat_zero : (0 : ℤ).to_nat = 0 := rfl

@[simp] lemma to_nat_one : (1 : ℤ).to_nat = 1 := rfl

@[simp] theorem to_nat_of_nonneg {a : ℤ} (h : 0 ≤ a) : (to_nat a : ℤ) = a :=
by rw [to_nat_eq_max, max_eq_left h]

@[simp] lemma to_nat_sub_of_le {a b : ℤ} (h : b ≤ a) : (to_nat (a - b) : ℤ) = a - b :=
int.to_nat_of_nonneg (sub_nonneg_of_le h)

@[simp] theorem to_nat_coe_nat (n : ℕ) : to_nat ↑n = n := rfl

@[simp] lemma to_nat_coe_nat_add_one {n : ℕ} : ((n : ℤ) + 1).to_nat = n + 1 := rfl

theorem le_to_nat (a : ℤ) : a ≤ to_nat a :=
by rw [to_nat_eq_max]; apply le_max_left

@[simp] theorem to_nat_le {a : ℤ} {n : ℕ} : to_nat a ≤ n ↔ a ≤ n :=
by rw [(coe_nat_le_coe_nat_iff _ _).symm, to_nat_eq_max, max_le_iff];
   exact and_iff_left (coe_zero_le _)

@[simp] theorem lt_to_nat {n : ℕ} {a : ℤ} : n < to_nat a ↔ (n : ℤ) < a :=
le_iff_le_iff_lt_iff_lt.1 to_nat_le

theorem to_nat_le_to_nat {a b : ℤ} (h : a ≤ b) : to_nat a ≤ to_nat b :=
by rw to_nat_le; exact le_trans h (le_to_nat b)

theorem to_nat_lt_to_nat {a b : ℤ} (hb : 0 < b) : to_nat a < to_nat b ↔ a < b :=
⟨λ h, begin cases a, exact lt_to_nat.1 h, exact lt_trans (neg_succ_of_nat_lt_zero a) hb, end,
 λ h, begin rw lt_to_nat, cases a, exact h, exact hb end⟩

theorem lt_of_to_nat_lt {a b : ℤ} (h : to_nat a < to_nat b) : a < b :=
(to_nat_lt_to_nat $ lt_to_nat.1 $ lt_of_le_of_lt (nat.zero_le _) h).1 h

lemma to_nat_add {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  (a + b).to_nat = a.to_nat + b.to_nat :=
begin
  lift a to ℕ using ha,
  lift b to ℕ using hb,
  norm_cast,
end

lemma to_nat_add_nat {a : ℤ} (ha : 0 ≤ a) (n : ℕ) : (a + n).to_nat = a.to_nat + n :=
begin
  lift a to ℕ using ha,
  norm_cast,
end

@[simp]
lemma pred_to_nat : ∀ (i : ℤ), (i - 1).to_nat = i.to_nat - 1
| (0:ℕ)   := rfl
| (n+1:ℕ) := by simp
| -[1+ n] := rfl

@[simp]
lemma to_nat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.to_nat - 1 : ℕ) : ℤ) = i - 1 :=
by simp [h, le_of_lt h] with push_cast

@[simp] lemma to_nat_sub_to_nat_neg : ∀ (n : ℤ), ↑n.to_nat - ↑((-n).to_nat) = n
| (0 : ℕ)   := rfl
| (n+1 : ℕ) := show ↑(n+1) - (0:ℤ) = n+1, from sub_zero _
| -[1+ n]   := show 0 - (n+1 : ℤ)  = _,   from zero_sub _

@[simp] lemma to_nat_add_to_nat_neg_eq_nat_abs : ∀ (n : ℤ), (n.to_nat) + ((-n).to_nat) = n.nat_abs
| (0 : ℕ)   := rfl
| (n+1 : ℕ) := show (n+1) + 0 = n+1, from add_zero _
| -[1+ n]   := show 0 + (n+1) = n+1, from zero_add _

/-- If `n : ℕ`, then `int.to_nat' n = some n`, if `n : ℤ` is negative, then `int.to_nat' n = none`.
-/
def to_nat' : ℤ → option ℕ
| (n : ℕ) := some n
| -[1+ n] := none

theorem mem_to_nat' : ∀ (a : ℤ) (n : ℕ), n ∈ to_nat' a ↔ a = n
| (m : ℕ) n := option.some_inj.trans coe_nat_inj'.symm
| -[1+ m] n := by split; intro h; cases h

lemma to_nat_of_nonpos : ∀ {z : ℤ}, z ≤ 0 → z.to_nat = 0
| (0 : ℕ)     := λ _, rfl
| (n + 1 : ℕ) := λ h, (h.not_lt (by { exact_mod_cast nat.succ_pos n })).elim
| (-[1+ n])  := λ _, rfl

/-! ### units -/

@[simp] theorem units_nat_abs (u : units ℤ) : nat_abs u = 1 :=
units.ext_iff.1 $ nat.units_eq_one ⟨nat_abs u, nat_abs ↑u⁻¹,
  by rw [← nat_abs_mul, units.mul_inv]; refl,
  by rw [← nat_abs_mul, units.inv_mul]; refl⟩

theorem units_eq_one_or (u : units ℤ) : u = 1 ∨ u = -1 :=
by simpa only [units.ext_iff, units_nat_abs] using nat_abs_eq u

lemma is_unit_eq_one_or {a : ℤ} : is_unit a → a = 1 ∨ a = -1
| ⟨x, hx⟩ := hx ▸ (units_eq_one_or _).imp (congr_arg coe) (congr_arg coe)

lemma is_unit_iff {a : ℤ} : is_unit a ↔ a = 1 ∨ a = -1 :=
begin
  refine ⟨λ h, is_unit_eq_one_or h, λ h, _⟩,
  rcases h with rfl | rfl,
  { exact is_unit_one },
  { exact is_unit_one.neg }
end

theorem is_unit_iff_nat_abs_eq {n : ℤ} : is_unit n ↔ n.nat_abs = 1 :=
by simp [nat_abs_eq_iff, is_unit_iff]

lemma units_inv_eq_self (u : units ℤ) : u⁻¹ = u :=
(units_eq_one_or u).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

@[simp] lemma units_mul_self (u : units ℤ) : u * u = 1 :=
(units_eq_one_or u).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

-- `units.coe_mul` is a "wrong turn" for the simplifier, this undoes it and simplifies further
@[simp] lemma units_coe_mul_self (u : units ℤ) : (u * u : ℤ) = 1 :=
by rw [←units.coe_mul, units_mul_self, units.coe_one]

@[simp] lemma neg_one_pow_ne_zero {n : ℕ} : (-1 : ℤ)^n ≠ 0 :=
pow_ne_zero _ (abs_pos.mp trivial)

/-! ### bitwise ops -/

@[simp] lemma bodd_zero : bodd 0 = ff := rfl
@[simp] lemma bodd_one : bodd 1 = tt := rfl
lemma bodd_two : bodd 2 = ff := rfl

@[simp, norm_cast] lemma bodd_coe (n : ℕ) : int.bodd n = nat.bodd n := rfl

@[simp] lemma bodd_sub_nat_nat (m n : ℕ) : bodd (sub_nat_nat m n) = bxor m.bodd n.bodd :=
by apply sub_nat_nat_elim m n (λ m n i, bodd i = bxor m.bodd n.bodd); intros;
  simp; cases i.bodd; simp

@[simp] lemma bodd_neg_of_nat (n : ℕ) : bodd (neg_of_nat n) = n.bodd :=
by cases n; simp; refl

@[simp] lemma bodd_neg (n : ℤ) : bodd (-n) = bodd n :=
by cases n; simp [has_neg.neg, int.coe_nat_eq, int.neg, bodd, -of_nat_eq_coe]

@[simp] lemma bodd_add (m n : ℤ) : bodd (m + n) = bxor (bodd m) (bodd n) :=
by cases m with m m; cases n with n n; unfold has_add.add;
  simp [int.add, -of_nat_eq_coe, bool.bxor_comm]

@[simp] lemma bodd_mul (m n : ℤ) : bodd (m * n) = bodd m && bodd n :=
by cases m with m m; cases n with n n;
  simp [← int.mul_def, int.mul, -of_nat_eq_coe, bool.bxor_comm]

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
| (n : ℕ) :=
  by rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ),
         by cases bodd n; refl]; exact congr_arg of_nat n.bodd_add_div2
| -[1+ n] := begin
    refine eq.trans _ (congr_arg neg_succ_of_nat n.bodd_add_div2),
    dsimp [bodd], cases nat.bodd n; dsimp [cond, bnot, div2, int.mul],
    { change -[1+ 2 * nat.div2 n] = _, rw zero_add },
    { rw [zero_add, add_comm], refl }
  end

theorem div2_val : ∀ n, div2 n = n / 2
| (n : ℕ) := congr_arg of_nat n.div2_val
| -[1+ n] := congr_arg neg_succ_of_nat n.div2_val

lemma bit0_val (n : ℤ) : bit0 n = 2 * n := (two_mul _).symm

lemma bit1_val (n : ℤ) : bit1 n = 2 * n + 1 := congr_arg (+(1:ℤ)) (bit0_val _)

lemma bit_val (b n) : bit b n = 2 * n + cond b 1 0 :=
by { cases b, apply (bit0_val n).trans (add_zero _).symm, apply bit1_val }

lemma bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
(bit_val _ _).trans $ (add_comm _ _).trans $ bodd_add_div2 _

/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
def {u} bit_cases_on {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n :=
by rw [← bit_decomp n]; apply h

@[simp] lemma bit_zero : bit ff 0 = 0 := rfl

@[simp] lemma bit_coe_nat (b) (n : ℕ) : bit b n = nat.bit b n :=
by rw [bit_val, nat.bit_val]; cases b; refl

@[simp] lemma bit_neg_succ (b) (n : ℕ) : bit b -[1+ n] = -[1+ nat.bit (bnot b) n] :=
by rw [bit_val, nat.bit_val]; cases b; refl

@[simp] lemma bodd_bit (b n) : bodd (bit b n) = b :=
by rw bit_val; simp; cases b; cases bodd n; refl

@[simp] lemma bodd_bit0 (n : ℤ) : bodd (bit0 n) = ff := bodd_bit ff n

@[simp] lemma bodd_bit1 (n : ℤ) : bodd (bit1 n) = tt := bodd_bit tt n

@[simp] lemma div2_bit (b n) : div2 (bit b n) = n :=
begin
  rw [bit_val, div2_val, add_comm, int.add_mul_div_left, (_ : (_/2:ℤ) = 0), zero_add],
  cases b,
  { simp },
  { show of_nat _ = _, rw nat.div_eq_zero; simp },
  { cc }
end

lemma bit0_ne_bit1 (m n : ℤ) : bit0 m ≠ bit1 n :=
mt (congr_arg bodd) $ by simp

lemma bit1_ne_bit0 (m n : ℤ) : bit1 m ≠ bit0 n :=
(bit0_ne_bit1 _ _).symm

lemma bit1_ne_zero (m : ℤ) : bit1 m ≠ 0 :=
by simpa only [bit0_zero] using bit1_ne_bit0 m 0

@[simp] lemma test_bit_zero (b) : ∀ n, test_bit (bit b n) 0 = b
| (n : ℕ) := by rw [bit_coe_nat]; apply nat.test_bit_zero
| -[1+ n] := by rw [bit_neg_succ]; dsimp [test_bit]; rw [nat.test_bit_zero];
                clear test_bit_zero; cases b; refl

@[simp] lemma test_bit_succ (m b) : ∀ n, test_bit (bit b n) (nat.succ m) = test_bit n m
| (n : ℕ) := by rw [bit_coe_nat]; apply nat.test_bit_succ
| -[1+ n] := by rw [bit_neg_succ]; dsimp [test_bit]; rw [nat.test_bit_succ]

private meta def bitwise_tac : tactic unit := `[
  funext m,
  funext n,
  cases m with m m; cases n with n n; try {refl},
  all_goals {
    apply congr_arg of_nat <|> apply congr_arg neg_succ_of_nat,
    try {dsimp [nat.land, nat.ldiff, nat.lor]},
    try {rw [
      show nat.bitwise (λ a b, a && bnot b) n m =
           nat.bitwise (λ a b, b && bnot a) m n, from
      congr_fun (congr_fun (@nat.bitwise_swap (λ a b, b && bnot a) rfl) n) m]},
    apply congr_arg (λ f, nat.bitwise f m n),
    funext a,
    funext b,
    cases a; cases b; refl
  },
  all_goals {unfold nat.land nat.ldiff nat.lor}
]

theorem bitwise_or   : bitwise bor                  = lor   := by bitwise_tac
theorem bitwise_and  : bitwise band                 = land  := by bitwise_tac
theorem bitwise_diff : bitwise (λ a b, a && bnot b) = ldiff := by bitwise_tac
theorem bitwise_xor  : bitwise bxor                 = lxor  := by bitwise_tac

@[simp] lemma bitwise_bit (f : bool → bool → bool) (a m b n) :
  bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
begin
  cases m with m m; cases n with n n;
  repeat { rw [← int.coe_nat_eq] <|> rw bit_coe_nat <|> rw bit_neg_succ };
  unfold bitwise nat_bitwise bnot;
  [ induction h : f ff ff,
    induction h : f ff tt,
    induction h : f tt ff,
    induction h : f tt tt ],
  all_goals {
    unfold cond, rw nat.bitwise_bit,
    repeat { rw bit_coe_nat <|> rw bit_neg_succ <|> rw bnot_bnot } },
  all_goals { unfold bnot {fail_if_unchanged := ff}; rw h; refl }
end

@[simp] lemma lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
by rw [← bitwise_or, bitwise_bit]

@[simp] lemma land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) :=
by rw [← bitwise_and, bitwise_bit]

@[simp] lemma ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) :=
by rw [← bitwise_diff, bitwise_bit]

@[simp] lemma lxor_bit (a m b n) : lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) :=
by rw [← bitwise_xor, bitwise_bit]

@[simp] lemma lnot_bit (b) : ∀ n, lnot (bit b n) = bit (bnot b) (lnot n)
| (n : ℕ) := by simp [lnot]
| -[1+ n] := by simp [lnot]

@[simp] lemma test_bit_bitwise (f : bool → bool → bool) (m n k) :
  test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) :=
begin
  induction k with k IH generalizing m n;
  apply bit_cases_on m; intros a m';
  apply bit_cases_on n; intros b n';
  rw bitwise_bit,
  { simp [test_bit_zero] },
  { simp [test_bit_succ, IH] }
end

@[simp] lemma test_bit_lor (m n k) : test_bit (lor m n) k = test_bit m k || test_bit n k :=
by rw [← bitwise_or, test_bit_bitwise]

@[simp] lemma test_bit_land (m n k) : test_bit (land m n) k = test_bit m k && test_bit n k :=
by rw [← bitwise_and, test_bit_bitwise]

@[simp]
lemma test_bit_ldiff (m n k) : test_bit (ldiff m n) k = test_bit m k && bnot (test_bit n k) :=
by rw [← bitwise_diff, test_bit_bitwise]

@[simp] lemma test_bit_lxor (m n k) : test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) :=
by rw [← bitwise_xor, test_bit_bitwise]

@[simp] lemma test_bit_lnot : ∀ n k, test_bit (lnot n) k = bnot (test_bit n k)
| (n : ℕ) k := by simp [lnot, test_bit]
| -[1+ n] k := by simp [lnot, test_bit]

lemma shiftl_add : ∀ (m : ℤ) (n : ℕ) (k : ℤ), shiftl m (n + k) = shiftl (shiftl m n) k
| (m : ℕ) n (k:ℕ) := congr_arg of_nat (nat.shiftl_add _ _ _)
| -[1+ m] n (k:ℕ) := congr_arg neg_succ_of_nat (nat.shiftl'_add _ _ _ _)
| (m : ℕ) n -[1+k] := sub_nat_nat_elim n k.succ
    (λ n k i, shiftl ↑m i = nat.shiftr (nat.shiftl m n) k)
    (λ i n, congr_arg coe $
      by rw [← nat.shiftl_sub, nat.add_sub_cancel_left]; apply nat.le_add_right)
    (λ i n, congr_arg coe $
      by rw [add_assoc, nat.shiftr_add, ← nat.shiftl_sub, nat.sub_self]; refl)
| -[1+ m] n -[1+k] := sub_nat_nat_elim n k.succ
    (λ n k i, shiftl -[1+ m] i = -[1+ nat.shiftr (nat.shiftl' tt m n) k])
    (λ i n, congr_arg neg_succ_of_nat $
      by rw [← nat.shiftl'_sub, nat.add_sub_cancel_left]; apply nat.le_add_right)
    (λ i n, congr_arg neg_succ_of_nat $
      by rw [add_assoc, nat.shiftr_add, ← nat.shiftl'_sub, nat.sub_self]; refl)

lemma shiftl_sub (m : ℤ) (n : ℕ) (k : ℤ) : shiftl m (n - k) = shiftr (shiftl m n) k :=
shiftl_add _ _ _

@[simp] lemma shiftl_neg (m n : ℤ) : shiftl m (-n) = shiftr m n := rfl
@[simp] lemma shiftr_neg (m n : ℤ) : shiftr m (-n) = shiftl m n := by rw [← shiftl_neg, neg_neg]

@[simp] lemma shiftl_coe_nat (m n : ℕ) : shiftl m n = nat.shiftl m n := rfl
@[simp] lemma shiftr_coe_nat (m n : ℕ) : shiftr m n = nat.shiftr m n := by cases n; refl

@[simp] lemma shiftl_neg_succ (m n : ℕ) : shiftl -[1+ m] n = -[1+ nat.shiftl' tt m n] := rfl
@[simp]
lemma shiftr_neg_succ (m n : ℕ) : shiftr -[1+ m] n = -[1+ nat.shiftr m n] := by cases n; refl

lemma shiftr_add : ∀ (m : ℤ) (n k : ℕ), shiftr m (n + k) = shiftr (shiftr m n) k
| (m : ℕ) n k := by rw [shiftr_coe_nat, shiftr_coe_nat,
                        ← int.coe_nat_add, shiftr_coe_nat, nat.shiftr_add]
| -[1+ m] n k := by rw [shiftr_neg_succ, shiftr_neg_succ,
                        ← int.coe_nat_add, shiftr_neg_succ, nat.shiftr_add]

lemma shiftl_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), shiftl m n = m * ↑(2 ^ n)
| (m : ℕ) n := congr_arg coe (nat.shiftl_eq_mul_pow _ _)
| -[1+ m] n := @congr_arg ℕ ℤ _ _ (λi, -i) (nat.shiftl'_tt_eq_mul_pow _ _)

lemma shiftr_eq_div_pow : ∀ (m : ℤ) (n : ℕ), shiftr m n = m / ↑(2 ^ n)
| (m : ℕ) n := by rw shiftr_coe_nat; exact congr_arg coe (nat.shiftr_eq_div_pow _ _)
| -[1+ m] n := begin
  rw [shiftr_neg_succ, neg_succ_of_nat_div, nat.shiftr_eq_div_pow], refl,
  exact coe_nat_lt_coe_nat_of_lt (pow_pos dec_trivial _)
end

lemma one_shiftl (n : ℕ) : shiftl 1 n = (2 ^ n : ℕ) :=
congr_arg coe (nat.one_shiftl _)

@[simp] lemma zero_shiftl : ∀ n : ℤ, shiftl 0 n = 0
| (n : ℕ) := congr_arg coe (nat.zero_shiftl _)
| -[1+ n] := congr_arg coe (nat.zero_shiftr _)

@[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 := zero_shiftl _

/-! ### Least upper bound property for integers -/

/-- A computable version of `exists_least_of_bdd`: given a decidable predicate on the
integers, with an explicit lower bound and a proof that it is somewhere true, return
the least value for which the predicate is true. -/
def least_of_bdd {P : ℤ → Prop} [decidable_pred P]
  (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z) (Hinh : ∃ z : ℤ, P z) :
  {lb : ℤ // P lb ∧ (∀ z : ℤ, P z → lb ≤ z)} :=
have EX : ∃ n : ℕ, P (b + n), from
  let ⟨elt, Helt⟩ := Hinh in
  match elt, le.dest (Hb _ Helt), Helt with
  | ._, ⟨n, rfl⟩, Hn := ⟨n, Hn⟩
  end,
⟨b + (nat.find EX : ℤ), nat.find_spec EX, λ z h,
  match z, le.dest (Hb _ h), h with
  | ._, ⟨n, rfl⟩, h := add_le_add_left
    (int.coe_nat_le.2 $ nat.find_min' _ h) _
  end⟩

theorem exists_least_of_bdd {P : ℤ → Prop}
  (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → b ≤ z) (Hinh : ∃ z : ℤ, P z) :
  ∃ lb : ℤ, P lb ∧ (∀ z : ℤ, P z → lb ≤ z) :=
by classical; exact let ⟨b, Hb⟩ := Hbdd, ⟨lb, H⟩ := least_of_bdd b Hb Hinh in ⟨lb, H⟩

/-- A computable version of `exists_greatest_of_bdd`: given a decidable predicate on the
integers, with an explicit upper bound and a proof that it is somewhere true, return
the greatest value for which the predicate is true. -/
def greatest_of_bdd {P : ℤ → Prop} [decidable_pred P]
  (b : ℤ) (Hb : ∀ z : ℤ, P z → z ≤ b) (Hinh : ∃ z : ℤ, P z) :
  {ub : ℤ // P ub ∧ (∀ z : ℤ, P z → z ≤ ub)} :=
have Hbdd' : ∀ (z : ℤ), P (-z) → -b ≤ z, from λ z h, neg_le.1 (Hb _ h),
have Hinh' : ∃ z : ℤ, P (-z), from
let ⟨elt, Helt⟩ := Hinh in ⟨-elt, by rw [neg_neg]; exact Helt⟩,
let ⟨lb, Plb, al⟩ := least_of_bdd (-b) Hbdd' Hinh' in
⟨-lb, Plb, λ z h, le_neg.1 $ al _ $ by rwa neg_neg⟩

theorem exists_greatest_of_bdd {P : ℤ → Prop}
  (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → z ≤ b) (Hinh : ∃ z : ℤ, P z) :
  ∃ ub : ℤ, P ub ∧ (∀ z : ℤ, P z → z ≤ ub) :=
by classical; exact let ⟨b, Hb⟩ := Hbdd, ⟨lb, H⟩ := greatest_of_bdd b Hb Hinh in ⟨lb, H⟩

end int

attribute [irreducible] int.nonneg
