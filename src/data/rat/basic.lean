/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.int.sqrt
import data.equiv.encodable
import algebra.group
import algebra.euclidean_domain
import algebra.ordered_field

/-!
# Basics for the Rational Numbers

## Summary

We define a rational number `q` as a structure `{ num, denom, pos, cop }`, where
- `num` is the numerator of `q`,
- `denom` is the denominator of `q`,
- `pos` is a proof that `denom > 0`, and
- `cop` is a proof `num` and `denom` are coprime.

We then define the expected (discrete) field structure on `ℚ` and prove basic lemmas about it.
Moreoever, we provide the expected casts from `ℕ` and `ℤ` into `ℚ`, i.e. `(↑n : ℚ) = n / 1`.

## Main Definitions

- `rat` is the structure encoding `ℚ`.
- `rat.mk n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

/-- `rat`, or `ℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure rat := mk' ::
(num : ℤ)
(denom : ℕ)
(pos : 0 < denom)
(cop : num.nat_abs.coprime denom)
notation `ℚ` := rat

namespace rat

protected def repr : ℚ → string
| ⟨n, d, _, _⟩ := if d = 1 then _root_.repr n else
  _root_.repr n ++ "/" ++ _root_.repr d

instance : has_repr ℚ := ⟨rat.repr⟩
instance : has_to_string ℚ := ⟨rat.repr⟩
meta instance : has_to_format ℚ := ⟨coe ∘ rat.repr⟩

instance : encodable ℚ := encodable.of_equiv (Σ n : ℤ, {d : ℕ // 0 < d ∧ n.nat_abs.coprime d})
  ⟨λ ⟨a, b, c, d⟩, ⟨a, b, c, d⟩, λ⟨a, b, c, d⟩, ⟨a, b, c, d⟩,
   λ ⟨a, b, c, d⟩, rfl, λ⟨a, b, c, d⟩, rfl⟩

/-- Embed an integer as a rational number -/
def of_int (n : ℤ) : ℚ :=
⟨n, 1, nat.one_pos, nat.coprime_one_right _⟩

instance : has_zero ℚ := ⟨of_int 0⟩
instance : has_one ℚ := ⟨of_int 1⟩
instance : inhabited ℚ := ⟨0⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ+` (not necessarily coprime) -/
def mk_pnat (n : ℤ) : ℕ+ → ℚ | ⟨d, dpos⟩ :=
let n' := n.nat_abs, g := n'.gcd d in
⟨n / g, d / g, begin
  apply (nat.le_div_iff_mul_le _ _ (nat.gcd_pos_of_pos_right _ dpos)).2,
  simp, exact nat.le_of_dvd dpos (nat.gcd_dvd_right _ _)
end, begin
  have : int.nat_abs (n / ↑g) = n' / g,
  { cases int.nat_abs_eq n with e e; rw e, { refl },
    rw [int.neg_div_of_dvd, int.nat_abs_neg], { refl },
    exact int.coe_nat_dvd.2 (nat.gcd_dvd_left _ _) },
  rw this,
  exact nat.coprime_div_gcd_div_gcd (nat.gcd_pos_of_pos_right _ dpos)
end⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ`. In the case `d = 0`, we
  define `n / 0 = 0` by convention. -/
def mk_nat (n : ℤ) (d : ℕ) : ℚ :=
if d0 : d = 0 then 0 else mk_pnat n ⟨d, nat.pos_of_ne_zero d0⟩

/-- Form the quotient `n / d` where `n d : ℤ`. -/
def mk : ℤ → ℤ → ℚ
| n (d : ℕ) := mk_nat n d
| n -[1+ d] := mk_pnat (-n) d.succ_pnat

localized "infix ` /. `:70 := rat.mk" in rat

theorem mk_pnat_eq (n d h) : mk_pnat n ⟨d, h⟩ = n /. d :=
by change n /. d with dite _ _ _; simp [ne_of_gt h]

theorem mk_nat_eq (n d) : mk_nat n d = n /. d := rfl

@[simp] theorem mk_zero (n) : n /. 0 = 0 := rfl

@[simp] theorem zero_mk_pnat (n) : mk_pnat 0 n = 0 :=
by cases n; simp [mk_pnat]; change int.nat_abs 0 with 0; simp *; refl

@[simp] theorem zero_mk_nat (n) : mk_nat 0 n = 0 :=
by by_cases n = 0; simp [*, mk_nat]

@[simp] theorem zero_mk (n) : 0 /. n = 0 :=
by cases n; simp [mk]

private lemma gcd_abs_dvd_left {a b} : (nat.gcd (int.nat_abs a) b : ℤ) ∣ a :=
int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ nat.gcd_dvd_left (int.nat_abs a) b

@[simp] theorem mk_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 :=
begin
  constructor; intro h; [skip, {subst a, simp}],
  have : ∀ {a b}, mk_pnat a b = 0 → a = 0,
  { intros a b e, cases b with b h,
    injection e with e,
    apply int.eq_mul_of_div_eq_right gcd_abs_dvd_left e },
  cases b with b; simp [mk, mk_nat] at h,
  { simp [mt (congr_arg int.of_nat) b0] at h,
    exact this h },
  { apply neg_inj, simp [this h] }
end

theorem mk_eq : ∀ {a b c d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0),
  a /. b = c /. d ↔ a * d = c * b :=
suffices ∀ a b c d hb hd, mk_pnat a ⟨b, hb⟩ = mk_pnat c ⟨d, hd⟩ ↔ a * d = c * b,
begin
  intros, cases b with b b; simp [mk, mk_nat, nat.succ_pnat],
  simp [mt (congr_arg int.of_nat) hb],
  all_goals {
    cases d with d d; simp [mk, mk_nat, nat.succ_pnat],
    simp [mt (congr_arg int.of_nat) hd],
    all_goals { rw this, try {refl} } },
  { change a * ↑(d.succ) = -c * ↑b ↔ a * -(d.succ) = c * b,
    constructor; intro h; apply neg_inj; simpa [left_distrib, neg_add_eq_iff_eq_add,
      eq_neg_iff_add_eq_zero, neg_eq_iff_add_eq_zero] using h },
  { change -a * ↑d = c * b.succ ↔ a * d = c * -b.succ,
    constructor; intro h; apply neg_inj;
    simp [left_distrib, *] at * },
  { change -a * d.succ = -c * b.succ ↔ a * -d.succ = c * -b.succ,
    simp [left_distrib, sub_eq_add_neg], cc }
end,
begin
  intros, simp [mk_pnat], constructor; intro h,
  { cases h with ha hb,
    have ha, {
      have dv := @gcd_abs_dvd_left,
      have := int.eq_mul_of_div_eq_right dv ha,
      rw ← int.mul_div_assoc _ dv at this,
      exact int.eq_mul_of_div_eq_left (dvd_mul_of_dvd_right dv _) this.symm },
    have hb, {
      have dv := λ {a b}, nat.gcd_dvd_right (int.nat_abs a) b,
      have := nat.eq_mul_of_div_eq_right dv hb,
      rw ← nat.mul_div_assoc _ dv at this,
      exact nat.eq_mul_of_div_eq_left (dvd_mul_of_dvd_right dv _) this.symm },
    have m0 : (a.nat_abs.gcd b * c.nat_abs.gcd d : ℤ) ≠ 0, {
      refine int.coe_nat_ne_zero.2 (ne_of_gt _),
      apply mul_pos; apply nat.gcd_pos_of_pos_right; assumption },
    apply eq_of_mul_eq_mul_right m0,
    simpa [mul_comm, mul_left_comm] using
      congr (congr_arg (*) ha.symm) (congr_arg coe hb) },
  { suffices : ∀ a c, a * d = c * b →
      a / a.gcd b = c / c.gcd d ∧ b / a.gcd b = d / c.gcd d,
    { cases this a.nat_abs c.nat_abs
        (by simpa [int.nat_abs_mul] using congr_arg int.nat_abs h) with h₁ h₂,
      have hs := congr_arg int.sign h,
      simp [int.sign_eq_one_of_pos (int.coe_nat_lt.2 hb),
            int.sign_eq_one_of_pos (int.coe_nat_lt.2 hd)] at hs,
      conv in a { rw ← int.sign_mul_nat_abs a },
      conv in c { rw ← int.sign_mul_nat_abs c },
      rw [int.mul_div_assoc, int.mul_div_assoc],
      exact ⟨congr (congr_arg (*) hs) (congr_arg coe h₁), h₂⟩,
      all_goals { exact int.coe_nat_dvd.2 (nat.gcd_dvd_left _ _) } },
    intros a c h,
    suffices bd : b / a.gcd b = d / c.gcd d,
    { refine ⟨_, bd⟩,
      apply nat.eq_of_mul_eq_mul_left hb,
      rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _), mul_comm,
          nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), bd,
          ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), h, mul_comm,
          nat.mul_div_assoc _ (nat.gcd_dvd_left _ _)] },
    suffices : ∀ {a c : ℕ} (b>0) (d>0),
      a * d = c * b → b / a.gcd b ≤ d / c.gcd d,
    { exact le_antisymm (this _ hb _ hd h) (this _ hd _ hb h.symm) },
    intros a c b hb d hd h,
    have gb0 := nat.gcd_pos_of_pos_right a hb,
    have gd0 := nat.gcd_pos_of_pos_right c hd,
    apply nat.le_of_dvd,
    apply (nat.le_div_iff_mul_le _ _ gd0).2,
    simp, apply nat.le_of_dvd hd (nat.gcd_dvd_right _ _),
    apply (nat.coprime_div_gcd_div_gcd gb0).symm.dvd_of_dvd_mul_left,
    refine ⟨c / c.gcd d, _⟩,
    rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _),
        ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _)],
    apply congr_arg (/ c.gcd d),
    rw [mul_comm, ← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _),
        mul_comm, h, nat.mul_div_assoc _ (nat.gcd_dvd_right _ _), mul_comm] }
end

@[simp] theorem div_mk_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) :
  (a * c) /. (b * c) = a /. b :=
begin
  by_cases b0 : b = 0, { subst b0, simp },
  apply (mk_eq (mul_ne_zero b0 c0) b0).2, simp [mul_comm, mul_assoc]
end

@[simp] theorem num_denom : ∀ {a : ℚ}, a.num /. a.denom = a
| ⟨n, d, h, (c:_=1)⟩ := show mk_nat n d = _,
  by simp [mk_nat, ne_of_gt h, mk_pnat, c]

theorem num_denom' {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d := num_denom.symm

theorem of_int_eq_mk (z : ℤ) : of_int z = z /. 1 := num_denom'

@[elab_as_eliminator] def {u} num_denom_cases_on {C : ℚ → Sort u}
   : ∀ (a : ℚ) (H : ∀ n d, 0 < d → (int.nat_abs n).coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩ H := by rw num_denom'; exact H n d h c

@[elab_as_eliminator] def {u} num_denom_cases_on' {C : ℚ → Sort u}
   (a : ℚ) (H : ∀ (n:ℤ) (d:ℕ), d ≠ 0 → C (n /. d)) : C a :=
num_denom_cases_on a $ λ n d h c,
H n d $ ne_of_gt h

theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a :=
begin
  cases e : a /. b with n d h c,
  rw [rat.num_denom', rat.mk_eq b0
    (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.nat_abs_dvd.1 $ int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $
    c.dvd_of_dvd_mul_right _),
  have := congr_arg int.nat_abs e,
  simp [int.nat_abs_mul, int.nat_abs_of_nat] at this, simp [this]
end

theorem denom_dvd (a b : ℤ) : ((a /. b).denom : ℤ) ∣ b :=
begin
  by_cases b0 : b = 0, {simp [b0]},
  cases e : a /. b with n d h c,
  rw [num_denom', mk_eq b0 (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ c.symm.dvd_of_dvd_mul_left _),
  rw [← int.nat_abs_mul, ← int.coe_nat_dvd, int.dvd_nat_abs, ← e], simp
end

protected def add : ℚ → ℚ → ℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * d₂ + n₂ * d₁) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_add ℚ := ⟨rat.add⟩

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
  (fv : ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
    f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
  (f0 : ∀ {n₁ d₁ n₂ d₂} (d₁0 : d₁ ≠ 0) (d₂0 : d₂ ≠ 0), f₂ n₁ d₁ n₂ d₂ ≠ 0)
  (a b c d : ℤ) (b0 : b ≠ 0) (d0 : d ≠ 0)
  (H : ∀ {n₁ d₁ n₂ d₂} (h₁ : a * d₁ = n₁ * b) (h₂ : c * d₂ = n₂ * d),
       f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
  f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d :=
begin
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  generalize hc : c /. d = x, cases x with n₂ d₂ h₂ c₂, rw num_denom' at hc,
  rw fv,
  have d₁0 := ne_of_gt (int.coe_nat_lt.2 h₁),
  have d₂0 := ne_of_gt (int.coe_nat_lt.2 h₂),
  exact (mk_eq (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((mk_eq b0 d₁0).1 ha) ((mk_eq d0 d₂0).1 hc))
end

@[simp] theorem add_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b + c /. d = (a * d + c * b) /. (b * d) :=
begin
  apply lift_binop_eq rat.add; intros; try {assumption},
  { apply mk_pnat_eq },
  { apply mul_ne_zero d₁0 d₂0 },
  calc (n₁ * d₂ + n₂ * d₁) * (b * d) =
          (n₁ * b) * d₂ * d + (n₂ * d) * (d₁ * b) : by simp [mul_add, mul_comm, mul_left_comm]
    ... = (a * d₁) * d₂ * d + (c * d₂) * (d₁ * b) : by rw [h₁, h₂]
    ... = (a * d + c * b) * (d₁ * d₂)             : by simp [mul_add, mul_comm, mul_left_comm]
end

protected def neg : ℚ → ℚ
| ⟨n, d, h, c⟩ := ⟨-n, d, h, by simp [c]⟩

instance : has_neg ℚ := ⟨rat.neg⟩

@[simp] theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b :=
begin
  by_cases b0 :  b = 0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  show rat.mk' _ _ _ _ = _, rw num_denom',
  have d0 := ne_of_gt (int.coe_nat_lt.2 h₁),
  apply (mk_eq d0 b0).2, have h₁ := (mk_eq b0 d0).1 ha,
  simp only [neg_mul_eq_neg_mul_symm, congr_arg has_neg.neg h₁]
end

protected def mul : ℚ → ℚ → ℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * n₂) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_mul ℚ := ⟨rat.mul⟩

@[simp] theorem mul_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  (a /. b) * (c /. d) = (a * c) /. (b * d) :=
begin
  apply lift_binop_eq rat.mul; intros; try {assumption},
  { apply mk_pnat_eq },
  { apply mul_ne_zero d₁0 d₂0 },
  cc
end

protected def inv : ℚ → ℚ
| ⟨(n+1:ℕ), d, h, c⟩ := ⟨d, n+1, n.succ_pos, c.symm⟩
| ⟨0, d, h, c⟩ := 0
| ⟨-[1+ n], d, h, c⟩ := ⟨-d, n+1, n.succ_pos, nat.coprime.symm $ by simp; exact c⟩

instance : has_inv ℚ := ⟨rat.inv⟩

@[simp] theorem inv_def {a b : ℤ} : (a /. b)⁻¹ = b /. a :=
begin
  by_cases a0 : a = 0, { subst a0, simp, refl },
  by_cases b0 : b = 0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n d h c, rw num_denom' at ha,
  refine eq.trans (_ : rat.inv ⟨n, d, h, c⟩ = d /. n) _,
  { cases n with n; [cases n with n, skip],
    { refl },
    { change int.of_nat n.succ with (n+1:ℕ),
      unfold rat.inv, rw num_denom' },
    { unfold rat.inv, rw num_denom', refl } },
  have n0 : n ≠ 0,
  { refine mt (λ (n0 : n = 0), _) a0,
    subst n0, simp at ha,
    exact (mk_eq_zero b0).1 ha },
  have d0 := ne_of_gt (int.coe_nat_lt.2 h),
  have ha := (mk_eq b0 d0).1 ha,
  apply (mk_eq n0 a0).2,
  cc
end

variables (a b c : ℚ)

protected theorem add_zero : a + 0 = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem zero_add : 0 + a = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem add_comm : a + b = b + a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂]; cc

protected theorem add_assoc : a + b + c = a + (b + c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_add, mul_comm, mul_left_comm, add_left_comm, add_assoc]

protected theorem add_left_neg : -a + a = 0 :=
num_denom_cases_on' a $ λ n d h,
by simp [h]

protected theorem mul_one : a * 1 = a :=
num_denom_cases_on' a $ λ n d h,
by change (1:ℚ) with 1 /. 1; simp [h]

protected theorem one_mul : 1 * a = a :=
num_denom_cases_on' a $ λ n d h,
by change (1:ℚ) with 1 /. 1; simp [h]

protected theorem mul_comm : a * b = b * a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂, mul_comm]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_comm, mul_left_comm]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero];
   refine (div_mk_div_cancel_left (int.coe_nat_ne_zero.2 h₃)).symm.trans _;
   simp [mul_add, mul_comm, mul_assoc, mul_left_comm]

protected theorem mul_add : a * (b + c) = a * b + a * c :=
by rw [rat.mul_comm, rat.add_mul, rat.mul_comm, rat.mul_comm c a]

protected theorem zero_ne_one : 0 ≠ (1:ℚ) :=
mt (λ (h : 0 = 1 /. 1), (mk_eq_zero one_ne_zero).1 h.symm) one_ne_zero

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
num_denom_cases_on' a $ λ n d h a0,
have n0 : n ≠ 0, from mt (by intro e; subst e; simp) a0,
by simp [h, n0, mul_comm]; exact
eq.trans (by simp) (@div_mk_div_cancel_left 1 1 _ n0)

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
eq.trans (rat.mul_comm _ _) (rat.mul_inv_cancel _ h)

instance : decidable_eq ℚ := by tactic.mk_dec_eq_instance

instance : field ℚ :=
{ zero             := 0,
  add              := rat.add,
  neg              := rat.neg,
  one              := 1,
  mul              := rat.mul,
  inv              := rat.inv,
  zero_add         := rat.zero_add,
  add_comm         := rat.add_comm,
  add_assoc        := rat.add_assoc,
  add_left_neg     := rat.add_left_neg,
  mul_one          := rat.mul_one,
  one_mul          := rat.one_mul,
  mul_comm         := rat.mul_comm,
  mul_assoc        := rat.mul_assoc,
  left_distrib     := rat.mul_add,
  right_distrib    := rat.add_mul,
  zero_ne_one      := rat.zero_ne_one,
  mul_inv_cancel   := rat.mul_inv_cancel,
  inv_zero         := rfl }

/- Extra instances to short-circuit type class resolution -/
instance : division_ring ℚ      := by apply_instance
instance : integral_domain ℚ    := by apply_instance
-- TODO(Mario): this instance slows down data.real.basic
--instance : domain ℚ           := by apply_instance
instance : nonzero_comm_ring ℚ  := by apply_instance
instance : comm_ring ℚ          := by apply_instance
--instance : ring ℚ             := by apply_instance
instance : comm_semiring ℚ      := by apply_instance
instance : semiring ℚ           := by apply_instance
instance : add_comm_group ℚ     := by apply_instance
instance : add_group ℚ          := by apply_instance
instance : add_comm_monoid ℚ    := by apply_instance
instance : add_monoid ℚ         := by apply_instance
instance : add_left_cancel_semigroup ℚ := by apply_instance
instance : add_right_cancel_semigroup ℚ := by apply_instance
instance : add_comm_semigroup ℚ := by apply_instance
instance : add_semigroup ℚ      := by apply_instance
instance : comm_monoid ℚ        := by apply_instance
instance : monoid ℚ             := by apply_instance
instance : comm_semigroup ℚ     := by apply_instance
instance : semigroup ℚ          := by apply_instance

theorem sub_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b - c /. d = (a * d - c * b) /. (b * d) :=
by simp [b0, d0, sub_eq_add_neg]

@[simp] lemma denom_neg_eq_denom : ∀ q : ℚ, (-q).denom = q.denom
| ⟨_, d, _, _⟩ := rfl

@[simp] lemma num_neg_eq_neg_num : ∀ q : ℚ, (-q).num = -(q.num)
| ⟨n, _, _, _⟩ := rfl

@[simp] lemma num_zero : rat.num 0 = 0 := rfl

lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 :=
have q = q.num /. q.denom, from num_denom.symm,
by simpa [hq]

lemma zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
⟨λ _, by simp *, zero_of_num_zero⟩

lemma num_ne_zero_of_ne_zero {q : ℚ} (h : q ≠ 0) : q.num ≠ 0 :=
assume : q.num = 0,
h $ zero_of_num_zero this

@[simp] lemma num_one : (1 : ℚ).num = 1 := rfl

@[simp] lemma denom_one : (1 : ℚ).denom = 1 := rfl

lemma denom_ne_zero (q : ℚ) : q.denom ≠ 0 :=
ne_of_gt q.pos

lemma eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.denom = q.num * p.denom :=
begin
  conv_lhs { rw [←(@num_denom p), ←(@num_denom q)] },
  apply rat.mk_eq,
  { exact_mod_cast p.denom_ne_zero },
  { exact_mod_cast q.denom_ne_zero }
end

lemma mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
assume : n = 0,
hq $ by simpa [this] using hqnd

lemma mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
assume : d = 0,
hq $ by simpa [this] using hqnd

lemma mk_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
assume : n /. d = 0,
h $ (mk_eq_zero hd).1 this

lemma mul_num_denom (q r : ℚ) : q * r = (q.num * r.num) /. ↑(q.denom * r.denom) :=
have hq' : (↑q.denom : ℤ) ≠ 0, by have := denom_ne_zero q; simpa,
have hr' : (↑r.denom : ℤ) ≠ 0, by have := denom_ne_zero r; simpa,
suffices (q.num /. ↑q.denom) * (r.num /. ↑r.denom) = (q.num * r.num) /. ↑(q.denom * r.denom),
  by simpa using this,
by simp [mul_def hq' hr', -num_denom]

lemma div_num_denom (q r : ℚ) : q / r = (q.num * r.denom) /. (q.denom * r.num) :=
if hr : r.num = 0 then
  have hr' : r = 0, from zero_of_num_zero hr,
  by simp *
else calc q / r = q * r⁻¹ : div_eq_mul_inv
            ... = (q.num /. q.denom) * (r.num /. r.denom)⁻¹ : by simp
            ... = (q.num /. q.denom) * (r.denom /. r.num) : by rw inv_def
            ... = (q.num * r.denom) /. (q.denom * r.num) : mul_def (by simpa using denom_ne_zero q) hr

lemma num_denom_mk {q : ℚ} {n d : ℤ} (hn : n ≠ 0) (hd : d ≠ 0) (qdf : q = n /. d) :
      ∃ c : ℤ, n = c * q.num ∧ d = c * q.denom :=
have hq : q ≠ 0, from
  assume : q = 0,
  hn $ (rat.mk_eq_zero hd).1 (by cc),
have q.num /. q.denom = n /. d, by rwa [num_denom],
have q.num * d = n * ↑(q.denom), from (rat.mk_eq (by simp [rat.denom_ne_zero]) hd).1 this,
begin
  existsi n / q.num,
  have hqdn : q.num ∣ n, begin rw qdf, apply rat.num_dvd, assumption end,
  split,
  { rw int.div_mul_cancel hqdn },
  { apply int.eq_mul_div_of_mul_eq_mul_of_dvd_left,
    { apply rat.num_ne_zero_of_ne_zero hq },
    repeat { assumption } }
end

theorem mk_pnat_num (n : ℤ) (d : ℕ+) :
  (mk_pnat n d).num = n / nat.gcd n.nat_abs d :=
by cases d; refl

theorem mk_pnat_denom (n : ℤ) (d : ℕ+) :
  (mk_pnat n d).denom = d / nat.gcd n.nat_abs d :=
by cases d; refl

theorem mul_num (q₁ q₂ : ℚ) : (q₁ * q₂).num =
  (q₁.num * q₂.num) / nat.gcd (q₁.num * q₂.num).nat_abs (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_denom (q₁ q₂ : ℚ) : (q₁ * q₂).denom =
  (q₁.denom * q₂.denom) / nat.gcd (q₁.num * q₂.num).nat_abs (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num :=
by rw [mul_num, int.nat_abs_mul, nat.coprime.gcd_eq_one, int.coe_nat_one, int.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

theorem mul_self_denom (q : ℚ) : (q * q).denom = q.denom * q.denom :=
by rw [rat.mul_denom, int.nat_abs_mul, nat.coprime.gcd_eq_one, nat.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

lemma add_num_denom (q r : ℚ) : q + r =
  ((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ) :=
have hqd : (q.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 q.3,
have hrd : (r.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 r.3,
by conv_lhs { rw [←@num_denom q, ←@num_denom r, rat.add_def hqd hrd] };
  simp [mul_comm]

section casts

theorem coe_int_eq_mk : ∀ (z : ℤ), ↑z = z /. 1
| (n : ℕ) := show (n:ℚ) = n /. 1,
  by induction n with n IH n; simp [*, show (1:ℚ) = 1 /. 1, from rfl]
| -[1+ n] := show (-(n + 1) : ℚ) = -[1+ n] /. 1, begin
  induction n with n IH, {refl},
  show -(n + 1 + 1 : ℚ) = -[1+ n.succ] /. 1,
  rw [neg_add, IH],
  simpa [show -1 = (-1) /. 1, from rfl]
end

theorem mk_eq_div (n d : ℤ) : n /. d = ((n : ℚ) / d) :=
begin
  by_cases d0 : d = 0, {simp [d0, div_zero]},
  simp [division_def, coe_int_eq_mk, mul_def one_ne_zero d0]
end

theorem coe_int_eq_of_int (z : ℤ) : ↑z = of_int z :=
(coe_int_eq_mk z).trans (of_int_eq_mk z).symm

@[simp, norm_cast] theorem coe_int_num (n : ℤ) : (n : ℚ).num = n :=
by rw coe_int_eq_of_int; refl

@[simp, norm_cast] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1 :=
by rw coe_int_eq_of_int; refl

lemma coe_int_num_of_denom_eq_one {q : ℚ} (hq : q.denom = 1) : ↑(q.num) = q :=
by { conv_rhs { rw [←(@num_denom q), hq] }, rw [coe_int_eq_mk], refl }

instance : can_lift ℚ ℤ :=
⟨coe, λ q, q.denom = 1, λ q hq, ⟨q.num, coe_int_num_of_denom_eq_one hq⟩⟩

theorem coe_nat_eq_mk (n : ℕ) : ↑n = n /. 1 :=
by rw [← int.cast_coe_nat, coe_int_eq_mk]

@[simp, norm_cast] theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n :=
by rw [← int.cast_coe_nat, coe_int_num]

@[simp, norm_cast] theorem coe_nat_denom (n : ℕ) : (n : ℚ).denom = 1 :=
by rw [← int.cast_coe_nat, coe_int_denom]

end casts

lemma inv_def' {q : ℚ} : q⁻¹ = (q.denom : ℚ) / q.num :=
by { conv_lhs { rw ←(@num_denom q) }, cases q, simp [div_num_denom] }

@[simp] lemma mul_own_denom_eq_num {q : ℚ} : q * q.denom = q.num :=
begin
  suffices : mk (q.num) ↑(q.denom) * mk ↑(q.denom) 1 = mk (q.num) 1, by
  { conv { for q [1] { rw ←(@num_denom q) }}, rwa [coe_int_eq_mk, coe_nat_eq_mk] },
  have : (q.denom : ℤ) ≠ 0, from ne_of_gt (by exact_mod_cast q.pos),
  rw [(rat.mul_def this one_ne_zero), (mul_comm (q.denom : ℤ) 1), (div_mk_div_cancel_left this)]
end

end rat
