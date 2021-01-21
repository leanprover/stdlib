/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import data.multiset.basic

/-!
# Associated, prime, and irreducible elements.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

lemma is_unit.pow [monoid α] {a : α} (n : ℕ) : is_unit a → is_unit (a ^ n) :=
λ ⟨u, hu⟩, ⟨u ^ n, by simp *⟩

theorem is_unit_iff_dvd_one [comm_monoid α] {x : α} : is_unit x ↔ x ∣ 1 :=
⟨by rintro ⟨u, rfl⟩; exact ⟨_, u.mul_inv.symm⟩,
 λ ⟨y, h⟩, ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

theorem is_unit_iff_forall_dvd [comm_monoid α] {x : α} :
  is_unit x ↔ ∀ y, x ∣ y :=
is_unit_iff_dvd_one.trans ⟨λ h y, dvd.trans h (one_dvd _), λ h, h _⟩

theorem is_unit_of_dvd_unit {α} [comm_monoid α] {x y : α}
  (xy : x ∣ y) (hu : is_unit y) : is_unit x :=
is_unit_iff_dvd_one.2 $ dvd_trans xy $ is_unit_iff_dvd_one.1 hu

theorem is_unit_int {n : ℤ} : is_unit n ↔ n.nat_abs = 1 :=
⟨begin rintro ⟨u, rfl⟩, exact (int.units_eq_one_or u).elim (by simp) (by simp) end,
  λ h, is_unit_iff_dvd_one.2 ⟨n, by rw [← int.nat_abs_mul_self, h]; refl⟩⟩

lemma is_unit_of_dvd_one [comm_monoid α] : ∀a ∣ 1, is_unit (a:α)
| a ⟨b, eq⟩ := ⟨units.mk_of_mul_eq_one a b eq.symm, rfl⟩

lemma dvd_and_not_dvd_iff [comm_cancel_monoid_with_zero α] {x y : α} :
  x ∣ y ∧ ¬y ∣ x ↔ dvd_not_unit x y :=
⟨λ ⟨⟨d, hd⟩, hyx⟩, ⟨λ hx0, by simpa [hx0] using hyx, ⟨d,
    mt is_unit_iff_dvd_one.1 (λ ⟨e, he⟩, hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩), hd⟩⟩,
  λ ⟨hx0, d, hdu, hdx⟩, ⟨⟨d, hdx⟩, λ ⟨e, he⟩, hdu (is_unit_of_dvd_one _
    ⟨e, mul_left_cancel' hx0 $ by conv {to_lhs, rw [he, hdx]};simp [mul_assoc]⟩)⟩⟩

lemma pow_dvd_pow_iff [comm_cancel_monoid_with_zero α]
  {x : α} {n m : ℕ} (h0 : x ≠ 0) (h1 : ¬ is_unit x) :
  x ^ n ∣ x ^ m ↔ n ≤ m :=
begin
  split,
  { intro h, rw [← not_lt], intro hmn, apply h1,
    have : x ^ m * x ∣ x ^ m * 1,
    { rw [← pow_succ', mul_one], exact dvd_trans (pow_dvd_pow _ (nat.succ_le_of_lt hmn)) h },
    rwa [mul_dvd_mul_iff_left, ← is_unit_iff_dvd_one] at this, apply pow_ne_zero m h0 },
  { apply pow_dvd_pow }
end

section prime
variables [comm_monoid_with_zero α]

/-- prime element of a `comm_monoid_with_zero` -/
def prime (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ (∀a b, p ∣ a * b → p ∣ a ∨ p ∣ b)

namespace prime
variables {p : α} (hp : prime p)

lemma ne_zero (hp : prime p) : p ≠ 0 :=
hp.1

lemma not_unit (hp : prime p) : ¬ is_unit p :=
hp.2.1

lemma ne_one (hp : prime p) : p ≠ 1 :=
λ h, hp.2.1 (h.symm ▸ is_unit_one)

lemma div_or_div (hp : prime p) {a b : α} (h : p ∣ a * b) :
  p ∣ a ∨ p ∣ b :=
hp.2.2 a b h

lemma dvd_of_dvd_pow (hp : prime p) {a : α} {n : ℕ} (h : p ∣ a^n) :
  p ∣ a :=
begin
  induction n with n ih,
  { rw pow_zero at h,
    have := is_unit_of_dvd_one _ h,
    have := not_unit hp,
    contradiction },
  rw pow_succ at h,
  cases div_or_div hp h with dvd_a dvd_pow,
  { assumption },
  exact ih dvd_pow
end

end prime

@[simp] lemma not_prime_zero : ¬ prime (0 : α) :=
λ h, h.ne_zero rfl

@[simp] lemma not_prime_one : ¬ prime (1 : α) :=
λ h, h.not_unit is_unit_one

lemma exists_mem_multiset_dvd_of_prime {s : multiset α} {p : α} (hp : prime p) :
  p ∣ s.prod → ∃a∈s, p ∣ a :=
multiset.induction_on s (assume h, (hp.not_unit $ is_unit_of_dvd_one _ h).elim) $
assume a s ih h,
  have p ∣ a * s.prod, by simpa using h,
  match hp.div_or_div this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

end prime

lemma left_dvd_or_dvd_right_of_dvd_prime_mul [comm_cancel_monoid_with_zero α] {a : α} :
  ∀ {b p : α}, prime p → a ∣ p * b → p ∣ a ∨ a ∣ b :=
begin
  rintros b p hp ⟨c, hc⟩,
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with h | ⟨x, rfl⟩,
  { exact or.inl h },
  { rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc,
    exact or.inr (hc.symm ▸ dvd_mul_right _ _) }
end

/-- `irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
@[class] def irreducible [monoid α] (p : α) : Prop :=
¬ is_unit p ∧ ∀a b, p = a * b → is_unit a ∨ is_unit b

namespace irreducible

lemma not_unit [monoid α] {p : α} (hp : irreducible p) : ¬ is_unit p :=
hp.1

lemma is_unit_or_is_unit [monoid α] {p : α} (hp : irreducible p) {a b : α} (h : p = a * b) :
  is_unit a ∨ is_unit b :=
hp.2 a b h

end irreducible

@[simp] theorem not_irreducible_one [monoid α] : ¬ irreducible (1 : α) :=
by simp [irreducible]

@[simp] theorem not_irreducible_zero [monoid_with_zero α] : ¬ irreducible (0 : α)
| ⟨hn0, h⟩ := have is_unit (0:α) ∨ is_unit (0:α), from h 0 0 ((mul_zero 0).symm),
  this.elim hn0 hn0

theorem irreducible.ne_zero [monoid_with_zero α] : ∀ {p:α}, irreducible p → p ≠ 0
| _ hp rfl := not_irreducible_zero hp

theorem of_irreducible_mul {α} [monoid α] {x y : α} :
  irreducible (x * y) → is_unit x ∨ is_unit y
| ⟨_, h⟩ := h _ _ rfl

theorem irreducible_or_factor {α} [monoid α] (x : α) (h : ¬ is_unit x) :
  irreducible x ∨ ∃ a b, ¬ is_unit a ∧ ¬ is_unit b ∧ a * b = x :=
begin
  haveI := classical.dec,
  refine or_iff_not_imp_right.2 (λ H, _),
  simp [h, irreducible] at H ⊢,
  refine λ a b h, classical.by_contradiction $ λ o, _,
  simp [not_or_distrib] at o,
  exact H _ o.1 _ o.2 h.symm
end

lemma irreducible_of_prime [comm_cancel_monoid_with_zero α] {p : α} (hp : prime p) :
  irreducible p :=
⟨hp.not_unit, λ a b hab,
  (show a * b ∣ a ∨ a * b ∣ b, from hab ▸ hp.div_or_div (hab ▸ (dvd_refl _))).elim
    (λ ⟨x, hx⟩, or.inr (is_unit_iff_dvd_one.2
      ⟨x, mul_right_cancel' (show a ≠ 0, from λ h, by simp [*, prime] at *)
        $ by conv {to_lhs, rw hx}; simp [mul_comm, mul_assoc, mul_left_comm]⟩))
    (λ ⟨x, hx⟩, or.inl (is_unit_iff_dvd_one.2
      ⟨x, mul_right_cancel' (show b ≠ 0, from λ h, by simp [*, prime] at *)
        $ by conv {to_lhs, rw hx}; simp [mul_comm, mul_assoc, mul_left_comm]⟩))⟩

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul [comm_cancel_monoid_with_zero α]
  {p : α} (hp : prime p) {a b : α} {k l : ℕ} :
  p ^ k ∣ a → p ^ l ∣ b → p ^ ((k + l) + 1) ∣ a * b → p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩,
have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z),
  by simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz,
have hp0: p ^ (k + l) ≠ 0, from pow_ne_zero _ hp.ne_zero,
have hpd : p ∣ x * y, from ⟨z, by rwa [mul_right_inj' hp0] at h⟩,
(hp.div_or_div hpd).elim
  (λ ⟨d, hd⟩, or.inl ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)
  (λ ⟨d, hd⟩, or.inr ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
lemma dvd_symm_of_irreducible [monoid α] {p q : α}
  (hp : irreducible p) (hq : irreducible q) : p ∣ q → q ∣ p :=
begin
  tactic.unfreeze_local_instances,
  rintros ⟨q', rfl⟩,
  rw is_unit.mul_right_dvd (or.resolve_left (of_irreducible_mul hq) hp.not_unit),
end

lemma dvd_symm_iff_of_irreducible [monoid α] {p q : α}
  (hp : irreducible p) (hq : irreducible q) : p ∣ q ↔ q ∣ p :=
⟨dvd_symm_of_irreducible hp hq, dvd_symm_of_irreducible hq hp⟩

/-- Two elements of a `monoid` are `associated` if one of them is another one
multiplied by a unit on the right. -/
def associated [monoid α] (x y : α) : Prop := ∃u:units α, x * u = y

local infix ` ~ᵤ ` : 50 := associated

namespace associated

@[refl] protected theorem refl [monoid α] (x : α) : x ~ᵤ x := ⟨1, by simp⟩

@[symm] protected theorem symm [monoid α] : ∀{x y : α}, x ~ᵤ y → y ~ᵤ x
| x _ ⟨u, rfl⟩ := ⟨u⁻¹, by rw [mul_assoc, units.mul_inv, mul_one]⟩

@[trans] protected theorem trans [monoid α] : ∀{x y z : α}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
| x _ _ ⟨u, rfl⟩ ⟨v, rfl⟩ := ⟨u * v, by rw [units.coe_mul, mul_assoc]⟩

/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
protected def setoid (α : Type*) [monoid α] : setoid α :=
{ r := associated, iseqv := ⟨associated.refl, λa b, associated.symm, λa b c, associated.trans⟩ }

end associated

local attribute [instance] associated.setoid

theorem unit_associated_one [monoid α] {u : units α} : (u : α) ~ᵤ 1 := ⟨u⁻¹, units.mul_inv u⟩

theorem associated_one_iff_is_unit [monoid α] {a : α} : (a : α) ~ᵤ 1 ↔ is_unit a :=
iff.intro
  (assume h, let ⟨c, h⟩ := h.symm in h ▸ ⟨c, (one_mul _).symm⟩)
  (assume ⟨c, h⟩, associated.symm ⟨c, by simp [h]⟩)

theorem associated_zero_iff_eq_zero [monoid_with_zero α] (a : α) : a ~ᵤ 0 ↔ a = 0 :=
iff.intro
  (assume h, let ⟨u, h⟩ := h.symm in by simpa using h.symm)
  (assume h, h ▸ associated.refl a)

theorem associated_one_of_mul_eq_one [comm_monoid α] {a : α} (b : α) (hab : a * b = 1) : a ~ᵤ 1 :=
show (units.mk_of_mul_eq_one a b hab : α) ~ᵤ 1, from unit_associated_one

theorem associated_one_of_associated_mul_one [comm_monoid α] {a b : α} :
  a * b ~ᵤ 1 → a ~ᵤ 1
| ⟨u, h⟩ := associated_one_of_mul_eq_one (b * u) $ by simpa [mul_assoc] using h

lemma associated_mul_mul [comm_monoid α] {a₁ a₂ b₁ b₂ : α} :
  a₁ ~ᵤ b₁ → a₂ ~ᵤ b₂ → (a₁ * a₂) ~ᵤ (b₁ * b₂)
| ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ := ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩

lemma associated_pow_pow [comm_monoid α] {a b : α} {n : ℕ} (h : a ~ᵤ b) :
  a ^ n ~ᵤ b ^ n :=
begin
  induction n with n ih, { simp [h] },
  convert associated_mul_mul h ih,
end

lemma dvd_of_associated [monoid α] {a b : α} : a ~ᵤ b → a ∣ b := λ ⟨u, hu⟩, ⟨u, hu.symm⟩

lemma dvd_dvd_of_associated [monoid α] {a b : α} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
⟨dvd_of_associated h, dvd_of_associated h.symm⟩

theorem associated_of_dvd_dvd [cancel_monoid_with_zero α]
  {a b : α} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b :=
begin
  rcases hab with ⟨c, rfl⟩,
  rcases hba with ⟨d, a_eq⟩,
  by_cases ha0 : a = 0,
  { simp [*] at * },
  have hac0 : a * c ≠ 0,
  { intro con, rw [con, zero_mul] at a_eq, apply ha0 a_eq, },
  have : a * (c * d) =  a * 1 := by rw [← mul_assoc, ← a_eq, mul_one],
  have hcd : (c * d) = 1, from mul_left_cancel' ha0 this,
  have : a * c * (d * c) = a * c * 1 := by rw [← mul_assoc, ← a_eq, mul_one],
  have hdc : d * c = 1, from mul_left_cancel' hac0 this,
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩
end

theorem dvd_dvd_iff_associated [cancel_monoid_with_zero α] {a b : α} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
⟨λ ⟨h1, h2⟩, associated_of_dvd_dvd h1 h2, dvd_dvd_of_associated⟩

lemma exists_associated_mem_of_dvd_prod [comm_cancel_monoid_with_zero α] {p : α}
  (hp : prime p) {s : multiset α} : (∀ r ∈ s, prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
multiset.induction_on s (by simp [mt is_unit_iff_dvd_one.2 hp.not_unit])
  (λ a s ih hs hps, begin
    rw [multiset.prod_cons] at hps,
    cases hp.div_or_div hps with h h,
    { use [a, by simp],
      cases h with u hu,
      cases ((irreducible_of_prime (hs a (multiset.mem_cons.2
        (or.inl rfl)))).2 p u hu).resolve_left hp.not_unit with v hv,
      exact ⟨v, by simp [hu, hv]⟩ },
    { rcases ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h with ⟨q, hq₁, hq₂⟩,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)

lemma dvd_iff_dvd_of_rel_left [comm_monoid_with_zero α] {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ units.mul_right_dvd.symm

lemma dvd_iff_dvd_of_rel_right [comm_monoid_with_zero α] {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ units.dvd_mul_right.symm

lemma eq_zero_iff_of_associated [comm_monoid_with_zero α] {a b : α} (h : a ~ᵤ b) : a = 0 ↔ b = 0 :=
⟨λ ha, let ⟨u, hu⟩ := h in by simp [hu.symm, ha],
  λ hb, let ⟨u, hu⟩ := h.symm in by simp [hu.symm, hb]⟩

lemma ne_zero_iff_of_associated [comm_monoid_with_zero α] {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
by haveI := classical.dec; exact not_iff_not.2 (eq_zero_iff_of_associated h)

lemma prime_of_associated [comm_monoid_with_zero α] {p q : α} (h : p ~ᵤ q) (hp : prime p) :
  prime q :=
⟨(ne_zero_iff_of_associated h).1 hp.ne_zero,
  let ⟨u, hu⟩ := h in
    ⟨λ ⟨v, hv⟩, hp.not_unit ⟨v * u⁻¹, by simp [hv, hu.symm]⟩,
      hu ▸ by { simp [units.mul_right_dvd], intros a b, exact hp.div_or_div }⟩⟩

lemma prime_iff_of_associated [comm_monoid_with_zero α] {p q : α}
  (h : p ~ᵤ q) : prime p ↔ prime q :=
⟨prime_of_associated h, prime_of_associated h.symm⟩

lemma is_unit_iff_of_associated [monoid α] {a b : α} (h :  a ~ᵤ b) : is_unit a ↔ is_unit b :=
⟨let ⟨u, hu⟩ := h in λ ⟨v, hv⟩, ⟨v * u, by simp [hv, hu.symm]⟩,
  let ⟨u, hu⟩ := h.symm in λ ⟨v, hv⟩, ⟨v * u, by simp [hv, hu.symm]⟩⟩

lemma irreducible_of_associated [comm_monoid_with_zero α] {p q : α} (h : p ~ᵤ q)
  (hp : irreducible p) : irreducible q :=
⟨mt (is_unit_iff_of_associated h).2 hp.1,
  let ⟨u, hu⟩ := h in λ a b hab,
  have hpab : p = a * (b * (u⁻¹ : units α)),
    from calc p = (p * u) * (u ⁻¹ : units α) : by simp
      ... = _ : by rw hu; simp [hab, mul_assoc],
  (hp.2 _ _ hpab).elim or.inl (λ ⟨v, hv⟩, or.inr ⟨v * u, by simp [hv]⟩)⟩

lemma irreducible_iff_of_associated [comm_monoid_with_zero α] {p q : α} (h : p ~ᵤ q) :
  irreducible p ↔ irreducible q :=
⟨irreducible_of_associated h, irreducible_of_associated h.symm⟩

lemma associated_mul_left_cancel [comm_cancel_monoid_with_zero α] {a b c d : α}
(h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c) (ha : a ≠ 0) : b ~ᵤ d :=
let ⟨u, hu⟩ := h in let ⟨v, hv⟩ := associated.symm h₁ in
⟨u * (v : units α), mul_left_cancel' ha
  begin
    rw [← hv, mul_assoc c (v : α) d, mul_left_comm c, ← hu],
    simp [hv.symm, mul_assoc, mul_comm, mul_left_comm]
  end⟩

lemma associated_mul_right_cancel [comm_cancel_monoid_with_zero α] {a b c d : α} :
  a * b ~ᵤ c * d → b ~ᵤ d → b ≠ 0 → a ~ᵤ c :=
by rw [mul_comm a, mul_comm c]; exact associated_mul_left_cancel

section unique_units
variables [monoid α] [unique (units α)]

theorem associated_iff_eq {x y : α} : x ~ᵤ y ↔ x = y :=
begin
  split,
  { rintro ⟨c, rfl⟩, simp [subsingleton.elim c 1] },
  { rintro rfl, refl },
end

theorem associated_eq_eq : (associated : α → α → Prop) = eq :=
by { ext, rw associated_iff_eq }

end unique_units

/-- The quotient of a monoid by the `associated` relation. Two elements `x` and `y`
  are associated iff there is a unit `u` such that `x * u = y`. There is a natural
  monoid structure on `associates α`. -/
def associates (α : Type*) [monoid α] : Type* :=
quotient (associated.setoid α)

namespace associates
open associated

/-- The canonical quotient map from a monoid `α` into the `associates` of `α` -/
protected def mk {α : Type*} [monoid α] (a : α) : associates α :=
⟦ a ⟧

instance [monoid α] : inhabited (associates α) := ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_associated [monoid α] {a b : α} :
  associates.mk a = associates.mk b ↔ a ~ᵤ b :=
iff.intro quotient.exact quot.sound

theorem quotient_mk_eq_mk [monoid α] (a : α) : ⟦ a ⟧ = associates.mk a := rfl

theorem quot_mk_eq_mk [monoid α] (a : α) : quot.mk setoid.r a = associates.mk a := rfl

theorem forall_associated [monoid α] {p : associates α → Prop} :
  (∀a, p a) ↔ (∀a, p (associates.mk a)) :=
iff.intro
  (assume h a, h _)
  (assume h a, quotient.induction_on a h)

theorem mk_surjective [monoid α] : function.surjective (@associates.mk α _) :=
forall_associated.2 (λ a, ⟨a, rfl⟩)

instance [monoid α] : has_one (associates α) := ⟨⟦ 1 ⟧⟩

theorem one_eq_mk_one [monoid α] : (1 : associates α) = associates.mk 1 := rfl

instance [monoid α] : has_bot (associates α) := ⟨1⟩

lemma exists_rep [monoid α] (a : associates α) : ∃ a0 : α, associates.mk a0 = a :=
quot.exists_rep a

section comm_monoid
variable [comm_monoid α]

instance : has_mul (associates α) :=
⟨λa' b', quotient.lift_on₂ a' b' (λa b, ⟦ a * b ⟧) $
  assume a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩,
  quotient.sound $ ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩⟩

theorem mk_mul_mk {x y : α} : associates.mk x * associates.mk y = associates.mk (x * y) :=
rfl

instance : comm_monoid (associates α) :=
{ one       := 1,
  mul       := (*),
  mul_one   := assume a', quotient.induction_on a' $
    assume a, show ⟦a * 1⟧ = ⟦ a ⟧, by simp,
  one_mul   := assume a', quotient.induction_on a' $
    assume a, show ⟦1 * a⟧ = ⟦ a ⟧, by simp,
  mul_assoc := assume a' b' c', quotient.induction_on₃ a' b' c' $
    assume a b c, show ⟦a * b * c⟧ = ⟦a * (b * c)⟧, by rw [mul_assoc],
  mul_comm  := assume a' b', quotient.induction_on₂ a' b' $
    assume a b, show ⟦a * b⟧ = ⟦b * a⟧, by rw [mul_comm] }

instance : preorder (associates α) :=
{ le := has_dvd.dvd,
  le_refl := dvd_refl,
  le_trans := λ a b c, dvd_trans}

@[simp] lemma mk_one : associates.mk (1 : α) = 1 := rfl

/-- `associates.mk` as a `monoid_hom`. -/
protected def mk_monoid_hom : α →* (associates α) := ⟨associates.mk, mk_one, λ x y, mk_mul_mk⟩

@[simp] lemma mk_monoid_hom_apply (a : α) : associates.mk_monoid_hom a = associates.mk a := rfl

lemma associated_map_mk {f : associates α →* α}
  (hinv : function.right_inverse f associates.mk) (a : α) :
  a ~ᵤ f (associates.mk a) :=
associates.mk_eq_mk_iff_associated.1 (hinv (associates.mk a)).symm

lemma mk_pow (a : α) (n : ℕ) : associates.mk (a ^ n) = (associates.mk a) ^ n :=
by induction n; simp [*, pow_succ, associates.mk_mul_mk.symm]

lemma dvd_eq_le : ((∣) : associates α → associates α → Prop) = (≤) := rfl

theorem prod_mk {p : multiset α} : (p.map associates.mk).prod = associates.mk p.prod :=
multiset.induction_on p (by simp; refl) $ assume a s ih, by simp [ih]; refl

theorem rel_associated_iff_map_eq_map {p q : multiset α} :
  multiset.rel associated p q ↔ p.map associates.mk = q.map associates.mk :=
by rw [← multiset.rel_eq];
  simp [multiset.rel_map_left, multiset.rel_map_right, mk_eq_mk_iff_associated]

theorem mul_eq_one_iff {x y : associates α} : x * y = 1 ↔ (x = 1 ∧ y = 1) :=
iff.intro
  (quotient.induction_on₂ x y $ assume a b h,
    have a * b ~ᵤ 1, from quotient.exact h,
    ⟨quotient.sound $ associated_one_of_associated_mul_one this,
      quotient.sound $ associated_one_of_associated_mul_one $ by rwa [mul_comm] at this⟩)
  (by simp {contextual := tt})

theorem prod_eq_one_iff {p : multiset (associates α)} :
  p.prod = 1 ↔ (∀a ∈ p, (a:associates α) = 1) :=
multiset.induction_on p
  (by simp)
  (by simp [mul_eq_one_iff, or_imp_distrib, forall_and_distrib] {contextual := tt})

theorem units_eq_one (u : units (associates α)) : u = 1 :=
units.ext (mul_eq_one_iff.1 u.val_inv).1

instance unique_units : unique (units (associates α)) :=
{ default := 1, uniq := associates.units_eq_one }

theorem coe_unit_eq_one (u : units (associates α)): (u : associates α) = 1 :=
by simp

theorem is_unit_iff_eq_one (a : associates α) : is_unit a ↔ a = 1 :=
iff.intro
  (assume ⟨u, h⟩, h ▸ coe_unit_eq_one _)
  (assume h, h.symm ▸ is_unit_one)

theorem is_unit_mk {a : α} : is_unit (associates.mk a) ↔ is_unit a :=
calc is_unit (associates.mk a) ↔ a ~ᵤ 1 :
    by rw [is_unit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
  ... ↔ is_unit a : associated_one_iff_is_unit

section order

theorem mul_mono {a b c d : associates α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
  a * c ≤ b * d :=
let ⟨x, hx⟩ := h₁, ⟨y, hy⟩ := h₂ in
⟨x * y, by simp [hx, hy, mul_comm, mul_assoc, mul_left_comm]⟩

theorem one_le {a : associates α} : 1 ≤ a :=
dvd.intro _ (one_mul a)

theorem prod_le_prod {p q : multiset (associates α)} (h : p ≤ q) : p.prod ≤ q.prod :=
begin
  haveI := classical.dec_eq (associates α),
  haveI := classical.dec_eq α,
  suffices : p.prod ≤ (p + (q - p)).prod, { rwa [multiset.add_sub_of_le h] at this },
  suffices : p.prod * 1 ≤ p.prod * (q - p).prod, { simpa },
  exact mul_mono (le_refl p.prod) one_le
end

theorem le_mul_right {a b : associates α} : a ≤ a * b := ⟨b, rfl⟩

theorem le_mul_left {a b : associates α} : a ≤ b * a :=
by rw [mul_comm]; exact le_mul_right

end order

end comm_monoid

instance [has_zero α] [monoid α] : has_zero (associates α) := ⟨⟦ 0 ⟧⟩
instance [has_zero α] [monoid α] : has_top (associates α) := ⟨0⟩

section comm_monoid_with_zero

variables [comm_monoid_with_zero α]

@[simp] theorem mk_eq_zero {a : α} : associates.mk a = 0 ↔ a = 0 :=
⟨assume h, (associated_zero_iff_eq_zero a).1 $ quotient.exact h, assume h, h.symm ▸ rfl⟩

instance : comm_monoid_with_zero (associates α) :=
{ zero_mul := by { rintro ⟨a⟩, show associates.mk (0 * a) = associates.mk 0, rw [zero_mul] },
  mul_zero := by { rintro ⟨a⟩, show associates.mk (a * 0) = associates.mk 0, rw [mul_zero] },
  .. associates.comm_monoid, .. associates.has_zero }

instance [nontrivial α] : nontrivial (associates α) :=
⟨⟨0, 1,
assume h,
have (0 : α) ~ᵤ 1, from quotient.exact h,
have (0 : α) = 1, from ((associated_zero_iff_eq_zero 1).1 this.symm).symm,
zero_ne_one this⟩⟩

lemma exists_non_zero_rep {a : associates α} : a ≠ 0 → ∃ a0 : α, a0 ≠ 0 ∧ associates.mk a0 = a :=
quotient.induction_on a (λ b nz, ⟨b, mt (congr_arg quotient.mk) nz, rfl⟩)

theorem dvd_of_mk_le_mk {a b : α} : associates.mk a ≤ associates.mk b → a ∣ b
| ⟨c', hc'⟩ := (quotient.induction_on c' $ assume c hc,
    let ⟨d, hd⟩ := (quotient.exact hc).symm in
    ⟨(↑d) * c,
      calc b = (a * c) * ↑d : hd.symm
        ... = a * (↑d * c) : by ac_refl⟩) hc'

theorem mk_le_mk_of_dvd {a b : α} : a ∣ b → associates.mk a ≤ associates.mk b :=
assume ⟨c, hc⟩, ⟨associates.mk c, by simp [hc]; refl⟩

theorem mk_le_mk_iff_dvd_iff {a b : α} : associates.mk a ≤ associates.mk b ↔ a ∣ b :=
iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

theorem mk_dvd_mk {a b : α} : associates.mk a ∣ associates.mk b ↔ a ∣ b :=
iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

lemma prime.le_or_le {p : associates α} (hp : prime p) {a b : associates α} (h : p ≤ a * b) :
  p ≤ a ∨ p ≤ b :=
hp.2.2 a b h

lemma exists_mem_multiset_le_of_prime {s : multiset (associates α)} {p : associates α}
  (hp : prime p) :
  p ≤ s.prod → ∃a∈s, p ≤ a :=
multiset.induction_on s (assume ⟨d, eq⟩, (hp.ne_one (mul_eq_one_iff.1 eq.symm).1).elim) $
assume a s ih h,
  have p ≤ a * s.prod, by simpa using h,
  match prime.le_or_le hp this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

lemma prime_mk (p : α) : prime (associates.mk p) ↔ _root_.prime p :=
begin
  rw [prime, _root_.prime, forall_associated],
  transitivity,
  { apply and_congr, refl,
    apply and_congr, refl,
    apply forall_congr, assume a,
    exact forall_associated },
  apply and_congr,
  { rw [(≠), mk_eq_zero] },
  apply and_congr,
  { rw [is_unit_mk], },
  apply forall_congr, assume a,
  apply forall_congr, assume b,
  rw [mk_mul_mk, mk_dvd_mk, mk_dvd_mk, mk_dvd_mk],
end

theorem irreducible_mk (a : α) : irreducible (associates.mk a) ↔ irreducible a :=
begin
  simp only [irreducible, is_unit_mk],
  apply and_congr iff.rfl,
  split,
  { rintro h x y rfl,
    simpa [is_unit_mk] using h (associates.mk x) (associates.mk y) rfl },
  { intros h x y,
    refine quotient.induction_on₂ x y (assume x y a_eq, _),
    rcases quotient.exact a_eq.symm with ⟨u, a_eq⟩,
    rw mul_assoc at a_eq,
    show is_unit (associates.mk x) ∨ is_unit (associates.mk y),
    simpa [is_unit_mk] using h _ _ a_eq.symm }
end

theorem mk_dvd_not_unit_mk_iff {a b : α} :
  dvd_not_unit (associates.mk a) (associates.mk b) ↔
  dvd_not_unit a b :=
begin
  rw [dvd_not_unit, dvd_not_unit, ne, ne, mk_eq_zero],
  apply and_congr_right, intro ane0,
  split,
  { contrapose!, rw forall_associated,
    intros h x hx hbax,
    rw [mk_mul_mk, mk_eq_mk_iff_associated] at hbax,
    cases hbax with u hu,
    apply h (x * ↑u⁻¹),
    { rw is_unit_mk at hx,
      rw is_unit_iff_of_associated,
      apply hx,
      use u,
      simp, },
    simp [← mul_assoc, ← hu] },
  { rintro ⟨x, ⟨hx, rfl⟩⟩,
    use associates.mk x,
    simp [is_unit_mk, mk_mul_mk, hx], }
end

theorem dvd_not_unit_of_lt {a b : associates α} (hlt : a < b) :
  dvd_not_unit a b :=
begin
  split, { rintro rfl, apply not_lt_of_le _ hlt, apply dvd_zero },
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩,
  refine ⟨x, _, rfl⟩,
  contrapose! ndvd,
  rcases ndvd with ⟨u, rfl⟩,
  simp,
end

end comm_monoid_with_zero

section comm_cancel_monoid_with_zero
variable [comm_cancel_monoid_with_zero α]

instance : partial_order (associates α) :=
{ le_antisymm := λ a' b', quotient.induction_on₂ a' b' (λ a b hab hba,
  quot.sound $ associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba))
  .. associates.preorder }

instance : order_bot (associates α) :=
{ bot := 1,
  bot_le := assume a, one_le,
  .. associates.partial_order }

instance : order_top (associates α) :=
{ top := 0,
  le_top := assume a, ⟨0, (mul_zero a).symm⟩,
  .. associates.partial_order }

instance : no_zero_divisors (associates α) :=
⟨λ x y,
  (quotient.induction_on₂ x y $ assume a b h,
    have a * b = 0, from (associated_zero_iff_eq_zero _).1 (quotient.exact h),
    have a = 0 ∨ b = 0, from mul_eq_zero.1 this,
    this.imp (assume h, h.symm ▸ rfl) (assume h, h.symm ▸ rfl))⟩

theorem irreducible_iff_prime_iff :
  (∀ a : α, irreducible a ↔ prime a) ↔ (∀ a : (associates α), irreducible a ↔ prime a) :=
begin
  rw forall_associated, split;
  intros h a; have ha := h a; rw irreducible_mk at *; rw prime_mk at *; exact ha,
end

lemma eq_of_mul_eq_mul_left :
  ∀(a b c : associates α), a ≠ 0 → a * b = a * c → b = c :=
begin
  rintros ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h,
  rcases quotient.exact' h with ⟨u, hu⟩,
  have hu : a * (b * ↑u) = a * c, { rwa [← mul_assoc] },
  exact quotient.sound' ⟨u, mul_left_cancel' (mt mk_eq_zero.2 ha) hu⟩
end

lemma eq_of_mul_eq_mul_right :
  ∀(a b c : associates α), b ≠ 0 → a * b = c * b → a = c :=
λ a b c bne0, (mul_comm b a) ▸ (mul_comm b c) ▸ (eq_of_mul_eq_mul_left b a c bne0)

lemma le_of_mul_le_mul_left (a b c : associates α) (ha : a ≠ 0) :
  a * b ≤ a * c → b ≤ c
| ⟨d, hd⟩ := ⟨d, eq_of_mul_eq_mul_left a _ _ ha $ by rwa ← mul_assoc⟩

lemma one_or_eq_of_le_of_prime :
  ∀(p m : associates α), prime p → m ≤ p → (m = 1 ∨ m = p)
| _ m ⟨hp0, hp1, h⟩ ⟨d, rfl⟩ :=
match h m d (dvd_refl _) with
| or.inl h := classical.by_cases (assume : m = 0, by simp [this]) $
  assume : m ≠ 0,
  have m * d ≤ m * 1, by simpa using h,
  have d ≤ 1, from associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this,
  have d = 1, from bot_unique this,
  by simp [this]
| or.inr h := classical.by_cases (assume : d = 0, by simp [this] at hp0; contradiction) $
  assume : d ≠ 0,
  have d * m ≤ d * 1, by simpa [mul_comm] using h,
  or.inl $ bot_unique $ associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this
end

instance : comm_cancel_monoid_with_zero (associates α) :=
{ mul_left_cancel_of_ne_zero := eq_of_mul_eq_mul_left,
  mul_right_cancel_of_ne_zero := eq_of_mul_eq_mul_right,
  .. (infer_instance : comm_monoid_with_zero (associates α)) }

theorem dvd_not_unit_iff_lt {a b : associates α} :
  dvd_not_unit a b ↔ a < b :=
dvd_and_not_dvd_iff.symm

end comm_cancel_monoid_with_zero

end associates
