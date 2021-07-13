/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import data.set.countable
import set_theory.schroeder_bernstein
import data.fintype.card
import data.nat.enat

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `cardinal` the type of cardinal numbers (in a given universe).
* `cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `cardinal`.
* There is an instance that `cardinal` forms a `canonically_ordered_comm_semiring`.
* Addition `c₁ + c₂` is defined by `cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `cardinal.mul_def : #α * #β = #(α * β)`.
* The order `c₁ ≤ c₂` is defined by `cardinal.le_def α β : #α ≤ #β ↔ nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `cardinal.omega` the cardinality of `ℕ`. This definition is universe polymorphic:
  `cardinal.omega.{u} : cardinal.{u}`
  (contrast with `ℕ : Type`, which lives in a specific universe).
  In some cases the universe level has to be given explicitly.
* `cardinal.min (I : nonempty ι) (c : ι → cardinal)` is the minimal cardinal in the range of `c`.
* `cardinal.succ c` is the successor cardinal, the smallest cardinal larger than `c`.
* `cardinal.sum` is the sum of a collection of cardinals.
* `cardinal.sup` is the supremum of a collection of cardinals.
* `cardinal.powerlt c₁ c₂` or `c₁ ^< c₂` is defined as `sup_{γ < β} α^γ`.

## Main Statements

* Cantor's theorem: `cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `set_theory/cardinal_ordinal.lean`.
* There is an instance `has_pow cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, omega,
Cantor's theorem, König's theorem, Konig's theorem
-/

open function set
open_locale classical

universes u v w x
variables {α β : Type u}

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance cardinal.is_equivalent : setoid (Type u) :=
{ r := λα β, nonempty (α ≃ β),
  iseqv := ⟨λα,
    ⟨equiv.refl α⟩,
    λα β ⟨e⟩, ⟨e.symm⟩,
    λα β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def cardinal : Type (u + 1) := quotient cardinal.is_equivalent

namespace cardinal

/-- The cardinal number of a type -/
def mk : Type u → cardinal := quotient.mk

localized "notation `#` := cardinal.mk" in cardinal

protected lemma eq : mk α = mk β ↔ nonempty (α ≃ β) := quotient.eq

@[simp] theorem mk_def (α : Type u) : @eq cardinal ⟦α⟧ (mk α) := rfl

@[simp] theorem mk_out (c : cardinal) : mk (c.out) = c := quotient.out_eq _

/-- We define the order on cardinal numbers by `mk α ≤ mk β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : has_le cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, nonempty $ α ↪ β) $
  assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
    propext ⟨assume ⟨e⟩, ⟨e.congr e₁ e₂⟩, assume ⟨e⟩, ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

theorem le_def (α β : Type u) : mk α ≤ mk β ↔ nonempty (α ↪ β) :=
iff.rfl

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : injective f) : mk α ≤ mk β :=
⟨⟨f, hf⟩⟩

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : surjective f) : mk β ≤ mk α :=
⟨embedding.of_surjective f hf⟩

theorem le_mk_iff_exists_set {c : cardinal} {α : Type u} :
  c ≤ mk α ↔ ∃ p : set α, mk p = c :=
⟨quotient.induction_on c $ λ β ⟨⟨f, hf⟩⟩,
  ⟨set.range f, eq.symm $ quot.sound ⟨equiv.of_injective f hf⟩⟩,
λ ⟨p, e⟩, e ▸ ⟨⟨subtype.val, λ a b, subtype.eq⟩⟩⟩

theorem out_embedding {c c' : cardinal} : c ≤ c' ↔ nonempty (c.out ↪ c'.out) :=
by { transitivity _, rw [←quotient.out_eq c, ←quotient.out_eq c'], refl }

protected lemma eq_congr : α ≃ β → # α = # β :=
λ h, quot.sound ⟨h⟩

noncomputable instance : linear_order cardinal.{u} :=
{ le          := (≤),
  le_refl     := by rintros ⟨α⟩; exact ⟨embedding.refl _⟩,
  le_trans    := by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.trans e₂⟩,
  le_antisymm := by rintros ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩; exact quotient.sound (e₁.antisymm e₂),
  le_total    := by rintros ⟨α⟩ ⟨β⟩; exact embedding.total,
  decidable_le := classical.dec_rel _ }

-- short-circuit type class inference
noncomputable instance : distrib_lattice cardinal.{u} := by apply_instance

instance : has_zero cardinal.{u} := ⟨⟦pempty⟧⟩

instance : inhabited cardinal.{u} := ⟨0⟩

@[simp]
lemma eq_zero_of_is_empty {α : Type u} [is_empty α] : mk α = 0 :=
quotient.sound ⟨equiv.equiv_pempty α⟩

lemma eq_zero_iff_is_empty {α : Type u} : mk α = 0 ↔ is_empty α :=
⟨λ e, let ⟨h⟩ := quotient.exact e in
  equiv.equiv_empty_equiv α $ h.trans equiv.empty_equiv_pempty.symm,
  @eq_zero_of_is_empty _⟩

theorem ne_zero_iff_nonempty {α : Type u} : mk α ≠ 0 ↔ nonempty α :=
(not_iff_not.2 eq_zero_iff_is_empty).trans not_is_empty_iff

instance : has_one cardinal.{u} := ⟨⟦punit⟧⟩

instance : nontrivial cardinal.{u} :=
⟨⟨1, 0, ne_zero_iff_nonempty.2 ⟨punit.star⟩⟩⟩

theorem le_one_iff_subsingleton {α : Type u} : mk α ≤ 1 ↔ subsingleton α :=
⟨λ ⟨f⟩, ⟨λ a b, f.injective (subsingleton.elim _ _)⟩,
 λ ⟨h⟩, ⟨⟨λ a, punit.star, λ a b _, h _ _⟩⟩⟩

theorem one_lt_iff_nontrivial {α : Type u} : 1 < mk α ↔ nontrivial α :=
by { rw [← not_iff_not, not_nontrivial_iff_subsingleton, ← le_one_iff_subsingleton], simp }

instance : has_add cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, mk (α ⊕ β)) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.sum_congr e₁ e₂⟩⟩

@[simp] theorem add_def (α β) : mk α + mk β = mk (α ⊕ β) := rfl

instance : has_mul cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, mk (α × β)) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.prod_congr e₁ e₂⟩⟩

@[simp] theorem mul_def (α β : Type u) : mk α * mk β = mk (α × β) := rfl

private theorem add_comm (a b : cardinal.{u}) : a + b = b + a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.sum_comm α β⟩

private theorem mul_comm (a b : cardinal.{u}) : a * b = b * a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.prod_comm α β⟩

private theorem zero_add (a : cardinal.{u}) : 0 + a = a :=
quotient.induction_on a $ assume α, quotient.sound ⟨equiv.empty_sum pempty α⟩

private theorem zero_mul (a : cardinal.{u}) : 0 * a = 0 :=
quotient.induction_on a $ assume α, quotient.sound ⟨equiv.pempty_prod α⟩

private theorem one_mul (a : cardinal.{u}) : 1 * a = a :=
quotient.induction_on a $ assume α, quotient.sound ⟨equiv.punit_prod α⟩

private theorem left_distrib (a b c : cardinal.{u}) : a * (b + c) = a * b + a * c :=
quotient.induction_on₃ a b c $ assume α β γ, quotient.sound ⟨equiv.prod_sum_distrib α β γ⟩

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero  {a b : cardinal.{u}} :
  a * b = 0 → a = 0 ∨ b = 0 :=
begin
  refine quotient.induction_on b _,
  refine quotient.induction_on a _,
  intros a b h,
  contrapose h,
  simp_rw [not_or_distrib, ← ne.def] at h,
  have := @prod.nonempty a b (ne_zero_iff_nonempty.mp h.1) (ne_zero_iff_nonempty.mp h.2),
  exact ne_zero_iff_nonempty.mpr this
end

instance : comm_semiring cardinal.{u} :=
{ zero          := 0,
  one           := 1,
  add           := (+),
  mul           := (*),
  zero_add      := zero_add,
  add_zero      := assume a, by rw [add_comm a 0, zero_add a],
  add_assoc     := λa b c, quotient.induction_on₃ a b c $ assume α β γ,
    quotient.sound ⟨equiv.sum_assoc α β γ⟩,
  add_comm      := add_comm,
  zero_mul      := zero_mul,
  mul_zero      := assume a, by rw [mul_comm a 0, zero_mul a],
  one_mul       := one_mul,
  mul_one       := assume a, by rw [mul_comm a 1, one_mul a],
  mul_assoc     := λa b c, quotient.induction_on₃ a b c $ assume α β γ,
    quotient.sound ⟨equiv.prod_assoc α β γ⟩,
  mul_comm      := mul_comm,
  left_distrib  := left_distrib,
  right_distrib := assume a b c,
    by rw [mul_comm (a + b) c, left_distrib c a b, mul_comm c a, mul_comm c b] }

/-- The cardinal exponential. `mk α ^ mk β` is the cardinal of `β → α`. -/
protected def power (a b : cardinal.{u}) : cardinal.{u} :=
quotient.lift_on₂ a b (λα β, mk (β → α)) $ assume α₁ α₂ β₁ β₂ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.arrow_congr e₂ e₁⟩

instance : has_pow cardinal cardinal := ⟨cardinal.power⟩
local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow

@[simp] theorem power_def (α β) : mk α ^ mk β = mk (β → α) := rfl

@[simp] theorem power_zero {a : cardinal} : a ^ 0 = 1 :=
quotient.induction_on a $ assume α, quotient.sound
⟨equiv.pempty_arrow_equiv_punit α⟩

@[simp] theorem power_one {a : cardinal} : a ^ 1 = a :=
quotient.induction_on a $ assume α, quotient.sound
⟨equiv.punit_arrow_equiv α⟩

@[simp] theorem one_power {a : cardinal} : 1 ^ a = 1 :=
quotient.induction_on a $ assume α, quotient.sound
⟨equiv.arrow_punit_equiv_punit α⟩

@[simp] theorem prop_eq_two : mk (ulift Prop) = 2 :=
quot.sound ⟨equiv.ulift.trans $ equiv.Prop_equiv_bool.trans equiv.bool_equiv_punit_sum_punit⟩

@[simp] theorem zero_power {a : cardinal} : a ≠ 0 → 0 ^ a = 0 :=
quotient.induction_on a $ assume α heq,
(ne_zero_iff_nonempty.1 heq).elim $ assume a,
by { haveI : nonempty α := ⟨a⟩, exact quotient.sound ⟨equiv.equiv_pempty _⟩ }

theorem power_ne_zero {a : cardinal} (b) : a ≠ 0 → a ^ b ≠ 0 :=
quotient.induction_on₂ a b $ λ α β h,
let ⟨a⟩ := ne_zero_iff_nonempty.1 h in
ne_zero_iff_nonempty.2 ⟨λ _, a⟩

theorem mul_power {a b c : cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_prod_equiv_prod_arrow α β γ⟩

theorem power_add {a b c : cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.sum_arrow_equiv_prod_arrow β γ α⟩

theorem power_mul {a b c : cardinal} : a ^ (b * c) = (a ^ b) ^ c :=
by rw [_root_.mul_comm b c];
from (quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.curry γ β α⟩)

@[simp] lemma pow_cast_right (κ : cardinal.{u}) :
  ∀ n : ℕ, (κ ^ (↑n : cardinal.{u})) = @has_pow.pow _ _ monoid.has_pow κ n
| 0 := by simp
| (_+1) := by rw [nat.cast_succ, power_add, power_one, _root_.mul_comm, pow_succ, pow_cast_right]

section order_properties
open sum

protected theorem zero_le : ∀(a : cardinal), 0 ≤ a :=
by rintro ⟨α⟩; exact ⟨embedding.of_is_empty⟩

protected theorem add_le_add : ∀{a b c d : cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sum_map e₂⟩

protected theorem add_le_add_left (a) {b c : cardinal} : b ≤ c → a + b ≤ a + c :=
cardinal.add_le_add (le_refl _)


protected theorem le_iff_exists_add {a b : cardinal} : a ≤ b ↔ ∃ c, b = a + c :=
⟨quotient.induction_on₂ a b $ λ α β ⟨⟨f, hf⟩⟩,
  have (α ⊕ ((range f)ᶜ : set β)) ≃ β, from
    (equiv.sum_congr (equiv.of_injective f hf) (equiv.refl _)).trans $
    (equiv.set.sum_compl (range f)),
  ⟨⟦↥(range f)ᶜ⟧, quotient.sound ⟨this.symm⟩⟩,
 λ ⟨c, e⟩, add_zero a ▸ e.symm ▸ cardinal.add_le_add_left _ (cardinal.zero_le _)⟩

instance : order_bot cardinal.{u} :=
{ bot := 0, bot_le := cardinal.zero_le, ..cardinal.linear_order }

instance : canonically_ordered_comm_semiring cardinal.{u} :=
{ add_le_add_left       := λ a b h c, cardinal.add_le_add_left _ h,
  lt_of_add_lt_add_left := λ a b c, lt_imp_lt_of_le_imp_le (cardinal.add_le_add_left _),
  le_iff_exists_add     := @cardinal.le_iff_exists_add,
  eq_zero_or_eq_zero_of_mul_eq_zero := @cardinal.eq_zero_or_eq_zero_of_mul_eq_zero,
  ..cardinal.order_bot,
  ..cardinal.comm_semiring, ..cardinal.linear_order }

noncomputable instance : canonically_linear_ordered_add_monoid cardinal.{u} :=
{ .. (infer_instance : canonically_ordered_add_monoid cardinal.{u}),
  .. cardinal.linear_order }

@[simp] theorem zero_lt_one : (0 : cardinal) < 1 :=
lt_of_le_of_ne (zero_le _) zero_ne_one

lemma zero_power_le (c : cardinal.{u}) : (0 : cardinal.{u}) ^ c ≤ 1 :=
by { by_cases h : c = 0, rw [h, power_zero], rw [zero_power h], apply zero_le }

theorem power_le_power_left : ∀{a b c : cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩; exact
  let ⟨a⟩ := ne_zero_iff_nonempty.1 hα in
  ⟨@embedding.arrow_congr_right _ _ _ ⟨a⟩ e⟩

theorem power_le_max_power_one {a b c : cardinal} (h : b ≤ c) : a ^ b ≤ max (a ^ c) 1 :=
begin
  by_cases ha : a = 0,
  simp [ha, zero_power_le],
  exact le_trans (power_le_power_left ha h) (le_max_left _ _)
end

theorem power_le_power_right {a b c : cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ ⟨e⟩, ⟨embedding.arrow_congr_left e⟩

end order_properties

/-- **Cantor's theorem** -/
theorem cantor : ∀(a : cardinal.{u}), a < 2 ^ a :=
by rw ← prop_eq_two; rintros ⟨a⟩; exact ⟨
  ⟨⟨λ a b, ⟨a = b⟩, λ a b h, cast (ulift.up.inj (@congr_fun _ _ _ _ h b)).symm rfl⟩⟩,
  λ ⟨⟨f, hf⟩⟩, cantor_injective (λ s, f (λ a, ⟨s a⟩)) $
    λ s t h, by funext a; injection congr_fun (hf h) a⟩

instance : no_top_order cardinal.{u} :=
{ no_top := λ a, ⟨_, cantor a⟩, ..cardinal.linear_order }

/-- The minimum cardinal in a family of cardinals (the existence
  of which is provided by `injective_min`). -/
noncomputable def min {ι} (I : nonempty ι) (f : ι → cardinal) : cardinal :=
f $ classical.some $
@embedding.min_injective _ (λ i, (f i).out) I

theorem min_eq {ι} (I) (f : ι → cardinal) : ∃ i, min I f = f i :=
⟨_, rfl⟩

theorem min_le {ι I} (f : ι → cardinal) (i) : min I f ≤ f i :=
by rw [← mk_out (min I f), ← mk_out (f i)]; exact
let ⟨g⟩ := classical.some_spec
  (@embedding.min_injective _ (λ i, (f i).out) I) in
⟨g i⟩

theorem le_min {ι I} {f : ι → cardinal} {a} : a ≤ min I f ↔ ∀ i, a ≤ f i :=
⟨λ h i, le_trans h (min_le _ _),
 λ h, let ⟨i, e⟩ := min_eq I f in e.symm ▸ h i⟩

protected theorem wf : @well_founded cardinal.{u} (<) :=
⟨λ a, classical.by_contradiction $ λ h,
  let ι := {c :cardinal // ¬ acc (<) c},
      f : ι → cardinal := subtype.val,
      ⟨⟨c, hc⟩, hi⟩ := @min_eq ι ⟨⟨_, h⟩⟩ f in
    hc (acc.intro _ (λ j ⟨_, h'⟩,
      classical.by_contradiction $ λ hj, h' $
      by have := min_le f ⟨j, hj⟩; rwa hi at this))⟩

instance has_wf : @has_well_founded cardinal.{u} := ⟨(<), cardinal.wf⟩

instance wo : @is_well_order cardinal.{u} (<) := ⟨cardinal.wf⟩

/-- The successor cardinal - the smallest cardinal greater than
  `c`. This is not the same as `c + 1` except in the case of finite `c`. -/
noncomputable def succ (c : cardinal) : cardinal :=
@min {c' // c < c'} ⟨⟨_, cantor _⟩⟩ subtype.val

theorem lt_succ_self (c : cardinal) : c < succ c :=
by cases min_eq _ _ with s e; rw [succ, e]; exact s.2

theorem succ_le {a b : cardinal} : succ a ≤ b ↔ a < b :=
⟨lt_of_lt_of_le (lt_succ_self _), λ h,
  by exact min_le _ (subtype.mk b h)⟩

theorem lt_succ {a b : cardinal} : a < succ b ↔ a ≤ b :=
by rw [← not_le, succ_le, not_lt]

theorem add_one_le_succ (c : cardinal) : c + 1 ≤ succ c :=
begin
  refine quot.induction_on c (λ α, _) (lt_succ_self c),
  refine quot.induction_on (succ (quot.mk setoid.r α)) (λ β h, _),
  cases h.left with f,
  have : ¬ surjective f := λ hn,
    ne_of_lt h (quotient.sound ⟨equiv.of_bijective f ⟨f.injective, hn⟩⟩),
  cases not_forall.1 this with b nex,
  refine ⟨⟨sum.rec (by exact f) _, _⟩⟩,
  { exact λ _, b },
  { intros a b h, rcases a with a|⟨⟨⟨⟩⟩⟩; rcases b with b|⟨⟨⟨⟩⟩⟩,
    { rw f.injective h },
    { exact nex.elim ⟨_, h⟩ },
    { exact nex.elim ⟨_, h.symm⟩ },
    { refl } }
end

lemma succ_ne_zero (c : cardinal) : succ c ≠ 0 :=
by { rw [←pos_iff_ne_zero, lt_succ], apply zero_le }

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → cardinal) : cardinal := mk Σ i, (f i).out

theorem le_sum {ι} (f : ι → cardinal) (i) : f i ≤ sum f :=
by rw ← quotient.out_eq (f i); exact
⟨⟨λ a, ⟨i, a⟩, λ a b h, eq_of_heq $ by injection h⟩⟩

@[simp] theorem sum_mk {ι} (f : ι → Type*) : sum (λ i, mk (f i)) = mk (Σ i, f i) :=
quot.sound ⟨equiv.sigma_congr_right $ λ i,
  classical.choice $ quotient.exact $ quot.out_eq $ mk (f i)⟩

theorem sum_const (ι : Type u) (a : cardinal.{u}) : sum (λ _:ι, a) = mk ι * a :=
quotient.induction_on a $ λ α, by simp; exact
  quotient.sound ⟨equiv.sigma_equiv_prod _ _⟩

theorem sum_le_sum {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
⟨(embedding.refl _).sigma_map $ λ i, classical.choice $
  by have := H i; rwa [← quot.out_eq (f i), ← quot.out_eq (g i)] at this⟩

/-- The indexed supremum of cardinals is the smallest cardinal above
  everything in the family. -/
noncomputable def sup {ι} (f : ι → cardinal) : cardinal :=
@min {c // ∀ i, f i ≤ c} ⟨⟨sum f, le_sum f⟩⟩ (λ a, a.1)

theorem le_sup {ι} (f : ι → cardinal) (i) : f i ≤ sup f :=
by dsimp [sup]; cases min_eq _ _ with c hc; rw hc; exact c.2 i

theorem sup_le {ι} {f : ι → cardinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
⟨λ h i, le_trans (le_sup _ _) h,
 λ h, by dsimp [sup]; change a with (⟨a, h⟩:subtype _).1; apply min_le⟩

theorem sup_le_sup {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sup f ≤ sup g :=
sup_le.2 $ λ i, le_trans (H i) (le_sup _ _)

theorem sup_le_sum {ι} (f : ι → cardinal) : sup f ≤ sum f :=
sup_le.2 $ le_sum _

theorem sum_le_sup {ι : Type u} (f : ι → cardinal.{u}) : sum f ≤ mk ι * sup.{u u} f :=
by rw ← sum_const; exact sum_le_sum _ _ (le_sup _)

theorem sup_eq_zero {ι} {f : ι → cardinal} [is_empty ι] : sup f = 0 :=
by { rw [← nonpos_iff_eq_zero, sup_le], exact is_empty_elim }

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → cardinal) : cardinal := mk (Π i, (f i).out)

@[simp] theorem prod_mk {ι} (f : ι → Type*) : prod (λ i, mk (f i)) = mk (Π i, f i) :=
quot.sound ⟨equiv.Pi_congr_right $ λ i,
  classical.choice $ quotient.exact $ mk_out $ mk (f i)⟩

theorem prod_const (ι : Type u) (a : cardinal.{u}) : prod (λ _:ι, a) = a ^ mk ι :=
quotient.induction_on a $ by simp

theorem prod_le_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
⟨embedding.Pi_congr_right $ λ i, classical.choice $
  by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

theorem prod_ne_zero {ι} (f : ι → cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 :=
begin
  suffices : nonempty (Π i, (f i).out) ↔ ∀ i, nonempty (f i).out,
  { simpa [← ne_zero_iff_nonempty, prod] },
  exact classical.nonempty_pi
end

theorem prod_eq_zero {ι} (f : ι → cardinal) : prod f = 0 ↔ ∃ i, f i = 0 :=
not_iff_not.1 $ by simpa using prod_ne_zero f

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : cardinal.{u} → cardinal.{max u v}` -/
def lift (c : cardinal.{u}) : cardinal.{max u v} :=
quotient.lift_on c (λ α, ⟦ulift α⟧) $ λ α β ⟨e⟩,
quotient.sound ⟨equiv.ulift.trans $ e.trans equiv.ulift.symm⟩

theorem lift_mk (α) : lift.{u v} (mk α) = mk (ulift.{v u} α) := rfl

theorem lift_umax : lift.{u (max u v)} = lift.{u v} :=
funext $ λ a, quot.induction_on a $ λ α,
quotient.sound ⟨equiv.ulift.trans equiv.ulift.symm⟩

theorem lift_id' (a : cardinal) : lift a = a :=
quot.induction_on a $ λ α, quot.sound ⟨equiv.ulift⟩

@[simp] theorem lift_id : ∀ a, lift.{u u} a = a := lift_id'.{u u}

@[simp] theorem lift_lift (a : cardinal) :
  lift.{(max u v) w} (lift.{u v} a) = lift.{u (max v w)} a :=
quot.induction_on a $ λ α,
quotient.sound ⟨equiv.ulift.trans $ equiv.ulift.trans equiv.ulift.symm⟩

theorem lift_mk_le {α : Type u} {β : Type v} :
  lift.{u (max v w)} (mk α) ≤ lift.{v (max u w)} (mk β) ↔ nonempty (α ↪ β) :=
⟨λ ⟨f⟩, ⟨embedding.congr equiv.ulift equiv.ulift f⟩,
 λ ⟨f⟩, ⟨embedding.congr equiv.ulift.symm equiv.ulift.symm f⟩⟩

theorem lift_mk_eq {α : Type u} {β : Type v} :
  lift.{u (max v w)} (mk α) = lift.{v (max u w)} (mk β) ↔ nonempty (α ≃ β) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨equiv.ulift.symm.trans $ f.trans equiv.ulift⟩,
 λ ⟨f⟩, ⟨equiv.ulift.trans $ f.trans equiv.ulift.symm⟩⟩

@[simp] theorem lift_le {a b : cardinal} : lift a ≤ lift b ↔ a ≤ b :=
quotient.induction_on₂ a b $ λ α β,
by rw ← lift_umax; exact lift_mk_le

@[simp] theorem lift_inj {a b : cardinal} : lift a = lift b ↔ a = b :=
by simp [le_antisymm_iff]

@[simp] theorem lift_lt {a b : cardinal} : lift a < lift b ↔ a < b :=
by simp [lt_iff_le_not_le, -not_le]

@[simp] theorem lift_zero : lift 0 = 0 :=
quotient.sound ⟨equiv.ulift.trans equiv.pempty_equiv_pempty⟩

@[simp] theorem lift_one : lift 1 = 1 :=
quotient.sound ⟨equiv.ulift.trans equiv.punit_equiv_punit⟩

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
quotient.induction_on₂ a b $ λ α β,
quotient.sound ⟨equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
quotient.induction_on₂ a b $ λ α β,
quotient.sound ⟨equiv.ulift.trans (equiv.prod_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_power (a b) : lift (a ^ b) = lift a ^ lift b :=
quotient.induction_on₂ a b $ λ α β,
quotient.sound ⟨equiv.ulift.trans (equiv.arrow_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_two_power (a) : lift (2 ^ a) = 2 ^ lift a :=
by simp [bit0]

@[simp] theorem lift_min {ι I} (f : ι → cardinal) : lift (min I f) = min I (lift ∘ f) :=
le_antisymm (le_min.2 $ λ a, lift_le.2 $ min_le _ a) $
let ⟨i, e⟩ := min_eq I (lift ∘ f) in
by rw e; exact lift_le.2 (le_min.2 $ λ j, lift_le.1 $
by have := min_le (lift ∘ f) j; rwa e at this)

theorem lift_down {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a → ∃ a', lift a' = b :=
quotient.induction_on₂ a b $ λ α β,
by dsimp; rw [← lift_id (mk β), ← lift_umax, ← lift_umax.{u v}, lift_mk_le]; exact
λ ⟨f⟩, ⟨mk (set.range f), eq.symm $ lift_mk_eq.2
  ⟨embedding.equiv_of_surjective
    (embedding.cod_restrict _ f set.mem_range_self)
    $ λ ⟨a, ⟨b, e⟩⟩, ⟨b, subtype.eq e⟩⟩⟩

theorem le_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
      ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

@[simp] theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
le_antisymm
  (le_of_not_gt $ λ h, begin
    rcases lt_lift_iff.1 h with ⟨b, e, h⟩,
    rw [lt_succ, ← lift_le, e] at h,
    exact not_lt_of_le h (lt_succ_self _)
  end)
  (succ_le.2 $ lift_lt.2 $ lt_succ_self _)

@[simp] theorem lift_max {a : cardinal.{u}} {b : cardinal.{v}} :
  lift.{u (max v w)} a = lift.{v (max u w)} b ↔ lift.{u v} a = lift.{v u} b :=
calc lift.{u (max v w)} a = lift.{v (max u w)} b
  ↔ lift.{(max u v) w} (lift.{u v} a)
    = lift.{(max u v) w} (lift.{v u} b) : by simp
  ... ↔ lift.{u v} a = lift.{v u} b : lift_inj

theorem mk_prod {α : Type u} {β : Type v} :
  mk (α × β) = lift.{u v} (mk α) * lift.{v u} (mk β) :=
quotient.sound ⟨equiv.prod_congr (equiv.ulift).symm (equiv.ulift).symm⟩

theorem sum_const_eq_lift_mul (ι : Type u) (a : cardinal.{v}) :
  sum (λ _:ι, a) = lift.{u v} (mk ι) * lift.{v u} a :=
begin
  apply quotient.induction_on a,
  intro α,
  simp only [cardinal.mk_def, cardinal.sum_mk, cardinal.lift_id],
  convert mk_prod using 1,
  exact quotient.sound ⟨equiv.sigma_equiv_prod ι α⟩,
end

/-- `ω` is the smallest infinite cardinal, also known as ℵ₀. -/
def omega : cardinal.{u} := lift (mk ℕ)

lemma mk_nat : mk nat = omega := (lift_id _).symm

theorem omega_ne_zero : omega ≠ 0 :=
ne_zero_iff_nonempty.2 ⟨⟨0⟩⟩

theorem omega_pos : 0 < omega :=
pos_iff_ne_zero.2 omega_ne_zero

@[simp] theorem lift_omega : lift omega = omega := lift_lift _

/- properties about the cast from nat -/

@[simp] theorem mk_fin : ∀ (n : ℕ), mk (fin n) = n
| 0     := quotient.sound ⟨equiv.equiv_pempty _⟩
| (n+1) := by rw [nat.cast_succ, ← mk_fin]; exact
  quotient.sound (fintype.card_eq.1 $ by simp)

@[simp] theorem lift_nat_cast (n : ℕ) : lift n = n :=
by induction n; simp *

lemma lift_eq_nat_iff {a : cardinal.{u}} {n : ℕ} : lift.{u v} a = n ↔ a = n :=
by rw [← lift_nat_cast.{u v} n, lift_inj]

lemma nat_eq_lift_eq_iff {n : ℕ} {a : cardinal.{u}} :
  (n : cardinal) = lift.{u v} a ↔ (n : cardinal) = a :=
by rw [← lift_nat_cast.{u v} n, lift_inj]

theorem lift_mk_fin (n : ℕ) : lift (mk (fin n)) = n := by simp

theorem fintype_card (α : Type u) [fintype α] : mk α = fintype.card α :=
by rw [← lift_mk_fin.{u}, ← lift_id (mk α), lift_mk_eq.{u 0 u}];
   exact fintype.card_eq.1 (by simp)

theorem card_le_of_finset {α} (s : finset α) :
  (s.card : cardinal) ≤ cardinal.mk α :=
begin
  rw (_ : (s.card : cardinal) = cardinal.mk s),
  { exact ⟨function.embedding.subtype _⟩ },
  rw [cardinal.fintype_card, fintype.card_coe]
end

@[simp, norm_cast] theorem nat_cast_pow {m n : ℕ} : (↑(pow m n) : cardinal) = m ^ n :=
by induction n; simp [pow_succ', -_root_.add_comm, power_add, *]

@[simp, norm_cast] theorem nat_cast_le {m n : ℕ} : (m : cardinal) ≤ n ↔ m ≤ n :=
by rw [← lift_mk_fin, ← lift_mk_fin, lift_le]; exact
⟨λ ⟨⟨f, hf⟩⟩, by simpa only [fintype.card_fin] using fintype.card_le_of_injective f hf,
  λ h, ⟨(fin.cast_le h).to_embedding⟩⟩

@[simp, norm_cast] theorem nat_cast_lt {m n : ℕ} : (m : cardinal) < n ↔ m < n :=
by simp [lt_iff_le_not_le, -not_le]

@[simp, norm_cast] theorem nat_cast_inj {m n : ℕ} : (m : cardinal) = n ↔ m = n :=
by simp [le_antisymm_iff]

@[simp, norm_cast, priority 900] theorem nat_succ (n : ℕ) : (n.succ : cardinal) = succ n :=
le_antisymm (add_one_le_succ _) (succ_le.2 $ nat_cast_lt.2 $ nat.lt_succ_self _)

@[simp] theorem succ_zero : succ 0 = 1 :=
by norm_cast

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : finset α, s.card ≤ n) :
  # α ≤ n :=
begin
  refine lt_succ.1 (lt_of_not_ge $ λ hn, _),
  rw [← cardinal.nat_succ, ← cardinal.lift_mk_fin n.succ] at hn,
  cases hn with f,
  refine not_lt_of_le (H $ finset.univ.map f) _,
  rw [finset.card_map, ← fintype.card, fintype.card_ulift, fintype.card_fin],
  exact n.lt_succ_self
end

theorem cantor' (a) {b : cardinal} (hb : 1 < b) : a < b ^ a :=
by rw [← succ_le, (by norm_cast : succ 1 = 2)] at hb;
   exact lt_of_lt_of_le (cantor _) (power_le_power_right hb)

theorem one_le_iff_pos {c : cardinal} : 1 ≤ c ↔ 0 < c :=
by rw [← succ_zero, succ_le]

theorem one_le_iff_ne_zero {c : cardinal} : 1 ≤ c ↔ c ≠ 0 :=
by rw [one_le_iff_pos, pos_iff_ne_zero]

theorem nat_lt_omega (n : ℕ) : (n : cardinal.{u}) < omega :=
succ_le.1 $ by rw [← nat_succ, ← lift_mk_fin, omega, lift_mk_le.{0 0 u}]; exact
⟨⟨coe, λ a b, fin.ext⟩⟩

@[simp] theorem one_lt_omega : 1 < omega :=
by simpa using nat_lt_omega 1

theorem lt_omega {c : cardinal.{u}} : c < omega ↔ ∃ n : ℕ, c = n :=
⟨λ h, begin
  rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩,
  rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩,
  suffices : finite S,
  { cases this, resetI,
    existsi fintype.card S,
    rw [← lift_nat_cast.{0 u}, lift_inj, fintype_card S] },
  by_contra nf,
  have P : ∀ (n : ℕ) (IH : ∀ i<n, S), ∃ a : S, ¬ ∃ y h, IH y h = a :=
    λ n IH,
    let g : {i | i < n} → S := λ ⟨i, h⟩, IH i h in
    not_forall.1 (λ h, nf
      ⟨fintype.of_surjective g (λ a, subtype.exists.2 (h a))⟩),
  let F : ℕ → S := nat.lt_wf.fix (λ n IH, classical.some (P n IH)),
  refine not_le_of_lt h' ⟨⟨F, _⟩⟩,
  suffices : ∀ (n : ℕ) (m < n), F m ≠ F n,
  { refine λ m n, not_imp_not.1 (λ ne, _),
    rcases lt_trichotomy m n with h|h|h,
    { exact this n m h },
    { contradiction },
    { exact (this m n h).symm } },
  intros n m h,
  have := classical.some_spec (P n (λ y _, F y)),
  rw [← show F n = classical.some (P n (λ y _, F y)),
      from nat.lt_wf.fix_eq (λ n IH, classical.some (P n IH)) n] at this,
  exact λ e, this ⟨m, h, e⟩,
end, λ ⟨n, e⟩, e.symm ▸ nat_lt_omega _⟩

theorem omega_le {c : cardinal.{u}} : omega ≤ c ↔ ∀ n : ℕ, (n:cardinal) ≤ c :=
⟨λ h n, le_trans (le_of_lt (nat_lt_omega _)) h,
 λ h, le_of_not_lt $ λ hn, begin
  rcases lt_omega.1 hn with ⟨n, rfl⟩,
  exact not_le_of_lt (nat.lt_succ_self _) (nat_cast_le.1 (h (n+1)))
end⟩

theorem lt_omega_iff_fintype {α : Type u} : mk α < omega ↔ nonempty (fintype α) :=
lt_omega.trans ⟨λ ⟨n, e⟩, begin
  rw [← lift_mk_fin n] at e,
  cases quotient.exact e with f,
  exact ⟨fintype.of_equiv _ f.symm⟩
end, λ ⟨_⟩, by exactI ⟨_, fintype_card _⟩⟩

theorem lt_omega_iff_finite {α} {S : set α} : mk S < omega ↔ finite S :=
lt_omega_iff_fintype

instance can_lift_cardinal_nat : can_lift cardinal ℕ :=
⟨ coe, λ x, x < omega, λ x hx, let ⟨n, hn⟩ := lt_omega.mp hx in ⟨n, hn.symm⟩⟩

theorem add_lt_omega {a b : cardinal} (ha : a < omega) (hb : b < omega) : a + b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_add]; apply nat_lt_omega
end

lemma add_lt_omega_iff {a b : cardinal} : a + b < omega ↔ a < omega ∧ b < omega :=
⟨λ h, ⟨lt_of_le_of_lt (self_le_add_right _ _) h, lt_of_le_of_lt (self_le_add_left _ _) h⟩,
  λ⟨h1, h2⟩, add_lt_omega h1 h2⟩

theorem mul_lt_omega {a b : cardinal} (ha : a < omega) (hb : b < omega) : a * b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_mul]; apply nat_lt_omega
end

lemma mul_lt_omega_iff {a b : cardinal} : a * b < omega ↔ a = 0 ∨ b = 0 ∨ a < omega ∧ b < omega :=
begin
  split,
  { intro h, by_cases ha : a = 0, { left, exact ha },
    right, by_cases hb : b = 0, { left, exact hb },
    right, rw [← ne, ← one_le_iff_ne_zero] at ha hb, split,
    { rw [← mul_one a],
      refine lt_of_le_of_lt (canonically_ordered_semiring.mul_le_mul (le_refl a) hb) h },
    { rw [← _root_.one_mul b],
      refine lt_of_le_of_lt (canonically_ordered_semiring.mul_le_mul ha (le_refl b)) h }},
  rintro (rfl|rfl|⟨ha,hb⟩); simp only [*, mul_lt_omega, omega_pos, _root_.zero_mul, mul_zero]
end

lemma mul_lt_omega_iff_of_ne_zero {a b : cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
  a * b < omega ↔ a < omega ∧ b < omega :=
by simp [mul_lt_omega_iff, ha, hb]

theorem power_lt_omega {a b : cardinal} (ha : a < omega) (hb : b < omega) : a ^ b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_pow]; apply nat_lt_omega
end

lemma eq_one_iff_unique {α : Type*} :
  mk α = 1 ↔ subsingleton α ∧ nonempty α :=
calc mk α = 1 ↔ mk α ≤ 1 ∧ ¬mk α < 1 : eq_iff_le_not_lt
          ... ↔ subsingleton α ∧ nonempty α :
begin
  apply and_congr le_one_iff_subsingleton,
  push_neg,
  rw [one_le_iff_ne_zero, ne_zero_iff_nonempty]
end

theorem infinite_iff {α : Type u} : infinite α ↔ omega ≤ mk α :=
by rw [←not_lt, lt_omega_iff_fintype, not_nonempty_fintype]

lemma denumerable_iff {α : Type u} : nonempty (denumerable α) ↔ mk α = omega :=
⟨λ⟨h⟩, quotient.sound $ by exactI ⟨ (denumerable.eqv α).trans equiv.ulift.symm ⟩,
 λ h, by { cases quotient.exact h with f, exact ⟨denumerable.mk' $ f.trans equiv.ulift⟩ }⟩

lemma countable_iff (s : set α) : countable s ↔ mk s ≤ omega :=
begin
  rw [countable_iff_exists_injective], split,
  rintro ⟨f, hf⟩, exact ⟨embedding.trans ⟨f, hf⟩ equiv.ulift.symm.to_embedding⟩,
  rintro ⟨f'⟩, cases embedding.trans f' equiv.ulift.to_embedding with f hf, exact ⟨f, hf⟩
end

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
noncomputable def to_nat : zero_hom cardinal ℕ :=
⟨λ c, if h : c < omega.{v} then classical.some (lt_omega.1 h) else 0,
  begin
    have h : 0 < omega := nat_lt_omega 0,
    rw [dif_pos h, ← cardinal.nat_cast_inj, ← classical.some_spec (lt_omega.1 h), nat.cast_zero],
  end⟩

lemma to_nat_apply_of_lt_omega {c : cardinal} (h : c < omega) :
  c.to_nat = classical.some (lt_omega.1 h) :=
dif_pos h

@[simp]
lemma to_nat_apply_of_omega_le {c : cardinal} (h : omega ≤ c) :
  c.to_nat = 0 :=
dif_neg (not_lt_of_le h)

@[simp]
lemma cast_to_nat_of_lt_omega {c : cardinal} (h : c < omega) :
  ↑c.to_nat = c :=
by rw [to_nat_apply_of_lt_omega h, ← classical.some_spec (lt_omega.1 h)]

@[simp]
lemma to_nat_cast (n : ℕ) : cardinal.to_nat n = n :=
begin
  rw [to_nat_apply_of_lt_omega (nat_lt_omega n), ← nat_cast_inj],
  exact (classical.some_spec (lt_omega.1 (nat_lt_omega n))).symm,
end

/-- `to_nat` has a right-inverse: coercion. -/
lemma to_nat_right_inverse : function.right_inverse (coe : ℕ → cardinal) to_nat := to_nat_cast

lemma to_nat_surjective : surjective to_nat := to_nat_right_inverse.surjective

@[simp]
lemma mk_to_nat_of_infinite [h : infinite α] : (mk α).to_nat = 0 :=
dif_neg (not_lt_of_le (infinite_iff.1 h))

@[simp]
lemma mk_to_nat_eq_card [fintype α] : (mk α).to_nat = fintype.card α :=
by simp [fintype_card]

@[simp]
lemma zero_to_nat : cardinal.to_nat 0 = 0 :=
by rw [← to_nat_cast 0, nat.cast_zero]

@[simp]
lemma one_to_nat : cardinal.to_nat 1 = 1 :=
by rw [← to_nat_cast 1, nat.cast_one]

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to `⊤`. -/
noncomputable def to_enat : cardinal →+ enat :=
{ to_fun := λ c, if c < omega.{v} then c.to_nat else ⊤,
  map_zero' := by simp [if_pos (lt_trans zero_lt_one one_lt_omega)],
  map_add' := λ x y, begin
    by_cases hx : x < omega,
    { obtain ⟨x0, rfl⟩ := lt_omega.1 hx,
      by_cases hy : y < omega,
      { obtain ⟨y0, rfl⟩ := lt_omega.1 hy,
        simp only [add_lt_omega hx hy, hx, hy, to_nat_cast, if_true],
        rw [← nat.cast_add, to_nat_cast, enat.coe_add] },
      { rw [if_neg hy, if_neg, enat.add_top],
        contrapose! hy,
        apply lt_of_le_of_lt le_add_self hy } },
    { rw [if_neg hx, if_neg, enat.top_add],
      contrapose! hx,
      apply lt_of_le_of_lt le_self_add hx },
  end }

@[simp]
lemma to_enat_apply_of_lt_omega {c : cardinal} (h : c < omega) :
  c.to_enat = c.to_nat :=
if_pos h

@[simp]
lemma to_enat_apply_of_omega_le {c : cardinal} (h : omega ≤ c) :
  c.to_enat = ⊤ :=
if_neg (not_lt_of_le h)

@[simp]
lemma to_enat_cast (n : ℕ) : cardinal.to_enat n = n :=
by rw [to_enat_apply_of_lt_omega (nat_lt_omega n), to_nat_cast]

@[simp]
lemma mk_to_enat_of_infinite [h : infinite α] : (mk α).to_enat = ⊤ :=
to_enat_apply_of_omega_le (infinite_iff.1 h)

lemma to_enat_surjective : surjective to_enat :=
begin
  intro x,
  exact enat.cases_on x ⟨omega, to_enat_apply_of_omega_le (le_refl omega)⟩
    (λ n, ⟨n, to_enat_cast n⟩),
end

@[simp]
lemma mk_to_enat_eq_coe_card [fintype α] : (mk α).to_enat = fintype.card α :=
by simp [fintype_card]

lemma mk_int : mk ℤ = omega :=
denumerable_iff.mp ⟨by apply_instance⟩

lemma mk_pnat : mk ℕ+ = omega :=
denumerable_iff.mp ⟨by apply_instance⟩

lemma two_le_iff : (2 : cardinal) ≤ mk α ↔ ∃x y : α, x ≠ y :=
begin
  split,
  { rintro ⟨f⟩, refine ⟨f $ sum.inl ⟨⟩, f $ sum.inr ⟨⟩, _⟩, intro h, cases f.2 h },
  { rintro ⟨x, y, h⟩, by_contra h',
    rw [not_le, ←nat.cast_two, nat_succ, lt_succ, nat.cast_one, le_one_iff_subsingleton] at h',
    apply h, exactI subsingleton.elim _ _ }
end

lemma two_le_iff' (x : α) : (2 : cardinal) ≤ mk α ↔ ∃y : α, x ≠ y :=
begin
  rw [two_le_iff],
  split,
  { rintro ⟨y, z, h⟩, refine classical.by_cases (λ(h' : x = y), _) (λ h', ⟨y, h'⟩),
    rw [←h'] at h, exact ⟨z, h⟩ },
  { rintro ⟨y, h⟩, exact ⟨x, y, h⟩ }
end

/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
lt_of_not_ge $ λ ⟨F⟩, begin
  have : inhabited (Π (i : ι), (g i).out),
  { refine ⟨λ i, classical.choice $ ne_zero_iff_nonempty.1 _⟩,
    rw mk_out,
    exact ne_of_gt (lt_of_le_of_lt (zero_le _) (H i)) }, resetI,
  let G := inv_fun F,
  have sG : surjective G := inv_fun_surjective F.2,
  choose C hc using show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b,
  { assume i,
    simp only [- not_exists, not_exists.symm, not_forall.symm],
    refine λ h, not_le_of_lt (H i) _,
    rw [← mk_out (f i), ← mk_out (g i)],
    exact ⟨embedding.of_surjective _ h⟩ },
  exact (let ⟨⟨i, a⟩, h⟩ := sG C in hc i a (congr_fun h _))
end

@[simp] theorem mk_empty : mk empty = 0 :=
fintype_card empty

@[simp] theorem mk_pempty : mk pempty = 0 :=
fintype_card pempty

@[simp] theorem mk_plift_of_false {p : Prop} (h : ¬ p) : mk (plift p) = 0 :=
by { haveI : is_empty p := ⟨h⟩, exact quotient.sound ⟨equiv.plift.trans $ equiv.equiv_pempty _⟩ }

theorem mk_unit : mk unit = 1 :=
(fintype_card unit).trans nat.cast_one

@[simp] theorem mk_punit : mk punit = 1 :=
(fintype_card punit).trans nat.cast_one

@[simp] theorem mk_singleton {α : Type u} (x : α) : mk ({x} : set α) = 1 :=
quotient.sound ⟨equiv.set.singleton x⟩

@[simp] theorem mk_plift_of_true {p : Prop} (h : p) : mk (plift p) = 1 :=
quotient.sound ⟨equiv.plift.trans $ equiv.prop_equiv_punit h⟩

@[simp] theorem mk_bool : mk bool = 2 :=
quotient.sound ⟨equiv.bool_equiv_punit_sum_punit⟩

@[simp] theorem mk_Prop : mk Prop = 2 :=
(quotient.sound ⟨equiv.Prop_equiv_bool⟩ : mk Prop = mk bool).trans mk_bool

@[simp] theorem mk_set {α : Type u} : mk (set α) = 2 ^ mk α :=
begin
  rw [← prop_eq_two, cardinal.power_def (ulift Prop) α, cardinal.eq],
  exact ⟨equiv.arrow_congr (equiv.refl _) equiv.ulift.symm⟩,
end

@[simp] theorem mk_option {α : Type u} : mk (option α) = mk α + 1 :=
quotient.sound ⟨equiv.option_equiv_sum_punit α⟩

theorem mk_list_eq_sum_pow (α : Type u) : mk (list α) = sum (λ n : ℕ, (mk α)^(n:cardinal.{u})) :=
calc  mk (list α)
    = mk (Σ n, vector α n) : quotient.sound ⟨(equiv.sigma_preimage_equiv list.length).symm⟩
... = mk (Σ n, fin n → α) : quotient.sound ⟨equiv.sigma_congr_right $ λ n,
  ⟨vector.nth, vector.of_fn, vector.of_fn_nth, λ f, funext $ vector.nth_of_fn f⟩⟩
... = mk (Σ n : ℕ, ulift.{u} (fin n) → α) : quotient.sound ⟨equiv.sigma_congr_right $ λ n,
  equiv.arrow_congr equiv.ulift.symm (equiv.refl α)⟩
... = sum (λ n : ℕ, (mk α)^(n:cardinal.{u})) :
  by simp only [(lift_mk_fin _).symm, lift_mk, power_def, sum_mk]

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : mk (quot r) ≤ mk α :=
mk_le_of_surjective quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : setoid α} : mk (quotient s) ≤ mk α :=
mk_quot_le

theorem mk_subtype_le {α : Type u} (p : α → Prop) : mk (subtype p) ≤ mk α :=
⟨embedding.subtype p⟩

theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
  mk (subtype p) ≤ mk (subtype q) :=
⟨embedding.subtype_map (embedding.refl α) h⟩

@[simp] theorem mk_emptyc (α : Type u) : mk (∅ : set α) = 0 :=
quotient.sound ⟨equiv.set.pempty α⟩

lemma mk_emptyc_iff {α : Type u} {s : set α} : mk s = 0 ↔ s = ∅ :=
begin
  split,
  { intro h,
    have h2 : cardinal.mk s = cardinal.mk pempty, by simp [h],
    refine set.eq_empty_iff_forall_not_mem.mpr (λ _ hx, _),
    rcases cardinal.eq.mp h2 with ⟨f, _⟩,
    cases f ⟨_, hx⟩ },
  { intro, convert mk_emptyc _ }
end

theorem mk_univ {α : Type u} : mk (@univ α) = mk α :=
quotient.sound ⟨equiv.set.univ α⟩

theorem mk_image_le {α β : Type u} {f : α → β} {s : set α} : mk (f '' s) ≤ mk s :=
mk_le_of_surjective surjective_onto_image

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : set α} :
  lift.{v u} (mk (f '' s)) ≤ lift.{u v} (mk s) :=
lift_mk_le.{v u 0}.mpr ⟨embedding.of_surjective _ surjective_onto_image⟩

theorem mk_range_le {α β : Type u} {f : α → β} : mk (range f) ≤ mk α :=
mk_le_of_surjective surjective_onto_range

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
  lift.{v u} (mk (range f)) ≤ lift.{u v} (mk α) :=
lift_mk_le.{v u 0}.mpr ⟨embedding.of_surjective _ surjective_onto_range⟩

lemma mk_range_eq (f : α → β) (h : injective f) : mk (range f) = mk α :=
quotient.sound ⟨(equiv.of_injective f h).symm⟩

lemma mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : injective f) :
  lift.{v u} (mk (range f)) = lift.{u v} (mk α) :=
begin
  have := (@lift_mk_eq.{v u max u v} (range f) α).2 ⟨(equiv.of_injective f hf).symm⟩,
  simp only [lift_umax.{u v}, lift_umax.{v u}] at this,
  exact this
end

lemma mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : injective f) :
  lift.{v (max u w)} (# (range f)) = lift.{u (max v w)} (# α) :=
lift_mk_eq.mpr ⟨(equiv.of_injective f hf).symm⟩

theorem mk_image_eq {α β : Type u} {f : α → β} {s : set α} (hf : injective f) :
  mk (f '' s) = mk s :=
quotient.sound ⟨(equiv.set.image f s hf).symm⟩

theorem mk_Union_le_sum_mk {α ι : Type u} {f : ι → set α} : mk (⋃ i, f i) ≤ sum (λ i, mk (f i)) :=
calc mk (⋃ i, f i) ≤ mk (Σ i, f i) : mk_le_of_surjective (set.sigma_to_Union_surjective f)
  ... = sum (λ i, mk (f i)) : (sum_mk _).symm

theorem mk_Union_eq_sum_mk {α ι : Type u} {f : ι → set α} (h : ∀i j, i ≠ j → disjoint (f i) (f j)) :
  mk (⋃ i, f i) = sum (λ i, mk (f i)) :=
calc mk (⋃ i, f i) = mk (Σi, f i) : quot.sound ⟨set.Union_eq_sigma_of_disjoint h⟩
  ... = sum (λi, mk (f i)) : (sum_mk _).symm

lemma mk_Union_le {α ι : Type u} (f : ι → set α) :
  mk (⋃ i, f i) ≤ mk ι * cardinal.sup.{u u} (λ i, mk (f i)) :=
le_trans mk_Union_le_sum_mk (sum_le_sup _)

lemma mk_sUnion_le {α : Type u} (A : set (set α)) :
  mk (⋃₀ A) ≤ mk A * cardinal.sup.{u u} (λ s : A, mk s) :=
by { rw [sUnion_eq_Union], apply mk_Union_le }

lemma mk_bUnion_le {ι α : Type u} (A : ι → set α) (s : set ι) :
  mk (⋃(x ∈ s), A x) ≤ mk s * cardinal.sup.{u u} (λ x : s, mk (A x.1)) :=
by { rw [bUnion_eq_Union], apply mk_Union_le }

@[simp] lemma finset_card {α : Type u} {s : finset α} : ↑(finset.card s) = mk s :=
by rw [fintype_card, nat_cast_inj, fintype.card_coe]

lemma finset_card_lt_omega (s : finset α) : mk (↑s : set α) < omega :=
by { rw [lt_omega_iff_fintype], exact ⟨finset.subtype.fintype s⟩ }

theorem mk_eq_nat_iff_finset {α} {s : set α} {n : ℕ} :
  mk s = n ↔ ∃ t : finset α, (t : set α) = s ∧ t.card = n :=
begin
  split,
  { intro h,
    have : # s < omega, by { rw h, exact nat_lt_omega n },
    refine ⟨(lt_omega_iff_finite.1 this).to_finset, finite.coe_to_finset _, nat_cast_inj.1 _⟩,
    rwa [finset_card, finite.coe_sort_to_finset] },
  { rintro ⟨t, rfl, rfl⟩,
    exact finset_card.symm }
end

theorem mk_union_add_mk_inter {α : Type u} {S T : set α} :
  mk (S ∪ T : set α) + mk (S ∩ T : set α) = mk S + mk T :=
quot.sound ⟨equiv.set.union_sum_inter S T⟩

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
lemma mk_union_le {α : Type u} (S T : set α) : mk (S ∪ T : set α) ≤ mk S + mk T :=
@mk_union_add_mk_inter α S T ▸ self_le_add_right (mk (S ∪ T : set α)) (mk (S ∩ T : set α))

theorem mk_union_of_disjoint {α : Type u} {S T : set α} (H : disjoint S T) :
  mk (S ∪ T : set α) = mk S + mk T :=
quot.sound ⟨equiv.set.union H⟩

lemma mk_sum_compl {α} (s : set α) : #s + #(sᶜ : set α) = #α :=
quotient.sound ⟨equiv.set.sum_compl s⟩

lemma mk_le_mk_of_subset {α} {s t : set α} (h : s ⊆ t) : mk s ≤ mk t :=
⟨set.embedding_of_subset s t h⟩

lemma mk_subtype_mono {p q : α → Prop} (h : ∀x, p x → q x) : mk {x // p x} ≤ mk {x // q x} :=
⟨embedding_of_subset _ _ h⟩

lemma mk_set_le (s : set α) : mk s ≤ mk α :=
mk_subtype_le s

lemma mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : set α) (h : injective f) :
  lift.{v u} (mk (f '' s)) = lift.{u v} (mk s) :=
lift_mk_eq.{v u 0}.mpr ⟨(equiv.set.image f s h).symm⟩

lemma mk_image_eq_of_inj_on_lift {α : Type u} {β : Type v} (f : α → β) (s : set α)
  (h : inj_on f s) : lift.{v u} (mk (f '' s)) = lift.{u v} (mk s) :=
lift_mk_eq.{v u 0}.mpr ⟨(equiv.set.image_of_inj_on f s h).symm⟩

lemma mk_image_eq_of_inj_on {α β : Type u} (f : α → β) (s : set α) (h : inj_on f s) :
  mk (f '' s) = mk s :=
quotient.sound ⟨(equiv.set.image_of_inj_on f s h).symm⟩

lemma mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
  mk {a : α // p (e a)} = mk {b : β // p b} :=
quotient.sound ⟨equiv.subtype_equiv_of_subtype e⟩

lemma mk_sep (s : set α) (t : α → Prop) : mk ({ x ∈ s | t x } : set α) = mk { x : s | t x.1 } :=
quotient.sound ⟨equiv.set.sep s t⟩

lemma mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : injective f) : lift.{u v} (mk (f ⁻¹' s)) ≤ lift.{v u} (mk s) :=
begin
  rw lift_mk_le.{u v 0}, use subtype.coind (λ x, f x.1) (λ x, x.2),
  apply subtype.coind_injective, exact h.comp subtype.val_injective
end

lemma mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : s ⊆ range f) : lift.{v u} (mk s) ≤ lift.{u v} (mk (f ⁻¹' s)) :=
begin
  rw lift_mk_le.{v u 0},
  refine ⟨⟨_, _⟩⟩,
  { rintro ⟨y, hy⟩, rcases classical.subtype_of_exists (h hy) with ⟨x, rfl⟩, exact ⟨x, hy⟩ },
  rintro ⟨y, hy⟩ ⟨y', hy'⟩, dsimp,
  rcases classical.subtype_of_exists (h hy) with ⟨x, rfl⟩,
  rcases classical.subtype_of_exists (h hy') with ⟨x', rfl⟩,
  simp, intro hxx', rw hxx'
end

lemma mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : lift.{u v} (mk (f ⁻¹' s)) = lift.{v u} (mk s) :=
le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

lemma mk_preimage_of_injective (f : α → β) (s : set β) (h : injective f) :
  mk (f ⁻¹' s) ≤ mk s :=
by { convert mk_preimage_of_injective_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_subset_range (f : α → β) (s : set β)
  (h : s ⊆ range f) : mk s ≤ mk (f ⁻¹' s) :=
by { convert mk_preimage_of_subset_range_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_injective_of_subset_range (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : mk (f ⁻¹' s) = mk s :=
by { convert mk_preimage_of_injective_of_subset_range_lift.{u u} f s h h2 using 1; rw [lift_id] }

lemma mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : set α}
  {t : set β} (h : t ⊆ f '' s) :
    lift.{v u} (mk t) ≤ lift.{u v} (mk ({ x ∈ s | f x ∈ t } : set α)) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_subset_range_lift _ _ h using 1,
     rw [mk_sep], refl }

lemma mk_subset_ge_of_subset_image (f : α → β) {s : set α} {t : set β} (h : t ⊆ f '' s) :
  mk t ≤ mk ({ x ∈ s | f x ∈ t } : set α) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_subset_range _ _ h using 1,
     rw [mk_sep], refl }

theorem le_mk_iff_exists_subset {c : cardinal} {α : Type u} {s : set α} :
  c ≤ mk s ↔ ∃ p : set α, p ⊆ s ∧ mk p = c :=
begin
  rw [le_mk_iff_exists_set, ←subtype.exists_set_subtype],
  apply exists_congr, intro t, rw [mk_image_eq], apply subtype.val_injective
end

/-- The function α^{<β}, defined to be sup_{γ < β} α^γ.
  We index over {s : set β.out // mk s < β } instead of {γ // γ < β}, because the latter lives in a
  higher universe -/
noncomputable def powerlt (α β : cardinal.{u}) : cardinal.{u} :=
sup.{u u} (λ(s : {s : set β.out // mk s < β}), α ^ mk.{u} s)

infix ` ^< `:80 := powerlt

theorem powerlt_aux {c c' : cardinal} (h : c < c') :
  ∃(s : {s : set c'.out // mk s < c'}), mk s = c :=
begin
  cases out_embedding.mp (le_of_lt h) with f,
  have : mk ↥(range ⇑f) = c, { rwa [mk_range_eq, mk, quotient.out_eq c], exact f.2 },
  exact ⟨⟨range f, by convert h⟩, this⟩
end

lemma le_powerlt {c₁ c₂ c₃ : cardinal} (h : c₂ < c₃) : c₁ ^ c₂ ≤ c₁ ^< c₃ :=
by { rcases powerlt_aux h with ⟨s, rfl⟩, apply le_sup _ s }

lemma powerlt_le {c₁ c₂ c₃ : cardinal} : c₁ ^< c₂ ≤ c₃ ↔ ∀(c₄ < c₂), c₁ ^ c₄ ≤ c₃ :=
begin
  rw [powerlt, sup_le],
  split,
  { intros h c₄ hc₄, rcases powerlt_aux hc₄ with ⟨s, rfl⟩, exact h s },
  intros h s, exact h _ s.2
end

lemma powerlt_le_powerlt_left {a b c : cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
by { rw [powerlt, sup_le], rintro ⟨s, hs⟩, apply le_powerlt, exact lt_of_lt_of_le hs h }

lemma powerlt_succ {c₁ c₂ : cardinal} (h : c₁ ≠ 0) : c₁ ^< c₂.succ = c₁ ^ c₂ :=
begin
  apply le_antisymm,
  { rw powerlt_le, intros c₃ h2, apply power_le_power_left h, rwa [←lt_succ] },
  { apply le_powerlt, apply lt_succ_self }
end

lemma powerlt_max {c₁ c₂ c₃ : cardinal} : c₁ ^< max c₂ c₃ = max (c₁ ^< c₂) (c₁ ^< c₃) :=
by { cases le_total c₂ c₃; simp only [max_eq_left, max_eq_right, h, powerlt_le_powerlt_left] }

lemma zero_powerlt {a : cardinal} (h : a ≠ 0) : 0 ^< a = 1 :=
begin
  apply le_antisymm,
  { rw [powerlt_le], intros c hc, apply zero_power_le },
  convert le_powerlt (pos_iff_ne_zero.2 h), rw [power_zero]
end

lemma powerlt_zero {a : cardinal} : a ^< 0 = 0 :=
begin
  convert sup_eq_zero,
  exact subtype.is_empty_of_false (λ x, (zero_le _).not_lt),
end

end cardinal

lemma equiv.cardinal_eq {α β} : α ≃ β → cardinal.mk α = cardinal.mk β :=
cardinal.eq_congr
