/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
import algebra.pointwise
import group_theory.coset
import dynamics.periodic_pts
import algebra.iterate_hom

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`x ∈ G` is the minimal `n ≥ 1` such that `x ^ n = 1`.

## Main definitions

* `is_of_fin_order` is a predicate on an element `x` of a monoid `G` saying that `x` is of finite
  order.
* `is_of_fin_add_order` is the additive analogue of `is_of_find_order`.
* `order_of x` defines the order of an element `x` of a monoid `G`, by convention its value is `0`
  if `x` has infinite order.
* `add_order_of` is the additive analogue of `order_of`.

## Tags
order of an element
-/

open function nat

universes u v

variables {G : Type u} {A : Type v}
variables {x y : G} {a b : A} {n m : ℕ}

section monoid_add_monoid

variables [monoid G] [add_monoid A]

section is_of_fin_order

lemma is_periodic_pt_add_iff_nsmul_eq_zero (a : A) :
  is_periodic_pt ((+) a) n 0 ↔ n • a = 0 :=
by rw [is_periodic_pt, is_fixed_pt, add_left_iterate, add_zero]

@[to_additive is_periodic_pt_add_iff_nsmul_eq_zero]
lemma is_periodic_pt_mul_iff_pow_eq_one (x : G) : is_periodic_pt ((*) x) n 1 ↔ x ^ n = 1 :=
by rw [is_periodic_pt, is_fixed_pt, mul_left_iterate, mul_one]

/-- `is_of_fin_add_order` is a predicate on an element `a` of an additive monoid to be of finite
order, i.e. there exists `n ≥ 1` such that `n • a = 0`.-/
def is_of_fin_add_order (a : A) : Prop :=
(0 : A) ∈ periodic_pts ((+) a)

/-- `is_of_fin_order` is a predicate on an element `x` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `x ^ n = 1`.-/
@[to_additive is_of_fin_add_order]
def is_of_fin_order (x : G) : Prop :=
(1 : G) ∈ periodic_pts ((*) x)

lemma is_of_fin_add_order_of_mul_iff :
  is_of_fin_add_order (additive.of_mul x) ↔ is_of_fin_order x := iff.rfl

lemma is_of_fin_order_of_add_iff :
  is_of_fin_order (multiplicative.of_add a) ↔ is_of_fin_add_order a := iff.rfl

lemma is_of_fin_add_order_iff_nsmul_eq_zero (a : A) :
  is_of_fin_add_order a ↔ ∃ n, 0 < n ∧ n • a = 0 :=
by { convert iff.rfl, simp only [exists_prop, is_periodic_pt_add_iff_nsmul_eq_zero] }

@[to_additive is_of_fin_add_order_iff_nsmul_eq_zero]
lemma is_of_fin_order_iff_pow_eq_one (x : G) :
  is_of_fin_order x ↔ ∃ n, 0 < n ∧ x ^ n = 1 :=
by { convert iff.rfl, simp [is_periodic_pt_mul_iff_pow_eq_one] }

end is_of_fin_order

/-- `add_order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it
exists. Otherwise, i.e. if `a` is of infinite order, then `add_order_of a` is `0` by convention.-/
noncomputable def add_order_of (a : A) : ℕ :=
minimal_period ((+) a) 0

/-- `order_of x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `order_of x` is `0` by convention.-/
@[to_additive add_order_of]
noncomputable def order_of (x : G) : ℕ :=
minimal_period ((*) x) 1

attribute [to_additive add_order_of] order_of

@[to_additive]
lemma commute.order_of_mul_dvd_lcm (h : commute x y) :
  order_of (x * y) ∣ nat.lcm (order_of x) (order_of y) :=
begin
  convert function.commute.minimal_period_of_comp_dvd_lcm h.function_commute_mul_left,
  rw [order_of, comp_mul_left],
end

@[simp] lemma add_order_of_of_mul_eq_order_of (x : G) :
  add_order_of (additive.of_mul x) = order_of x := rfl

@[simp] lemma order_of_of_add_eq_add_order_of (a : A) :
  order_of (multiplicative.of_add a) = add_order_of a := rfl

@[to_additive add_order_of_pos']
lemma order_of_pos' (h : is_of_fin_order x) : 0 < order_of x :=
minimal_period_pos_of_mem_periodic_pts h

lemma pow_order_of_eq_one (x : G) : x ^ order_of x = 1 :=
begin
  convert is_periodic_pt_minimal_period ((*) x) _,
  rw [order_of, mul_left_iterate, mul_one],
end

lemma add_order_of_nsmul_eq_zero (a : A) : add_order_of a • a = 0 :=
begin
  convert is_periodic_pt_minimal_period ((+) a) _,
  rw [add_order_of, add_left_iterate, add_zero],
end

attribute [to_additive add_order_of_nsmul_eq_zero] pow_order_of_eq_one

@[to_additive add_order_of_eq_zero]
lemma order_of_eq_zero (h : ¬ is_of_fin_order x) : order_of x = 0 :=
by rwa [order_of, minimal_period, dif_neg]

lemma nsmul_ne_zero_of_lt_add_order_of' (n0 : n ≠ 0) (h : n < add_order_of a) :
  n • a ≠ 0 :=
λ j, not_is_periodic_pt_of_pos_of_lt_minimal_period n0 h
  ((is_periodic_pt_add_iff_nsmul_eq_zero a).mpr j)

@[to_additive nsmul_ne_zero_of_lt_add_order_of']
lemma pow_eq_one_of_lt_order_of' (n0 : n ≠ 0) (h : n < order_of x) : x ^ n ≠ 1 :=
λ j, not_is_periodic_pt_of_pos_of_lt_minimal_period n0 h
  ((is_periodic_pt_mul_iff_pow_eq_one x).mpr j)

lemma add_order_of_le_of_nsmul_eq_zero (hn : 0 < n) (h : n • a = 0) : add_order_of a ≤ n :=
is_periodic_pt.minimal_period_le hn (by rwa is_periodic_pt_add_iff_nsmul_eq_zero)

@[to_additive add_order_of_le_of_nsmul_eq_zero]
lemma order_of_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : order_of x ≤ n :=
is_periodic_pt.minimal_period_le hn (by rwa is_periodic_pt_mul_iff_pow_eq_one)

@[simp] lemma order_of_one : order_of (1 : G) = 1 :=
by rw [order_of, one_mul_eq_id, minimal_period_id]

@[simp] lemma add_order_of_zero : add_order_of (0 : A) = 1 :=
by simp only [←order_of_of_add_eq_add_order_of, order_of_one, of_add_zero]

attribute [to_additive add_order_of_zero] order_of_one

@[simp] lemma order_of_eq_one_iff : order_of x = 1 ↔ x = 1 :=
by rw [order_of, is_fixed_point_iff_minimal_period_eq_one, is_fixed_pt, mul_one]

@[simp] lemma add_order_of_eq_one_iff : add_order_of a = 1 ↔ a = 0 :=
by simp [← order_of_of_add_eq_add_order_of]

attribute [to_additive add_order_of_eq_one_iff] order_of_eq_one_iff

lemma pow_eq_mod_order_of {n : ℕ} : x ^ n = x ^ (n % order_of x) :=
calc x ^ n = x ^ (n % order_of x + order_of x * (n / order_of x)) : by rw [nat.mod_add_div]
       ... = x ^ (n % order_of x) : by simp [pow_add, pow_mul, pow_order_of_eq_one]

lemma nsmul_eq_mod_add_order_of {n : ℕ} : n • a = (n % add_order_of a) • a :=
begin
  apply multiplicative.of_add.injective,
  rw [← order_of_of_add_eq_add_order_of, of_add_nsmul, of_add_nsmul, pow_eq_mod_order_of],
end

attribute [to_additive nsmul_eq_mod_add_order_of] pow_eq_mod_order_of

lemma order_of_dvd_of_pow_eq_one (h : x ^ n = 1) : order_of x ∣ n :=
is_periodic_pt.minimal_period_dvd ((is_periodic_pt_mul_iff_pow_eq_one _).mpr h)

lemma add_order_of_dvd_of_nsmul_eq_zero (h : n • a = 0) : add_order_of a ∣ n :=
is_periodic_pt.minimal_period_dvd ((is_periodic_pt_add_iff_nsmul_eq_zero _).mpr h)

attribute [to_additive add_order_of_dvd_of_nsmul_eq_zero] order_of_dvd_of_pow_eq_one

lemma add_order_of_dvd_iff_nsmul_eq_zero {n : ℕ} : add_order_of a ∣ n ↔ n • a = 0 :=
⟨λ h, by rw [nsmul_eq_mod_add_order_of, nat.mod_eq_zero_of_dvd h, zero_nsmul],
  add_order_of_dvd_of_nsmul_eq_zero⟩

@[to_additive add_order_of_dvd_iff_nsmul_eq_zero]
lemma order_of_dvd_iff_pow_eq_one {n : ℕ} : order_of x ∣ n ↔ x ^ n = 1 :=
⟨λ h, by rw [pow_eq_mod_order_of, nat.mod_eq_zero_of_dvd h, pow_zero], order_of_dvd_of_pow_eq_one⟩

lemma exists_pow_eq_self_of_coprime (h : n.coprime (order_of x)) :
  ∃ m : ℕ, (x ^ n) ^ m = x :=
begin
  by_cases h0 : order_of x = 0,
  { rw [h0, coprime_zero_right] at h,
    exact ⟨1, by rw [h, pow_one, pow_one]⟩ },
  by_cases h1 : order_of x = 1,
  { exact ⟨0, by rw [order_of_eq_one_iff.mp h1, one_pow, one_pow]⟩ },
  obtain ⟨m, hm⟩ :=
    exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩),
  exact ⟨m, by rw [←pow_mul, pow_eq_mod_order_of, hm, pow_one]⟩,
end

lemma exists_nsmul_eq_self_of_coprime (a : A)
  (h : coprime n (add_order_of a)) : ∃ m : ℕ, m • (n • a) = a :=
begin
  change n.coprime (order_of (multiplicative.of_add a)) at h,
  exact exists_pow_eq_self_of_coprime h,
end

attribute [to_additive exists_nsmul_eq_self_of_coprime] exists_pow_eq_self_of_coprime

lemma add_order_of_eq_add_order_of_iff {B : Type*} [add_monoid B] {b : B} :
  add_order_of a = add_order_of b ↔ ∀ n : ℕ, n • a = 0 ↔ n • b = 0 :=
begin
  simp_rw ← add_order_of_dvd_iff_nsmul_eq_zero,
  exact ⟨λ h n, by rw h, λ h, nat.dvd_antisymm ((h _).mpr (dvd_refl _)) ((h _).mp (dvd_refl _))⟩,
end

@[to_additive add_order_of_eq_add_order_of_iff]
lemma order_of_eq_order_of_iff {H : Type*} [monoid H] {y : H} :
  order_of x = order_of y ↔ ∀ n : ℕ, x ^ n = 1 ↔ y ^ n = 1 :=
by simp_rw [← is_periodic_pt_mul_iff_pow_eq_one, ← minimal_period_eq_minimal_period_iff, order_of]

lemma add_order_of_injective {B : Type*} [add_monoid B] (f : A →+ B)
  (hf : function.injective f) (a : A) : add_order_of (f a) = add_order_of a :=
by simp_rw [add_order_of_eq_add_order_of_iff, ←f.map_nsmul, ←f.map_zero, hf.eq_iff, iff_self,
            forall_const]

@[to_additive add_order_of_injective]
lemma order_of_injective {H : Type*} [monoid H] (f : G →* H)
  (hf : function.injective f) (x : G) : order_of (f x) = order_of x :=
by simp_rw [order_of_eq_order_of_iff, ←f.map_pow, ←f.map_one, hf.eq_iff, iff_self, forall_const]

@[simp, norm_cast, to_additive] lemma order_of_submonoid {H : submonoid G}
  (y : H) : order_of (y : G) = order_of y :=
order_of_injective H.subtype subtype.coe_injective y

variables (x)

lemma order_of_pow' (h : n ≠ 0) :
  order_of (x ^ n) = order_of x / gcd (order_of x) n :=
begin
  convert minimal_period_iterate_eq_div_gcd h,
  simp only [order_of, mul_left_iterate],
end

variables (a)

lemma add_order_of_nsmul' (h : n ≠ 0) :
  add_order_of (n • a) = add_order_of a / gcd (add_order_of a) n :=
by simpa [← order_of_of_add_eq_add_order_of, of_add_nsmul] using order_of_pow' _ h

attribute [to_additive add_order_of_nsmul'] order_of_pow'

variable (n)

lemma order_of_pow'' (h : is_of_fin_order x) :
  order_of (x ^ n) = order_of x / gcd (order_of x) n :=
begin
  convert minimal_period_iterate_eq_div_gcd' h,
  simp only [order_of, mul_left_iterate],
end

lemma add_order_of_nsmul'' (h : is_of_fin_add_order a) :
  add_order_of (n • a) = add_order_of a / gcd (add_order_of a) n :=
by simp [← order_of_of_add_eq_add_order_of, of_add_nsmul,
  order_of_pow'' _ n (is_of_fin_order_of_add_iff.mpr h)]

attribute [to_additive add_order_of_nsmul''] order_of_pow''

section p_prime

variables {a x n} {p : ℕ} [hp : fact p.prime]
include hp

lemma add_order_of_eq_prime (hg : p • a = 0) (hg1 : a ≠ 0) : add_order_of a = p :=
minimal_period_eq_prime ((is_periodic_pt_add_iff_nsmul_eq_zero _).mpr hg)
  (by rwa [is_fixed_pt, add_zero])

@[to_additive add_order_of_eq_prime]
lemma order_of_eq_prime (hg : x ^ p = 1) (hg1 : x ≠ 1) : order_of x = p :=
minimal_period_eq_prime ((is_periodic_pt_mul_iff_pow_eq_one _).mpr hg)
  (by rwa [is_fixed_pt, mul_one])

lemma add_order_of_eq_prime_pow (hnot : ¬ (p ^ n) • a = 0) (hfin : (p ^ (n + 1)) • a = 0) :
  add_order_of a = p ^ (n + 1) :=
begin
  apply minimal_period_eq_prime_pow;
  rwa is_periodic_pt_add_iff_nsmul_eq_zero,
end

@[to_additive add_order_of_eq_prime_pow]
lemma order_of_eq_prime_pow (hnot : ¬ x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1) :
  order_of x = p ^ (n + 1) :=
begin
  apply minimal_period_eq_prime_pow;
  rwa is_periodic_pt_mul_iff_pow_eq_one,
end

omit hp
-- An example on how to determine the order of an element of a finite group.
example : order_of (-1 : units ℤ) = 2 :=
begin
  haveI : fact (prime 2) := ⟨prime_two⟩,
  exact order_of_eq_prime (int.units_mul_self _) dec_trivial,
end

end p_prime

end monoid_add_monoid

section cancel_monoid
variables [left_cancel_monoid G] (x)
variables [add_left_cancel_monoid A] (a)

lemma pow_injective_aux (h : n ≤ m)
  (hm : m < order_of x) (eq : x ^ n = x ^ m) : n = m :=
by_contradiction $ assume ne : n ≠ m,
  have h₁ : m - n > 0, from nat.pos_of_ne_zero (by simp [nat.sub_eq_iff_eq_add h, ne.symm]),
  have h₂ : m = n + (m - n) := (nat.add_sub_of_le h).symm,
  have h₃ : x ^ (m - n) = 1,
    by { rw [h₂, pow_add] at eq, apply mul_left_cancel, convert eq.symm, exact mul_one (x ^ n) },
  have le : order_of x ≤ m - n, from order_of_le_of_pow_eq_one h₁ h₃,
  have lt : m - n < order_of x,
    from (nat.sub_lt_left_iff_lt_add h).mpr $ nat.lt_add_left _ _ _ hm,
  lt_irrefl _ (le.trans_lt lt)

-- TODO: This lemma was originally private, but this doesn't seem to work with `to_additive`,
-- therefore the private got removed.
lemma nsmul_injective_aux {n m : ℕ} (h : n ≤ m)
  (hm : m < add_order_of a) (eq : n • a = m • a) : n = m :=
begin
  apply_fun multiplicative.of_add at eq,
  rw [of_add_nsmul, of_add_nsmul] at eq,
  rw ← order_of_of_add_eq_add_order_of at hm,
  exact pow_injective_aux (multiplicative.of_add a) h hm eq,
end

attribute [to_additive nsmul_injective_aux] pow_injective_aux

lemma nsmul_injective_of_lt_add_order_of {n m : ℕ}
  (hn : n < add_order_of a) (hm : m < add_order_of a) (eq : n • a = m • a) : n = m :=
(le_total n m).elim
  (assume h, nsmul_injective_aux a h hm eq)
  (assume h, (nsmul_injective_aux a h hn eq.symm).symm)

@[to_additive nsmul_injective_of_lt_add_order_of]
lemma pow_injective_of_lt_order_of
  (hn : n < order_of x) (hm : m < order_of x) (eq : x ^ n = x ^ m) : n = m :=
(le_total n m).elim
  (assume h, pow_injective_aux x h hm eq)
  (assume h, (pow_injective_aux x h hn eq.symm).symm)

end cancel_monoid

section group
variables [group G] [add_group A] {x a} {i : ℤ}

@[simp, norm_cast, to_additive] lemma order_of_subgroup {H : subgroup G}
  (y: H) : order_of (y : G) = order_of y :=
order_of_injective H.subtype subtype.coe_injective y

lemma gpow_eq_mod_order_of : x ^ i = x ^ (i % order_of x) :=
calc x ^ i = x ^ (i % order_of x + order_of x * (i / order_of x)) :
    by rw [int.mod_add_div]
       ... = x ^ (i % order_of x) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]

lemma gsmul_eq_mod_add_order_of : i • a = (i % add_order_of a) • a :=
begin
  apply multiplicative.of_add.injective,
  simp [of_add_gsmul, gpow_eq_mod_order_of],
end

attribute [to_additive gsmul_eq_mod_add_order_of] gpow_eq_mod_order_of

@[to_additive add_order_of_eq_zero_iff] lemma order_of_eq_zero_iff :
  order_of x = 0 ↔ ¬ is_of_fin_order x :=
⟨λ h H, (order_of_pos' H).ne' h, order_of_eq_zero⟩

@[to_additive nsmul_inj_iff_of_add_order_of_eq_zero]
lemma pow_inj_iff_of_order_of_eq_zero (h : order_of x = 0) {n m : ℕ} :
  x ^ n = x ^ m ↔ n = m :=
begin
  by_cases hx : x = 1,
  { rw [←order_of_eq_one_iff, h] at hx,
    contradiction },
  rw [order_of_eq_zero_iff, is_of_fin_order_iff_pow_eq_one] at h,
  push_neg at h,
  induction n with n IH generalizing m,
  { cases m,
    { simp },
    { simpa [eq_comm] using h m.succ m.zero_lt_succ } },
  { cases m,
    { simpa using h n.succ n.zero_lt_succ },
    { simp [pow_succ, IH] } }
end

lemma pow_inj_mod {n m : ℕ} :
  x ^ n = x ^ m ↔ n % order_of x = m % order_of x :=
begin
  cases (order_of x).zero_le.eq_or_lt with hx hx,
  { simp [pow_inj_iff_of_order_of_eq_zero, hx.symm] },
  rw [pow_eq_mod_order_of, @pow_eq_mod_order_of _ _ _ m],
  exact ⟨pow_injective_of_lt_order_of _ (nat.mod_lt _ hx) (nat.mod_lt _ hx), λ h, congr_arg _ h⟩
end

lemma nsmul_inj_mod {n m : ℕ} :
  n • a = m • a ↔ n % add_order_of a = m % add_order_of a :=
begin
  cases (add_order_of a).zero_le.eq_or_lt with hx hx,
  { simp [nsmul_inj_iff_of_add_order_of_eq_zero, hx.symm] },
  rw [nsmul_eq_mod_add_order_of, @nsmul_eq_mod_add_order_of _ _ _ m],
  refine ⟨nsmul_injective_of_lt_add_order_of a (nat.mod_lt n hx) (nat.mod_lt m hx), λ h, _⟩,
  rw h
end

attribute [to_additive nsmul_inj_mod] pow_inj_mod

end group

section fintype
variables [fintype G] [fintype A]

section finite_monoid
variables [monoid G] [add_monoid A]
open_locale big_operators

lemma sum_card_add_order_of_eq_card_nsmul_eq_zero [decidable_eq A] (hn : 0 < n) :
  ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ a : A, add_order_of a = m)).card
  = (finset.univ.filter (λ a : A, n • a = 0)).card :=
calc ∑ m in (finset.range n.succ).filter (∣ n),
        (finset.univ.filter (λ a : A, add_order_of a = m)).card
    = _ : (finset.card_bUnion (by { intros, apply finset.disjoint_filter.2, cc })).symm
... = _ : congr_arg finset.card (finset.ext (begin
  assume a,
  suffices : add_order_of a ≤ n ∧ add_order_of a ∣ n ↔ n • a = 0,
  { simpa [nat.lt_succ_iff], },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in
                by rw [hm, mul_comm, mul_nsmul, add_order_of_nsmul_eq_zero, nsmul_zero],
    λ h, ⟨add_order_of_le_of_nsmul_eq_zero hn h, add_order_of_dvd_of_nsmul_eq_zero h⟩⟩
end))

@[to_additive sum_card_add_order_of_eq_card_nsmul_eq_zero]
lemma sum_card_order_of_eq_card_pow_eq_one [decidable_eq G] (hn : 0 < n) :
  ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ x : G, order_of x = m)).card
  = (finset.univ.filter (λ x : G, x ^ n = 1)).card :=
calc ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ x : G, order_of x = m)).card
    = _ : (finset.card_bUnion (by { intros, apply finset.disjoint_filter.2, cc })).symm
... = _ : congr_arg finset.card (finset.ext (begin
  assume x,
  suffices : order_of x ≤ n ∧ order_of x ∣ n ↔ x ^ n = 1,
  { simpa [nat.lt_succ_iff], },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in by rw [hm, pow_mul, pow_order_of_eq_one, one_pow],
    λ h, ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩
end))

end finite_monoid

section finite_cancel_monoid
-- TODO: Of course everything also works for right_cancel_monoids.
variables [left_cancel_monoid G] [add_left_cancel_monoid A]

-- TODO: Use this to show that a finite left cancellative monoid is a group.
lemma exists_pow_eq_one (x : G) : is_of_fin_order x :=
begin
  refine (is_of_fin_order_iff_pow_eq_one _).mpr _,
  obtain ⟨i, j, a_eq, ne⟩ : ∃(i j : ℕ), x ^ i = x ^ j ∧ i ≠ j :=
    by simpa only [not_forall, exists_prop] using (not_injective_infinite_fintype (λi:ℕ, x^i)),
  wlog h'' : j ≤ i,
  refine ⟨i - j, nat.sub_pos_of_lt (lt_of_le_of_ne h'' ne.symm), mul_right_injective (x^j) _⟩,
  rw [mul_one, ← pow_add, ← a_eq, nat.add_sub_cancel' h''],
end

lemma exists_nsmul_eq_zero (a : A) : is_of_fin_add_order a :=
begin
  rcases exists_pow_eq_one (multiplicative.of_add a) with ⟨i, hi1, hi2⟩,
  refine ⟨i, hi1, multiplicative.of_add.injective _⟩,
  rw [add_left_iterate, of_add_zero, of_add_eq_one, add_zero],
  exact (is_periodic_pt_mul_iff_pow_eq_one (multiplicative.of_add a)).mp hi2,
end

attribute [to_additive exists_nsmul_eq_zero] exists_pow_eq_one

lemma add_order_of_le_card_univ : add_order_of a ≤ fintype.card A :=
finset.le_card_of_inj_on_range (• a)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, nsmul_injective_of_lt_add_order_of a hi hj)

@[to_additive add_order_of_le_card_univ]
lemma order_of_le_card_univ : order_of x ≤ fintype.card G :=
finset.le_card_of_inj_on_range ((^) x)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, pow_injective_of_lt_order_of x hi hj)

/-- This is the same as `add_order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative additive monoid.-/
lemma add_order_of_pos (a : A) : 0 < add_order_of a := add_order_of_pos' (exists_nsmul_eq_zero _)

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
@[to_additive add_order_of_pos]
lemma order_of_pos (x : G) : 0 < order_of x := order_of_pos' (exists_pow_eq_one x)

open nat

/-- This is the same as `add_order_of_nsmul'` and `add_order_of_nsmul` but with one assumption less
which is automatic in the case of a finite cancellative additive monoid. -/
lemma add_order_of_nsmul (a : A) :
  add_order_of (n • a) = add_order_of a / gcd (add_order_of a) n :=
add_order_of_nsmul'' _ _ (exists_nsmul_eq_zero _)

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid.-/
@[to_additive add_order_of_nsmul]
lemma order_of_pow (x : G) :
  order_of (x ^ n) = order_of x / gcd (order_of x) n := order_of_pow'' _ _ (exists_pow_eq_one _)

lemma mem_multiples_iff_mem_range_add_order_of [decidable_eq A] :
  b ∈ add_submonoid.multiples a ↔
  b ∈ (finset.range (add_order_of a)).image ((• a) : ℕ → A)  :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (add_order_of_pos a)
  (assume i, nsmul_eq_mod_add_order_of.symm)

@[to_additive mem_multiples_iff_mem_range_add_order_of]
lemma mem_powers_iff_mem_range_order_of [decidable_eq G] :
  y ∈ submonoid.powers x ↔ y ∈ (finset.range (order_of x)).image ((^) x : ℕ → G) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos x)
  (assume i, pow_eq_mod_order_of.symm)

noncomputable instance decidable_multiples [decidable_eq A] :
  decidable_pred (∈ add_submonoid.multiples a) :=
begin
  assume b,
  apply decidable_of_iff' (b ∈ (finset.range (add_order_of a)).image (• a)),
  exact mem_multiples_iff_mem_range_add_order_of,
end

@[to_additive decidable_multiples]
noncomputable instance decidable_powers [decidable_eq G] :
  decidable_pred (∈ submonoid.powers x) :=
begin
  assume y,
  apply decidable_of_iff'
    (y ∈ (finset.range (order_of x)).image ((^) x)),
  exact mem_powers_iff_mem_range_order_of
end

/-- The equivalence between `fin (order_of x)` and `submonoid.powers x`, sending `i` to `x ^ i`. -/
noncomputable def fin_equiv_powers (x : G) :
  fin (order_of x) ≃ (submonoid.powers x : set G) :=
equiv.of_bijective (λ n, ⟨x ^ ↑n, ⟨n, rfl⟩⟩) ⟨λ ⟨i, hi⟩ ⟨j, hj⟩ ij,
  subtype.mk_eq_mk.2 (pow_injective_of_lt_order_of x hi hj (subtype.mk_eq_mk.1 ij)),
  λ ⟨_, i, rfl⟩, ⟨⟨i % order_of x, mod_lt i (order_of_pos x)⟩, subtype.eq pow_eq_mod_order_of.symm⟩⟩

/-- The equivalence between `fin (add_order_of a)` and `add_submonoid.multiples a`,
  sending `i` to `i • a`."-/
noncomputable def fin_equiv_multiples (a : A) :
  fin (add_order_of a) ≃ (add_submonoid.multiples a : set A) :=
fin_equiv_powers (multiplicative.of_add a)

attribute [to_additive fin_equiv_multiples] fin_equiv_powers

@[simp] lemma fin_equiv_powers_apply {x : G} {n : fin (order_of x)} :
  fin_equiv_powers x n = ⟨x ^ ↑n, n, rfl⟩ := rfl

@[simp] lemma fin_equiv_multiples_apply {a : A} {n : fin (add_order_of a)} :
  fin_equiv_multiples a n = ⟨nsmul ↑n a, n, rfl⟩ := rfl

attribute [to_additive fin_equiv_multiples_apply] fin_equiv_powers_apply

@[simp] lemma fin_equiv_powers_symm_apply (x : G) (n : ℕ)
  {hn : ∃ (m : ℕ), x ^ m = x ^ n} :
  ((fin_equiv_powers x).symm ⟨x ^ n, hn⟩) = ⟨n % order_of x, nat.mod_lt _ (order_of_pos x)⟩ :=
by rw [equiv.symm_apply_eq, fin_equiv_powers_apply, subtype.mk_eq_mk,
  pow_eq_mod_order_of, fin.coe_mk]

@[simp] lemma fin_equiv_multiples_symm_apply (a : A) (n : ℕ)
  {hn : ∃ (m : ℕ), m • a = n • a} :
  ((fin_equiv_multiples a).symm ⟨n • a, hn⟩) =
    ⟨n % add_order_of a, nat.mod_lt _ (add_order_of_pos a)⟩ :=
fin_equiv_powers_symm_apply (multiplicative.of_add a) n

attribute [to_additive fin_equiv_multiples_symm_apply] fin_equiv_powers_symm_apply

/-- The equivalence between `submonoid.powers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
noncomputable def powers_equiv_powers (h : order_of x = order_of y) :
  (submonoid.powers x : set G) ≃ (submonoid.powers y : set G) :=
(fin_equiv_powers x).symm.trans ((fin.cast h).to_equiv.trans (fin_equiv_powers y))

/-- The equivalence between `submonoid.multiples` of two elements `a, b` of the same additive order,
  mapping `i • a` to `i • b`. -/
noncomputable def multiples_equiv_multiples (h : add_order_of a = add_order_of b) :
  (add_submonoid.multiples a : set A) ≃ (add_submonoid.multiples b : set A) :=
(fin_equiv_multiples a).symm.trans ((fin.cast h).to_equiv.trans (fin_equiv_multiples b))

attribute [to_additive multiples_equiv_multiples] powers_equiv_powers

@[simp]
lemma powers_equiv_powers_apply (h : order_of x = order_of y)
  (n : ℕ) : powers_equiv_powers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩ :=
begin
  rw [powers_equiv_powers, equiv.trans_apply, equiv.trans_apply,
    fin_equiv_powers_symm_apply, ← equiv.eq_symm_apply, fin_equiv_powers_symm_apply],
  simp [h]
end

@[simp]
lemma multiples_equiv_multiples_apply (h : add_order_of a = add_order_of b)
  (n : ℕ) : multiples_equiv_multiples h ⟨n • a, n, rfl⟩ = ⟨n • b, n, rfl⟩ :=
powers_equiv_powers_apply h n

attribute [to_additive multiples_equiv_multiples_apply] powers_equiv_powers_apply

lemma order_eq_card_powers [decidable_eq G] :
  order_of x = fintype.card (submonoid.powers x : set G) :=
(fintype.card_fin (order_of x)).symm.trans (fintype.card_eq.2 ⟨fin_equiv_powers x⟩)

lemma add_order_of_eq_card_multiples [decidable_eq A] :
  add_order_of a = fintype.card (add_submonoid.multiples a : set A) :=
(fintype.card_fin (add_order_of a)).symm.trans (fintype.card_eq.2 ⟨fin_equiv_multiples a⟩)

attribute [to_additive add_order_of_eq_card_multiples] order_eq_card_powers

end finite_cancel_monoid

section finite_group
variables [group G] [add_group A]

lemma exists_gpow_eq_one (x : G) : ∃ (i : ℤ) (H : i ≠ 0), x ^ (i : ℤ) = 1 :=
--lemma exists_gpow_eq_one (a : α) : ∃ (i : ℤ) (H : i ≠ 0), a ^ (i : ℤ) = 1 :=
begin
  rcases exists_pow_eq_one x with ⟨w, hw1, hw2⟩,
  refine ⟨w, int.coe_nat_ne_zero.mpr (ne_of_gt hw1), _⟩,
  rw gpow_coe_nat,
  exact (is_periodic_pt_mul_iff_pow_eq_one _).mp hw2,
end

lemma exists_gsmul_eq_zero (a : A) : ∃ (i : ℤ) (H : i ≠ 0), i • a = 0 :=
@exists_gpow_eq_one (multiplicative A) _ _ a

attribute [to_additive] exists_gpow_eq_one

lemma mem_multiples_iff_mem_gmultiples :
  b ∈ add_submonoid.multiples a ↔ b ∈ add_subgroup.gmultiples a :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩, λ ⟨i, hi⟩, ⟨(i % add_order_of a).nat_abs,
  by { simp only [nsmul_eq_smul] at hi ⊢,
       rwa  [← gsmul_coe_nat,
       int.nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2
          (add_order_of_pos a))), ← gsmul_eq_mod_add_order_of] } ⟩⟩

open subgroup

@[to_additive mem_multiples_iff_mem_gmultiples]
lemma mem_powers_iff_mem_gpowers : y ∈ submonoid.powers x ↔ y ∈ gpowers x :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩,
λ ⟨i, hi⟩, ⟨(i % order_of x).nat_abs,
  by rwa [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
    (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos x))),
    ← gpow_eq_mod_order_of]⟩⟩

lemma multiples_eq_gmultiples (a : A) :
  (add_submonoid.multiples a : set A) = add_subgroup.gmultiples a :=
set.ext $ λ y, mem_multiples_iff_mem_gmultiples

@[to_additive multiples_eq_gmultiples]
lemma powers_eq_gpowers (x : G) : (submonoid.powers x : set G) = gpowers x :=
set.ext $ λ x, mem_powers_iff_mem_gpowers

lemma mem_gmultiples_iff_mem_range_add_order_of [decidable_eq A] :
  b ∈ add_subgroup.gmultiples a ↔ b ∈ (finset.range (add_order_of a)).image (• a) :=
by rw [← mem_multiples_iff_mem_gmultiples, mem_multiples_iff_mem_range_add_order_of]

@[to_additive mem_gmultiples_iff_mem_range_add_order_of]
lemma mem_gpowers_iff_mem_range_order_of [decidable_eq G] :
  y ∈ subgroup.gpowers x ↔ y ∈ (finset.range (order_of x)).image ((^) x : ℕ → G) :=
by rw [← mem_powers_iff_mem_gpowers, mem_powers_iff_mem_range_order_of]

noncomputable instance decidable_gmultiples [decidable_eq A] :
  decidable_pred (∈ add_subgroup.gmultiples a) :=
begin
  simp_rw ←set_like.mem_coe,
  rw ← multiples_eq_gmultiples,
  exact decidable_multiples,
end

@[to_additive decidable_gmultiples]
noncomputable instance decidable_gpowers [decidable_eq G] :
  decidable_pred (∈ subgroup.gpowers x) :=
begin
  simp_rw ←set_like.mem_coe,
  rw ← powers_eq_gpowers,
  exact decidable_powers,
end

/-- The equivalence between `fin (order_of x)` and `subgroup.gpowers x`, sending `i` to `x ^ i`. -/
noncomputable def fin_equiv_gpowers (x : G) :
  fin (order_of x) ≃ (subgroup.gpowers x : set G) :=
(fin_equiv_powers x).trans (equiv.set.of_eq (powers_eq_gpowers x))

/-- The equivalence between `fin (add_order_of a)` and `subgroup.gmultiples a`,
  sending `i` to `i • a`. -/
noncomputable def fin_equiv_gmultiples (a : A) :
  fin (add_order_of a) ≃ (add_subgroup.gmultiples a : set A) :=
fin_equiv_gpowers (multiplicative.of_add a)

attribute [to_additive fin_equiv_gmultiples] fin_equiv_gpowers

@[simp] lemma fin_equiv_gpowers_apply {n : fin (order_of x)} :
  fin_equiv_gpowers x n = ⟨x ^ (n : ℕ), n, gpow_coe_nat x n⟩ := rfl

@[simp] lemma fin_equiv_gmultiples_apply {n : fin (add_order_of a)} :
  fin_equiv_gmultiples a n = ⟨(n : ℕ) • a, n, gsmul_coe_nat a n⟩ :=
fin_equiv_gpowers_apply

attribute [to_additive fin_equiv_gmultiples_apply] fin_equiv_gpowers_apply

@[simp] lemma fin_equiv_gpowers_symm_apply (x : G) (n : ℕ)
  {hn : ∃ (m : ℤ), x ^ m = x ^ n} :
  ((fin_equiv_gpowers x).symm ⟨x ^ n, hn⟩) = ⟨n % order_of x, nat.mod_lt _ (order_of_pos x)⟩ :=
by { rw [fin_equiv_gpowers, equiv.symm_trans_apply, equiv.set.of_eq_symm_apply],
  exact fin_equiv_powers_symm_apply x n }

@[simp] lemma fin_equiv_gmultiples_symm_apply (a : A) (n : ℕ)
  {hn : ∃ (m : ℤ), m • a = n • a} :
  ((fin_equiv_gmultiples a).symm ⟨n • a, hn⟩) =
    ⟨n % add_order_of a, nat.mod_lt _ (add_order_of_pos a)⟩ :=
fin_equiv_gpowers_symm_apply (multiplicative.of_add a) n

attribute [to_additive fin_equiv_gmultiples_symm_apply] fin_equiv_gpowers_symm_apply

/-- The equivalence between `subgroup.gpowers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
noncomputable def gpowers_equiv_gpowers (h : order_of x = order_of y) :
  (subgroup.gpowers x : set G) ≃ (subgroup.gpowers y : set G) :=
(fin_equiv_gpowers x).symm.trans ((fin.cast h).to_equiv.trans (fin_equiv_gpowers y))

/-- The equivalence between `subgroup.gmultiples` of two elements `a, b` of the same additive order,
  mapping `i • a` to `i • b`. -/
noncomputable def gmultiples_equiv_gmultiples (h : add_order_of a = add_order_of b) :
  (add_subgroup.gmultiples a : set A) ≃ (add_subgroup.gmultiples b : set A) :=
(fin_equiv_gmultiples a).symm.trans ((fin.cast h).to_equiv.trans (fin_equiv_gmultiples b))

attribute [to_additive gmultiples_equiv_gmultiples] gpowers_equiv_gpowers

@[simp]
lemma gpowers_equiv_gpowers_apply (h : order_of x = order_of y)
  (n : ℕ) : gpowers_equiv_gpowers h ⟨x ^ n, n, gpow_coe_nat x n⟩ = ⟨y ^ n, n, gpow_coe_nat y n⟩ :=
begin
  rw [gpowers_equiv_gpowers, equiv.trans_apply, equiv.trans_apply,
    fin_equiv_gpowers_symm_apply, ← equiv.eq_symm_apply, fin_equiv_gpowers_symm_apply],
  simp [h]
end

@[simp]
lemma gmultiples_equiv_gmultiples_apply (h : add_order_of a = add_order_of b) (n : ℕ) :
  gmultiples_equiv_gmultiples h ⟨n • a, n, gsmul_coe_nat a n⟩ = ⟨n • b, n, gsmul_coe_nat b n⟩ :=
gpowers_equiv_gpowers_apply h n

attribute [to_additive gmultiples_equiv_gmultiples_apply] gpowers_equiv_gpowers_apply

lemma order_eq_card_gpowers [decidable_eq G] :
  order_of x = fintype.card (subgroup.gpowers x : set G) :=
(fintype.card_fin (order_of x)).symm.trans (fintype.card_eq.2 ⟨fin_equiv_gpowers x⟩)

lemma add_order_eq_card_gmultiples [decidable_eq A] :
  add_order_of a = fintype.card (add_subgroup.gmultiples a : set A) :=
(fintype.card_fin (add_order_of a)).symm.trans (fintype.card_eq.2 ⟨fin_equiv_gmultiples a⟩)

attribute [to_additive add_order_eq_card_gmultiples] order_eq_card_gpowers

open quotient_group

/- TODO: use cardinal theory, introduce `card : set G → ℕ`, or setup decidability for cosets -/
lemma order_of_dvd_card_univ : order_of x ∣ fintype.card G :=
begin
  classical,
  have ft_prod : fintype (quotient (gpowers x) × (gpowers x)),
    from fintype.of_equiv G group_equiv_quotient_times_subgroup,
  have ft_s : fintype (gpowers x),
    from @fintype.prod_right _ _ _ ft_prod _,
  have ft_cosets : fintype (quotient (gpowers x)),
    from @fintype.prod_left _ _ _ ft_prod ⟨⟨1, (gpowers x).one_mem⟩⟩,
  have eq₁ : fintype.card G = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
    from calc fintype.card G = @fintype.card _ ft_prod :
        @fintype.card_congr _ _ _ ft_prod group_equiv_quotient_times_subgroup
      ... = @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s) :
        congr_arg (@fintype.card _) $ subsingleton.elim _ _
      ... = @fintype.card _ ft_cosets * @fintype.card _ ft_s :
        @fintype.card_prod _ _ ft_cosets ft_s,
  have eq₂ : order_of x = @fintype.card _ ft_s,
    from calc order_of x = _ : order_eq_card_gpowers
      ... = _ : congr_arg (@fintype.card _) $ subsingleton.elim _ _,
  exact dvd.intro (@fintype.card (quotient (subgroup.gpowers x)) ft_cosets)
          (by rw [eq₁, eq₂, mul_comm])
end

lemma add_order_of_dvd_card_univ : add_order_of a ∣ fintype.card A :=
begin
  rw ← order_of_of_add_eq_add_order_of,
  exact order_of_dvd_card_univ,
end

attribute [to_additive add_order_of_dvd_card_univ] order_of_dvd_card_univ

@[simp] lemma pow_card_eq_one : x ^ fintype.card G = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ x _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]

@[simp] lemma card_nsmul_eq_zero {a : A} : fintype.card A • a = 0 :=
begin
  apply multiplicative.of_add.injective,
  rw [of_add_nsmul, of_add_zero],
  exact pow_card_eq_one,
end

attribute [to_additive card_nsmul_eq_zero] pow_card_eq_one

/-- If `gcd(|G|,n)=1` then the `n`th power map is a bijection -/
@[simps] def pow_coprime (h : nat.coprime (fintype.card G) n) : G ≃ G :=
{ to_fun := λ g, g ^ n,
  inv_fun := λ g, g ^ (nat.gcd_b (fintype.card G) n),
  left_inv := λ g, by
  { have key : g ^ _ = g ^ _ := congr_arg (λ n : ℤ, g ^ n) (nat.gcd_eq_gcd_ab (fintype.card G) n),
    rwa [gpow_add, gpow_mul, gpow_mul, gpow_coe_nat, gpow_coe_nat, gpow_coe_nat,
      h.gcd_eq_one, pow_one, pow_card_eq_one, one_gpow, one_mul, eq_comm] at key },
  right_inv := λ g, by
  { have key : g ^ _ = g ^ _ := congr_arg (λ n : ℤ, g ^ n) (nat.gcd_eq_gcd_ab (fintype.card G) n),
    rwa [gpow_add, gpow_mul, gpow_mul', gpow_coe_nat, gpow_coe_nat, gpow_coe_nat,
      h.gcd_eq_one, pow_one, pow_card_eq_one, one_gpow, one_mul, eq_comm] at key } }

@[simp] lemma pow_coprime_one (h : nat.coprime (fintype.card G) n) : pow_coprime h 1 = 1 :=
one_pow n

@[simp] lemma pow_coprime_inv (h : nat.coprime (fintype.card G) n) {g : G} :
  pow_coprime h g⁻¹ = (pow_coprime h g)⁻¹ :=
inv_pow g n

variable (a)

lemma image_range_add_order_of [decidable_eq A] :
  finset.image (λ i, i • a) (finset.range (add_order_of a)) =
  (add_subgroup.gmultiples a : set A).to_finset :=
by {ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_gmultiples_iff_mem_range_add_order_of] }

/-- TODO: Generalise to `submonoid.powers`.-/
@[to_additive image_range_add_order_of]
lemma image_range_order_of [decidable_eq G] :
  finset.image (λ i, x ^ i) (finset.range (order_of x)) = (gpowers x : set G).to_finset :=
by { ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_gpowers_iff_mem_range_order_of] }

lemma gcd_nsmul_card_eq_zero_iff : n • a = 0 ↔ (gcd n (fintype.card A)) • a = 0 :=
⟨λ h, gcd_nsmul_eq_zero _ h $ card_nsmul_eq_zero,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card A) in
    by rw [hm, mul_comm, mul_nsmul, h, nsmul_zero]⟩

/-- TODO: Generalise to `finite_cancel_monoid`. -/
@[to_additive gcd_nsmul_card_eq_zero_iff]
lemma pow_gcd_card_eq_one_iff : x ^ n = 1 ↔ x ^ (gcd n (fintype.card G)) = 1 :=
⟨λ h, pow_gcd_eq_one _ h $ pow_card_eq_one,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card G) in
    by rw [hm, pow_mul, h, one_pow]⟩

end finite_group

end fintype

section pow_is_subgroup

/-- A nonempty idempotent subset of a finite cancellative monoid is a submonoid -/
def submonoid_of_idempotent {M : Type*} [left_cancel_monoid M] [fintype M] (S : set M)
  (hS1 : S.nonempty) (hS2 : S * S = S) : submonoid M :=
have pow_mem : ∀ a : M, a ∈ S → ∀ n : ℕ, a ^ (n + 1) ∈ S :=
λ a ha, nat.rec (by rwa [zero_add, pow_one])
  (λ n ih, (congr_arg2 (∈) (pow_succ a (n + 1)).symm hS2).mp (set.mul_mem_mul ha ih)),
{ carrier := S,
  one_mem' := by {
    obtain ⟨a, ha⟩ := hS1,
    rw [←pow_order_of_eq_one a, ←nat.sub_add_cancel (order_of_pos a)],
    exact pow_mem a ha (order_of a - 1) },
  mul_mem' := λ a b ha hb, (congr_arg2 (∈) rfl hS2).mp (set.mul_mem_mul ha hb) }

/-- A nonempty idempotent subset of a finite group is a subgroup -/
def subgroup_of_idempotent {G : Type*} [group G] [fintype G] (S : set G)
  (hS1 : S.nonempty) (hS2 : S * S = S) : subgroup G :=
{ carrier := S,
  inv_mem' := λ a ha, by {
    rw [←one_mul a⁻¹, ←pow_one a, ←pow_order_of_eq_one a, ←pow_sub a (order_of_pos a)],
    exact (submonoid_of_idempotent S hS1 hS2).pow_mem ha (order_of a - 1) },
  .. submonoid_of_idempotent S hS1 hS2 }

/-- If `S` is a nonempty subset of a finite group `G`, then `S ^ |G|` is a subgroup -/
def pow_card_subgroup {G : Type*} [group G] [fintype G] (S : set G) (hS : S.nonempty) :
  subgroup G :=
have one_mem : (1 : G) ∈ (S ^ fintype.card G) := by
{ obtain ⟨a, ha⟩ := hS,
  rw ← pow_card_eq_one,
  exact set.pow_mem_pow ha (fintype.card G) },
subgroup_of_idempotent (S ^ (fintype.card G)) ⟨1, one_mem⟩ begin
  classical,
  refine (set.eq_of_subset_of_card_le
    (λ b hb, (congr_arg (∈ _) (one_mul b)).mp (set.mul_mem_mul one_mem hb)) (ge_of_eq _)).symm,
  change _ = fintype.card (_ * _ : set G),
  rw [←pow_add, group.card_pow_eq_card_pow_card_univ S (fintype.card G) le_rfl,
      group.card_pow_eq_card_pow_card_univ S (fintype.card G + fintype.card G) le_add_self],
end

end pow_is_subgroup
