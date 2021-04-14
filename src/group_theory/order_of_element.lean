/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
import algebra.big_operators.order
import group_theory.coset
import data.nat.totient
import data.int.gcd
import data.set.finite
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
variables {x : G} {a : A} {n m : ℕ}

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
lemma commute.order_of_mul_dvd_lcm {y : G} (h : commute x y) :
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

/-
DT: this lemma had been removed, right?  In favour of `nsmul_ne_zero_of_lt_add_order_of'`
I think
lemma add_order_of_le_of_nsmul_eq_zero' {m : ℕ} (h : m < add_order_of x) : ¬ (0 < m ∧ m • x = 0) :=
begin
  convert is_periodic_pt_minimal_period ((+) a) _,
  rw [add_order_of, add_left_iterate, add_zero],
end
-/

@[to_additive add_order_of_nsmul_eq_zero]
lemma pow_order_of_eq_one (x : G) : x ^ order_of x = 1 :=
begin
  convert is_periodic_pt_minimal_period ((*) x) _,
  rw [order_of, mul_left_iterate, mul_one],
end

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
begin
  rw [order_of, one_mul_eq_id],
  exact minimal_period_id,
end

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

lemma nsmul_eq_mod_add_order_of {n : ℕ} : n • x = (n % add_order_of x) • x :=
begin
  apply multiplicative.of_add.injective,
  rw [← order_of_of_add_eq_add_order_of, of_add_nsmul, of_add_nsmul, pow_eq_mod_order_of],
end

attribute [to_additive nsmul_eq_mod_add_order_of] pow_eq_mod_order_of

lemma add_order_of_dvd_of_nsmul_eq_zero (h : n • a = 0) : add_order_of a ∣ n :=
is_periodic_pt.minimal_period_dvd ((is_periodic_pt_add_iff_nsmul_eq_zero _).mpr h)

lemma add_order_of_dvd_of_nsmul_eq_zero {n : ℕ} (h : n • x = 0) : add_order_of x ∣ n :=
begin
  apply_fun multiplicative.of_add at h,
  rw ← order_of_of_add_eq_add_order_of,
  rw of_add_nsmul at h,
  exact order_of_dvd_of_pow_eq_one h,
end

attribute [to_additive add_order_of_dvd_of_nsmul_eq_zero] order_of_dvd_of_pow_eq_one

lemma add_order_of_dvd_iff_nsmul_eq_zero {n : ℕ} : add_order_of x ∣ n ↔ n • x = 0 :=
⟨λ h, by rw [nsmul_eq_mod_add_order_of, nat.mod_eq_zero_of_dvd h, zero_nsmul],
  add_order_of_dvd_of_nsmul_eq_zero⟩

@[to_additive add_order_of_dvd_iff_nsmul_eq_zero]
lemma order_of_dvd_iff_pow_eq_one {n : ℕ} : order_of a ∣ n ↔ a ^ n = 1 :=
⟨λ h, by rw [pow_eq_mod_order_of, nat.mod_eq_zero_of_dvd h, pow_zero], order_of_dvd_of_pow_eq_one⟩

lemma commute.order_of_mul_dvd_lcm (h : commute a b) :
  order_of (a * b) ∣ nat.lcm (order_of a) (order_of b) :=
by rw [order_of_dvd_iff_pow_eq_one, h.mul_pow, order_of_dvd_iff_pow_eq_one.mp
  (nat.dvd_lcm_left _ _), order_of_dvd_iff_pow_eq_one.mp (nat.dvd_lcm_right _ _), one_mul]

lemma add_order_of_eq_prime {p : ℕ} [hp : fact p.prime]
(hg : p • x = 0) (hg1 : x ≠ 0) : add_order_of x = p :=
(hp.out.2 _ (add_order_of_dvd_of_nsmul_eq_zero hg)).resolve_left (mt add_order_of_eq_one_iff.1 hg1)

@[to_additive add_order_of_eq_prime]
lemma order_of_eq_prime {p : ℕ} [hp : fact p.prime]
  (hg : a^p = 1) (hg1 : a ≠ 1) : order_of a = p :=
(hp.out.2 _ (order_of_dvd_of_pow_eq_one hg)).resolve_left (mt order_of_eq_one_iff.1 hg1)

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
  change coprime n (order_of (multiplicative.of_add a)) at h,
  exact exists_pow_eq_self_of_coprime h,
end

lemma add_order_of_eq_add_order_of_iff {A : Type*} [add_monoid A] {y : A} :
  add_order_of x = add_order_of y ↔ ∀ n : ℕ, n • x = 0 ↔ n • y = 0 :=
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
  add_order_of (n • x) = add_order_of x / gcd (add_order_of x) n :=
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
  add_order_of (n • x) = add_order_of x / gcd (add_order_of x) n :=
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
  (hm : m < add_order_of x) (eq : n • x = m • x) : n = m :=
begin
  apply_fun multiplicative.of_add at eq,
  rw [of_add_nsmul, of_add_nsmul] at eq,
  rw ← order_of_of_add_eq_add_order_of at hm,
  exact pow_injective_aux (multiplicative.of_add x) h hm eq,
end

attribute [to_additive nsmul_injective_aux] pow_injective_aux

lemma nsmul_injective_of_lt_add_order_of {n m : ℕ}
  (hn : n < add_order_of x) (hm : m < add_order_of x) (eq : n • x = m • x) : n = m :=
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

lemma gsmul_eq_mod_add_order_of : i •ℤ a = (i % add_order_of a) •ℤ a :=
begin
  apply multiplicative.of_add.injective,
  simp [of_add_gsmul, gpow_eq_mod_order_of],
end

attribute [to_additive gsmul_eq_mod_add_order_of] gpow_eq_mod_order_of

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
  rcases exists_pow_eq_one (multiplicative.of_add x) with ⟨i, hi1, hi2⟩,
  refine ⟨i, hi1, multiplicative.of_add.injective _⟩,
  rw [of_add_nsmul, hi2, of_add_zero],
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

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
lemma order_of_pos (x : G) : 0 < order_of x := order_of_pos' (exists_pow_eq_one x)

/-- This is the same as `add_order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative additive monoid.-/
lemma add_order_of_pos (a : A) : 0 < add_order_of a :=
begin
  rw ← order_of_of_add_eq_add_order_of,
  exact order_of_pos _,
end

attribute [to_additive add_order_of_pos] order_of_pos

variables {n : ℕ}

open nat

lemma exists_pow_eq_self_of_coprime {α : Type*} [monoid α] {a : α} (h : coprime n (order_of a)) :
  ∃ m : ℕ, (a ^ n) ^ m = a :=
begin
  by_cases h0 : order_of a = 0,
  { rw [h0, coprime_zero_right] at h,
    exact ⟨1, by rw [h, pow_one, pow_one]⟩ },
  by_cases h1 : order_of a = 1,
  { rw order_of_eq_one_iff at h1,
    exact ⟨37, by rw [h1, one_pow, one_pow]⟩ },
  obtain ⟨m, hm⟩ :=
    exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩),
  exact ⟨m, by rw [←pow_mul, pow_eq_mod_order_of, hm, pow_one]⟩,
end

lemma exists_nsmul_eq_self_of_coprime {H : Type*} [add_monoid H] (x : H)
  (h : coprime n (add_order_of x)) : ∃ m : ℕ, m • (n • x) = x :=
begin
  have h' : coprime n (order_of (multiplicative.of_add x)),
  { simp_rw order_of_of_add_eq_add_order_of,
    exact h },
  cases exists_pow_eq_self_of_coprime h' with m hpow,
  use m,
  apply multiplicative.of_add.injective,
  simpa [of_add_nsmul],
end

attribute [to_additive exists_nsmul_eq_self_of_coprime] exists_pow_eq_self_of_coprime

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid.-/
lemma order_of_pow (x : G) :
  order_of (x ^ n) = order_of x / gcd (order_of x) n := order_of_pow'' _ _ (exists_pow_eq_one _)

/-- This is the same as `add_order_of_nsmul'` and `add_order_of_nsmul` but with one assumption less
which is automatic in the case of a finite cancellative additive monoid. -/
lemma add_order_of_nsmul (a : A) :
  add_order_of (n • a) = add_order_of a / gcd (add_order_of a) n :=
begin
  rw [← order_of_of_add_eq_add_order_of, of_add_nsmul],
  exact order_of_pow _,
end

attribute [to_additive add_order_of_nsmul] order_of_pow

lemma mem_multiples_iff_mem_range_add_order_of [decidable_eq A] {b : A} :
  b ∈ add_submonoid.multiples a ↔
  b ∈ (finset.range (add_order_of a)).image ((• a) : ℕ → A)  :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (add_order_of_pos a)
  (assume i, nsmul_eq_mod_add_order_of.symm)

@[to_additive mem_multiples_iff_mem_range_add_order_of]
lemma mem_powers_iff_mem_range_order_of [decidable_eq G] {y : G} :
  y ∈ submonoid.powers x ↔ y ∈ (finset.range (order_of x)).image ((^) x : ℕ → G) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos x)
  (assume i, pow_eq_mod_order_of.symm)

noncomputable instance decidable_multiples [decidable_eq A] :
  decidable_pred (add_submonoid.multiples a : set A) :=
begin
  assume b,
  apply decidable_of_iff' (b ∈ (finset.range (add_order_of a)).image (• a)),
  exact mem_multiples_iff_mem_range_add_order_of,
end

@[to_additive decidable_multiples]
noncomputable instance decidable_powers [decidable_eq G] :
  decidable_pred (submonoid.powers x : set G) :=
begin
  assume y,
  apply decidable_of_iff'
    (y ∈ (finset.range (order_of x)).image ((^) x)),
  exact mem_powers_iff_mem_range_order_of
end

lemma order_eq_card_powers [decidable_eq G] :
  order_of x = fintype.card (submonoid.powers x : set G) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨x ^ n, ⟨n, rfl⟩⟩ },
  { rintros ⟨_, i, rfl⟩ _,
    exact ⟨i % order_of x, mod_lt i (order_of_pos x), subtype.eq pow_eq_mod_order_of.symm⟩ },
  { exact λ _ _, finset.mem_univ _ },
  { exact λ i j hi hj eq, pow_injective_of_lt_order_of x hi hj (subtype.mk_eq_mk.mp eq) }
end

lemma add_order_of_eq_card_multiples [decidable_eq A] :
  add_order_of a = fintype.card (add_submonoid.multiples a : set A) :=
begin
  rw [← order_of_of_add_eq_add_order_of, order_eq_card_powers],
  apply fintype.card_congr,
  rw ←of_add_image_multiples_eq_powers_of_add,
  exact (equiv.set.image _ _ (equiv.injective _)).symm
end

attribute [to_additive add_order_of_eq_card_multiples] order_eq_card_powers

end finite_cancel_monoid

section finite_group
variables [group G] [add_group A]

lemma exists_gpow_eq_one (x : G) : ∃ i ≠ 0, x ^ (i : ℤ) = 1 :=
begin
  rcases exists_pow_eq_one x with ⟨w, hw1, hw2⟩,
  exact ⟨w, int.coe_nat_ne_zero.mpr (ne_of_gt hw1), (is_periodic_pt_mul_iff_pow_eq_one _).mp hw2⟩,
end

lemma exists_gsmul_eq_zero (a : A) : ∃ i ≠ 0, i •ℤ a = 0 :=
exists_gpow_eq_one (multiplicative.of_add a)

attribute [to_additive exists_gsmul_eq_zero] exists_gpow_eq_one

lemma mem_multiples_iff_mem_gmultiples {b : A} :
  b ∈ add_submonoid.multiples a ↔ b ∈ add_subgroup.gmultiples a :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩, λ ⟨i, hi⟩, ⟨(i % add_order_of a).nat_abs,
  by { simp only [nsmul_eq_smul] at hi ⊢,
       rwa  [← gsmul_coe_nat,
       int.nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2
          (add_order_of_pos x))), ← gsmul_eq_mod_add_order_of] } ⟩⟩

open subgroup

@[to_additive mem_multiples_iff_mem_gmultiples]
lemma mem_powers_iff_mem_gpowers {y : G} : y ∈ submonoid.powers x ↔ y ∈ gpowers x :=
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

lemma mem_gmultiples_iff_mem_range_add_order_of [decidable_eq A] {b : A} :
  b ∈ add_subgroup.gmultiples a ↔ b ∈ (finset.range (add_order_of a)).image (• a) :=
by rw [← mem_multiples_iff_mem_gmultiples, mem_multiples_iff_mem_range_add_order_of]

@[to_additive mem_gmultiples_iff_mem_range_add_order_of]
lemma mem_gpowers_iff_mem_range_order_of [decidable_eq G] {y : G} :
  y ∈ subgroup.gpowers x ↔ y ∈ (finset.range (order_of x)).image ((^) x : ℕ → G) :=
by rw [← mem_powers_iff_mem_gpowers, mem_powers_iff_mem_range_order_of]

noncomputable instance decidable_gmultiples [decidable_eq A] :
  decidable_pred (add_subgroup.gmultiples a : set A) :=
begin
  rw ← multiples_eq_gmultiples,
  exact decidable_multiples,
end

@[to_additive decidable_gmultiples]
noncomputable instance decidable_gpowers [decidable_eq G] :
  decidable_pred (subgroup.gpowers x : set G) :=
begin
  rw ← powers_eq_gpowers,
  exact decidable_powers,
end

lemma order_eq_card_gpowers [decidable_eq G] :
  order_of x = fintype.card (subgroup.gpowers x : set G) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨x ^ (n : ℤ), ⟨n, rfl⟩⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
    have pos : (0 : ℤ) < order_of x := int.coe_nat_lt.mpr $ order_of_pos x,
    have 0 ≤ i % (order_of x) := int.mod_nonneg _ $ ne_of_gt pos,
    ⟨int.to_nat (i % order_of x),
      by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
        exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { exact λ _ _, finset.mem_univ _ },
  { exact λ i j hi hj eq, pow_injective_of_lt_order_of x hi hj $ subtype.mk_eq_mk.mp eq }
end

lemma add_order_eq_card_gmultiples [decidable_eq A] :
  add_order_of a = fintype.card (add_subgroup.gmultiples a : set A) :=
begin
  rw [← order_of_of_add_eq_add_order_of, order_eq_card_gpowers],
  apply fintype.card_congr,
  rw ← of_add_image_gmultiples_eq_gpowers_of_add,
  exact (equiv.set.image _ _ (equiv.injective _)).symm
end

attribute [to_additive add_order_eq_card_gmultiples] order_eq_card_gpowers

open quotient_group

/- TODO: use cardinal theory, introduce `card : set G → ℕ`, or setup decidability for cosets -/
lemma order_of_dvd_card_univ : order_of x ∣ fintype.card G :=
begin
  classical,
  have ft_prod : fintype (quotient (gpowers x) × (gpowers x)),
    from fintype.of_equiv G group_equiv_quotient_times_subgroup,
  have ft_s : fintype (gpowers x),
    from @fintype.fintype_prod_right _ _ _ ft_prod _,
  have ft_cosets : fintype (quotient (gpowers x)),
    from @fintype.fintype_prod_left _ _ _ ft_prod ⟨⟨1, (gpowers x).one_mem⟩⟩,
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
