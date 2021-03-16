/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import group_theory.submonoid.operations
import algebra.big_operators.basic
import algebra.free_monoid

/-!
# Submonoids: membership criteria

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n •ℕ x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`: the multiplicative (resp., additive) closure
  of `{x}` consists of powers (resp., natural multiples) of `x`.

## Tags
submonoid, submonoids
-/

open_locale big_operators

variables {M : Type*} [monoid M] {s : set M}
variables {A : Type*} [add_monoid A] {t : set A}

namespace submonoid

variables (S : submonoid M)

@[simp, norm_cast] theorem coe_pow (x : S) (n : ℕ) : ↑(x ^ n) = (x ^ n : M) :=
S.subtype.map_pow x n

@[simp, norm_cast] theorem coe_list_prod (l : list S) : (l.prod : M) = (l.map coe).prod :=
S.subtype.map_list_prod l

@[simp, norm_cast] theorem coe_multiset_prod {M} [comm_monoid M] (S : submonoid M)
  (m : multiset S) : (m.prod : M) = (m.map coe).prod :=
S.subtype.map_multiset_prod m

@[simp, norm_cast] theorem coe_finset_prod {ι M} [comm_monoid M] (S : submonoid M)
  (f : ι → S) (s : finset ι) :
  ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
S.subtype.map_prod f s

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
lemma list_prod_mem : ∀ {l : list M}, (∀x ∈ l, x ∈ S) → l.prod ∈ S
| []     h := S.one_mem
| (a::l) h :=
  suffices a * l.prod ∈ S, by rwa [list.prod_cons],
  have a ∈ S ∧ (∀ x ∈ l, x ∈ S), from list.forall_mem_cons.1 h,
  S.mul_mem this.1 (list_prod_mem this.2)

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is
in the `add_submonoid`."]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M) :
  (∀a ∈ m, a ∈ S) → m.prod ∈ S :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact S.list_prod_mem hl
end

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`
is in the `add_submonoid`."]
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) :
  ∏ c in t, f c ∈ S :=
S.multiset_prod_mem (t.1.map f) $ λ x hx, let ⟨i, hi, hix⟩ := multiset.mem_map.1 hx in hix ▸ h i hi

lemma pow_mem {x : M} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
by simpa only [coe_pow] using ((⟨x, hx⟩ : S) ^ n).coe_prop

open set

@[to_additive]
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S)
  {x : M} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (le_def.1 $ le_supr S i) hi⟩,
  suffices : x ∈ closure (⋃ i, (S i : set M)) → ∃ i, x ∈ S i,
    by simpa only [closure_Union, closure_eq (S _)] using this,
  refine (λ hx, closure_induction hx (λ _, mem_Union.1) _ _),
  { exact hι.elim (λ i, ⟨i, (S i).one_mem⟩) },
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    rcases hS i j with ⟨k, hki, hkj⟩,
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩ }
end

@[to_additive]
lemma coe_supr_of_directed {ι} [nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S) :
  ((⨆ i, S i : submonoid M) : set M) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

@[to_additive]
lemma mem_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : M} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

@[to_additive]
lemma coe_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set M) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

@[to_additive]
lemma mem_sup_left {S T : submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

@[to_additive]
lemma mem_sup_right {S T : submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

@[to_additive]
lemma mem_supr_of_mem {ι : Type*} {S : ι → submonoid M} (i : ι) :
  ∀ {x : M}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

@[to_additive]
lemma mem_Sup_of_mem {S : set (submonoid M)} {s : submonoid M}
  (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

end submonoid

namespace free_monoid

variables {α : Type*}

open submonoid

@[to_additive]
theorem closure_range_of : closure (set.range $ @of α) = ⊤ :=
eq_top_iff.2 $ λ x hx, free_monoid.rec_on x (one_mem _) $ λ x xs hxs,
  mul_mem _ (subset_closure $ set.mem_range_self _) hxs

end free_monoid

namespace submonoid

variables {N : Type*} [monoid N]

open monoid_hom

lemma closure_singleton_eq (x : M) : closure ({x} : set M) = (powers_hom M x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨multiplicative.of_add 1, trivial, pow_one x⟩) $
  λ x ⟨n, _, hn⟩, hn ▸ pow_mem _ (subset_closure $ set.mem_singleton _) _

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
lemma mem_closure_singleton {x y : M} : y ∈ closure ({x} : set M) ↔ ∃ n:ℕ, x^n=y :=
by simp [closure_singleton_eq, exists_multiplicative_iff]

lemma mem_closure_singleton_self {y : M} : y ∈ closure ({y} : set M) :=
mem_closure_singleton.2 ⟨1, pow_one y⟩

lemma closure_singleton_one : closure ({1} : set M) = ⊥ :=
by simp [eq_bot_iff_forall, mem_closure_singleton]

@[to_additive]
lemma closure_eq_mrange (s : set M) : closure s = (free_monoid.lift (coe : s → M)).mrange :=
by rw [mrange, ← free_monoid.closure_range_of, map_mclosure, ← set.range_comp,
  free_monoid.lift_comp_of, subtype.range_coe]

@[to_additive]
lemma exists_list_of_mem_closure {s : set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : list M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  rw [closure_eq_mrange, mem_mrange] at hx,
  rcases hx with ⟨l, hx⟩,
  exact ⟨list.map coe l, λ y hy, let ⟨z, hz, hy⟩ := list.mem_map.1 hy in hy ▸ z.2, hx⟩
end

/-- The submonoid generated by an element. -/
def powers (n : N) : submonoid N :=
submonoid.copy (powers_hom N n).mrange (set.range ((^) n : ℕ → N)) $
by ext; simp [exists_multiplicative_iff]

@[simp] lemma mem_powers (n : N) : n ∈ powers n := ⟨1, pow_one _⟩

lemma powers_eq_closure (n : N) : powers n = closure {n} :=
by { ext, exact mem_closure_singleton.symm }

lemma powers_subset {n : N} {P : submonoid N} (h : n ∈ P) : powers n ≤ P :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := P.pow_mem h i end

end submonoid

namespace submonoid

variables {N : Type*} [comm_monoid N]

open monoid_hom

@[to_additive]
lemma sup_eq_range (s t : submonoid N) : s ⊔ t = (s.subtype.coprod t.subtype).mrange :=
by rw [mrange, ← mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl,
  map_mrange, coprod_comp_inr, range_subtype, range_subtype]

@[to_additive]
lemma mem_sup {s t : submonoid N} {x : N} :
  x ∈ s ⊔ t ↔ ∃ (y ∈ s) (z ∈ t), y * z = x :=
by simp only [sup_eq_range, mem_mrange, coprod_apply, prod.exists, submonoid.exists,
  coe_subtype, subtype.coe_mk]

end submonoid

namespace add_submonoid

open set

lemma nsmul_mem (S : add_submonoid A) {x : A} (hx : x ∈ S) :
  ∀ n : ℕ, n •ℕ x ∈ S
| 0     := S.zero_mem
| (n+1) := S.add_mem hx (nsmul_mem n)

lemma closure_singleton_eq (x : A) : closure ({x} : set A) = (multiples_hom A x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨1, trivial, one_nsmul x⟩) $
  λ x ⟨n, _, hn⟩, hn ▸ nsmul_mem _ (subset_closure $ set.mem_singleton _) _

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
lemma mem_closure_singleton {x y : A} :
  y ∈ closure ({x} : set A) ↔ ∃ n:ℕ, n •ℕ x = y :=
by rw [closure_singleton_eq, add_monoid_hom.mem_mrange]; refl

lemma closure_singleton_zero : closure ({0} : set A) = ⊥ :=
by simp [eq_bot_iff_forall, mem_closure_singleton]

/-- The additive submonoid generated by an element. -/
def multiples (x : A) : add_submonoid A :=
add_submonoid.copy (multiples_hom A x).mrange (set.range (λ i, nsmul i x : ℕ → A)) $
set.ext (λ n, exists_congr $ λ i, by simp; refl)

@[simp] lemma mem_multiples (x : A) : x ∈ multiples x := ⟨1, one_nsmul _⟩

lemma multiples_eq_closure (x : A) : multiples x = closure {x} :=
by { ext, exact mem_closure_singleton.symm }

lemma multiples_subset {x : A} {P : add_submonoid A} (h : x ∈ P) : multiples x ≤ P :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := P.nsmul_mem h i end

attribute [to_additive add_submonoid.multiples] submonoid.powers
attribute [to_additive add_submonoid.mem_multiples] submonoid.mem_powers
attribute [to_additive add_submonoid.multiples_eq_closure] submonoid.powers_eq_closure
attribute [to_additive add_submonoid.multiples_subset] submonoid.powers_subset

end add_submonoid
