/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import algebra.semiconj
import ring_theory.subring

/-!
# Commuting pairs of elements in monoids

## Main definitions

* `commute a b` : `a * b = b * a`
* `centralizer a` : `{ x | commute a x }`
* `set.centralizer s` : elements that commute with all `a ∈ s`

We prove that `centralizer` and `set_centralilzer` are submonoid/subgroups/subrings depending on the
available structures, and provide operations on `commute _ _`.

E.g., if `a`, `b`, and c are elements of a semiring, and that `hb :
commute a b` and `hc : commute a c`.  Then `hb.pow_left 5` proves
`commute (a ^ 5) b` and `(hb.pow_right 2).add_right (hb.mul_right hc)`
proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations,
so for rewriting we need syntax like `rw [(hb.pow_left 5).eq]`
rather than just `rw [hb.pow_left 5]`.

## Implementation details

Most of the proofs come from the properties of `semiconj_by`.
-/

variables {a b : M} (hab : commute a b) (m n : ℕ)

@[simp] theorem gpow_right : commute a (b ^ m) := hab.gpow_right m
@[simp] theorem gpow_left : commute (a ^ m) b := (hab.symm.gpow_right m).symm
@[simp] theorem gpow_gpow : commute (a ^ m) (b ^ n) := (hab.gpow_right n).gpow_left m

@[simp] theorem self_gpow : commute a (a ^ n) := (commute.refl a).gpow_right n
@[simp] theorem gpow_self : commute (a ^ n) a := (commute.refl a).gpow_left n
@[simp] theorem gpow_gpow_self : commute (a ^ m) (a ^ n) := (commute.refl a).gpow_gpow m n

end group

section semiring

variables {A : Type*}

variables [semiring A] {a b : A} (hab : commute a b) (m n : ℕ)

@[simp] theorem cast_nat_right : commute a (n : A) := semiconj_by.cast_nat_right a n
@[simp] theorem cast_nat_left : commute (n : A) a := semiconj_by.cast_nat_left n a

end semiring

section ring

variables {R : Type*} [ring R] {a b c : R}

variables (hab : commute a b) (m n : ℤ)

@[simp] theorem gsmul_right : commute a (m •ℤ b) := hab.gsmul_right m
@[simp] theorem gsmul_left : commute (m •ℤ a) b := hab.gsmul_left m
@[simp] theorem gsmul_gsmul : commute (m •ℤ a) (n •ℤ b) := hab.gsmul_gsmul m n

@[simp] theorem self_gsmul : commute a (n •ℤ a) := (commute.refl a).gsmul_right n
@[simp] theorem gsmul_self : commute (n •ℤ a) a := (commute.refl a).gsmul_left n
@[simp] theorem self_gsmul_gsmul : commute (m •ℤ a) (n •ℤ a) := (commute.refl a).gsmul_gsmul m n

variable (a)

@[simp] theorem cast_int_right : commute a (n : R) :=
by rw [← gsmul_one n]; exact (commute.one_right a).gsmul_right n

@[simp] theorem cast_int_left : commute (n : R) a := (commute.cast_int_right a n).symm

end ring

section division_ring

variables {R : Type*} [division_ring R] {a b c : R}

end division_ring

end commute


-- Definitions and trivial theorems about them
section centralizer

variables {S : Type*} [has_mul S]

/-- Centralizer of an element `a : S` as the set of elements that commute with `a`; for `S` a
    monoid, `submonoid.centralizer` is the centralizer as a submonoid. -/
def centralizer (a : S) : set S := { x | commute a x }

@[simp] theorem mem_centralizer {a b : S} : b ∈ centralizer a ↔ commute a b := iff.rfl

/-- Centralizer of a set `T` as the set of elements of `S` that commute with all `a ∈ T`; for
    `S` a monoid, `submonoid.set.centralizer` is the set centralizer as a submonoid. -/
protected def set.centralizer (s : set S) : set S := { x | ∀ a ∈ s, commute a x }

@[simp] protected theorem set.mem_centralizer (s : set S) {x : S} :
  x ∈ s.centralizer ↔ ∀ a ∈ s, commute a x :=
iff.rfl

protected theorem set.mem_centralizer_iff_subset (s : set S) {x : S} :
  x ∈ s.centralizer ↔ s ⊆ centralizer x :=
by simp only [set.mem_centralizer, mem_centralizer, set.subset_def, commute.symm_iff]

protected theorem set.centralizer_eq (s : set S) :
  s.centralizer =  ⋂ a ∈ s, centralizer a :=
set.ext $ assume x,
by simp only [s.mem_centralizer, set.mem_bInter_iff, mem_centralizer]

protected theorem set.centralizer_decreasing {s t : set S} (h : s ⊆ t) :
  t.centralizer ⊆ s.centralizer :=
s.centralizer_eq.symm ▸ t.centralizer_eq.symm ▸ set.bInter_subset_bInter_left h

end centralizer

section monoid

variables {M : Type*} [monoid M] (a : M) (s : set M)

instance centralizer.is_submonoid : is_submonoid (centralizer a) :=
{ one_mem := commute.one_right a,
  mul_mem := λ _ _, commute.mul_right }

/-- Centralizer of an element `a` of a monoid is the submonoid of elements that commute with `a`. -/
def submonoid.centralizer : submonoid M :=
{ carrier := centralizer a,
  one_mem' := commute.one_right a,
  mul_mem' := λ _ _, commute.mul_right }

instance set.centralizer.is_submonoid : is_submonoid s.centralizer :=
by rw s.centralizer_eq; apply_instance

/-- Centralizer of a subset `T` of a monoid is the submonoid of elements that commute with
    all `a ∈ T`. -/
def submonoid.set.centralizer : submonoid M :=
{ carrier := s.centralizer,
  one_mem' := λ _ _, commute.one_right _,
  mul_mem' := λ _ _ h1 h2 a h, commute.mul_right (h1 a h) $ h2 a h }

@[simp] theorem monoid.centralizer_closure : (monoid.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing monoid.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact monoid.closure_subset)

-- Not sure if this should be an instance
lemma centralizer.inter_units_is_subgroup : is_subgroup { x : units M | commute a x } :=
{ one_mem := commute.one_right a,
  mul_mem := λ _ _, commute.mul_right,
  inv_mem := λ _, commute.units_inv_right }

theorem commute.list_prod_right {a : M} {l : list M} (h : ∀ x ∈ l, commute a x) :
  commute a l.prod :=
is_submonoid.list_prod_mem (λ x hx, mem_centralizer.2 (h x hx))

theorem commute.list_prod_left {l : list M} {a : M} (h : ∀ x ∈ l, commute x a) :
  commute l.prod a :=
(commute.list_prod_right (λ x hx, (h x hx).symm)).symm

end monoid

section group

variables {G : Type*} [group G] (a : G) (s : set G)

instance centralizer.is_subgroup : is_subgroup (centralizer a) :=
{ inv_mem := λ _, commute.inv_right }

instance set.centralizer.is_subgroup : is_subgroup s.centralizer :=
by rw s.centralizer_eq; apply_instance

@[simp] lemma group.centralizer_closure : (group.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing group.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact group.closure_subset)

end group

/- There is no `is_subsemiring` in mathlib, so we only prove `is_add_submonoid` here. -/
section semiring

variables {A : Type*} [semiring A] (a : A) (s : set A)

instance centralizer.is_add_submonoid : is_add_submonoid (centralizer a) :=
{ zero_mem := commute.zero_right a,
  add_mem := λ _ _, commute.add_right }

def centralizer.add_submonoid : add_submonoid A :=
{ carrier := centralizer a,
  zero_mem' := commute.zero_right a,
  add_mem' := λ _ _, commute.add_right }

instance set.centralizer.is_add_submonoid : is_add_submonoid s.centralizer :=
by rw s.centralizer_eq; apply_instance

def set.centralizer.add_submonoid : add_submonoid A :=
{ carrier := s.centralizer,
  zero_mem' := λ _ _, commute.zero_right _,
  add_mem' := λ _ _ h1 h2 a h, commute.add_right (h1 a h) $ h2 a h }

@[simp] lemma add_monoid.centralizer_closure : (add_monoid.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing add_monoid.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact add_monoid.closure_subset)

end semiring

section ring

variables {R : Type*} [ring R] (a : R) (s : set R)

instance centralizer.is_subring : is_subring (centralizer a) :=
{ neg_mem := λ _, commute.neg_right }

instance set.centralizer.is_subring : is_subring s.centralizer :=
by rw s.centralizer_eq; apply_instance

@[simp] lemma ring.centralizer_closure : (ring.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing ring.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact ring.closure_subset)

end ring

namespace commute

protected theorem mul_pow {M : Type*} [monoid M] {a b : M} (hab : commute a b) :
  ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
| 0 := by simp only [pow_zero, mul_one]
| (n + 1) := by simp only [pow_succ, mul_pow n];
                assoc_rw [(hab.symm.pow_right n).eq]; rw [mul_assoc]

protected theorem mul_gpow {G : Type*} [group G] {a b : G} (hab : commute a b) :
  ∀ (n : ℤ), (a * b) ^ n = a ^ n * b ^ n
| (n : ℕ) := hab.mul_pow n
| -[1+n] :=
    by { simp only [gpow_neg_succ, hab.mul_pow, mul_inv_rev],
         exact (hab.pow_pow n.succ n.succ).inv_inv.symm.eq }

end commute

theorem neg_pow {R : Type*} [ring R] (a : R) (n : ℕ) : (- a) ^ n = (-1) ^ n * a ^ n :=
(neg_one_mul a) ▸ (commute.neg_one_left a).mul_pow n
