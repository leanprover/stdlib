/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import algebra.module.linear_map
import group_theory.group_action.sub_mul_action
/-!

# Submodules of a module

In this file we define

* `submodule R M` : a subset of a `module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `subspace k M` : an abbreviation for `submodule` assuming that `k` is a `field`.

## Tags

submodule, subspace, linear map
-/

open function
open_locale big_operators

universes u' u v w
variables {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

set_option old_structure_cmd true

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure submodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] [semimodule R M] extends add_submonoid M, sub_mul_action R M : Type v.

/-- Reinterpret a `submodule` as an `add_submonoid`. -/
add_decl_doc submodule.to_add_submonoid

/-- Reinterpret a `submodule` as an `sub_mul_action`. -/
add_decl_doc submodule.to_sub_mul_action

namespace submodule

variables [semiring R] [add_comm_monoid M] [semimodule R M]

instance : has_coe_t (submodule R M) (set M) := ⟨λ s, s.carrier⟩
instance : has_mem M (submodule R M) := ⟨λ x p, x ∈ (p : set M)⟩
instance : has_coe_to_sort (submodule R M) := ⟨_, λ p, {x : M // x ∈ p}⟩

variables (p q : submodule R M)

@[simp, norm_cast] theorem coe_sort_coe : ↥(p : set M) = p := rfl

variables {p q}

protected theorem «exists» {q : p → Prop} : (∃ x, q x) ↔ (∃ x ∈ p, q ⟨x, ‹_›⟩) := set_coe.exists

protected theorem «forall» {q : p → Prop} : (∀ x, q x) ↔ (∀ x ∈ p, q ⟨x, ‹_›⟩) := set_coe.forall

theorem coe_injective : injective (coe : submodule R M → set M) :=
λ p q h, by cases p; cases q; congr'

@[simp, norm_cast] theorem coe_set_eq : (p : set M) = q ↔ p = q := coe_injective.eq_iff

@[simp] lemma mk_coe (S : set M) (h₁ h₂ h₃) :
  ((⟨S, h₁, h₂, h₃⟩ : submodule R M) : set M) = S := rfl

theorem ext'_iff : p = q ↔ (p : set M) = q := coe_set_eq.symm

@[ext] theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := coe_injective $ set.ext h

theorem to_add_submonoid_injective :
  injective (to_add_submonoid : submodule R M → add_submonoid M) :=
λ p q h, ext'_iff.2 $ add_submonoid.ext'_iff.1 h

@[simp] theorem to_add_submonoid_eq : p.to_add_submonoid = q.to_add_submonoid ↔ p = q :=
to_add_submonoid_injective.eq_iff

theorem to_sub_mul_action_injective :
  injective (to_sub_mul_action : submodule R M → sub_mul_action R M) :=
λ p q h, ext'_iff.2 $ sub_mul_action.ext'_iff.1 h

@[simp] theorem to_sub_mul_action_eq : p.to_sub_mul_action = q.to_sub_mul_action ↔ p = q :=
to_sub_mul_action_injective.eq_iff

end submodule

namespace submodule

section add_comm_monoid

variables [semiring S] [semiring R] [add_comm_monoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variables {semimodule_M : semimodule R M}
variables {p q : submodule R M}
variables {r : R} {x y : M}

variables [has_scalar S R] [semimodule S M] [is_scalar_tower S R M]

variables (p)
@[simp] lemma mem_carrier : x ∈ p.carrier ↔ x ∈ (p : set M) := iff.rfl

@[simp] theorem mem_coe : x ∈ (p : set M) ↔ x ∈ p := iff.rfl

@[simp] lemma zero_mem : (0 : M) ∈ p := p.zero_mem'

lemma add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p := p.add_mem' h₁ h₂

lemma smul_mem (r : S) (h : x ∈ p) : r • x ∈ p := p.to_sub_mul_action.smul_of_tower_mem r h

lemma sum_mem {t : finset ι} {f : ι → M} : (∀c∈t, f c ∈ p) → (∑ i in t, f i) ∈ p :=
p.to_add_submonoid.sum_mem

lemma sum_smul_mem {t : finset ι} {f : ι → M} (r : ι → S)
    (hyp : ∀ c ∈ t, f c ∈ p) : (∑ i in t, r i • f i) ∈ p :=
submodule.sum_mem _ (λ i hi, submodule.smul_mem  _ _ (hyp i hi))

@[simp] lemma smul_mem_iff' (u : units S) : (u:S) • x ∈ p ↔ x ∈ p :=
p.to_sub_mul_action.smul_mem_iff' u

instance : has_add p := ⟨λx y, ⟨x.1 + y.1, add_mem _ x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero_mem _⟩⟩
instance : inhabited p := ⟨0⟩
instance : has_scalar S p := ⟨λ c x, ⟨c • x.1, smul_mem _ c x.2⟩⟩

protected lemma nonempty : (p : set M).nonempty := ⟨0, p.zero_mem⟩

@[simp] lemma mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 := subtype.ext_iff_val

variables {p}
@[simp, norm_cast] lemma coe_eq_coe {x y : p} : (x : M) = y ↔ x = y := subtype.ext_iff_val.symm
@[simp, norm_cast] lemma coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 := @coe_eq_coe _ _ _ _ _ _ x 0
@[simp, norm_cast] lemma coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : p) : M) = 0 := rfl
@[simp, norm_cast] lemma coe_smul (s : S) (x : p) : ((s • x : p) : M) = s • ↑x := rfl
@[simp, norm_cast] lemma coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : M) ∈ p := x.2

@[simp] protected lemma eta (x : p) (hx : (x : M) ∈ p) : (⟨x, hx⟩ : p) = x := subtype.eta x hx

variables (p)

instance : add_comm_monoid p :=
{ add := (+), zero := 0, .. p.to_add_submonoid.to_add_comm_monoid }

instance semimodule' : semimodule S p :=
by refine {smul := (•), ..p.to_sub_mul_action.mul_action', ..};
   { intros, apply set_coe.ext, simp [smul_add, add_smul, mul_smul] }
instance : semimodule R p := p.semimodule'

instance : is_scalar_tower S R p :=
p.to_sub_mul_action.is_scalar_tower

instance no_zero_smul_divisors [no_zero_smul_divisors R M] : no_zero_smul_divisors R p :=
⟨λ c x h,
  have c = 0 ∨ (x : M) = 0,
  from eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h),
  this.imp_right (@subtype.ext_iff _ _ x 0).mpr⟩

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[R] M :=
by refine {to_fun := coe, ..}; simp [coe_smul]

@[simp] theorem subtype_apply (x : p) : p.subtype x = x := rfl

lemma subtype_eq_val : ((submodule.subtype p) : p → M) = subtype.val := rfl

end add_comm_monoid

section add_comm_group

variables [ring R] [add_comm_group M]
variables {semimodule_M : semimodule R M}
variables (p p' : submodule R M)
variables {r : R} {x y : M}

lemma neg_mem (hx : x ∈ p) : -x ∈ p := p.to_sub_mul_action.neg_mem hx

/-- Reinterpret a submodule as an additive subgroup. -/
def to_add_subgroup : add_subgroup M :=
{ neg_mem' := λ _, p.neg_mem , .. p.to_add_submonoid }

@[simp] lemma coe_to_add_subgroup : (p.to_add_subgroup : set M) = p := rfl

lemma sub_mem : x ∈ p → y ∈ p → x - y ∈ p := p.to_add_subgroup.sub_mem

@[simp] lemma neg_mem_iff : -x ∈ p ↔ x ∈ p := p.to_add_subgroup.neg_mem_iff

lemma add_mem_iff_left : y ∈ p → (x + y ∈ p ↔ x ∈ p) := p.to_add_subgroup.add_mem_cancel_right

lemma add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) := p.to_add_subgroup.add_mem_cancel_left

instance : has_neg p := ⟨λx, ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast] lemma coe_neg (x : p) : ((-x : p) : M) = -x := rfl

instance : add_comm_group p :=
{ add := (+), zero := 0, neg := has_neg.neg, ..p.to_add_subgroup.to_add_comm_group }

@[simp, norm_cast] lemma coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y := rfl

end add_comm_group

section ordered_monoid

variables [semiring R]

/-- A submodule of an `ordered_add_comm_monoid` is an `ordered_add_comm_monoid`. -/
instance to_ordered_add_comm_monoid
  {M} [ordered_add_comm_monoid M] [semimodule R M] (S : submodule R M) :
  ordered_add_comm_monoid S :=
subtype.coe_injective.ordered_add_comm_monoid coe rfl (λ _ _, rfl)

/-- A submodule of a `linear_ordered_add_comm_monoid` is a `linear_ordered_add_comm_monoid`. -/
instance to_linear_ordered_add_comm_monoid
  {M} [linear_ordered_add_comm_monoid M] [semimodule R M] (S : submodule R M) :
  linear_ordered_add_comm_monoid S :=
subtype.coe_injective.linear_ordered_add_comm_monoid coe rfl (λ _ _, rfl)

/-- A submodule of an `ordered_cancel_add_comm_monoid` is an `ordered_cancel_add_comm_monoid`. -/
instance to_ordered_cancel_add_comm_monoid
  {M} [ordered_cancel_add_comm_monoid M] [semimodule R M] (S : submodule R M) :
  ordered_cancel_add_comm_monoid S :=
subtype.coe_injective.ordered_cancel_add_comm_monoid coe rfl (λ _ _, rfl)

/-- A submodule of a `linear_ordered_cancel_add_comm_monoid` is a
`linear_ordered_cancel_add_comm_monoid`. -/
instance to_linear_ordered_cancel_add_comm_monoid
  {M} [linear_ordered_cancel_add_comm_monoid M] [semimodule R M] (S : submodule R M) :
  linear_ordered_cancel_add_comm_monoid S :=
subtype.coe_injective.linear_ordered_cancel_add_comm_monoid coe rfl (λ _ _, rfl)

end ordered_monoid

section ordered_group

variables [ring R]

/-- A submodule of an `ordered_add_comm_group` is an `ordered_add_comm_group`. -/
instance to_ordered_add_comm_group
  {M} [ordered_add_comm_group M] [semimodule R M] (S : submodule R M) :
  ordered_add_comm_group S :=
subtype.coe_injective.ordered_add_comm_group coe rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)

/-- A submodule of a `linear_ordered_add_comm_group` is a
`linear_ordered_add_comm_group`. -/
instance to_linear_ordered_add_comm_group
  {M} [linear_ordered_add_comm_group M] [semimodule R M] (S : submodule R M) :
  linear_ordered_add_comm_group S :=
subtype.coe_injective.linear_ordered_add_comm_group coe rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)

end ordered_group

end submodule

namespace submodule

variables [division_ring S] [semiring R] [add_comm_monoid M] [semimodule R M]
variables [has_scalar S R] [semimodule S M] [is_scalar_tower S R M]

variables (p : submodule R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
p.to_sub_mul_action.smul_mem_iff s0

end submodule

/-- Subspace of a vector space. Defined to equal `submodule`. -/
abbreviation subspace (R : Type u) (M : Type v)
  [field R] [add_comm_group M] [vector_space R M] :=
submodule R M
