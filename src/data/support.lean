/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.conditionally_complete_lattice
import algebra.big_operators.basic
import algebra.group.prod
import algebra.group.pi
import algebra.module.pi

/-!
# Support of a function

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
-/

universes u v w x y

open set
open_locale big_operators
namespace function

variables {α : Type u} {β : Type v} {ι : Sort w} {A : Type x} {B : Type y}

/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def support [has_zero A] (f : α → A) : set α := {x | f x ≠ 0}

lemma nmem_support [has_zero A] {f : α → A} {x : α} :
  x ∉ support f ↔ f x = 0 :=
not_not

lemma compl_support [has_zero A] {f : α → A} : (support f)ᶜ = {x | f x = 0} :=
ext $ λ x, nmem_support

@[simp]
lemma mem_support [has_zero A] {f : α → A} {x : α} :
  x ∈ support f ↔ f x ≠ 0 :=
iff.rfl

lemma support_subset_iff [has_zero A] {f : α → A} {s : set α} :
  support f ⊆ s ↔ ∀ x, f x ≠ 0 → x ∈ s :=
iff.rfl

lemma support_subset_iff' [has_zero A] {f : α → A} {s : set α} :
  support f ⊆ s ↔ ∀ x ∉ s, f x = 0 :=
forall_congr $ λ x, by classical; exact not_imp_comm

@[simp] lemma support_eq_empty_iff [has_zero A] {f : α → A} :
  support f = ∅ ↔ f = 0 :=
by { simp_rw [← subset_empty_iff, support_subset_iff', funext_iff], simp }

@[simp] lemma support_zero' [has_zero A] : support (0 : α → A) = ∅ :=
support_eq_empty_iff.2 rfl

@[simp] lemma support_zero [has_zero A] : support (λ x : α, (0 : A)) = ∅ :=
support_zero'

lemma support_binop_subset [has_zero A] (op : A → A → A) (op0 : op 0 0 = 0) (f g : α → A) :
  support (λ x, op (f x) (g x)) ⊆ support f ∪ support g :=
λ x hx, classical.by_cases
  (λ hf : f x = 0, or.inr $ λ hg, hx $ by simp only [hf, hg, op0])
  or.inl

lemma support_add [add_monoid A] (f g : α → A) :
  support (λ x, f x + g x) ⊆ support f ∪ support g :=
support_binop_subset (+) (zero_add _) f g

@[simp] lemma support_neg [add_group A] (f : α → A) :
  support (λ x, -f x) = support f :=
set.ext $ λ x, not_congr neg_eq_zero

lemma support_sub [add_group A] (f g : α → A) :
  support (λ x, f x - g x) ⊆ support f ∪ support g :=
support_binop_subset (has_sub.sub) (sub_self _) f g

@[simp] lemma support_mul [mul_zero_class A] [no_zero_divisors A] (f g : α → A) :
  support (λ x, f x * g x) = support f ∩ support g :=
set.ext $ λ x, by simp only [support, ne.def, mul_eq_zero, mem_set_of_eq,
  mem_inter_iff, not_or_distrib]

lemma support_smul_subset_right [add_monoid A] [monoid B] [distrib_mul_action B A]
  (b : B) (f : α → A) :
  support (b • f) ⊆ support f :=
λ x hbf hf, hbf $ by rw [pi.smul_apply, hf, smul_zero]

lemma support_smul_subset_left {R M} [semiring R] [add_comm_monoid M] [semimodule R M]
  (f : α → R) (g : α → M) :
  support (f • g) ⊆ support f :=
λ x hfg hf, hfg $ by rw [pi.smul_apply', hf, zero_smul]

lemma support_smul {R M} [semiring R] [add_comm_monoid M] [semimodule R M]
  [no_zero_smul_divisors R M] (f : α → R) (g : α → M) :
  support (f • g) = support f ∩ support g :=
ext $ λ x, smul_ne_zero

@[simp] lemma support_inv [division_ring A] (f : α → A) :
  support (λ x, (f x)⁻¹) = support f :=
set.ext $ λ x, not_congr inv_eq_zero

@[simp] lemma support_div [division_ring A] (f g : α → A) :
  support (λ x, f x / g x) = support f ∩ support g :=
by simp [div_eq_mul_inv]

lemma support_sup [has_zero A] [semilattice_sup A] (f g : α → A) :
  support (λ x, (f x) ⊔ (g x)) ⊆ support f ∪ support g :=
support_binop_subset (⊔) sup_idem f g

lemma support_inf [has_zero A] [semilattice_inf A] (f g : α → A) :
  support (λ x, (f x) ⊓ (g x)) ⊆ support f ∪ support g :=
support_binop_subset (⊓) inf_idem f g

lemma support_max [has_zero A] [linear_order A] (f g : α → A) :
  support (λ x, max (f x) (g x)) ⊆ support f ∪ support g :=
support_sup f g

lemma support_min [has_zero A] [linear_order A] (f g : α → A) :
  support (λ x, min (f x) (g x)) ⊆ support f ∪ support g :=
support_inf f g

lemma support_supr [has_zero A] [conditionally_complete_lattice A] [nonempty ι] (f : ι → α → A) :
  support (λ x, ⨆ i, f i x) ⊆ ⋃ i, support (f i) :=
begin
  intros x hx,
  classical,
  contrapose hx,
  simp only [mem_Union, not_exists, nmem_support] at hx ⊢,
  simp only [hx, csupr_const]
end

lemma support_infi [has_zero A] [conditionally_complete_lattice A] [nonempty ι] (f : ι → α → A) :
  support (λ x, ⨅ i, f i x) ⊆ ⋃ i, support (f i) :=
@support_supr _ _ (order_dual A) ⟨(0:A)⟩ _ _ f

lemma support_sum [add_comm_monoid A] (s : finset α) (f : α → β → A) :
  support (λ x, ∑ i in s, f i x) ⊆ ⋃ i ∈ s, support (f i) :=
begin
  intros x hx,
  classical,
  contrapose hx,
  simp only [mem_Union, not_exists, nmem_support] at hx ⊢,
  exact finset.sum_eq_zero hx
end

lemma support_prod_subset [comm_monoid_with_zero A] (s : finset α) (f : α → β → A) :
  support (λ x, ∏ i in s, f i x) ⊆ ⋂ i ∈ s, support (f i) :=
λ x hx, mem_bInter_iff.2 $ λ i hi H, hx $ finset.prod_eq_zero hi H

lemma support_prod [comm_monoid_with_zero A] [no_zero_divisors A] [nontrivial A]
  (s : finset α) (f : α → β → A) :
  support (λ x, ∏ i in s, f i x) = ⋂ i ∈ s, support (f i) :=
set.ext $ λ x, by
  simp only [support, ne.def, finset.prod_eq_zero_iff, mem_set_of_eq, set.mem_Inter, not_exists]

lemma support_comp_subset [has_zero A] [has_zero B] {g : A → B} (hg : g 0 = 0) (f : α → A) :
  support (g ∘ f) ⊆ support f :=
λ x, mt $ λ h, by simp [(∘), *]

lemma support_subset_comp [has_zero A] [has_zero B] {g : A → B} (hg : ∀ {x}, g x = 0 → x = 0)
  (f : α → A) :
  support f ⊆ support (g ∘ f) :=
λ x, mt hg

lemma support_comp_eq [has_zero A] [has_zero B] (g : A → B) (hg : ∀ {x}, g x = 0 ↔ x = 0)
  (f : α → A) :
  support (g ∘ f) = support f :=
set.ext $ λ x, not_congr hg

lemma support_comp_eq_preimage [has_zero B] (g : A → B) (f : α → A) :
  support (g ∘ f) = f ⁻¹' support g :=
rfl

lemma support_prod_mk [has_zero A] [has_zero B] (f : α → A) (g : α → B) :
  support (λ x, (f x, g x)) = support f ∪ support g :=
set.ext $ λ x, by simp only [support, not_and_distrib, mem_union_eq, mem_set_of_eq,
  prod.mk_eq_zero, ne.def]

end function

namespace pi
variables {A : Type*} {B : Type*} [decidable_eq A] [has_zero B] {a : A} {b : B}

lemma support_single_zero : function.support (pi.single a (0 : B)) = ∅ := by simp

@[simp]
lemma support_single_of_ne (h : b ≠ 0) :
  function.support (pi.single a b) = {a} :=
begin
  ext,
  simp only [mem_singleton_iff, ne.def, function.mem_support],
  split,
  { contrapose!,
    exact λ h', single_eq_of_ne h' b },
  { rintro rfl,
    rw single_eq_same,
    exact h }
end

lemma support_single [decidable_eq B] :
  function.support (pi.single a b) = if b = 0 then ∅ else {a} := by { split_ifs with h; simp [h] }

lemma support_single_subset : function.support (pi.single a b) ⊆ {a} :=
begin
  classical,
  rw support_single,
  split_ifs;
  simp
end

lemma support_single_disjoint {b' : B} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : A} :
  disjoint (function.support (single i b)) (function.support (single j b')) ↔ i ≠ j :=
by simpa [support_single, hb, hb'] using ne_comm

end pi
