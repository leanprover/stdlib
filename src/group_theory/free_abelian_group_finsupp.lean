/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import group_theory.free_abelian_group
import data.finsupp.basic

/-!
# Isomorphism between `free_abelian_group X` and `X →₀ ℤ`

In this file we construct the canonical isomorphism between `free_abelian_group X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `finsupp` to `free_abelian_group`.

## Main declarations

- `free_abelian_group.equiv_finsupp`: group isomorphism between `free_abelian_group X` and `X →₀ ℤ`
- `free_abelian_group.coeff`: the multiplicity of `x : X` in `a : free_abelian_group X`
- `free_abelian_group.support`: the finset of `x : X` that occur in `a : free_abelian_group X`

-/

noncomputable theory

open_locale big_operators

variables {X : Type*}

/-- The group homomorphism `free_abelian_group X →+ (X →₀ ℤ)`. -/
def free_abelian_group.to_finsupp : free_abelian_group X →+ (X →₀ ℤ) :=
free_abelian_group.lift $ λ x, finsupp.single x (1 : ℤ)

/-- The group homomorphism `(X →₀ ℤ) →+ free_abelian_group X`. -/
def finsupp.to_free_abelian_group : (X →₀ ℤ) →+ free_abelian_group X :=
finsupp.lift_add_hom $ λ x, (smul_add_hom ℤ (free_abelian_group X)).flip (free_abelian_group.of x)

open finsupp free_abelian_group

@[simp] lemma finsupp.to_free_abelian_group_comp_single_add_hom (x : X) :
  finsupp.to_free_abelian_group.comp (finsupp.single_add_hom x) =
    (smul_add_hom ℤ (free_abelian_group X)).flip (of x) :=
begin
  ext,
  simp only [add_monoid_hom.coe_comp, finsupp.single_add_hom_apply, function.comp_app,
    one_smul, to_free_abelian_group, finsupp.lift_add_hom_apply_single]
end

@[simp] lemma free_abelian_group.to_finsupp_comp_to_free_abelian_group :
  to_finsupp.comp to_free_abelian_group = add_monoid_hom.id (X →₀ ℤ) :=
begin
  ext x y, simp only [add_monoid_hom.id_comp],
  rw [add_monoid_hom.comp_assoc, finsupp.to_free_abelian_group_comp_single_add_hom],
  simp only [to_finsupp, add_monoid_hom.coe_comp, finsupp.single_add_hom_apply,
    function.comp_app, one_smul, lift.of, add_monoid_hom.flip_apply,
    smul_add_hom_one, add_monoid_hom.id_apply],
end

@[simp] lemma finsupp.to_free_abelian_group_comp_to_finsupp :
  to_free_abelian_group.comp to_finsupp = add_monoid_hom.id (free_abelian_group X) :=
begin
  ext,
  simp only [to_free_abelian_group, to_finsupp, finsupp.lift_add_hom_apply_single,
    add_monoid_hom.coe_comp, function.comp_app, one_smul, add_monoid_hom.id_apply, lift.of,
    add_monoid_hom.flip_apply, smul_add_hom_one],
end

@[simp] lemma finsupp.to_free_abelian_group_to_finsupp {X} (x : free_abelian_group X) :
  x.to_finsupp.to_free_abelian_group = x :=
by rw [← add_monoid_hom.comp_apply, finsupp.to_free_abelian_group_comp_to_finsupp,
  add_monoid_hom.id_apply]

namespace free_abelian_group
open finsupp

variable {X}

@[simp] lemma to_finsupp_of (x : X) :
  to_finsupp (of x) = finsupp.single x 1 :=
by simp only [to_finsupp, lift.of]

@[simp] lemma to_finsupp_to_free_abelian_group (f : X →₀ ℤ) :
  f.to_free_abelian_group.to_finsupp = f :=
by rw [← add_monoid_hom.comp_apply, to_finsupp_comp_to_free_abelian_group, add_monoid_hom.id_apply]

variable (X)

/-- The additive equivalence between `free_abelian_group X` and `(X →₀ ℤ)`. -/
@[simps]
def equiv_finsupp : free_abelian_group X ≃+ (X →₀ ℤ) :=
{ to_fun := to_finsupp,
  inv_fun := to_free_abelian_group,
  left_inv := to_free_abelian_group_to_finsupp,
  right_inv := to_finsupp_to_free_abelian_group,
  map_add' := to_finsupp.map_add }

variable {X}

/-- `coeff x` is the additive group homomorphism `free_abelian_group X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : free_abelian_group X →+ ℤ :=
(finsupp.apply_add_hom x).comp to_finsupp

/-- `support a` for `a : free_abelian_group X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
def support (a : free_abelian_group X) : finset X :=
a.to_finsupp.support

lemma mem_support_iff (x : X) (a : free_abelian_group X) :
  x ∈ a.support ↔ coeff x a ≠ 0 :=
by { rw [support, finsupp.mem_support_iff], exact iff.rfl }

lemma not_mem_support_iff (x : X) (a : free_abelian_group X) :
  x ∉ a.support ↔ coeff x a = 0 :=
by { rw [support, finsupp.not_mem_support_iff], exact iff.rfl }

@[simp] lemma support_zero : support (0 : free_abelian_group X) = ∅ :=
by simp only [support, finsupp.support_zero, add_monoid_hom.map_zero]

@[simp] lemma support_of (x : X) : support (of x) = {x} :=
by simp only [support, to_finsupp_of, finsupp.support_single_ne_zero (one_ne_zero)]

@[simp] lemma support_neg (a : free_abelian_group X) : support (-a) = support a :=
by simp only [support, add_monoid_hom.map_neg, finsupp.support_neg]

@[simp] lemma support_gsmul (k : ℤ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k • a) = support a :=
begin
  ext x,
  simp only [mem_support_iff, add_monoid_hom.map_gsmul],
  simp only [h, gsmul_int_int, false_or, ne.def, mul_eq_zero]
end

@[simp] lemma support_nsmul (k : ℕ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k • a) = support a :=
by { apply support_gsmul k _ a, exact_mod_cast h }

open_locale classical

lemma support_add (a b : free_abelian_group X) : (support (a + b)) ⊆ a.support ∪ b.support :=
begin
  simp only [support, add_monoid_hom.map_add],
  apply finsupp.support_add
end

end free_abelian_group
