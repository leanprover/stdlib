/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.dfinsupp
import data.finsupp.basic
import algebra.group.pi
import group_theory.submonoid.operations

/-!
# Equivalence between `finsupp` and `dfinsupp` constrained to the range of `single i`

## Main definitions

* `finsupp.single_submonoid` - the submonoid corresponding to the range of `finsupp.single`.
* `finsupp.single_submonoid.of` - the obvious map into `finsupp.single_submonoid`, a `→+`.
* `finsupp.equiv_dfinsupp_single_submonoid` - the `add_equiv` between a `finsupp` and a `dfinsupp`
  where each fibre is `finsupp.single_submonoid`.

## Implementation notes

Lean has a very hard time finding some typeclasses in this file - so in many cases we have to
explicitly build them.

-/

variables {ι : Type*} {M : Type*}

noncomputable theory

namespace finsupp

variables (M)

/-- The submonoid corresponding to the range of `finsupp.single`. -/
abbreviation single_submonoid [add_monoid M] (i : ι) : add_submonoid (ι →₀ M) :=
(finsupp.single_add_hom i : M →+ (ι →₀ M)).mrange

/-- The natural construction of elements of `finsupp.single_submonoid`. -/
abbreviation single_submonoid.of [add_monoid M] (i : ι) : M →+ single_submonoid M i :=
(finsupp.single_add_hom i : M →+ (ι →₀ M)).mrange_restrict

/-- Typeclass resolution can't find this for some reason, it is needed to define
`dfinsupp.add_comm_monoid_of_finsupp_single_submonoid`. -/
instance [add_comm_monoid M] (i : ι) : add_comm_monoid (single_submonoid M i) :=
by apply_instance

end finsupp

/-- Typeclass resolution can't find this for some reason, it is needed by the `≃+` to state
`finsupp.equiv_dfinsupp_single_submonoid`. -/
instance dfinsupp.add_comm_monoid_of_finsupp_single_submonoid [add_comm_monoid M] :
  add_comm_monoid (Π₀ (i : ι), finsupp.single_submonoid M i) :=
@dfinsupp.add_comm_monoid ι (λ i, finsupp.single_submonoid M i) _

/-- A `finsupp` is equivalent to a `dfinsupp` where each fibre is constrained to lie in
`finsupp.single_submonoid M i`. -/
noncomputable def finsupp.equiv_dfinsupp_single_submonoid [decidable_eq ι] [add_comm_monoid M] :
  (ι →₀ M) ≃+ (Π₀ i : ι, finsupp.single_submonoid M i) :=
add_monoid_hom.to_add_equiv
  (finsupp.lift_add_hom $ λ n : ι,
    (dfinsupp.single_add_hom (λ i, _) n).comp (finsupp.single_submonoid.of M n))
  (dfinsupp.lift_add_hom $ λ i : ι,
    (finsupp.single_submonoid M i).subtype)
  (begin
    ext i m : 2,
    simp
  end)
  (begin
    -- `ext` doesn't find this for some reason
    apply @dfinsupp.add_hom_ext' ι (λ i, finsupp.single_submonoid M i) _ _ _ _ _ _, intro i,
    ext ⟨x, r, _, rfl⟩ : 1,
    simp,
    refl,
  end)

@[simp]
lemma finsupp.equiv_dfinsupp_single_submonoid_single [decidable_eq ι] [add_comm_monoid M]
  (i : ι) (m : M) :
  finsupp.equiv_dfinsupp_single_submonoid (finsupp.single i m) =
    dfinsupp.single i (finsupp.single_submonoid.of M i m) :=
finsupp.lift_add_hom_apply_single _ i m

@[simp]
lemma finsupp.equiv_dfinsupp_single_submonoid_symm_single [decidable_eq ι] [add_comm_monoid M]
  (i : ι) (m : finsupp.single_submonoid M i) :
  finsupp.equiv_dfinsupp_single_submonoid.symm (dfinsupp.single i m) = ↑m :=
dfinsupp.lift_add_hom_apply_single _ i m
