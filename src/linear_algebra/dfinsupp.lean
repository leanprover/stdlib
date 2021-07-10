/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import data.finsupp.to_dfinsupp
import linear_algebra.basis

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `data.dfinsupp`.

In this file we define `linear_map` versions of various maps:

* `dfinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lmk s : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `λ f, f i` as a linear map;

* `dfinsupp.lsum`: `dfinsupp.sum` or `dfinsupp.lift_add_hom` as a `linear_map`;

## Implementation notes

This file should try to mirror `linear_algebra.finsupp` where possible. The API of `finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

variables {ι : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

variables [dec_ι : decidable_eq ι]
variables [semiring R] [Π i, add_comm_monoid (M i)] [Π i, module R (M i)]
variables [add_comm_monoid N] [module R N]

namespace dfinsupp

include dec_ι

/-- `dfinsupp.mk` as a `linear_map`. -/
def lmk (s : finset ι) : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i :=
{ to_fun := mk s, map_add' := λ _ _, mk_add, map_smul' := λ c x, mk_smul R x }

/-- `dfinsupp.single` as a `linear_map` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
{ to_fun := single i, map_smul' := λ r x, single_smul _, .. dfinsupp.single_add_hom _ _ }

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
lemma lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i x, φ (single i x) = ψ (single i x)) :
  φ = ψ :=
linear_map.to_add_monoid_hom_injective $ add_hom_ext h

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext] lemma lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
  φ = ψ :=
lhom_ext $ λ i, linear_map.congr_fun (h i)

omit dec_ι

/-- Interpret `λ (f : Π₀ i, M i), f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i :=
{ to_fun := λ f, f i,
  map_add' := λ f g, add_apply f g i,
  map_smul' := λ c f, smul_apply c f i}

include dec_ι

@[simp] lemma lmk_apply (s : finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x := rfl

@[simp] lemma lsingle_apply (i : ι) (x : M i) : (lsingle i : _ →ₗ[R] _) x = single i x := rfl

omit dec_ι

@[simp] lemma lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : _ →ₗ[R] _) f = f i := rfl

section lsum

/-- Typeclass inference can't find `dfinsupp.add_comm_monoid` without help for this case.
This instance allows it to be found where it is needed on the LHS of the colon in
`dfinsupp.module_of_linear_map`. -/
instance add_comm_monoid_of_linear_map : add_comm_monoid (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.add_comm_monoid _ (λ i, M i →ₗ[R] N) _

/-- Typeclass inference can't find `dfinsupp.module` without help for this case.
This is needed to define `dfinsupp.lsum` below.

The cause seems to be an inability to unify the `Π i, add_comm_monoid (M i →ₗ[R] N)` instance that
we have with the `Π i, has_zero (M i →ₗ[R] N)` instance which appears as a parameter to the
`dfinsupp` type. -/
instance module_of_linear_map [semiring S] [module S N] [smul_comm_class R S N] :
  module S (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.module _ (λ i, M i →ₗ[R] N) _ _ _ _

variables (S)

include dec_ι

/-- The `dfinsupp` version of `finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps apply symm_apply]
def lsum [semiring S] [module S N] [smul_comm_class R S N] :
  (Π i, M i →ₗ[R] N) ≃ₗ[S] ((Π₀ i, M i) →ₗ[R] N) :=
{ to_fun := λ F, {
    to_fun := sum_add_hom (λ i, (F i).to_add_monoid_hom),
    map_add' := (lift_add_hom (λ i, (F i).to_add_monoid_hom)).map_add,
    map_smul' := λ c f, by {
      apply dfinsupp.induction f,
      { rw [smul_zero, add_monoid_hom.map_zero, smul_zero] },
      { intros a b f ha hb hf,
        rw [smul_add, add_monoid_hom.map_add, add_monoid_hom.map_add, smul_add, hf, ←single_smul,
          sum_add_hom_single, sum_add_hom_single, linear_map.to_add_monoid_hom_coe,
          linear_map.map_smul], } } },
  inv_fun := λ F i, F.comp (lsingle i),
  left_inv := λ F, by { ext x y, simp },
  right_inv := λ F, by { ext x y, simp },
  map_add' := λ F G, by { ext x y, simp },
  map_smul' := λ c F, by { ext, simp } }

end lsum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/

section map_range

variables {β β₁ β₂: ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (β₁ i)] [Π i, add_comm_monoid (β₂ i)]
variables [Π i, module R (β i)] [Π i, module R (β₁ i)] [Π i, module R (β₂ i)]

lemma map_range_smul (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
  (r : R) (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i):
  map_range f hf (r • g) = r • map_range f hf g :=
begin
  ext,
  simp only [map_range_apply f, coe_smul, pi.smul_apply, hf']
end

/-- `dfinsupp.map_range` as an `linear_map`. -/
@[simps apply]
def map_range.linear_map (f : Π i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, f i x) (λ i, (f i).map_zero),
  map_smul' := λ r, map_range_smul _ _ _ (λ i, (f i).map_smul r),
  .. map_range.add_monoid_hom (λ i, (f i).to_add_monoid_hom) }

@[simp]
lemma map_range.linear_map_id :
  map_range.linear_map (λ i, (linear_map.id : (β₂ i) →ₗ[R] _)) = linear_map.id :=
linear_map.ext map_range_id

lemma map_range.linear_map_comp (f : Π i, β₁ i →ₗ[R] β₂ i) (f₂ : Π i, β i →ₗ[R] β₁ i):
  map_range.linear_map (λ i, (f i).comp (f₂ i)) =
    (map_range.linear_map f).comp (map_range.linear_map f₂) :=
linear_map.ext $ map_range_comp (λ i x, f i x) (λ i x, f₂ i x) _ _ _

/-- `dfinsupp.map_range.linear_map` as an `linear_equiv`. -/
@[simps apply]
def map_range.linear_equiv (e : Π i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, e i x) (λ i, (e i).map_zero),
  inv_fun := map_range (λ i x, (e i).symm x) (λ i, (e i).symm.map_zero),
  .. map_range.add_equiv (λ i, (e i).to_add_equiv),
  .. map_range.linear_map (λ i, (e i).to_linear_map) }

@[simp]
lemma map_range.linear_equiv_refl :
  (map_range.linear_equiv $ λ i, linear_equiv.refl R (β₁ i)) = linear_equiv.refl _ _ :=
linear_equiv.ext map_range_id

lemma map_range.linear_equiv_trans (f : Π i, β i ≃ₗ[R] β₁ i) (f₂ : Π i, β₁ i ≃ₗ[R] β₂ i):
  map_range.linear_equiv (λ i, (f i).trans (f₂ i)) =
    (map_range.linear_equiv f).trans (map_range.linear_equiv f₂) :=
linear_equiv.ext $ map_range_comp (λ i x, f₂ i x) (λ i x, f i x) _ _ _

@[simp]
lemma map_range.linear_equiv_symm (e : Π i, β₁ i ≃ₗ[R] β₂ i) :
  (map_range.linear_equiv e).symm = map_range.linear_equiv (λ i, (e i).symm) := rfl

end map_range

section basis

/-- The direct sum of free modules is free.

Note that while this is stated for `dfinsupp` not `direct_sum`, the types are defeq. -/
noncomputable def basis {η : ι → Type*} (b : Π i, basis (η i) R (M i)) :
  basis (Σ i, η i) R (Π₀ i, M i) :=
basis.of_repr ((map_range.linear_equiv (λ i, (b i).repr)).trans
  (sigma_finsupp_lequiv_dfinsupp R).symm)

end basis

end dfinsupp
