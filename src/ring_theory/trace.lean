/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.bilinear_form
import linear_algebra.char_poly.coeff
import linear_algebra.trace
import ring_theory.power_basis

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/

universes u v w

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables {K L : Type*} [field K] [field L] [algebra K L]
variables {ι : Type w} [fintype ι]

open finite_dimensional
open linear_map
open matrix

open_locale big_operators
open_locale matrix

namespace algebra

variables (b : basis ι R S)

variables (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R :=
(linear_map.trace R S).comp (lmul R S).to_linear_map

variables {S}

-- Not a `simp` lemma since there are more interesting ways to rewrite `trace R S x`,
-- for example `trace_trace`
lemma trace_apply (x) : trace R S x = linear_map.trace R S (lmul R S x) := rfl

lemma trace_eq_zero_of_not_exists_basis
  (h : ¬ ∃ (s : finset S), nonempty (basis s R S)) : trace R S = 0 :=
by { ext s, simp [trace_apply, linear_map.trace, h] }

include b

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma trace_eq_matrix_trace [decidable_eq ι] (b : basis ι R S) (s : S) :
  trace R S s = matrix.trace _ R _ (algebra.left_mul_matrix b s) :=
by rw [trace_apply, linear_map.trace_eq_matrix_trace _ b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
lemma trace_algebra_map_of_basis (x : R) :
  trace R S (algebra_map R S x) = fintype.card ι • x :=
begin
  haveI := classical.dec_eq ι,
  rw [trace_apply, linear_map.trace_eq_matrix_trace R b, trace_diag],
  convert finset.sum_const _,
  ext i,
  simp,
end
omit b

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
lemma trace_algebra_map (x : K) : trace K L (algebra_map K L x) = finrank K L • x :=
begin
  by_cases H : ∃ (s : finset L), nonempty (basis s K L),
  { rw [trace_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some] },
  { simp [trace_eq_zero_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis_finset H] }
end

lemma trace_trace_of_basis [algebra S T] [is_scalar_tower R S T]
  {ι κ : Type*} [fintype ι] [fintype κ]
  (b : basis ι R S) (c : basis κ S T) (x : T) :
  trace R S (trace S T x) = trace R T x :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq κ,
  rw [trace_eq_matrix_trace (b.smul c), trace_eq_matrix_trace b, trace_eq_matrix_trace c,
      matrix.trace_apply, matrix.trace_apply, matrix.trace_apply,
      ← finset.univ_product_univ, finset.sum_product],
  refine finset.sum_congr rfl (λ i _, _),
  simp only [alg_hom.map_sum, smul_left_mul_matrix, finset.sum_apply,
      -- The unifier is not smart enough to apply this one by itself:
      finset.sum_apply i _ (λ y, left_mul_matrix b (left_mul_matrix c x y y))]
end

lemma trace_comp_trace_of_basis [algebra S T] [is_scalar_tower R S T]
  {ι κ : Type*} [fintype ι] [fintype κ]
  (b : basis ι R S) (c : basis κ S T) :
  (trace R S).comp ((trace S T).restrict_scalars R) = trace R T :=
by { ext, rw [linear_map.comp_apply, linear_map.restrict_scalars_apply, trace_trace_of_basis b c] }

@[simp]
lemma trace_trace [algebra K T] [algebra L T] [is_scalar_tower K L T]
  [finite_dimensional K L] [finite_dimensional L T] (x : T) :
  trace K L (trace L T x) = trace K T x :=
trace_trace_of_basis (basis.of_vector_space K L) (basis.of_vector_space L T) x

@[simp]
lemma trace_comp_trace [algebra K T] [algebra L T] [is_scalar_tower K L T]
  [finite_dimensional K L] [finite_dimensional L T] :
  (trace K L).comp ((trace L T).restrict_scalars K) = trace K T :=
by { ext, rw [linear_map.comp_apply, linear_map.restrict_scalars_apply, trace_trace] }

section trace_form

variables (R S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : bilin_form R S :=
(linear_map.compr₂ (lmul R S).to_linear_map (trace R S)).to_bilin

variables {S}

-- This is a nicer lemma than the one produced by `@[simps] def trace_form`.
@[simp] lemma trace_form_apply (x y : S) : trace_form R S x y = trace R S (x * y) := rfl

lemma trace_form_is_sym : sym_bilin_form.is_sym (trace_form R S) :=
λ x y, congr_arg (trace R S) (mul_comm _ _)

lemma trace_form_to_matrix [decidable_eq ι] (i j) :
  bilin_form.to_matrix b (trace_form R S) i j = trace R S (b i * b j) :=
by rw [bilin_form.to_matrix_apply, trace_form_apply]

lemma trace_form_to_matrix_power_basis (h : power_basis R S) :
  bilin_form.to_matrix h.basis (trace_form R S) = λ i j, (trace R S (h.gen ^ (i + j : ℕ))) :=
by { ext, rw [trace_form_to_matrix, pow_add, h.basis_eq_pow, h.basis_eq_pow] }

end trace_form

section eq_prod_roots

open polynomial

variables {F : Type*} [field F]
variables [algebra K S] [algebra K F]

lemma trace_gen_eq_sum_roots [nontrivial S] (pb : power_basis K S)
  (hf : (minpoly K pb.gen).splits (algebra_map K F)) :
  algebra_map K F (trace K S pb.gen) =
    ((minpoly K pb.gen).map (algebra_map K F)).roots.sum :=
begin
  have d_pos : 0 < pb.dim := power_basis.dim_pos pb,
  have d_pos' : 0 < (minpoly K pb.gen).nat_degree, { simpa },
  haveI : nonempty (fin pb.dim) := ⟨⟨0, d_pos⟩⟩,
  -- Write the LHS as the `d-1`'th coefficient of `minpoly K pb.gen`
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_char_poly_coeff, char_poly_left_mul_matrix,
      ring_hom.map_neg, ← pb.nat_degree_minpoly, fintype.card_fin,
      ← next_coeff_of_pos_nat_degree _ d_pos',
      ← next_coeff_map (algebra_map K F).injective],
  -- Rewrite `minpoly K pb.gen` as a product over the roots.
  conv_lhs { rw eq_prod_roots_of_splits hf },
  rw [monic.next_coeff_mul, next_coeff_C_eq_zero, zero_add, monic.next_coeff_multiset_prod],
  -- And conclude both sides are the same.
  simp_rw [next_coeff_X_sub_C, multiset.sum_map_neg, neg_neg],
  -- Now we deal with the side conditions.
  { intros, apply monic_X_sub_C },
  { convert monic_one, simp [(minpoly.monic pb.is_integral_gen).leading_coeff] },
  { apply monic_multiset_prod_of_monic,
    intros, apply monic_X_sub_C },
end

end eq_prod_roots

end algebra
