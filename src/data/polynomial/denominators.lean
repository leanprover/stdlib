/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.erase_lead
/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ polynomial R` the "mathematical" expression `b ^ f.nat_degree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/

open polynomial finset

section denoms_clearable

variables {R K : Type*} [semiring R] [comm_semiring K] {i : R →+* K}
variables {a b : R} {bi : K}
-- TODO: use hypothesis (ub : is_unit (i b)) to work with localizations.

/-- `denoms_clearable` formalizes the property that `b ^ N * f (a / b)`
does not have denominators, if the inequality `f.nat_degree ≤ N` holds.

In the implementation, we also use provide an inverse in the existential.
-/
def denoms_clearable (a b : R) (N : ℕ) (f : polynomial R) (i : R →+* K) : Prop :=
  ∃ D : R, ∃ bi : K, bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)

lemma denoms_clearable_zero (N : ℕ) (a b : R) (bu : bi * i b = 1) :
  denoms_clearable a b N 0 i :=
⟨0, bi, bu, by simp only [eval_zero, ring_hom.map_zero, mul_zero, map_zero]⟩

lemma denoms_clearable_C_mul_X_pow {N : ℕ} (a : R) (bu : bi * i b = 1) {n : ℕ} (r : R)
  (nN : n ≤ N) : denoms_clearable a b N (C r * X ^ n) i :=
begin
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, _⟩,
  rw [C_mul_X_pow_eq_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C],
  rw [ring_hom.map_mul, ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_pow, eval_X, mul_comm],
  rw [← nat.sub_add_cancel nN] {occs := occurrences.pos [2]},
  rw [pow_add, mul_assoc, mul_comm (i b ^ n), mul_pow, mul_assoc, mul_assoc (i a ^ n), ← mul_pow],
  rw [bu, one_pow, mul_one],
end

lemma denoms_clearable.add {N : ℕ} {a b : R} {f g : polynomial R} :
    denoms_clearable a b N f i →
    denoms_clearable a b N g i →
    denoms_clearable a b N (f + g) i :=
λ ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩, ⟨Df + Dg, bf, bfu,
  begin
    rw [ring_hom.map_add, polynomial.map_add, eval_add, mul_add, Hf, Hg],
    congr,
    refine @inv_unique K _ (i b) bg bf _ _;
    rwa mul_comm,
  end ⟩

lemma denoms_clearable_of_nat_degree_le (N : ℕ) (a b : R) {bi : K} (bu : bi * i b = 1) :
  ∀ (f : polynomial R), f.nat_degree ≤ N → denoms_clearable a b N f i :=
induction_with_nat_degree_le N
  (denoms_clearable_zero N a b bu)
  (λ N_1 r r0, denoms_clearable_C_mul_X_pow N a b bu N_1 r)
  (λ f g fN gN df dg, df.add dg)

/-- If `i : R → K` is a ring homomorphism, `f` is a polynomial with coefficients in `R`,
`a, b` are elements of `R`, with `i b` invertible, then there is a `D ∈ R` such that
`b ^ f.nat_degree * f (a / b)` equals `i D`. -/
theorem denoms_clearable_nat_degree
  (i : R →+* K) (f : polynomial R) (a b : R) (bi : K) (bu : bi * i b = 1) :
  denoms_clearable a b f.nat_degree f i :=
denoms_clearable_of_nat_degree_le (f.nat_degree) a b bu f le_rfl

end denoms_clearable
