/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import field_theory.minpoly

/-!
# Power basis

This file defines a structure `power_basis R S`, giving a basis of the
`R`-algebra `S` as a finite list of powers `1, x, ..., x^n`.
For example, if `x` is algebraic over a ring/field, adjoining `x`
gives a `power_basis` structure generated by `x`.

## Definitions

* `power_basis R A`: a structure containing an `x` and an `n` such that
`1, x, ..., x^n` is a basis for the `R`-algebra `A` (viewed as an `R`-module).

* `finrank (hf : f ≠ 0) : finite_dimensional.finrank K (adjoin_root f) = f.nat_degree`,
  the dimension of `adjoin_root f` equals the degree of `f`

* `power_basis.lift (pb : power_basis R S)`: if `y : S'` satisfies the same
  equations as `pb.gen`, this is the map `S →ₐ[R] S'` sending `pb.gen` to `y`

* `power_basis.equiv`: if two power bases satisfy the same equations, they are
  equivalent as algebras

## Implementation notes

Throughout this file, `R`, `S`, ... are `comm_ring`s, `A`, `B`, ... are
`integral_domain`s and `K`, `L`, ... are `field`s.
`S` is an `R`-algebra, `B` is an `A`-algebra, `L` is a `K`-algebra.

## Tags

power basis, powerbasis

-/

open polynomial

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra S T] [algebra R T] [is_scalar_tower R S T]
variables {A B : Type*} [integral_domain A] [integral_domain B] [algebra A B]
variables {K L : Type*} [field K] [field L] [algebra K L]

/-- `pb : power_basis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)`
is a basis for the `R`-algebra `S` (viewed as `R`-module).

This is a structure, not a class, since the same algebra can have many power bases.
For the common case where `S` is defined by adjoining an integral element to `R`,
the canonical power basis is given by `{algebra,intermediate_field}.adjoin.power_basis`.
-/
@[nolint has_inhabited_instance]
structure power_basis (R S : Type*) [comm_ring R] [ring S] [algebra R S] :=
(gen : S)
(dim : ℕ)
(basis : basis (fin dim) R S)
(basis_eq_pow : ∀ i, basis i = gen ^ (i : ℕ))

namespace power_basis

@[simp] lemma coe_basis (pb : power_basis R S) :
  ⇑pb.basis = λ (i : fin pb.dim), pb.gen ^ (i : ℕ) :=
funext pb.basis_eq_pow

/-- Cannot be an instance because `power_basis` cannot be a class. -/
lemma finite_dimensional [algebra K S] (pb : power_basis K S) : finite_dimensional K S :=
finite_dimensional.of_fintype_basis pb.basis

lemma finrank [algebra K S] (pb : power_basis K S) : finite_dimensional.finrank K S = pb.dim :=
by rw [finite_dimensional.finrank_eq_card_basis pb.basis, fintype.card_fin]

lemma mem_span_pow' {x y : S} {d : ℕ} :
  y ∈ submodule.span R (set.range (λ (i : fin d), x ^ (i : ℕ))) ↔
    ∃ f : polynomial R, f.degree < d ∧ y = aeval x f :=
begin
  have : set.range (λ (i : fin d), x ^ (i : ℕ)) = (λ (i : ℕ), x ^ i) '' ↑(finset.range d),
  { ext n,
    simp_rw [set.mem_range, set.mem_image, finset.mem_coe, finset.mem_range],
    exact ⟨λ ⟨⟨i, hi⟩, hy⟩, ⟨i, hi, hy⟩, λ ⟨i, hi, hy⟩, ⟨⟨i, hi⟩, hy⟩⟩ },
  simp only [this, finsupp.mem_span_image_iff_total, degree_lt_iff_coeff_zero,
    exists_iff_exists_finsupp, coeff, aeval, eval₂_ring_hom', eval₂_eq_sum, polynomial.sum, support,
    finsupp.mem_supported', finsupp.total, finsupp.sum, algebra.smul_def, eval₂_zero, exists_prop,
    linear_map.id_coe, eval₂_one, id.def, not_lt, finsupp.coe_lsum, linear_map.coe_smul_right,
    finset.mem_range, alg_hom.coe_mk, finset.mem_coe],
  simp_rw [@eq_comm _ y],
  exact iff.rfl
end

lemma mem_span_pow {x y : S} {d : ℕ} (hd : d ≠ 0) :
  y ∈ submodule.span R (set.range (λ (i : fin d), x ^ (i : ℕ))) ↔
    ∃ f : polynomial R, f.nat_degree < d ∧ y = aeval x f :=
begin
  rw mem_span_pow',
  split;
  { rintros ⟨f, h, hy⟩,
    refine ⟨f, _, hy⟩,
    by_cases hf : f = 0,
    { simp only [hf, nat_degree_zero, degree_zero] at h ⊢,
      exact lt_of_le_of_ne (nat.zero_le d) hd.symm <|> exact with_bot.bot_lt_some d },
    simpa only [degree_eq_nat_degree hf, with_bot.coe_lt_coe] using h },
end

lemma dim_ne_zero [nontrivial S] (pb : power_basis R S) : pb.dim ≠ 0 :=
λ h, one_ne_zero $
show (1 : S) = 0,
by { rw [← pb.basis.total_repr 1, finsupp.total_apply, finsupp.sum_fintype],
     { refine finset.sum_eq_zero (λ x hx, _),
       cases x with x x_lt,
       rw h at x_lt,
       cases x_lt },
     { simp } }

lemma dim_pos [nontrivial S] (pb : power_basis R S) : 0 < pb.dim :=
nat.pos_of_ne_zero pb.dim_ne_zero

lemma exists_eq_aeval [nontrivial S] (pb : power_basis R S) (y : S) :
  ∃ f : polynomial R, f.nat_degree < pb.dim ∧ y = aeval pb.gen f :=
(mem_span_pow pb.dim_ne_zero).mp (by simpa using pb.basis.mem_span y)

section minpoly

open_locale big_operators

variable [algebra A S]

/-- `pb.minpoly_gen` is a minimal polynomial for `pb.gen`.

If `A` is not a field, it might not necessarily be *the* minimal polynomial,
however `nat_degree_minpoly` shows its degree is indeed minimal.
-/
noncomputable def minpoly_gen (pb : power_basis A S) : polynomial A :=
X ^ pb.dim -
  ∑ (i : fin pb.dim), C (pb.basis.repr (pb.gen ^ pb.dim) i) * X ^ (i : ℕ)

@[simp]
lemma nat_degree_minpoly_gen (pb : power_basis A S) :
  nat_degree (minpoly_gen pb) = pb.dim :=
begin
  unfold minpoly_gen,
  apply nat_degree_eq_of_degree_eq_some,
  rw degree_sub_eq_left_of_degree_lt; rw degree_X_pow,
  apply degree_sum_fin_lt
end

lemma minpoly_gen_monic (pb : power_basis A S) : monic (minpoly_gen pb) :=
begin
  apply monic_sub_of_left (monic_pow (monic_X) _),
  rw degree_X_pow,
  exact degree_sum_fin_lt _
end

@[simp]
lemma aeval_minpoly_gen (pb : power_basis A S) : aeval pb.gen (minpoly_gen pb) = 0 :=
begin
  simp_rw [minpoly_gen, alg_hom.map_sub, alg_hom.map_sum, alg_hom.map_mul, alg_hom.map_pow,
           aeval_C, ← algebra.smul_def, aeval_X],
  refine sub_eq_zero.mpr ((pb.basis.total_repr (pb.gen ^ pb.dim)).symm.trans _),
  rw [finsupp.total_apply, finsupp.sum_fintype];
    simp only [pb.coe_basis, zero_smul, eq_self_iff_true, implies_true_iff]
end

lemma is_integral_gen (pb : power_basis A S) : is_integral A pb.gen :=
⟨minpoly_gen pb, minpoly_gen_monic pb, aeval_minpoly_gen pb⟩

lemma dim_le_nat_degree_of_root (h : power_basis A S) {p : polynomial A}
  (ne_zero : p ≠ 0) (root : aeval h.gen p = 0) :
  h.dim ≤ p.nat_degree :=
begin
  refine le_of_not_lt (λ hlt, ne_zero _),
  let p_coeff : fin (h.dim) → A := λ i, p.coeff i,
  suffices : ∀ i, p_coeff i = 0,
  { ext i,
    by_cases hi : i < h.dim,
    { exact this ⟨i, hi⟩ },
    exact coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le hlt (le_of_not_gt hi)) },
  intro i,
  refine linear_independent_iff'.mp h.basis.linear_independent _ _ _ i (finset.mem_univ _),
  rw aeval_eq_sum_range' hlt at root,
  rw finset.sum_fin_eq_sum_range,
  convert root,
  ext i,
  split_ifs with hi,
  { simp_rw [coe_basis, p_coeff, fin.coe_mk] },
  { rw [coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le hlt (le_of_not_gt hi)),
        zero_smul] }
end

@[simp]
lemma nat_degree_minpoly (pb : power_basis A S) :
  (minpoly A pb.gen).nat_degree = pb.dim :=
begin
  refine le_antisymm _
    (dim_le_nat_degree_of_root pb (minpoly.ne_zero pb.is_integral_gen) (minpoly.aeval _ _)),
  rw ← nat_degree_minpoly_gen,
  apply nat_degree_le_of_degree_le,
  rw ← degree_eq_nat_degree (minpoly_gen_monic pb).ne_zero,
  exact minpoly.min _ _ (minpoly_gen_monic pb) (aeval_minpoly_gen pb)
end

end minpoly

section equiv

variables [algebra A S] {S' : Type*} [comm_ring S'] [algebra A S']

lemma nat_degree_lt_nat_degree {p q : polynomial R} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
  p.nat_degree < q.nat_degree :=
begin
  by_cases hq : q = 0, { rw [hq, degree_zero] at hpq, have := not_lt_bot hpq, contradiction },
  rwa [degree_eq_nat_degree hp, degree_eq_nat_degree hq, with_bot.coe_lt_coe] at hpq
end

lemma constr_pow_aeval (pb : power_basis A S) {y : S'}
  (hy : aeval y (minpoly A pb.gen) = 0) (f : polynomial A) :
  pb.basis.constr A (λ i, y ^ (i : ℕ)) (aeval pb.gen f) = aeval y f :=
begin
  rw [← aeval_mod_by_monic_eq_self_of_root (minpoly.monic pb.is_integral_gen) (minpoly.aeval _ _),
      ← @aeval_mod_by_monic_eq_self_of_root _ _ _ _ _ f _ (minpoly.monic pb.is_integral_gen) y hy],
  by_cases hf : f %ₘ minpoly A pb.gen = 0,
  { simp only [hf, alg_hom.map_zero, linear_map.map_zero] },
  have : (f %ₘ minpoly A pb.gen).nat_degree < pb.dim,
  { rw ← pb.nat_degree_minpoly,
    apply nat_degree_lt_nat_degree hf,
    exact degree_mod_by_monic_lt _ (minpoly.monic pb.is_integral_gen)
      (minpoly.ne_zero pb.is_integral_gen) },
  rw [aeval_eq_sum_range' this, aeval_eq_sum_range' this, linear_map.map_sum],
  refine finset.sum_congr rfl (λ i (hi : i ∈ finset.range pb.dim), _),
  rw finset.mem_range at hi,
  rw linear_map.map_smul,
  congr,
  rw [← fin.coe_mk hi, ← pb.basis_eq_pow ⟨i, hi⟩, basis.constr_basis]
end

lemma constr_pow_gen (pb : power_basis A S) {y : S'}
  (hy : aeval y (minpoly A pb.gen) = 0) :
  pb.basis.constr A (λ i, y ^ (i : ℕ)) pb.gen = y :=
by { convert pb.constr_pow_aeval hy X; rw aeval_X }

lemma constr_pow_algebra_map (pb : power_basis A S) {y : S'}
  (hy : aeval y (minpoly A pb.gen) = 0) (x : A) :
  pb.basis.constr A (λ i, y ^ (i : ℕ)) (algebra_map A S x) = algebra_map A S' x :=
by { convert pb.constr_pow_aeval hy (C x); rw aeval_C }

lemma constr_pow_mul [nontrivial S] (pb : power_basis A S) {y : S'}
  (hy : aeval y (minpoly A pb.gen) = 0) (x x' : S) :
  pb.basis.constr A (λ i, y ^ (i : ℕ)) (x * x') =
    pb.basis.constr A (λ i, y ^ (i : ℕ)) x * pb.basis.constr A (λ i, y ^ (i : ℕ)) x' :=
begin
  obtain ⟨f, hf, rfl⟩ := pb.exists_eq_aeval x,
  obtain ⟨g, hg, rfl⟩ := pb.exists_eq_aeval x',
  simp only [← aeval_mul, pb.constr_pow_aeval hy]
end

/-- `pb.lift y hy` is the algebra map sending `pb.gen` to `y`,
where `hy` states the higher powers of `y` are the same as the higher powers of `pb.gen`. -/
noncomputable def lift [nontrivial S] (pb : power_basis A S) (y : S')
  (hy : aeval y (minpoly A pb.gen) = 0) :
  S →ₐ[A] S' :=
{ map_one' := by { convert pb.constr_pow_algebra_map hy 1 using 2; rw ring_hom.map_one },
  map_zero' := by { convert pb.constr_pow_algebra_map hy 0 using 2; rw ring_hom.map_zero },
  map_mul' := pb.constr_pow_mul hy,
  commutes' := pb.constr_pow_algebra_map hy,
  .. pb.basis.constr A (λ i, y ^ (i : ℕ)) }

@[simp] lemma lift_gen [nontrivial S] (pb : power_basis A S) (y : S')
  (hy : aeval y (minpoly A pb.gen) = 0) :
  pb.lift y hy pb.gen = y :=
pb.constr_pow_gen hy

@[simp] lemma lift_aeval [nontrivial S] (pb : power_basis A S) (y : S')
  (hy : aeval y (minpoly A pb.gen) = 0) (f : polynomial A) :
  pb.lift y hy (aeval pb.gen f) = aeval y f :=
pb.constr_pow_aeval hy f

/-- `pb.equiv pb' h` is an equivalence of algebras with the same power basis. -/
noncomputable def equiv [nontrivial S] [nontrivial S']
  (pb : power_basis A S) (pb' : power_basis A S')
  (h : minpoly A pb.gen = minpoly A pb'.gen) :
  S ≃ₐ[A] S' :=
alg_equiv.of_alg_hom
  (pb.lift pb'.gen (h.symm ▸ minpoly.aeval A pb'.gen))
  (pb'.lift pb.gen (h ▸ minpoly.aeval A pb.gen))
  (by { ext x, obtain ⟨f, hf, rfl⟩ := pb'.exists_eq_aeval x, simp })
  (by { ext x, obtain ⟨f, hf, rfl⟩ := pb.exists_eq_aeval x, simp })

@[simp]
lemma equiv_aeval [nontrivial S] [nontrivial S']
  (pb : power_basis A S) (pb' : power_basis A S')
  (h : minpoly A pb.gen = minpoly A pb'.gen)
  (f : polynomial A) :
  pb.equiv pb' h (aeval pb.gen f) = aeval pb'.gen f :=
pb.lift_aeval _ (h.symm ▸ minpoly.aeval A _) _

@[simp]
lemma equiv_gen [nontrivial S] [nontrivial S']
  (pb : power_basis A S) (pb' : power_basis A S')
  (h : minpoly A pb.gen = minpoly A pb'.gen) :
  pb.equiv pb' h pb.gen = pb'.gen :=
pb.lift_gen _ (h.symm ▸ minpoly.aeval A _)

local attribute [irreducible] power_basis.lift

@[simp]
lemma equiv_symm [nontrivial S] [nontrivial S']
  (pb : power_basis A S) (pb' : power_basis A S')
  (h : minpoly A pb.gen = minpoly A pb'.gen) :
  (pb.equiv pb' h).symm = pb'.equiv pb h.symm :=
rfl

end equiv

end power_basis

open power_basis

/-- Useful lemma to show `x` generates a power basis:
the powers of `x` less than the degree of `x`'s minimal polynomial are linearly independent. -/
lemma is_integral.linear_independent_pow [algebra K S] {x : S} (hx : is_integral K x) :
  linear_independent K (λ (i : fin (minpoly K x).nat_degree), x ^ (i : ℕ)) :=
begin
  rw linear_independent_iff,
  intros p hp,
  set f : polynomial K := p.sum (λ i, monomial i) with hf0,
  have f_def : ∀ (i : fin _), f.coeff i = p i,
  { intro i,
    simp only [f, finsupp.sum, coeff_monomial, finset_sum_coeff],
    rw [finset.sum_eq_single, if_pos rfl],
    { intros b _ hb,
      rw if_neg (mt (λ h, _) hb),
      exact fin.coe_injective h },
    { intro hi,
      split_ifs; { exact finsupp.not_mem_support_iff.mp hi } } },
  have f_def' : ∀ i, f.coeff i = if hi : i < _ then p ⟨i, hi⟩ else 0,
  { intro i,
    split_ifs with hi,
    { exact f_def ⟨i, hi⟩ },
    simp only [f, finsupp.sum, coeff_monomial, finset_sum_coeff],
    apply finset.sum_eq_zero,
    rintro ⟨j, hj⟩ -,
    apply if_neg (mt _ hi),
    rintro rfl,
    exact hj },
  suffices : f = 0,
  { ext i, rw [← f_def, this, coeff_zero, finsupp.zero_apply] },
  contrapose hp with hf,
  intro h,
  have : (minpoly K x).degree ≤ f.degree,
  { apply minpoly.degree_le_of_ne_zero K x hf,
    convert h,
    simp_rw [finsupp.total_apply, aeval_def, hf0, finsupp.sum, eval₂_finset_sum],
    apply finset.sum_congr rfl,
    rintro i -,
    simp only [algebra.smul_def, eval₂_monomial] },
  have : ¬ (minpoly K x).degree ≤ f.degree,
  { apply not_le_of_lt,
    rw [degree_eq_nat_degree (minpoly.ne_zero hx), degree_lt_iff_coeff_zero],
    intros i hi,
    rw [f_def' i, dif_neg],
    exact hi.not_lt },
  contradiction
end

lemma is_integral.mem_span_pow [nontrivial R] {x y : S} (hx : is_integral R x)
  (hy : ∃ f : polynomial R, y = aeval x f) :
  y ∈ submodule.span R (set.range (λ (i : fin (minpoly R x).nat_degree),
    x ^ (i : ℕ))) :=
begin
  obtain ⟨f, rfl⟩ := hy,
  apply mem_span_pow'.mpr _,
  have := minpoly.monic hx,
  refine ⟨f.mod_by_monic (minpoly R x),
      lt_of_lt_of_le (degree_mod_by_monic_lt _ this (ne_zero_of_monic this)) degree_le_nat_degree,
      _⟩,
  conv_lhs { rw ← mod_by_monic_add_div f this },
  simp only [add_zero, zero_mul, minpoly.aeval, aeval_add, alg_hom.map_mul]
end

namespace power_basis

section map

variables {S' : Type*} [comm_ring S'] [algebra R S']

/-- `power_basis.map pb (e : S ≃ₐ[R] S')` is the power basis for `S'` generated by `e pb.gen`. -/
@[simps]
noncomputable def map (pb : power_basis R S) (e : S ≃ₐ[R] S') : power_basis R S' :=
{ dim := pb.dim,
  basis := pb.basis.map e.to_linear_equiv,
  gen := e pb.gen,
  basis_eq_pow :=
    λ i, by rw [basis.map_apply, pb.basis_eq_pow, e.to_linear_equiv_apply, e.map_pow] }

variables [algebra A S] [algebra A S']

@[simp]
lemma minpoly_gen_map (pb : power_basis A S) (e : S ≃ₐ[A] S') :
  (pb.map e).minpoly_gen = pb.minpoly_gen :=
by { dsimp only [minpoly_gen, map_dim], -- Turn `fin (pb.map e).dim` into `fin pb.dim`
     simp only [linear_equiv.trans_apply, map_basis, basis.map_repr,
        map_gen, alg_equiv.to_linear_equiv_apply, e.to_linear_equiv_symm, alg_equiv.map_pow,
        alg_equiv.symm_apply_apply, sub_right_inj] }

@[simp]
lemma equiv_map [nontrivial S] [nontrivial S'] (pb : power_basis A S) (e : S ≃ₐ[A] S')
  (h : minpoly A pb.gen = minpoly A (pb.map e).gen) :
  pb.equiv (pb.map e) h = e :=
by { ext x, obtain ⟨f, hf, rfl⟩ := pb.exists_eq_aeval x, simp [aeval_alg_equiv] }

end map

end power_basis
