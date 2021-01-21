/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import field_theory.adjoin

/-!
# Power basis

This file defines a structure `power_basis R S`, giving a basis of the
`R`-algebra `S` as a finite list of powers `1, x, ..., x^n`.
There are also constructors for `power_basis` when adjoining an algebraic
element to a ring/field.

## Definitions

* `power_basis R A`: a structure containing an `x` and an `n` such that
`1, x, ..., x^n` is a basis for the `R`-algebra `A` (viewed as an `R`-module).

* `findim (hf : f ≠ 0) : finite_dimensional.findim K (adjoin_root f) = f.nat_degree`,
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
(is_basis : is_basis R (λ (i : fin dim), gen ^ (i : ℕ)))

namespace power_basis

/-- Cannot be an instance because `power_basis` cannot be a class. -/
lemma finite_dimensional [algebra K S] (pb : power_basis K S) : finite_dimensional K S :=
finite_dimensional.of_fintype_basis pb.is_basis

lemma findim [algebra K S] (pb : power_basis K S) : finite_dimensional.findim K S = pb.dim :=
by rw [finite_dimensional.findim_eq_card_basis pb.is_basis, fintype.card_fin]

/-- TODO: this mixes `polynomial` and `finsupp`, we should hide this behind a
new function `polynomial.of_finsupp`. -/
lemma polynomial.mem_supported_range {f : polynomial R} {d : ℕ} :
  (f : finsupp ℕ R) ∈ finsupp.supported R R (↑(finset.range d) : set ℕ) ↔ f.degree < d :=
by { simp_rw [finsupp.mem_supported', finset.mem_coe, finset.mem_range, not_lt,
              degree_lt_iff_coeff_zero],
     refl }

lemma mem_span_pow' {x y : S} {d : ℕ} :
  y ∈ submodule.span R (set.range (λ (i : fin d), x ^ (i : ℕ))) ↔
    ∃ f : polynomial R, f.degree < d ∧ y = aeval x f :=
begin
  have : set.range (λ (i : fin d), x ^ (i : ℕ)) = (λ (i : ℕ), x ^ i) '' ↑(finset.range d),
  { ext n,
    simp_rw [set.mem_range, set.mem_image, finset.mem_coe, finset.mem_range],
    exact ⟨λ ⟨⟨i, hi⟩, hy⟩, ⟨i, hi, hy⟩, λ ⟨i, hi, hy⟩, ⟨⟨i, hi⟩, hy⟩⟩ },
  rw [this, finsupp.mem_span_iff_total],
  -- In the next line we use that `polynomial R := finsupp ℕ R`.
  -- It would be nice to have a function `polynomial.of_finsupp`.
  apply exists_congr,
  rintro (f : polynomial R),
  simp only [exists_prop, polynomial.mem_supported_range, eq_comm],
  apply and_congr iff.rfl,
  split;
  { rintro rfl;
    rw [finsupp.total_apply, aeval_def, eval₂_eq_sum, eq_comm],
    apply finset.sum_congr rfl,
    rintro i -,
    simp only [algebra.smul_def] }
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
by { rw [← pb.is_basis.total_repr 1, finsupp.total_apply, finsupp.sum_fintype],
     { refine finset.sum_eq_zero (λ x hx, _),
       cases x with x x_lt,
       rw h at x_lt,
       cases x_lt },
     { simp } }

lemma exists_eq_aeval [nontrivial S] (pb : power_basis R S) (y : S) :
  ∃ f : polynomial R, f.nat_degree < pb.dim ∧ y = aeval pb.gen f :=
(mem_span_pow pb.dim_ne_zero).mp (pb.is_basis.mem_span y)

section minpoly

open_locale big_operators

variable [algebra A S]

/-- `pb.minpoly_gen` is a minimal polynomial for `pb.gen`.

If `A` is not a field, it might not necessarily be *the* minimal polynomial,
however `nat_degree_minpoly` shows its degree is indeed minimal.
-/
noncomputable def minpoly_gen (pb : power_basis A S) : polynomial A :=
X ^ pb.dim -
  ∑ (i : fin pb.dim), C (pb.is_basis.repr (pb.gen ^ pb.dim) i) * X ^ (i : ℕ)

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
  refine sub_eq_zero.mpr ((pb.is_basis.total_repr (pb.gen ^ pb.dim)).symm.trans _),
  rw [finsupp.total_apply, finsupp.sum_fintype],
  intro i, rw zero_smul
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
  refine linear_independent_iff'.mp h.is_basis.1 finset.univ _ _ i (finset.mem_univ _),
  rw aeval_eq_sum_range' hlt at root,
  rw finset.sum_fin_eq_sum_range,
  convert root,
  ext i,
  split_ifs with hi,
  { refl },
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
  pb.is_basis.constr (λ i, y ^ (i : ℕ)) (aeval pb.gen f) = aeval y f :=
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
  exact @constr_basis _ _ _ _ _ _ _ _ _ _ _ (⟨i, hi⟩ : fin pb.dim) pb.is_basis,
end

lemma constr_pow_gen (pb : power_basis A S) {y : S'}
  (hy : aeval y (minpoly A pb.gen) = 0) :
  pb.is_basis.constr (λ i, y ^ (i : ℕ)) pb.gen = y :=
by { convert pb.constr_pow_aeval hy X; rw aeval_X }

lemma constr_pow_algebra_map (pb : power_basis A S) {y : S'}
  (hy : aeval y (minpoly A pb.gen) = 0) (x : A) :
  pb.is_basis.constr (λ i, y ^ (i : ℕ)) (algebra_map A S x) = algebra_map A S' x :=
by { convert pb.constr_pow_aeval hy (C x); rw aeval_C }

lemma constr_pow_mul [nontrivial S] (pb : power_basis A S) {y : S'}
  (hy : aeval y (minpoly A pb.gen) = 0) (x x' : S) :
  pb.is_basis.constr (λ i, y ^ (i : ℕ)) (x * x') =
    pb.is_basis.constr (λ i, y ^ (i : ℕ)) x * pb.is_basis.constr (λ i, y ^ (i : ℕ)) x' :=
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
  .. pb.is_basis.constr (λ i, y ^ (i : ℕ)) }

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

namespace algebra

open power_basis

lemma mem_span_power_basis [nontrivial R] {x y : S} (hx : _root_.is_integral R x)
  (hy : ∃ f : polynomial R, y = aeval x f) :
  y ∈ submodule.span R (set.range (λ (i : fin (minpoly R x).nat_degree),
    x ^ (i : ℕ))) :=
begin
  obtain ⟨f, rfl⟩ := hy,
  rw mem_span_pow',
  have := minpoly.monic hx,
  refine ⟨f.mod_by_monic (minpoly R x),
    lt_of_lt_of_le (degree_mod_by_monic_lt _ this (ne_zero_of_monic this)) degree_le_nat_degree,
    _⟩,
  conv_lhs { rw ← mod_by_monic_add_div f this },
  simp only [add_zero, zero_mul, minpoly.aeval, aeval_add, alg_hom.map_mul]
end

lemma linear_independent_power_basis [algebra K S] {x : S} (hx : _root_.is_integral K x) :
  linear_independent K (λ (i : fin (minpoly K x).nat_degree), x ^ (i : ℕ)) :=
begin
  rw linear_independent_iff,
  intros p hp,
  let f : polynomial K := p.sum (λ i, monomial i),
  have f_def : ∀ (i : fin _), f.coeff i = p i,
  { intro i,
    -- TODO: how can we avoid unfolding here?
    change (p.sum (λ i pi, finsupp.single i pi) : ℕ →₀ K) i = p i,
    simp_rw [finsupp.sum_apply, finsupp.single_apply, finsupp.sum],
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
    -- TODO: how can we avoid unfolding here?
    change (p.sum (λ i pi, finsupp.single i pi) : ℕ →₀ K) i = 0,
    simp_rw [finsupp.sum_apply, finsupp.single_apply, finsupp.sum],
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
    rw [finsupp.total_apply, aeval_def, eval₂_eq_sum, finsupp.sum_sum_index],
    { apply finset.sum_congr rfl,
      rintro i -,
      simp only [algebra.smul_def, monomial, finsupp.lsingle_apply, zero_mul, ring_hom.map_zero,
        finsupp.sum_single_index] },
    { intro, simp only [ring_hom.map_zero, zero_mul] },
    { intros, simp only [ring_hom.map_add, add_mul] } },
  have : ¬ (minpoly K x).degree ≤ f.degree,
  { apply not_le_of_lt,
    rw [degree_eq_nat_degree (minpoly.ne_zero hx), degree_lt_iff_coeff_zero],
    intros i hi,
    rw [f_def' i, dif_neg],
    exact not_lt_of_ge hi },
  contradiction
end

lemma power_basis_is_basis [algebra K S] {x : S} (hx : _root_.is_integral K x) :
  is_basis K (λ (i : fin (minpoly K x).nat_degree),
    (⟨x, subset_adjoin (set.mem_singleton x)⟩ ^ (i : ℕ) : adjoin K ({x} : set S))) :=
begin
  have hST : function.injective (algebra_map (adjoin K ({x} : set S)) S) := subtype.coe_injective,
  have hx' : _root_.is_integral K
    (show adjoin K ({x} : set S), from ⟨x, subset_adjoin (set.mem_singleton x)⟩),
  { apply (is_integral_algebra_map_iff hST).mp,
    convert hx,
    apply_instance },
  have minpoly_eq := minpoly.eq_of_algebra_map_eq hST hx' rfl,
  refine ⟨_, _root_.eq_top_iff.mpr _⟩,
  { have := linear_independent_power_basis hx',
    rwa minpoly_eq at this },
  { rintros ⟨y, hy⟩ _,
    have := mem_span_power_basis hx',
    rw minpoly_eq at this,
    apply this,
    { rw [adjoin_singleton_eq_range] at hy,
      obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy,
      use f,
      ext,
      exact (is_scalar_tower.algebra_map_aeval K (adjoin K {x}) S ⟨x, _⟩ _).symm } }
end

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.power_basis [algebra K S] {x : S} (hx : _root_.is_integral K x) :
  power_basis K (adjoin K ({x} : set S)) :=
{ gen := ⟨x, subset_adjoin (set.mem_singleton x)⟩,
  dim := (minpoly K x).nat_degree,
  is_basis := power_basis_is_basis hx }

end algebra

namespace adjoin_root

variables {f : polynomial K}

lemma power_basis_is_basis (hf : f ≠ 0) : is_basis K (λ (i : fin f.nat_degree), (root f ^ i.val)) :=
begin
  set f' := f * C (f.leading_coeff⁻¹) with f'_def,
  have deg_f' : f'.nat_degree = f.nat_degree,
  { rw [nat_degree_mul hf, nat_degree_C, add_zero],
    { rwa [ne.def, C_eq_zero, inv_eq_zero, leading_coeff_eq_zero] } },
  have f'_monic : monic f' := monic_mul_leading_coeff_inv hf,
  have aeval_f' : aeval (root f) f' = 0,
  { rw [f'_def, alg_hom.map_mul, aeval_eq, mk_self, zero_mul] },
  have hx : is_integral K (root f) := ⟨f', f'_monic, aeval_f'⟩,
  have minpoly_eq : f' = minpoly K (root f),
  { apply minpoly.unique K _ f'_monic aeval_f',
    intros q q_monic q_aeval,
    have commutes : (lift (algebra_map K (adjoin_root f)) (root f) q_aeval).comp (mk q) = mk f,
    { ext,
      { simp only [ring_hom.comp_apply, mk_C, lift_of], refl },
      { simp only [ring_hom.comp_apply, mk_X, lift_root] } },
    rw [degree_eq_nat_degree f'_monic.ne_zero, degree_eq_nat_degree q_monic.ne_zero,
        with_bot.coe_le_coe, deg_f'],
    apply nat_degree_le_of_dvd,
    { rw [←ideal.mem_span_singleton, ←ideal.quotient.eq_zero_iff_mem],
      change mk f q = 0,
      rw [←commutes, ring_hom.comp_apply, mk_self, ring_hom.map_zero] },
    { exact q_monic.ne_zero } },
  refine ⟨_, eq_top_iff.mpr _⟩,
  { rw [←deg_f', minpoly_eq],
    exact algebra.linear_independent_power_basis hx, },
  { rintros y -,
    rw [←deg_f', minpoly_eq],
    apply algebra.mem_span_power_basis hx,
    obtain ⟨g⟩ := y,
    use g,
    rw aeval_eq,
    refl }
end

/-- The power basis `1, root f, ..., root f ^ (d - 1)` for `adjoin_root f`,
where `f` is an irreducible polynomial over a field of degree `d`. -/
noncomputable def power_basis (hf : f ≠ 0) :
  power_basis K (adjoin_root f) :=
{ gen := root f,
  dim := f.nat_degree,
  is_basis := power_basis_is_basis hf }

end adjoin_root

namespace intermediate_field

lemma power_basis_is_basis {x : L} (hx : is_integral K x) :
  is_basis K (λ (i : fin (minpoly K x).nat_degree), (adjoin_simple.gen K x ^ (i : ℕ))) :=
begin
  let ϕ := (adjoin_root_equiv_adjoin K hx).to_linear_equiv,
  have key : ϕ (adjoin_root.root (minpoly K x)) = adjoin_simple.gen K x,
  { exact intermediate_field.adjoin_root_equiv_adjoin_apply_root K hx },
  suffices : ϕ ∘ (λ (i : fin (minpoly K x).nat_degree),
    adjoin_root.root (minpoly K x) ^ (i.val)) =
      (λ (i : fin (minpoly K x).nat_degree),
        (adjoin_simple.gen K x) ^ ↑i),
  { rw ← this, exact linear_equiv.is_basis
    (adjoin_root.power_basis_is_basis (minpoly.ne_zero hx)) ϕ },
  ext y,
  rw [function.comp_app, fin.val_eq_coe, alg_equiv.to_linear_equiv_apply, alg_equiv.map_pow],
  rw intermediate_field.adjoin_root_equiv_adjoin_apply_root K hx,
end

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.power_basis {x : L} (hx : is_integral K x) :
  power_basis K K⟮x⟯ :=
{ gen := adjoin_simple.gen K x,
  dim := (minpoly K x).nat_degree,
  is_basis := power_basis_is_basis hx }

@[simp] lemma adjoin.power_basis.gen_eq {x : L} (hx : is_integral K x) :
  (adjoin.power_basis hx).gen = adjoin_simple.gen K x := rfl

lemma adjoin.finite_dimensional {x : L} (hx : is_integral K x) : finite_dimensional K K⟮x⟯ :=
power_basis.finite_dimensional (adjoin.power_basis hx)

lemma adjoin.findim {x : L} (hx : is_integral K x) :
  finite_dimensional.findim K K⟮x⟯ = (minpoly K x).nat_degree :=
begin
  rw power_basis.findim (adjoin.power_basis hx),
  refl,
end

end intermediate_field

namespace power_basis

open intermediate_field

/-- `pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable def equiv_adjoin_simple (pb : power_basis K L) :
  K⟮pb.gen⟯ ≃ₐ[K] L :=
(adjoin.power_basis pb.is_integral_gen).equiv pb
  (minpoly.eq_of_algebra_map_eq (algebra_map K⟮pb.gen⟯ L).injective
    (adjoin.power_basis pb.is_integral_gen).is_integral_gen
    (by rw [adjoin.power_basis.gen_eq, adjoin_simple.algebra_map_gen]))

@[simp]
lemma equiv_adjoin_simple_aeval (pb : power_basis K L) (f : polynomial K) :
  pb.equiv_adjoin_simple (aeval (adjoin_simple.gen K pb.gen) f) = aeval pb.gen f :=
equiv_aeval _ pb _ f

@[simp]
lemma equiv_adjoin_simple_gen (pb : power_basis K L) :
  pb.equiv_adjoin_simple (adjoin_simple.gen K pb.gen) = pb.gen :=
equiv_gen _ pb _

@[simp]
lemma equiv_adjoin_simple_symm_aeval (pb : power_basis K L) (f : polynomial K) :
  pb.equiv_adjoin_simple.symm (aeval pb.gen f) = aeval (adjoin_simple.gen K pb.gen) f :=
by rw [equiv_adjoin_simple, equiv_symm, equiv_aeval, adjoin.power_basis.gen_eq]

@[simp]
lemma equiv_adjoin_simple_symm_gen (pb : power_basis K L) :
  pb.equiv_adjoin_simple.symm pb.gen = (adjoin_simple.gen K pb.gen) :=
by rw [equiv_adjoin_simple, equiv_symm, equiv_gen, adjoin.power_basis.gen_eq]

end power_basis
