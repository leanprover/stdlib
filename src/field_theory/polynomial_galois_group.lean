/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/

import analysis.complex.polynomial
import field_theory.galois
import group_theory.perm.cycle_type
import ring_theory.eisenstein_criterion

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.splitting_field`, and some specific
results about the Galois groups of ℚ-polynomials with specific numbers of non-real roots.

## Main definitions

- `polynomial.gal p`: the Galois group of a polynomial p.
- `polynomial.gal.restrict p E`: the restriction homomorphism `(E ≃ₐ[F] E) → gal p`.
- `polynomial.gal.gal_action p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `polynomial.gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `polynomial.gal.gal_action_hom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `polynomial.gal.restrict_prod_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `polynomial.gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`.
- `polynomial.gal.gal_action_hom_bijective_of_prime_degree`:
An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
equals the number of real roots plus the number of roots not fixed by complex conjugation
(i.e. with some imaginary component).

-/

noncomputable theory
open_locale classical

open finite_dimensional

namespace polynomial

variables {F : Type*} [field F] (p q : polynomial F) (E : Type*) [field E] [algebra F E]

/-- The Galois group of a polynomial. -/
@[derive [has_coe_to_fun, group, fintype]]
def gal := p.splitting_field ≃ₐ[F] p.splitting_field

namespace gal

@[ext] lemma ext {σ τ : p.gal} (h : ∀ x ∈ p.root_set p.splitting_field, σ x = τ x) : σ = τ :=
begin
  refine alg_equiv.ext (λ x, (alg_hom.mem_equalizer σ.to_alg_hom τ.to_alg_hom x).mp
      ((set_like.ext_iff.mp _ x).mpr algebra.mem_top)),
  rwa [eq_top_iff, ←splitting_field.adjoin_roots, algebra.adjoin_le_iff],
end

/-- If `p` splits in `F` then the `p.gal` is trivial. -/
def unique_gal_of_splits (h : p.splits (ring_hom.id F)) : unique p.gal :=
{ default := 1,
  uniq := λ f, alg_equiv.ext (λ x, by { obtain ⟨y, rfl⟩ := algebra.mem_bot.mp
    ((set_like.ext_iff.mp ((is_splitting_field.splits_iff _ p).mp h) x).mp algebra.mem_top),
    rw [alg_equiv.commutes, alg_equiv.commutes] }) }

instance [h : fact (p.splits (ring_hom.id F))] : unique p.gal :=
unique_gal_of_splits _ (h.1)

instance unique_gal_zero : unique (0 : polynomial F).gal :=
unique_gal_of_splits _ (splits_zero _)

instance unique_gal_one : unique (1 : polynomial F).gal :=
unique_gal_of_splits _ (splits_one _)

instance unique_gal_C (x : F) : unique (C x).gal :=
unique_gal_of_splits _ (splits_C _ _)

instance unique_gal_X : unique (X : polynomial F).gal :=
unique_gal_of_splits _ (splits_X _)

instance unique_gal_X_sub_C (x : F) : unique (X - C x).gal :=
unique_gal_of_splits _ (splits_X_sub_C _)

instance unique_gal_X_pow (n : ℕ) : unique (X ^ n : polynomial F).gal :=
unique_gal_of_splits _ (splits_X_pow _ _)

instance [h : fact (p.splits (algebra_map F E))] : algebra p.splitting_field E :=
(is_splitting_field.lift p.splitting_field p h.1).to_ring_hom.to_algebra

instance [h : fact (p.splits (algebra_map F E))] : is_scalar_tower F p.splitting_field E :=
is_scalar_tower.of_algebra_map_eq
  (λ x, ((is_splitting_field.lift p.splitting_field p h.1).commutes x).symm)

/-- Restrict from a superfield automorphism into a member of `gal p`. -/
def restrict [fact (p.splits (algebra_map F E))] : (E ≃ₐ[F] E) →* p.gal :=
alg_equiv.restrict_normal_hom p.splitting_field

lemma restrict_surjective [fact (p.splits (algebra_map F E))] [normal F E] :
  function.surjective (restrict p E) :=
alg_equiv.restrict_normal_hom_surjective E

section roots_action

/-- The function taking `roots p p.splitting_field` to `roots p E`. This is actually a bijection,
see `polynomial.gal.map_roots_bijective`. -/
def map_roots [fact (p.splits (algebra_map F E))] :
  root_set p p.splitting_field → root_set p E :=
λ x, ⟨is_scalar_tower.to_alg_hom F p.splitting_field E x, begin
  have key := subtype.mem x,
  by_cases p = 0,
  { simp only [h, root_set_zero] at key,
    exact false.rec _ key },
  { rw [mem_root_set h, aeval_alg_hom_apply, (mem_root_set h).mp key, alg_hom.map_zero] } end⟩

lemma map_roots_bijective [h : fact (p.splits (algebra_map F E))] :
  function.bijective (map_roots p E) :=
begin
  split,
  { exact λ _ _ h, subtype.ext (ring_hom.injective _ (subtype.ext_iff.mp h)) },
  { intro y,
    -- this is just an equality of two different ways to write the roots of `p` as an `E`-polynomial
    have key := roots_map
      (is_scalar_tower.to_alg_hom F p.splitting_field E : p.splitting_field →+* E)
      ((splits_id_iff_splits _).mpr (is_splitting_field.splits p.splitting_field p)),
    rw [map_map, alg_hom.comp_algebra_map] at key,
    have hy := subtype.mem y,
    simp only [root_set, finset.mem_coe, multiset.mem_to_finset, key, multiset.mem_map] at hy,
    rcases hy with ⟨x, hx1, hx2⟩,
    exact ⟨⟨x, multiset.mem_to_finset.mpr hx1⟩, subtype.ext hx2⟩ }
end

/-- The bijection between `root_set p p.splitting_field` and `root_set p E`. -/
def roots_equiv_roots [fact (p.splits (algebra_map F E))] :
  (root_set p p.splitting_field) ≃ (root_set p E) :=
equiv.of_bijective (map_roots p E) (map_roots_bijective p E)

instance gal_action_aux : mul_action p.gal (root_set p p.splitting_field) :=
{ smul := λ ϕ x, ⟨ϕ x, begin
    have key := subtype.mem x,
    --simp only [root_set, finset.mem_coe, multiset.mem_to_finset] at *,
    by_cases p = 0,
    { simp only [h, root_set_zero] at key,
      exact false.rec _ key },
    { rw mem_root_set h,
      change aeval (ϕ.to_alg_hom x) p = 0,
      rw [aeval_alg_hom_apply, (mem_root_set h).mp key, alg_hom.map_zero] } end⟩,
  one_smul := λ _, by { ext, refl },
  mul_smul := λ _ _ _, by { ext, refl } }

/-- The action of `gal p` on the roots of `p` in `E`. -/
instance gal_action [fact (p.splits (algebra_map F E))] : mul_action p.gal (root_set p E) :=
{ smul := λ ϕ x, roots_equiv_roots p E (ϕ • ((roots_equiv_roots p E).symm x)),
  one_smul := λ _, by simp only [equiv.apply_symm_apply, one_smul],
  mul_smul := λ _ _ _, by simp only [equiv.apply_symm_apply, equiv.symm_apply_apply, mul_smul] }

variables {p E}

/-- `polynomial.gal.restrict p E` is compatible with `polynomial.gal.gal_action p E`. -/
@[simp] lemma restrict_smul [fact (p.splits (algebra_map F E))]
  (ϕ : E ≃ₐ[F] E) (x : root_set p E) : ↑((restrict p E ϕ) • x) = ϕ x :=
begin
  let ψ := alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F p.splitting_field E),
  change ↑(ψ (ψ.symm _)) = ϕ x,
  rw alg_equiv.apply_symm_apply ψ,
  change ϕ (roots_equiv_roots p E ((roots_equiv_roots p E).symm x)) = ϕ x,
  rw equiv.apply_symm_apply (roots_equiv_roots p E),
end

variables (p E)

/-- `polynomial.gal.gal_action` as a permutation representation -/
def gal_action_hom [fact (p.splits (algebra_map F E))] : p.gal →* equiv.perm (root_set p E) :=
{ to_fun := λ ϕ, equiv.mk (λ x, ϕ • x) (λ x, ϕ⁻¹ • x)
  (λ x, inv_smul_smul ϕ x) (λ x, smul_inv_smul ϕ x),
  map_one' := by { ext1 x, exact mul_action.one_smul x },
  map_mul' := λ x y, by { ext1 z, exact mul_action.mul_smul x y z } }

lemma gal_action_hom_restrict [fact (p.splits (algebra_map F E))]
  (ϕ : E ≃ₐ[F] E) (x : root_set p E) : ↑(gal_action_hom p E (restrict p E ϕ) x) = ϕ x :=
restrict_smul ϕ x

/-- `gal p` embeds as a subgroup of permutations of the roots of `p` in `E`. -/
lemma gal_action_hom_injective [fact (p.splits (algebra_map F E))] :
  function.injective (gal_action_hom p E) :=
begin
  rw monoid_hom.injective_iff,
  intros ϕ hϕ,
  ext x hx,
  have key := equiv.perm.ext_iff.mp hϕ (roots_equiv_roots p E ⟨x, hx⟩),
  change roots_equiv_roots p E (ϕ • (roots_equiv_roots p E).symm
    (roots_equiv_roots p E ⟨x, hx⟩)) = roots_equiv_roots p E ⟨x, hx⟩ at key,
  rw equiv.symm_apply_apply at key,
  exact subtype.ext_iff.mp (equiv.injective (roots_equiv_roots p E) key),
end

end roots_action

variables {p q}

/-- `polynomial.gal.restrict`, when both fields are splitting fields of polynomials. -/
def restrict_dvd (hpq : p ∣ q) : q.gal →* p.gal :=
if hq : q = 0 then 1 else @restrict F _ p _ _ _
  ⟨splits_of_splits_of_dvd (algebra_map F q.splitting_field) hq (splitting_field.splits q) hpq⟩

lemma restrict_dvd_surjective (hpq : p ∣ q) (hq : q ≠ 0) :
  function.surjective (restrict_dvd hpq) :=
by simp only [restrict_dvd, dif_neg hq, restrict_surjective]

variables (p q)

/-- The Galois group of a product maps into the product of the Galois groups.  -/
def restrict_prod : (p * q).gal →* p.gal × q.gal :=
monoid_hom.prod (restrict_dvd (dvd_mul_right p q)) (restrict_dvd (dvd_mul_left q p))

/-- `polynomial.gal.restrict_prod` is actually a subgroup embedding. -/
lemma restrict_prod_injective : function.injective (restrict_prod p q) :=
begin
  by_cases hpq : (p * q) = 0,
  { haveI : unique (p * q).gal := by { rw hpq, apply_instance },
    exact λ f g h, eq.trans (unique.eq_default f) (unique.eq_default g).symm },
  intros f g hfg,
  dsimp only [restrict_prod, restrict_dvd] at hfg,
  simp only [dif_neg hpq, monoid_hom.prod_apply, prod.mk.inj_iff] at hfg,
  ext x hx,
  rw [root_set, map_mul, polynomial.roots_mul] at hx,
  cases multiset.mem_add.mp (multiset.mem_to_finset.mp hx) with h h,
  { haveI : fact (p.splits (algebra_map F (p * q).splitting_field)) :=
      ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits (p * q)) (dvd_mul_right p q)⟩,
    have key : x = algebra_map (p.splitting_field) (p * q).splitting_field
      ((roots_equiv_roots p _).inv_fun ⟨x, multiset.mem_to_finset.mpr h⟩) :=
      subtype.ext_iff.mp (equiv.apply_symm_apply (roots_equiv_roots p _) ⟨x, _⟩).symm,
    rw [key, ←alg_equiv.restrict_normal_commutes, ←alg_equiv.restrict_normal_commutes],
    exact congr_arg _ (alg_equiv.ext_iff.mp hfg.1 _) },
  { haveI : fact (q.splits (algebra_map F (p * q).splitting_field)) :=
      ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits (p * q)) (dvd_mul_left q p)⟩,
    have key : x = algebra_map (q.splitting_field) (p * q).splitting_field
      ((roots_equiv_roots q _).inv_fun ⟨x, multiset.mem_to_finset.mpr h⟩) :=
      subtype.ext_iff.mp (equiv.apply_symm_apply (roots_equiv_roots q _) ⟨x, _⟩).symm,
    rw [key, ←alg_equiv.restrict_normal_commutes, ←alg_equiv.restrict_normal_commutes],
    exact congr_arg _ (alg_equiv.ext_iff.mp hfg.2 _) },
  { rwa [ne.def, mul_eq_zero, map_eq_zero, map_eq_zero, ←mul_eq_zero] }
end

lemma mul_splits_in_splitting_field_of_mul {p₁ q₁ p₂ q₂ : polynomial F}
  (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (h₁ : p₁.splits (algebra_map F q₁.splitting_field))
  (h₂ : p₂.splits (algebra_map F q₂.splitting_field)) :
  (p₁ * p₂).splits (algebra_map F (q₁ * q₂).splitting_field) :=
begin
  apply splits_mul,
  { rw ← (splitting_field.lift q₁ (splits_of_splits_of_dvd _
      (mul_ne_zero hq₁ hq₂) (splitting_field.splits _) (dvd_mul_right q₁ q₂))).comp_algebra_map,
    exact splits_comp_of_splits _ _ h₁, },
  { rw ← (splitting_field.lift q₂ (splits_of_splits_of_dvd _
      (mul_ne_zero hq₁ hq₂) (splitting_field.splits _) (dvd_mul_left q₂ q₁))).comp_algebra_map,
    exact splits_comp_of_splits _ _ h₂, },
end

/-- `p` splits in the splitting field of `p ∘ q`, for `q` non-constant. -/
lemma splits_in_splitting_field_of_comp (hq : q.nat_degree ≠ 0) :
  p.splits (algebra_map F (p.comp q).splitting_field) :=
begin
  let P : polynomial F → Prop := λ r, r.splits (algebra_map F (r.comp q).splitting_field),
  have key1 : ∀ {r : polynomial F}, irreducible r → P r,
  { intros r hr,
    by_cases hr' : nat_degree r = 0,
    { exact splits_of_nat_degree_le_one _ (le_trans (le_of_eq hr') zero_le_one) },
    obtain ⟨x, hx⟩ := exists_root_of_splits _ (splitting_field.splits (r.comp q))
      (λ h, hr' ((mul_eq_zero.mp (nat_degree_comp.symm.trans
        (nat_degree_eq_of_degree_eq_some h))).resolve_right hq)),
    rw [←aeval_def, aeval_comp] at hx,
    have h_normal : normal F (r.comp q).splitting_field := splitting_field.normal (r.comp q),
    have qx_int := normal.is_integral h_normal (aeval x q),
    exact splits_of_splits_of_dvd _
      (minpoly.ne_zero qx_int)
      (normal.splits h_normal _)
      (dvd_symm_of_irreducible (minpoly.irreducible qx_int) hr (minpoly.dvd F _ hx)) },
  have key2 : ∀ {p₁ p₂ : polynomial F}, P p₁ → P p₂ → P (p₁ * p₂),
  { intros p₁ p₂ hp₁ hp₂,
    by_cases h₁ : p₁.comp q = 0,
    { cases comp_eq_zero_iff.mp h₁ with h h,
      { rw [h, zero_mul],
        exact splits_zero _ },
      { exact false.rec _ (hq (by rw [h.2, nat_degree_C])) } },
    by_cases h₂ : p₂.comp q = 0,
    { cases comp_eq_zero_iff.mp h₂ with h h,
      { rw [h, mul_zero],
        exact splits_zero _ },
      { exact false.rec _ (hq (by rw [h.2, nat_degree_C])) } },
    have key := mul_splits_in_splitting_field_of_mul h₁ h₂ hp₁ hp₂,
    rwa ← mul_comp at key },
  exact wf_dvd_monoid.induction_on_irreducible p (splits_zero _)
    (λ _, splits_of_is_unit _) (λ _ _ _ h, key2 (key1 h)),
end

/-- `polynomial.gal.restrict` for the composition of polynomials. -/
def restrict_comp (hq : q.nat_degree ≠ 0) : (p.comp q).gal →* p.gal :=
@restrict F _ p _ _ _ ⟨splits_in_splitting_field_of_comp p q hq⟩

lemma restrict_comp_surjective (hq : q.nat_degree ≠ 0) :
  function.surjective (restrict_comp p q hq) :=
by simp only [restrict_comp, restrict_surjective]

variables {p q}

/-- For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`. -/
lemma card_of_separable (hp : p.separable) :
  fintype.card p.gal = finrank F p.splitting_field :=
begin
  haveI : is_galois F p.splitting_field := is_galois.of_separable_splitting_field hp,
  exact is_galois.card_aut_eq_finrank F p.splitting_field,
end

lemma prime_degree_dvd_card [char_zero F] (p_irr : irreducible p) (p_deg : p.nat_degree.prime) :
  p.nat_degree ∣ fintype.card p.gal :=
begin
  rw gal.card_of_separable p_irr.separable,
  have hp : p.degree ≠ 0 :=
    λ h, nat.prime.ne_zero p_deg (nat_degree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h)),
  let α : p.splitting_field := root_of_splits (algebra_map F p.splitting_field)
    (splitting_field.splits p) hp,
  have hα : is_integral F α :=
    (is_algebraic_iff_is_integral F).mp (algebra.is_algebraic_of_finite α),
  use finite_dimensional.finrank F⟮α⟯ p.splitting_field,
  suffices : (minpoly F α).nat_degree = p.nat_degree,
  { rw [←finite_dimensional.finrank_mul_finrank F F⟮α⟯ p.splitting_field,
        intermediate_field.adjoin.finrank hα, this] },
  suffices : minpoly F α ∣ p,
  { have key := dvd_symm_of_irreducible (minpoly.irreducible hα) p_irr this,
    apply le_antisymm,
    { exact nat_degree_le_of_dvd this p_irr.ne_zero },
    { exact nat_degree_le_of_dvd key (minpoly.ne_zero hα) } },
  apply minpoly.dvd F α,
  rw [aeval_def, map_root_of_splits _ (splitting_field.splits p) hp],
end

section rationals

lemma splits_ℚ_ℂ {p : polynomial ℚ} : fact (p.splits (algebra_map ℚ ℂ)) :=
⟨is_alg_closed.splits_codomain p⟩

local attribute [instance] splits_ℚ_ℂ

/-- The number of complex roots equals the number of real roots plus
    the number of roots not fixed by complex conjugation (i.e. with some imaginary component). -/
lemma card_complex_roots_eq_card_real_add_card_not_gal_inv (p : polynomial ℚ) :
  (p.root_set ℂ).to_finset.card = (p.root_set ℝ).to_finset.card +
  (gal_action_hom p ℂ (restrict p ℂ (complex.conj_ae.restrict_scalars ℚ))).support.card :=
begin
  by_cases hp : p = 0,
  { simp_rw [hp, root_set_zero, set.to_finset_eq_empty_iff.mpr rfl, finset.card_empty, zero_add],
    refine eq.symm (nat.le_zero_iff.mp ((finset.card_le_univ _).trans (le_of_eq _))),
    simp_rw [hp, root_set_zero, fintype.card_eq_zero_iff],
    apply_instance },
  have inj : function.injective (is_scalar_tower.to_alg_hom ℚ ℝ ℂ) := (algebra_map ℝ ℂ).injective,
  rw [←finset.card_image_of_injective _ subtype.coe_injective,
      ←finset.card_image_of_injective _ inj],
  let a : finset ℂ := _,
  let b : finset ℂ := _,
  let c : finset ℂ := _,
  change a.card = b.card + c.card,
  have ha : ∀ z : ℂ, z ∈ a ↔ aeval z p = 0 :=
  λ z, by rw [set.mem_to_finset, mem_root_set hp],
  have hb : ∀ z : ℂ, z ∈ b ↔ aeval z p = 0 ∧ z.im = 0,
  { intro z,
    simp_rw [finset.mem_image, exists_prop, set.mem_to_finset, mem_root_set hp],
    split,
    { rintros ⟨w, hw, rfl⟩,
      exact ⟨by rw [aeval_alg_hom_apply, hw, alg_hom.map_zero], rfl⟩ },
    { rintros ⟨hz1, hz2⟩,
      have key : is_scalar_tower.to_alg_hom ℚ ℝ ℂ z.re = z := by { ext, refl, rw hz2, refl },
      exact ⟨z.re, inj (by rwa [←aeval_alg_hom_apply, key, alg_hom.map_zero]), key⟩ } },
  have hc0 : ∀ w : p.root_set ℂ, gal_action_hom p ℂ
    (restrict p ℂ (complex.conj_ae.restrict_scalars ℚ)) w = w ↔ w.val.im = 0,
  { intro w,
    rw [subtype.ext_iff, gal_action_hom_restrict],
    exact complex.eq_conj_iff_im },
  have hc : ∀ z : ℂ, z ∈ c ↔ aeval z p = 0 ∧ z.im ≠ 0,
  { intro z,
    simp_rw [finset.mem_image, exists_prop],
    split,
    { rintros ⟨w, hw, rfl⟩,
      exact ⟨(mem_root_set hp).mp w.2, mt (hc0 w).mpr (equiv.perm.mem_support.mp hw)⟩ },
    { rintros ⟨hz1, hz2⟩,
      exact ⟨⟨z, (mem_root_set hp).mpr hz1⟩,
        equiv.perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩ } },
  rw ← finset.card_disjoint_union,
  { apply congr_arg finset.card,
    simp_rw [finset.ext_iff, finset.mem_union, ha, hb, hc],
    tauto },
  { intro z,
    rw [finset.inf_eq_inter, finset.mem_inter, hb, hc],
    tauto },
  { apply_instance },
end

/-- An irreducible polynomial of prime degree with two non-real roots has full Galois group. -/
lemma gal_action_hom_bijective_of_prime_degree
  {p : polynomial ℚ} (p_irr : irreducible p) (p_deg : p.nat_degree.prime)
  (p_roots : fintype.card (p.root_set ℂ) = fintype.card (p.root_set ℝ) + 2) :
  function.bijective (gal_action_hom p ℂ) :=
begin
  have h1 : fintype.card (p.root_set ℂ) = p.nat_degree,
  { simp_rw [root_set_def, finset.coe_sort_coe, fintype.card_coe],
    rw [multiset.to_finset_card_of_nodup, ←nat_degree_eq_card_roots],
    { exact is_alg_closed.splits_codomain p },
    { exact nodup_roots ((separable_map (algebra_map ℚ ℂ)).mpr p_irr.separable) } },
  have h2 : fintype.card p.gal = fintype.card (gal_action_hom p ℂ).range :=
  fintype.card_congr (monoid_hom.of_injective (gal_action_hom_injective p ℂ)).to_equiv,
  let conj := restrict p ℂ (complex.conj_ae.restrict_scalars ℚ),
  refine ⟨gal_action_hom_injective p ℂ, λ x, (congr_arg (has_mem.mem x)
    (show (gal_action_hom p ℂ).range = ⊤, from _)).mpr (subgroup.mem_top x)⟩,
  apply equiv.perm.subgroup_eq_top_of_swap_mem,
  { rwa h1 },
  { rw [h1, ←h2],
    exact prime_degree_dvd_card p_irr p_deg },
  { exact ⟨conj, rfl⟩ },
  { rw ← equiv.perm.card_support_eq_two,
    apply nat.add_left_cancel,
    rw [←p_roots, ←set.to_finset_card (root_set p ℝ), ←set.to_finset_card (root_set p ℂ)],
    exact (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm },
end

/-- An irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group. -/
lemma gal_action_hom_bijective_of_prime_degree'
  {p : polynomial ℚ} (p_irr : irreducible p) (p_deg : p.nat_degree.prime)
  (p_roots1 : fintype.card (p.root_set ℝ) + 1 ≤ fintype.card (p.root_set ℂ))
  (p_roots2 : fintype.card (p.root_set ℂ) ≤ fintype.card (p.root_set ℝ) + 3) :
  function.bijective (gal_action_hom p ℂ) :=
begin
  apply gal_action_hom_bijective_of_prime_degree p_irr p_deg,
  let n := (gal_action_hom p ℂ (restrict p ℂ
    (complex.conj_ae.restrict_scalars ℚ))).support.card,
  have hn : 2 ∣ n :=
  equiv.perm.two_dvd_card_support (by rw [←monoid_hom.map_pow, ←monoid_hom.map_pow,
    show alg_equiv.restrict_scalars ℚ complex.conj_ae ^ 2 = 1,
    from alg_equiv.ext complex.conj_conj, monoid_hom.map_one, monoid_hom.map_one]),
  have key := card_complex_roots_eq_card_real_add_card_not_gal_inv p,
  simp_rw [set.to_finset_card] at key,
  rw [key, add_le_add_iff_left] at p_roots1 p_roots2,
  rw [key, add_right_inj],
  suffices : ∀ m : ℕ, 2 ∣ m → 1 ≤ m → m ≤ 3 → m = 2,
  { exact this n hn p_roots1 p_roots2 },
  rintros m ⟨k, rfl⟩ h2 h3,
  exact le_antisymm (nat.lt_succ_iff.mp (lt_of_le_of_ne h3 (show 2 * k ≠ 2 * 1 + 1,
    from nat.two_mul_ne_two_mul_add_one))) (nat.succ_le_iff.mpr (lt_of_le_of_ne h2
    (show 2 * 0 + 1 ≠ 2 * k, from nat.two_mul_ne_two_mul_add_one.symm))),
end

end rationals

end gal

end polynomial
