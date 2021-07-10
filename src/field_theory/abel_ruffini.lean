/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/

import group_theory.solvable
import field_theory.polynomial_galois_group
import ring_theory.roots_of_unity

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `SBF F E` : the intermediate field of solvable-by-radicals elements

## Main results

* `solvable_gal_of_solvable_by_rad` : the minimal polynomial of an element of `SBF F E` has
solvable Galois group
-/

noncomputable theory
open_locale classical

open polynomial intermediate_field

section abel_ruffini

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma gal_zero_is_solvable : is_solvable (0 : polynomial F).gal :=
by apply_instance

lemma gal_one_is_solvable : is_solvable (1 : polynomial F).gal :=
by apply_instance

lemma gal_C_is_solvable (x : F) : is_solvable (C x).gal :=
by apply_instance

lemma gal_X_is_solvable : is_solvable (X : polynomial F).gal :=
by apply_instance

lemma gal_X_sub_C_is_solvable (x : F) : is_solvable (X - C x).gal :=
by apply_instance

lemma gal_X_pow_is_solvable (n : ℕ) : is_solvable (X ^ n : polynomial F).gal :=
by apply_instance

lemma gal_mul_is_solvable {p q : polynomial F}
  (hp : is_solvable p.gal) (hq : is_solvable q.gal) : is_solvable (p * q).gal :=
solvable_of_solvable_injective (gal.restrict_prod_injective p q)

lemma gal_prod_is_solvable {s : multiset (polynomial F)}
  (hs : ∀ p ∈ s, is_solvable (gal p)) : is_solvable s.prod.gal :=
begin
  apply multiset.induction_on' s,
  { exact gal_one_is_solvable },
  { intros p t hps hts ht,
    rw [multiset.insert_eq_cons, multiset.prod_cons],
    exact gal_mul_is_solvable (hs p hps) ht },
end

lemma gal_is_solvable_of_splits {p q : polynomial F}
  (hpq : fact (p.splits (algebra_map F q.splitting_field))) (hq : is_solvable q.gal) :
  is_solvable p.gal :=
begin
  haveI : is_solvable (q.splitting_field ≃ₐ[F] q.splitting_field) := hq,
  exact solvable_of_surjective (alg_equiv.restrict_normal_hom_surjective q.splitting_field),
end

lemma gal_is_solvable_tower (p q : polynomial F)
  (hpq : p.splits (algebra_map F q.splitting_field))
  (hp : is_solvable p.gal)
  (hq : is_solvable (q.map (algebra_map F p.splitting_field)).gal) :
  is_solvable q.gal :=
begin
  let K := p.splitting_field,
  let L := q.splitting_field,
  haveI : fact (p.splits (algebra_map F L)) := ⟨hpq⟩,
  let ϕ : (L ≃ₐ[K] L) ≃* (q.map (algebra_map F K)).gal :=
    (is_splitting_field.alg_equiv L (q.map (algebra_map F K))).aut_congr,
  have ϕ_inj : function.injective ϕ.to_monoid_hom := ϕ.injective,
  haveI : is_solvable (K ≃ₐ[F] K) := hp,
  haveI : is_solvable (L ≃ₐ[K] L) := solvable_of_solvable_injective ϕ_inj,
  exact is_solvable_of_is_scalar_tower F p.splitting_field q.splitting_field,
end

section gal_X_pow_sub_C

lemma gal_X_pow_sub_one_is_solvable (n : ℕ) : is_solvable (X ^ n - 1 : polynomial F).gal :=
begin
  by_cases hn : n = 0,
  { rw [hn, pow_zero, sub_self],
    exact gal_zero_is_solvable },
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
  have hn'' : (X ^ n - 1 : polynomial F) ≠ 0 :=
    λ h, one_ne_zero ((leading_coeff_X_pow_sub_one hn').symm.trans (congr_arg leading_coeff h)),
  apply is_solvable_of_comm,
  intros σ τ,
  ext a ha,
  rw [mem_root_set hn'', alg_hom.map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha,
  have key : ∀ σ : (X ^ n - 1 : polynomial F).gal, ∃ m : ℕ, σ a = a ^ m,
  { intro σ,
    obtain ⟨m, hm⟩ := σ.to_alg_hom.to_ring_hom.map_root_of_unity_eq_pow_self
      ⟨is_unit.unit (is_unit_of_pow_eq_one a n ha hn'),
      by { ext, rwa [units.coe_pow, is_unit.unit_spec, subtype.coe_mk n hn'] }⟩,
    use m,
    convert hm,
    all_goals { exact (is_unit.unit_spec _).symm } },
  obtain ⟨c, hc⟩ := key σ,
  obtain ⟨d, hd⟩ := key τ,
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_pow, hd, σ.map_pow, hc, ←pow_mul, pow_mul'],
end

lemma gal_X_pow_sub_C_is_solvable_aux (n : ℕ) (a : F)
  (h : (X ^ n - 1 : polynomial F).splits (ring_hom.id F)) : is_solvable (X ^ n - C a).gal :=
begin
  by_cases ha : a = 0,
  { rw [ha, C_0, sub_zero],
    exact gal_X_pow_is_solvable n },
  have ha' : algebra_map F (X ^ n - C a).splitting_field a ≠ 0 :=
    mt ((ring_hom.injective_iff _).mp (ring_hom.injective _) a) ha,
  by_cases hn : n = 0,
  { rw [hn, pow_zero, ←C_1, ←C_sub],
    exact gal_C_is_solvable (1 - a) },
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
  have hn'' : X ^ n - C a ≠ 0 :=
    λ h, one_ne_zero ((leading_coeff_X_pow_sub_C hn').symm.trans (congr_arg leading_coeff h)),
  have hn''' : (X ^ n - 1 : polynomial F) ≠ 0 :=
    λ h, one_ne_zero ((leading_coeff_X_pow_sub_one hn').symm.trans (congr_arg leading_coeff h)),
  have mem_range : ∀ {c}, c ^ n = 1 → ∃ d, algebra_map F (X ^ n - C a).splitting_field d = c :=
    λ c hc, ring_hom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c (or.resolve_left h hn'''
      (minpoly.irreducible ((splitting_field.normal (X ^ n - C a)).is_integral c)) (minpoly.dvd F c
      (by rwa [map_id, alg_hom.map_sub, sub_eq_zero, aeval_X_pow, aeval_one])))),
  apply is_solvable_of_comm,
  intros σ τ,
  ext b hb,
  rw [mem_root_set hn'', alg_hom.map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hb,
  have hb' : b ≠ 0,
  { intro hb',
    rw [hb', zero_pow hn'] at hb,
    exact ha' hb.symm },
  have key : ∀ σ : (X ^ n - C a).gal, ∃ c, σ b = b * algebra_map F _ c,
  { intro σ,
    have key : (σ b / b) ^ n = 1 := by rw [div_pow, ←σ.map_pow, hb, σ.commutes, div_self ha'],
    obtain ⟨c, hc⟩ := mem_range key,
    use c,
    rw [hc, mul_div_cancel' (σ b) hb'] },
  obtain ⟨c, hc⟩ := key σ,
  obtain ⟨d, hd⟩ := key τ,
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_mul, τ.commutes, hd, σ.map_mul, σ.commutes, hc],
  rw [mul_assoc, mul_assoc, mul_right_inj' hb', mul_comm],
end

lemma splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [field F] {E : Type*} [field E]
  (i : F →+* E) (n : ℕ) {a : F} (ha : a ≠ 0) (h : (X ^ n - C a).splits i) : (X ^ n - 1).splits i :=
begin
  have ha' : i a ≠ 0 := mt (i.injective_iff.mp (i.injective) a) ha,
  by_cases hn : n = 0,
  { rw [hn, pow_zero, sub_self],
    exact splits_zero i },
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
  have hn'' : (X ^ n - C a).degree ≠ 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt with_bot.coe_eq_coe.mp hn),
  obtain ⟨b, hb⟩ := exists_root_of_splits i h hn'',
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hb,
  have hb' : b ≠ 0,
  { intro hb',
    rw [hb', zero_pow hn'] at hb,
    exact ha' hb.symm },
  let s := ((X ^ n - C a).map i).roots,
  have hs : _ = _ * (s.map _).prod := eq_prod_roots_of_splits h,
  rw [leading_coeff_X_pow_sub_C hn', ring_hom.map_one, C_1, one_mul] at hs,
  have hs' : s.card = n := (nat_degree_eq_card_roots h).symm.trans nat_degree_X_pow_sub_C,
  apply @splits_of_exists_multiset F E _ _ i (X ^ n - 1) (s.map (λ c : E, c / b)),
  rw [leading_coeff_X_pow_sub_one hn', ring_hom.map_one, C_1, one_mul, multiset.map_map],
  have C_mul_C : (C (i a⁻¹)) * (C (i a)) = 1,
  { rw [←C_mul, ←i.map_mul, inv_mul_cancel ha, i.map_one, C_1] },
  have key1 : (X ^ n - 1).map i = C (i a⁻¹) * ((X ^ n - C a).map i).comp (C b * X),
  { rw [map_sub, map_sub, map_pow, map_X, map_C, map_one, sub_comp, pow_comp, X_comp, C_comp,
        mul_pow, ←C_pow, hb, mul_sub, ←mul_assoc, C_mul_C, one_mul] },
  have key2 : (λ q : polynomial E, q.comp (C b * X)) ∘ (λ c : E, X - C c) =
    (λ c : E, C b * (X - C (c / b))),
  { ext1 c,
    change (X - C c).comp (C b * X) = C b * (X - C (c / b)),
    rw [sub_comp, X_comp, C_comp, mul_sub, ←C_mul, mul_div_cancel' c hb'] },
  rw [key1, hs, prod_comp, multiset.map_map, key2, multiset.prod_map_mul, multiset.map_const,
      multiset.prod_repeat, hs', ←C_pow, hb, ←mul_assoc, C_mul_C, one_mul],
  all_goals { exact field.to_nontrivial F },
end

lemma gal_X_pow_sub_C_is_solvable (n : ℕ) (x : F) : is_solvable (X ^ n - C x).gal :=
begin
  by_cases hx : x = 0,
  { rw [hx, C_0, sub_zero],
    exact gal_X_pow_is_solvable n },
  apply gal_is_solvable_tower (X ^ n - 1) (X ^ n - C x),
  { exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (splitting_field.splits _) },
  { exact gal_X_pow_sub_one_is_solvable n },
  { rw [map_sub, map_pow, map_X, map_C],
    apply gal_X_pow_sub_C_is_solvable_aux,
    have key := splitting_field.splits (X ^ n - 1 : polynomial F),
    rwa [←splits_id_iff_splits, map_sub, map_pow, map_X, map_one] at key },
end

end gal_X_pow_sub_C

variables (F)

/-- Inductive definition of solvable by radicals -/
inductive is_solvable_by_rad : E → Prop
| base (a : F) : is_solvable_by_rad (algebra_map F E a)
| add (a b : E) : is_solvable_by_rad a → is_solvable_by_rad b → is_solvable_by_rad (a + b)
| neg (α : E) : is_solvable_by_rad α → is_solvable_by_rad (-α)
| mul (α β : E) : is_solvable_by_rad α → is_solvable_by_rad β → is_solvable_by_rad (α * β)
| inv (α : E) : is_solvable_by_rad α → is_solvable_by_rad α⁻¹
| rad (α : E) (n : ℕ) (hn : n ≠ 0) : is_solvable_by_rad (α^n) → is_solvable_by_rad α

variables (E)

/-- The intermediate field of solvable-by-radicals elements -/
def solvable_by_rad : intermediate_field F E :=
{ carrier := is_solvable_by_rad F,
  zero_mem' := by { convert is_solvable_by_rad.base (0 : F), rw ring_hom.map_zero },
  add_mem' := is_solvable_by_rad.add,
  neg_mem' := is_solvable_by_rad.neg,
  one_mem' := by { convert is_solvable_by_rad.base (1 : F), rw ring_hom.map_one },
  mul_mem' := is_solvable_by_rad.mul,
  inv_mem' := is_solvable_by_rad.inv,
  algebra_map_mem' := is_solvable_by_rad.base }

namespace solvable_by_rad

variables {F} {E} {α : E}

lemma induction (P : solvable_by_rad F E → Prop)
(base : ∀ α : F, P (algebra_map F (solvable_by_rad F E) α))
(add : ∀ α β : solvable_by_rad F E, P α → P β → P (α + β))
(neg : ∀ α : solvable_by_rad F E, P α → P (-α))
(mul : ∀ α β : solvable_by_rad F E, P α → P β → P (α * β))
(inv : ∀ α : solvable_by_rad F E, P α → P α⁻¹)
(rad : ∀ α : solvable_by_rad F E, ∀ n : ℕ, n ≠ 0 → P (α^n) → P α)
(α : solvable_by_rad F E) : P α :=
begin
  revert α,
  suffices : ∀ (α : E), is_solvable_by_rad F α → (∃ β : solvable_by_rad F E, ↑β = α ∧ P β),
  { intro α,
    obtain ⟨α₀, hα₀, Pα⟩ := this α (subtype.mem α),
    convert Pα,
    exact subtype.ext hα₀.symm },
  apply is_solvable_by_rad.rec,
  { exact λ α, ⟨algebra_map F (solvable_by_rad F E) α, rfl, base α⟩ },
  { intros α β hα hβ Pα Pβ,
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
    exact ⟨α₀ + β₀, by {rw [←hα₀, ←hβ₀], refl }, add α₀ β₀ Pα Pβ⟩ },
  { intros α hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    exact ⟨-α₀, by {rw ←hα₀, refl }, neg α₀ Pα⟩ },
  { intros α β hα hβ Pα Pβ,
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
    exact ⟨α₀ * β₀, by {rw [←hα₀, ←hβ₀], refl }, mul α₀ β₀ Pα Pβ⟩ },
  { intros α hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    exact ⟨α₀⁻¹, by {rw ←hα₀, refl }, inv α₀ Pα⟩ },
  { intros α n hn hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    refine ⟨⟨α, is_solvable_by_rad.rad α n hn hα⟩, rfl, rad _ n hn _⟩,
    convert Pα,
    exact subtype.ext (eq.trans ((solvable_by_rad F E).coe_pow _ n) hα₀.symm) }
end

theorem is_integral (α : solvable_by_rad F E) : is_integral F α :=
begin
  revert α,
  apply solvable_by_rad.induction,
  { exact λ _, is_integral_algebra_map },
  { exact λ _ _, is_integral_add },
  { exact λ _, is_integral_neg },
  { exact λ _ _, is_integral_mul },
  { exact λ α hα, subalgebra.inv_mem_of_algebraic (integral_closure F (solvable_by_rad F E))
      (show is_algebraic F ↑(⟨α, hα⟩ : integral_closure F (solvable_by_rad F E)),
        by exact (is_algebraic_iff_is_integral F).mpr hα) },
  { intros α n hn hα,
    obtain ⟨p, h1, h2⟩ := (is_algebraic_iff_is_integral F).mpr hα,
    refine (is_algebraic_iff_is_integral F).mp ⟨p.comp (X ^ n),
      ⟨λ h, h1 (leading_coeff_eq_zero.mp _), by rw [aeval_comp, aeval_X_pow, h2]⟩⟩,
    rwa [←leading_coeff_eq_zero, leading_coeff_comp, leading_coeff_X_pow, one_pow, mul_one] at h,
    rwa nat_degree_X_pow }
end

/-- The statement to be proved inductively -/
def P (α : solvable_by_rad F E) : Prop := is_solvable (minpoly F α).gal

/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
lemma induction3 {α : solvable_by_rad F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α :=
begin
  let p := minpoly F (α ^ n),
  have hp : p.comp (X ^ n) ≠ 0,
  { intro h,
    cases (comp_eq_zero_iff.mp h) with h' h',
    { exact minpoly.ne_zero (is_integral (α ^ n)) h' },
    { exact hn (by rw [←nat_degree_C _, ←h'.2, nat_degree_X_pow]) } },
  apply gal_is_solvable_of_splits,
  { exact ⟨splits_of_splits_of_dvd _ hp (splitting_field.splits (p.comp (X ^ n)))
      (minpoly.dvd F α (by rw [aeval_comp, aeval_X_pow, minpoly.aeval]))⟩ },
  { refine gal_is_solvable_tower p (p.comp (X ^ n)) _ hα _,
    { exact gal.splits_in_splitting_field_of_comp _ _ (by rwa [nat_degree_X_pow]) },
    { obtain ⟨s, hs⟩ := exists_multiset_of_splits _ (splitting_field.splits p),
      rw [map_comp, map_pow, map_X, hs, mul_comp, C_comp],
      apply gal_mul_is_solvable (gal_C_is_solvable _),
      rw prod_comp,
      apply gal_prod_is_solvable,
      intros q hq,
      rw multiset.mem_map at hq,
      obtain ⟨q, hq, rfl⟩ := hq,
      rw multiset.mem_map at hq,
      obtain ⟨q, hq, rfl⟩ := hq,
      rw [sub_comp, X_comp, C_comp],
      exact gal_X_pow_sub_C_is_solvable n q } },
end

/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
lemma induction2 {α β γ : solvable_by_rad F E} (hγ : γ ∈ F⟮α, β⟯) (hα : P α) (hβ : P β) : P γ :=
begin
  let p := (minpoly F α),
  let q := (minpoly F β),
  have hpq := polynomial.splits_of_splits_mul _ (mul_ne_zero (minpoly.ne_zero (is_integral α))
    (minpoly.ne_zero (is_integral β))) (splitting_field.splits (p * q)),
  let f : F⟮α, β⟯ →ₐ[F] (p * q).splitting_field := classical.choice (alg_hom_mk_adjoin_splits
  begin
    intros x hx,
    cases hx,
    rw hx,
    exact ⟨is_integral α, hpq.1⟩,
    cases hx,
    exact ⟨is_integral β, hpq.2⟩,
  end),
  have key : minpoly F γ = minpoly F (f ⟨γ, hγ⟩) := minpoly.unique'
    (minpoly.irreducible (is_integral γ)) begin
      suffices : aeval (⟨γ, hγ⟩ : F ⟮α, β⟯) (minpoly F γ) = 0,
      { rw [aeval_alg_hom_apply, this, alg_hom.map_zero] },
      apply (algebra_map F⟮α, β⟯ (solvable_by_rad F E)).injective,
      rw [ring_hom.map_zero, is_scalar_tower.algebra_map_aeval],
      exact minpoly.aeval F γ,
    end (minpoly.monic (is_integral γ)),
  rw [P, key],
  exact gal_is_solvable_of_splits ⟨normal.splits (splitting_field.normal _) _⟩
    (gal_mul_is_solvable hα hβ),
end

/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
lemma induction1 {α β : solvable_by_rad F E} (hβ : β ∈ F⟮α⟯) (hα : P α) : P β :=
induction2 (adjoin.mono F _ _ (ge_of_eq (set.pair_eq_singleton α)) hβ) hα hα

theorem is_solvable (α : solvable_by_rad F E) :
  is_solvable (minpoly F α).gal :=
begin
  revert α,
  apply solvable_by_rad.induction,
  { exact λ α, by { rw minpoly.eq_X_sub_C, exact gal_X_sub_C_is_solvable α } },
  { exact λ α β, induction2 (add_mem _ (subset_adjoin F _ (set.mem_insert α _))
      (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
  { exact λ α, induction1 (neg_mem _ (mem_adjoin_simple_self F α)) },
  { exact λ α β, induction2 (mul_mem _ (subset_adjoin F _ (set.mem_insert α _))
      (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
  { exact λ α, induction1 (inv_mem _ (mem_adjoin_simple_self F α)) },
  { exact λ α n, induction3 },
end

/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with an
`is_solvable_by_rad` root has solvable Galois group -/
lemma is_solvable' {α : E} {q : polynomial F} (q_irred : irreducible q)
  (q_aeval : aeval α q = 0) (hα : is_solvable_by_rad F α) :
  _root_.is_solvable q.gal :=
begin
  haveI : _root_.is_solvable (q * C q.leading_coeff⁻¹).gal := by
  { rw [minpoly.unique'' q_irred q_aeval,
        ←show minpoly F (⟨α, hα⟩ : solvable_by_rad F E) = minpoly F α,
        from minpoly.eq_of_algebra_map_eq (ring_hom.injective _) (is_integral ⟨α, hα⟩) rfl],
    exact is_solvable ⟨α, hα⟩ },
  refine solvable_of_surjective (gal.restrict_dvd_surjective ⟨C q.leading_coeff⁻¹, rfl⟩ _),
  rw [mul_ne_zero_iff, ne, ne, C_eq_zero, inv_eq_zero],
  exact ⟨q_irred.ne_zero, leading_coeff_ne_zero.mpr q_irred.ne_zero⟩,
end

end solvable_by_rad

end abel_ruffini
