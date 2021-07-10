/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.algebraic
import ring_theory.localization

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.

## Implementation notes

The proofs of the `comap_ne_bot` and `comap_lt_comap` families use an approach
specific for their situation: we construct an element in `I.comap f` from the
coefficients of a minimal polynomial.
Once mathlib has more material on the localization at a prime ideal, the results
can be proven using more general going-up/going-down theory.
-/

variables {R : Type*} [comm_ring R]

namespace ideal

open polynomial
open submodule

section comm_ring
variables {S : Type*} [comm_ring S] {f : R →+* S} {I J : ideal S}

lemma coeff_zero_mem_comap_of_root_mem_of_eval_mem {r : S} (hr : r ∈ I) {p : polynomial R}
  (hp : p.eval₂ f r ∈ I) : p.coeff 0 ∈ I.comap f :=
begin
  rw [←p.div_X_mul_X_add, eval₂_add, eval₂_C, eval₂_mul, eval₂_X] at hp,
  refine mem_comap.mpr ((I.add_mem_iff_right _).mp hp),
  exact I.mul_mem_left _ hr
end

lemma coeff_zero_mem_comap_of_root_mem {r : S} (hr : r ∈ I) {p : polynomial R}
  (hp : p.eval₂ f r = 0) : p.coeff 0 ∈ I.comap f :=
coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)

lemma exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {r : S}
  (r_non_zero_divisor : ∀ {x}, x * r = 0 → x = 0) (hr : r ∈ I)
  {p : polynomial R} : ∀ (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0),
  ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f :=
begin
  refine p.rec_on_horner _ _ _,
  { intro h, contradiction },
  { intros p a coeff_eq_zero a_ne_zero ih p_ne_zero hp,
    refine ⟨0, _, coeff_zero_mem_comap_of_root_mem hr hp⟩,
    simp [coeff_eq_zero, a_ne_zero] },
  { intros p p_nonzero ih mul_nonzero hp,
    rw [eval₂_mul, eval₂_X] at hp,
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (r_non_zero_divisor hp),
    refine ⟨i + 1, _, _⟩; simp [hi, mem] }
end

/-- Let `P` be an ideal in `R[x]`.  The map
`R[x]/P → (R / (P ∩ R))[x] / (P / (P ∩ R))`
is injective.
-/
lemma injective_quotient_le_comap_map (P : ideal (polynomial R)) :
  function.injective ((map (map_ring_hom (quotient.mk (P.comap C))) P).quotient_map
    (map_ring_hom (quotient.mk (P.comap C))) le_comap_map) :=
begin
  refine quotient_map_injective' (le_of_eq _),
  rw comap_map_of_surjective
    (map_ring_hom (quotient.mk (P.comap C))) (map_surjective _ quotient.mk_surjective),
  refine le_antisymm (sup_le le_rfl _) (le_sup_of_le_left le_rfl),
  refine λ p hp, polynomial_mem_ideal_of_coeff_mem_ideal P p (λ n, quotient.eq_zero_iff_mem.mp _),
  simpa only [coeff_map, coe_map_ring_hom] using ext_iff.mp (ideal.mem_bot.mp (mem_comap.mp hp)) n,
end

/--
The identity in this lemma asserts that the "obvious" square
```
    R    → (R / (P ∩ R))
    ↓          ↓
R[x] / P → (R / (P ∩ R))[x] / (P / (P ∩ R))
```
commutes.  It is used, for instance, in the proof of `quotient_mk_comp_C_is_integral_of_jacobson`,
in the file `ring_theory/jacobson`.
-/
lemma quotient_mk_maps_eq (P : ideal (polynomial R)) :
  ((quotient.mk (map (map_ring_hom (quotient.mk (P.comap C))) P)).comp C).comp
    (quotient.mk (P.comap C)) =
  ((map (map_ring_hom (quotient.mk (P.comap C))) P).quotient_map
    (map_ring_hom (quotient.mk (P.comap C))) le_comap_map).comp ((quotient.mk P).comp C) :=
begin
  refine ring_hom.ext (λ x, _),
  repeat { rw [ring_hom.coe_comp, function.comp_app] },
  rw [quotient_map_mk, coe_map_ring_hom, map_C],
end

/--
This technical lemma asserts the existence of a polynomial `p` in an ideal `P ⊂ R[x]`
that is non-zero in the quotient `R / (P ∩ R) [x]`.  The assumptions are equivalent to
`P ≠ 0` and `P ∩ R = (0)`.
-/
lemma exists_nonzero_mem_of_ne_bot {P : ideal (polynomial R)}
  (Pb : P ≠ ⊥) (hP : ∀ (x : R), C x ∈ P → x = 0) :
  ∃ p : polynomial R, p ∈ P ∧ (polynomial.map (quotient.mk (P.comap C)) p) ≠ 0 :=
begin
  obtain ⟨m, hm⟩ := submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr Pb),
  refine ⟨m, submodule.coe_mem m, λ pp0, hm (submodule.coe_eq_zero.mp _)⟩,
  refine (is_add_group_hom.injective_iff (polynomial.map (quotient.mk (P.comap C)))).mp _ _ pp0,
  refine map_injective _ ((quotient.mk (P.comap C)).injective_iff_ker_eq_bot.mpr _),
  rw [mk_ker],
  exact (submodule.eq_bot_iff _).mpr (λ x hx, hP x (mem_comap.mp hx)),
end

end comm_ring

section integral_domain
variables {S : Type*} [integral_domain S] {f : R →+* S} {I J : ideal S}

lemma exists_coeff_ne_zero_mem_comap_of_root_mem {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I)
  {p : polynomial R} : ∀ (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0),
  ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f :=
exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
  (λ _ h, or.resolve_right (mul_eq_zero.mp h) r_ne_zero) hr

lemma exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff
  [is_prime I] (hIJ : I ≤ J) {r : S} (hr : r ∈ (J : set S) \ I)
  {p : polynomial R} (p_ne_zero : p.map (quotient.mk (I.comap f)) ≠ 0) (hpI : p.eval₂ f r ∈ I) :
  ∃ i, p.coeff i ∈ (J.comap f : set R) \ (I.comap f) :=
begin
  obtain ⟨hrJ, hrI⟩ := hr,
  have rbar_ne_zero : quotient.mk I r ≠ 0 := mt (quotient.mk_eq_zero I).mp hrI,
  have rbar_mem_J : quotient.mk I r ∈ J.map (quotient.mk I) := mem_map_of_mem _ hrJ,
  have quotient_f : ∀ x ∈ I.comap f, (quotient.mk I).comp f x = 0,
  { simp [quotient.eq_zero_iff_mem] },
  have rbar_root : (p.map (quotient.mk (I.comap f))).eval₂
    (quotient.lift (I.comap f) _ quotient_f)
    (quotient.mk I r) = 0,
  { convert quotient.eq_zero_iff_mem.mpr hpI,
    exact trans (eval₂_map _ _ _) (hom_eval₂ p f (quotient.mk I) r).symm },
  obtain ⟨i, ne_zero, mem⟩ :=
    exists_coeff_ne_zero_mem_comap_of_root_mem rbar_ne_zero rbar_mem_J p_ne_zero rbar_root,
  rw coeff_map at ne_zero mem,
  refine ⟨i, (mem_quotient_iff_mem hIJ).mp _, mt _ ne_zero⟩,
  { simpa using mem },
  simp [quotient.eq_zero_iff_mem],
end

lemma comap_ne_bot_of_root_mem {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I)
  {p : polynomial R} (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0) :
  I.comap f ≠ ⊥ :=
λ h, let ⟨i, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp in
absurd (mem_bot.mp (eq_bot_iff.mp h mem)) hi

lemma comap_lt_comap_of_root_mem_sdiff [I.is_prime] (hIJ : I ≤ J)
  {r : S} (hr : r ∈ (J : set S) \ I)
  {p : polynomial R} (p_ne_zero : p.map (quotient.mk (I.comap f)) ≠ 0) (hp : p.eval₂ f r ∈ I) :
  I.comap f < J.comap f :=
let ⟨i, hJ, hI⟩ := exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff hIJ hr p_ne_zero hp
in set_like.lt_iff_le_and_exists.mpr ⟨comap_mono hIJ, p.coeff i, hJ, hI⟩

variables [algebra R S]

lemma comap_ne_bot_of_algebraic_mem {x : S}
  (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_algebraic R x) : I.comap (algebra_map R S) ≠ ⊥ :=
let ⟨p, p_ne_zero, hp⟩ := hx
in comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp

lemma comap_ne_bot_of_integral_mem [nontrivial R] {x : S}
  (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_integral R x) : I.comap (algebra_map R S) ≠ ⊥ :=
comap_ne_bot_of_algebraic_mem x_ne_zero x_mem (hx.is_algebraic R)

lemma eq_bot_of_comap_eq_bot [nontrivial R] (hRS : algebra.is_integral R S)
  (hI : I.comap (algebra_map R S) = ⊥) : I = ⊥ :=
begin
  refine eq_bot_iff.2 (λ x hx, _),
  by_cases hx0 : x = 0,
  { exact hx0.symm ▸ ideal.zero_mem ⊥ },
  { exact absurd hI (comap_ne_bot_of_integral_mem hx0 hx (hRS x)) }
end

lemma mem_of_one_mem (h : (1 : S) ∈ I) (x) : x ∈ I :=
(I.eq_top_iff_one.mpr h).symm ▸ mem_top

lemma comap_lt_comap_of_integral_mem_sdiff [hI : I.is_prime] (hIJ : I ≤ J)
  {x : S} (mem : x ∈ (J : set S) \ I) (integral : is_integral R x) :
  I.comap (algebra_map R S) < J.comap (algebra_map _ _) :=
begin
  obtain ⟨p, p_monic, hpx⟩ := integral,
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem _ _,
  swap,
  { apply map_monic_ne_zero p_monic,
    apply quotient.nontrivial,
    apply mt comap_eq_top_iff.mp,
    apply hI.1 },
  convert I.zero_mem
end

lemma is_maximal_of_is_integral_of_is_maximal_comap
  (hRS : algebra.is_integral R S) (I : ideal S) [I.is_prime]
  (hI : is_maximal (I.comap (algebra_map R S))) : is_maximal I :=
⟨⟨mt comap_eq_top_iff.mpr hI.1.1,
  λ J I_lt_J, let ⟨I_le_J, x, hxJ, hxI⟩ := set_like.lt_iff_le_and_exists.mp I_lt_J in
  comap_eq_top_iff.1 $ hI.1.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (hRS x))⟩⟩

lemma is_maximal_of_is_integral_of_is_maximal_comap' {R S : Type*} [comm_ring R] [integral_domain S]
  (f : R →+* S) (hf : f.is_integral) (I : ideal S) [hI' : I.is_prime]
  (hI : is_maximal (I.comap f)) : is_maximal I :=
@is_maximal_of_is_integral_of_is_maximal_comap R _ S _ f.to_algebra hf I hI' hI

lemma is_maximal_comap_of_is_integral_of_is_maximal (hRS : algebra.is_integral R S)
  (I : ideal S) [hI : I.is_maximal] : is_maximal (I.comap (algebra_map R S)) :=
begin
  refine quotient.maximal_of_is_field _ _,
  haveI : is_prime (I.comap (algebra_map R S)) := comap_is_prime _ _,
  exact is_field_of_is_integral_of_is_field (is_integral_quotient_of_is_integral hRS)
    algebra_map_quotient_injective (by rwa ← quotient.maximal_ideal_iff_is_field_quotient),
end

lemma is_maximal_comap_of_is_integral_of_is_maximal' {R S : Type*} [comm_ring R] [integral_domain S]
  (f : R →+* S) (hf : f.is_integral) (I : ideal S) (hI : I.is_maximal) : is_maximal (I.comap f) :=
@is_maximal_comap_of_is_integral_of_is_maximal R _ S _ f.to_algebra hf I hI

lemma integral_closure.comap_ne_bot [nontrivial R] {I : ideal (integral_closure R S)}
  (I_ne_bot : I ≠ ⊥) : I.comap (algebra_map R (integral_closure R S)) ≠ ⊥ :=
let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot in
comap_ne_bot_of_integral_mem x_ne_zero x_mem (integral_closure.is_integral x)

lemma integral_closure.eq_bot_of_comap_eq_bot [nontrivial R] {I : ideal (integral_closure R S)} :
  I.comap (algebra_map R (integral_closure R S)) = ⊥ → I = ⊥ :=
imp_of_not_imp_not _ _ integral_closure.comap_ne_bot

lemma integral_closure.comap_lt_comap {I J : ideal (integral_closure R S)} [I.is_prime]
  (I_lt_J : I < J) :
  I.comap (algebra_map R (integral_closure R S)) < J.comap (algebra_map _ _) :=
let ⟨I_le_J, x, hxJ, hxI⟩ := set_like.lt_iff_le_and_exists.mp I_lt_J in
comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (integral_closure.is_integral x)

lemma integral_closure.is_maximal_of_is_maximal_comap
  (I : ideal (integral_closure R S)) [I.is_prime]
  (hI : is_maximal (I.comap (algebra_map R (integral_closure R S)))) : is_maximal I :=
is_maximal_of_is_integral_of_is_maximal_comap (λ x, integral_closure.is_integral x) I hI

/-- `comap (algebra_map R S)` is a surjection from the prime spec of `R` to prime spec of `S`.
`hP : (algebra_map R S).ker ≤ P` is a slight generalization of the extension being injective -/
lemma exists_ideal_over_prime_of_is_integral' (H : algebra.is_integral R S)
  (P : ideal R) [is_prime P] (hP : (algebra_map R S).ker ≤ P) :
  ∃ (Q : ideal S), is_prime Q ∧ Q.comap (algebra_map R S) = P :=
begin
  have hP0 : (0 : S) ∉ algebra.algebra_map_submonoid S P.prime_compl,
  { rintro ⟨x, ⟨hx, x0⟩⟩,
    exact absurd (hP x0) hx },
  let Rₚ := localization P.prime_compl,
  let Sₚ := localization (algebra.algebra_map_submonoid S P.prime_compl),
  letI : integral_domain (localization (algebra.algebra_map_submonoid S P.prime_compl)) :=
    is_localization.integral_domain_localization (le_non_zero_divisors_of_domain hP0),
  obtain ⟨Qₚ : ideal Sₚ, Qₚ_maximal⟩ := exists_maximal Sₚ,
  haveI Qₚ_max : is_maximal (comap _ Qₚ) := @is_maximal_comap_of_is_integral_of_is_maximal Rₚ _ Sₚ _
    (localization_algebra P.prime_compl S)
    (is_integral_localization H) _ Qₚ_maximal,
  refine ⟨comap (algebra_map S Sₚ) Qₚ, ⟨comap_is_prime _ Qₚ, _⟩⟩,
  convert localization.at_prime.comap_maximal_ideal,
  rw [comap_comap, ← local_ring.eq_maximal_ideal Qₚ_max, ← is_localization.map_comp _],
  refl
end

/-- More general going-up theorem than `exists_ideal_over_prime_of_is_integral'`.
TODO: Version of going-up theorem with arbitrary length chains (by induction on this)?
  Not sure how best to write an ascending chain in Lean -/
theorem exists_ideal_over_prime_of_is_integral (H : algebra.is_integral R S)
  (P : ideal R) [is_prime P] (I : ideal S) [is_prime I] (hIP : I.comap (algebra_map R S) ≤ P) :
  ∃ Q ≥ I, is_prime Q ∧ Q.comap (algebra_map R S) = P :=
begin
  obtain ⟨Q' : ideal I.quotient, ⟨Q'_prime, hQ'⟩⟩ := @exists_ideal_over_prime_of_is_integral'
    (I.comap (algebra_map R S)).quotient _ I.quotient _
    ideal.quotient_algebra
    (is_integral_quotient_of_is_integral H)
    (map (quotient.mk (I.comap (algebra_map R S))) P)
    (map_is_prime_of_surjective quotient.mk_surjective (by simp [hIP]))
    (le_trans
      (le_of_eq ((ring_hom.injective_iff_ker_eq_bot _).1 algebra_map_quotient_injective))
      bot_le),
  haveI := Q'_prime,
  refine ⟨Q'.comap _, le_trans (le_of_eq mk_ker.symm) (ker_le_comap _), ⟨comap_is_prime _ Q', _⟩⟩,
  rw comap_comap,
  refine trans _ (trans (congr_arg (comap (quotient.mk (comap (algebra_map R S) I))) hQ') _),
  { simpa [comap_comap] },
  { refine trans (comap_map_of_surjective _ quotient.mk_surjective _) (sup_eq_left.2 _),
    simpa [← ring_hom.ker_eq_comap_bot] using hIP},
end

/-- `comap (algebra_map R S)` is a surjection from the max spec of `S` to max spec of `R`.
`hP : (algebra_map R S).ker ≤ P` is a slight generalization of the extension being injective -/
lemma exists_ideal_over_maximal_of_is_integral (H : algebra.is_integral R S)
  (P : ideal R) [P_max : is_maximal P] (hP : (algebra_map R S).ker ≤ P) :
  ∃ (Q : ideal S), is_maximal Q ∧ Q.comap (algebra_map R S) = P :=
begin
  obtain ⟨Q, ⟨Q_prime, hQ⟩⟩ := exists_ideal_over_prime_of_is_integral' H P hP,
  haveI : Q.is_prime := Q_prime,
  exact ⟨Q, is_maximal_of_is_integral_of_is_maximal_comap H _ (hQ.symm ▸ P_max), hQ⟩,
end

end integral_domain

end ideal
