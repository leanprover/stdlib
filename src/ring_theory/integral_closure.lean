/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.adjoin.basic
import ring_theory.polynomial.scale_roots
import ring_theory.polynomial.tower

/-!
# Integral closure of a subring.

If A is an R-algebra then `a : A` is integral over R if it is a root of a monic polynomial
with coefficients in R. Enough theory is developed to prove that integral elements
form a sub-R-algebra of A.

## Main definitions

Let `R` be a `comm_ring` and let `A` be an R-algebra.

* `ring_hom.is_integral_elem (f : R →+* A) (x : A)` : `x` is integral with respect to the map `f`,

* `is_integral (x : A)`  : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                           coefficients in `R`.
* `integral_closure R A` : the integral closure of `R` in `A`, regarded as a sub-`R`-algebra of `A`.
-/

open_locale classical
open_locale big_operators
open polynomial submodule

section ring
variables {R S A : Type*}
variables [comm_ring R] [ring A] [ring S] (f : R →+* S)

/-- An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : polynomial R` evaluated under `f` -/
def ring_hom.is_integral_elem (f : R →+* A) (x : A) :=
∃ p : polynomial R, monic p ∧ eval₂ f x p = 0

/-- A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f` -/
def ring_hom.is_integral (f : R →+* A) :=
∀ x : A, f.is_integral_elem x

variables [algebra R A] (R)

/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : polynomial R`.
Equivalently, the element is integral over `R` with respect to the induced `algebra_map` -/
def is_integral (x : A) : Prop :=
(algebra_map R A).is_integral_elem x

variable (A)

/-- An algebra is integral if every element of the extension is integral over the base ring -/
def algebra.is_integral : Prop :=
(algebra_map R A).is_integral

variables {R A}

lemma ring_hom.is_integral_map {x : R} : f.is_integral_elem (f x) :=
⟨X - C x, monic_X_sub_C _, by simp⟩

theorem is_integral_algebra_map {x : R} : is_integral R (algebra_map R A x) :=
(algebra_map R A).is_integral_map

theorem is_integral_of_noetherian (H : is_noetherian R A) (x : A) :
  is_integral R x :=
begin
  let leval : @linear_map R (polynomial R) A _ _ _ _ _ := (aeval x).to_linear_map,
  let D : ℕ → submodule R A := λ n, (degree_le R n).map leval,
  let M := well_founded.min (is_noetherian_iff_well_founded.1 H)
    (set.range D) ⟨_, ⟨0, rfl⟩⟩,
  have HM : M ∈ set.range D := well_founded.min_mem _ _ _,
  cases HM with N HN,
  have HM : ¬M < D (N+1) := well_founded.not_lt_min
    (is_noetherian_iff_well_founded.1 H) (set.range D) _ ⟨N+1, rfl⟩,
  rw ← HN at HM,
  have HN2 : D (N+1) ≤ D N := classical.by_contradiction (λ H, HM
    (lt_of_le_not_le (map_mono (degree_le_mono
      (with_bot.coe_le_coe.2 (nat.le_succ N)))) H)),
  have HN3 : leval (X^(N+1)) ∈ D N,
  { exact HN2 (mem_map_of_mem (mem_degree_le.2 (degree_X_pow_le _))) },
  rcases HN3 with ⟨p, hdp, hpe⟩,
  refine ⟨X^(N+1) - p, monic_X_pow_sub (mem_degree_le.1 hdp), _⟩,
  show leval (X ^ (N + 1) - p) = 0,
  rw [linear_map.map_sub, hpe, sub_self]
end

theorem is_integral_of_submodule_noetherian (S : subalgebra R A)
  (H : is_noetherian R S.to_submodule) (x : A) (hx : x ∈ S) :
  is_integral R x :=
begin
  suffices : is_integral R (show S, from ⟨x, hx⟩),
  { rcases this with ⟨p, hpm, hpx⟩,
    replace hpx := congr_arg S.val hpx,
    refine ⟨p, hpm, eq.trans _ hpx⟩,
    simp only [aeval_def, eval₂, sum_def],
    rw S.val.map_sum,
    refine finset.sum_congr rfl (λ n hn, _),
    rw [S.val.map_mul, S.val.map_pow, S.val.commutes, S.val_apply, subtype.coe_mk], },
  refine is_integral_of_noetherian H ⟨x, hx⟩
end

end ring

section
variables {R A B S : Type*}
variables [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring S]
variables [algebra R A] [algebra R B] (f : R →+* S)

theorem is_integral_alg_hom (f : A →ₐ[R] B) {x : A} (hx : is_integral R x) : is_integral R (f x) :=
let ⟨p, hp, hpx⟩ :=
hx in ⟨p, hp, by rw [← aeval_def, aeval_alg_hom_apply, aeval_def, hpx, f.map_zero]⟩

theorem is_integral_of_is_scalar_tower [algebra A B] [is_scalar_tower R A B]
  (x : B) (hx : is_integral R x) : is_integral A x :=
let ⟨p, hp, hpx⟩ := hx in
⟨p.map $ algebra_map R A, monic_map _ hp,
  by rw [← aeval_def, ← is_scalar_tower.aeval_apply, aeval_def, hpx]⟩

section
local attribute [instance] subset.comm_ring algebra.of_is_subring

theorem is_integral_of_subring {x : A} (T : set R) [is_subring T]
  (hx : is_integral T x) : is_integral R x :=
is_integral_of_is_scalar_tower x hx

lemma is_integral_algebra_map_iff [algebra A B] [is_scalar_tower R A B]
  {x : A} (hAB : function.injective (algebra_map A B)) :
  is_integral R (algebra_map A B x) ↔ is_integral R x :=
begin
  split; rintros ⟨f, hf, hx⟩; use [f, hf],
  { exact is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero R A B hAB hx },
  { rw [is_scalar_tower.algebra_map_eq R A B, ← hom_eval₂, hx, ring_hom.map_zero] }
end

theorem is_integral_iff_is_integral_closure_finite {r : A} :
  is_integral R r ↔ ∃ s : set R, s.finite ∧ is_integral (ring.closure s) r :=
begin
  split; intro hr,
  { rcases hr with ⟨p, hmp, hpr⟩,
    refine ⟨_, set.finite_mem_finset _, p.restriction, monic_restriction.2 hmp, _⟩,
    erw [← aeval_def, is_scalar_tower.aeval_apply _ R, map_restriction, aeval_def, hpr] },
  rcases hr with ⟨s, hs, hsr⟩,
  exact is_integral_of_subring _ hsr
end

end

theorem fg_adjoin_singleton_of_integral (x : A) (hx : is_integral R x) :
  (algebra.adjoin R ({x} : set A)).to_submodule.fg :=
begin
  rcases hx with ⟨f, hfm, hfx⟩,
  existsi finset.image ((^) x) (finset.range (nat_degree f + 1)),
  apply le_antisymm,
  { rw span_le, intros s hs, rw finset.mem_coe at hs,
    rcases finset.mem_image.1 hs with ⟨k, hk, rfl⟩, clear hk,
    exact is_submonoid.pow_mem (algebra.subset_adjoin (set.mem_singleton _)) },
  intros r hr, change r ∈ algebra.adjoin R ({x} : set A) at hr,
  rw algebra.adjoin_singleton_eq_range at hr,
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩,
  rw ← mod_by_monic_add_div p hfm,
  rw ← aeval_def at hfx,
  rw [alg_hom.map_add, alg_hom.map_mul, hfx, zero_mul, add_zero],
  have : degree (p %ₘ f) ≤ degree f := degree_mod_by_monic_le p hfm,
  generalize_hyp : p %ₘ f = q at this ⊢,
  rw [← sum_C_mul_X_eq q, aeval_def, eval₂_sum, sum_def],
  refine sum_mem _ (λ k hkq, _),
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← algebra.smul_def],
  refine smul_mem _ _ (subset_span _),
  rw finset.mem_coe, refine finset.mem_image.2 ⟨_, _, rfl⟩,
  rw [finset.mem_range, nat.lt_succ_iff], refine le_of_not_lt (λ hk, _),
  rw [degree_le_iff_coeff_zero] at this,
  rw [mem_support_iff] at hkq, apply hkq, apply this,
  exact lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 hk)
end

theorem fg_adjoin_of_finite {s : set A} (hfs : s.finite)
  (his : ∀ x ∈ s, is_integral R x) : (algebra.adjoin R s).to_submodule.fg :=
set.finite.induction_on hfs (λ _, ⟨{1}, submodule.ext $ λ x,
  by { erw [algebra.adjoin_empty, finset.coe_singleton, ← one_eq_span, one_eq_range,
            linear_map.mem_range, algebra.mem_bot], refl }⟩)
(λ a s has hs ih his, by rw [← set.union_singleton, algebra.adjoin_union_coe_submodule]; exact
  fg_mul _ _ (ih $ λ i hi, his i $ set.mem_insert_of_mem a hi)
    (fg_adjoin_singleton_of_integral _ $ his a $ set.mem_insert a s)) his

theorem is_integral_of_mem_of_fg (S : subalgebra R A)
  (HS : S.to_submodule.fg) (x : A) (hx : x ∈ S) : is_integral R x :=
begin
  cases HS with y hy,
  obtain ⟨lx, hlx1, hlx2⟩ :
    ∃ (l : A →₀ R) (H : l ∈ finsupp.supported R R ↑y), (finsupp.total A A R id) l = x,
  { rwa [←(@finsupp.mem_span_image_iff_total A A R _ _ _ id ↑y x), set.image_id ↑y, hy] },
  have hyS : ∀ {p}, p ∈ y → p ∈ S := λ p hp, show p ∈ S.to_submodule,
    by { rw ← hy, exact subset_span hp },
  have : ∀ (jk : (↑(y.product y) : set (A × A))), jk.1.1 * jk.1.2 ∈ S.to_submodule :=
    λ jk, S.mul_mem (hyS (finset.mem_product.1 jk.2).1) (hyS (finset.mem_product.1 jk.2).2),
  rw [← hy, ← set.image_id ↑y] at this, simp only [finsupp.mem_span_image_iff_total] at this,
  choose ly hly1 hly2,
  let S₀ : set R := ring.closure ↑(lx.frange ∪ finset.bUnion finset.univ (finsupp.frange ∘ ly)),
  refine is_integral_of_subring S₀ _,
  letI : comm_ring S₀ := @subtype.comm_ring _ _ _ ring.closure.is_subring,
  letI : algebra S₀ A := algebra.of_is_subring _,
  have :
    span S₀ (insert 1 ↑y : set A) * span S₀ (insert 1 ↑y : set A) ≤ span S₀ (insert 1 ↑y : set A),
  { rw span_mul_span, refine span_le.2 (λ z hz, _),
    rcases set.mem_mul.1 hz with ⟨p, q, rfl | hp, hq, rfl⟩,
    { rw one_mul, exact subset_span hq },
    rcases hq with rfl | hq,
    { rw mul_one, exact subset_span (or.inr hp) },
    erw ← hly2 ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩,
    rw [finsupp.total_apply, finsupp.sum],
    refine (span S₀ (insert 1 ↑y : set A)).sum_mem (λ t ht, _),
    have : ly ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩ t ∈ S₀ :=
    ring.subset_closure (finset.mem_union_right _ $ finset.mem_bUnion.2
      ⟨⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩, finset.mem_univ _,
        finsupp.mem_frange.2 ⟨finsupp.mem_support_iff.1 ht, _, rfl⟩⟩),
    change (⟨_, this⟩ : S₀) • t ∈ _, exact smul_mem _ _ (subset_span $ or.inr $ hly1 _ ht) },
  haveI : is_subring (span S₀ (insert 1 ↑y : set A) : set A) :=
  { one_mem := subset_span $ or.inl rfl,
    mul_mem := λ p q hp hq, this $ mul_mem_mul hp hq,
    zero_mem := (span S₀ (insert 1 ↑y : set A)).zero_mem,
    add_mem := λ _ _, (span S₀ (insert 1 ↑y : set A)).add_mem,
    neg_mem := λ _, (span S₀ (insert 1 ↑y : set A)).neg_mem },
  have : span S₀ (insert 1 ↑y : set A) = (algebra.adjoin S₀ (↑y : set A)).to_submodule,
  { refine le_antisymm (span_le.2 $ set.insert_subset.2
        ⟨(algebra.adjoin S₀ ↑y).one_mem, algebra.subset_adjoin⟩) (λ z hz, _),
    rw [subalgebra.mem_to_submodule, algebra.mem_adjoin_iff] at hz, rw ← set_like.mem_coe,
    refine ring.closure_subset (set.union_subset (set.range_subset_iff.2 $ λ t, _)
      (λ t ht, subset_span $ or.inr ht)) hz,
    rw algebra.algebra_map_eq_smul_one,
    exact smul_mem (span S₀ (insert 1 ↑y : set A)) _ (subset_span $ or.inl rfl) },
  haveI : is_noetherian_ring ↥S₀ := is_noetherian_ring_closure _ (finset.finite_to_set _),
  refine is_integral_of_submodule_noetherian (algebra.adjoin S₀ ↑y)
    (is_noetherian_of_fg_of_noetherian _ ⟨insert 1 y, by rw [finset.coe_insert, this]⟩) _ _,
  rw [← hlx2, finsupp.total_apply, finsupp.sum], refine subalgebra.sum_mem _ (λ r hr, _),
  have : lx r ∈ S₀ := ring.subset_closure (finset.mem_union_left _ (finset.mem_image_of_mem _ hr)),
  change (⟨_, this⟩ : S₀) • r ∈ _,
  rw finsupp.mem_supported at hlx1,
  exact subalgebra.smul_mem _ (algebra.subset_adjoin $ hlx1 hr) _
end

lemma ring_hom.is_integral_of_mem_closure {x y z : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y)
  (hz : z ∈ ring.closure ({x, y} : set S)) :
  f.is_integral_elem z :=
begin
  letI : algebra R S := f.to_algebra,
  have := fg_mul _ _ (fg_adjoin_singleton_of_integral x hx) (fg_adjoin_singleton_of_integral y hy),
  rw [← algebra.adjoin_union_coe_submodule, set.singleton_union] at this,
  exact is_integral_of_mem_of_fg (algebra.adjoin R {x, y}) this z
    (algebra.mem_adjoin_iff.2  $ ring.closure_mono (set.subset_union_right _ _) hz),
end

theorem is_integral_of_mem_closure {x y z : A}
  (hx : is_integral R x) (hy : is_integral R y)
  (hz : z ∈ ring.closure ({x, y} : set A)) :
  is_integral R z :=
(algebra_map R A).is_integral_of_mem_closure hx hy hz

lemma ring_hom.is_integral_zero : f.is_integral_elem 0 :=
f.map_zero ▸ f.is_integral_map

theorem is_integral_zero : is_integral R (0:A) :=
(algebra_map R A).is_integral_zero

lemma ring_hom.is_integral_one : f.is_integral_elem 1 :=
f.map_one ▸ f.is_integral_map

theorem is_integral_one : is_integral R (1:A) :=
(algebra_map R A).is_integral_one

lemma ring_hom.is_integral_add {x y : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) :
  f.is_integral_elem (x + y) :=
f.is_integral_of_mem_closure hx hy (is_add_submonoid.add_mem
  (ring.subset_closure (or.inl rfl)) (ring.subset_closure (or.inr rfl)))

theorem is_integral_add {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) :
  is_integral R (x + y) :=
(algebra_map R A).is_integral_add hx hy

lemma ring_hom.is_integral_neg {x : S}
  (hx : f.is_integral_elem x) : f.is_integral_elem (-x) :=
f.is_integral_of_mem_closure hx hx (is_add_subgroup.neg_mem
  (ring.subset_closure (or.inl rfl)))

theorem is_integral_neg {x : A}
  (hx : is_integral R x) : is_integral R (-x) :=
(algebra_map R A).is_integral_neg hx

lemma ring_hom.is_integral_sub {x y : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) : f.is_integral_elem (x - y) :=
by simpa only [sub_eq_add_neg] using f.is_integral_add hx (f.is_integral_neg hy)

theorem is_integral_sub {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x - y) :=
(algebra_map R A).is_integral_sub hx hy

lemma ring_hom.is_integral_mul {x y : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) : f.is_integral_elem (x * y) :=
f.is_integral_of_mem_closure hx hy (is_submonoid.mul_mem
  (ring.subset_closure (or.inl rfl)) (ring.subset_closure (or.inr rfl)))

theorem is_integral_mul {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x * y) :=
(algebra_map R A).is_integral_mul hx hy

variables (R A)

/-- The integral closure of R in an R-algebra A. -/
def integral_closure : subalgebra R A :=
{ carrier := { r | is_integral R r },
  zero_mem' := is_integral_zero,
  one_mem' := is_integral_one,
  add_mem' := λ _ _, is_integral_add,
  mul_mem' := λ _ _, is_integral_mul,
  algebra_map_mem' := λ x, is_integral_algebra_map }

theorem mem_integral_closure_iff_mem_fg {r : A} :
  r ∈ integral_closure R A ↔ ∃ M : subalgebra R A, M.to_submodule.fg ∧ r ∈ M :=
⟨λ hr, ⟨algebra.adjoin R {r}, fg_adjoin_singleton_of_integral _ hr, algebra.subset_adjoin rfl⟩,
λ ⟨M, Hf, hrM⟩, is_integral_of_mem_of_fg M Hf _ hrM⟩

variables {R} {A}

/-- Mapping an integral closure along an `alg_equiv` gives the integral closure. -/
lemma integral_closure_map_alg_equiv (f : A ≃ₐ[R] B) :
  (integral_closure R A).map (f : A →ₐ[R] B) = integral_closure R B :=
begin
  ext y,
  rw subalgebra.mem_map,
  split,
  { rintros ⟨x, hx, rfl⟩,
    exact is_integral_alg_hom f hx },
  { intro hy,
    use [f.symm y, is_integral_alg_hom (f.symm : B →ₐ[R] A) hy],
    simp }
end

lemma integral_closure.is_integral (x : integral_closure R A) : is_integral R x :=
let ⟨p, hpm, hpx⟩ := x.2 in ⟨p, hpm, subtype.eq $
by rwa [← aeval_def, subtype.val_eq_coe, ← subalgebra.val_apply, aeval_alg_hom_apply] at hpx⟩

lemma ring_hom.is_integral_of_is_integral_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
  (hx : f.is_integral_elem (x * y)) : f.is_integral_elem x :=
begin
  obtain ⟨p, ⟨p_monic, hp⟩⟩ := hx,
  refine ⟨scale_roots p r, ⟨(monic_scale_roots_iff r).2 p_monic, _⟩⟩,
  convert scale_roots_eval₂_eq_zero f hp,
  rw [mul_comm x y, ← mul_assoc, hr, one_mul],
end

theorem is_integral_of_is_integral_mul_unit {x y : A} {r : R} (hr : algebra_map R A r * y = 1)
  (hx : is_integral R (x * y)) : is_integral R x :=
(algebra_map R A).is_integral_of_is_integral_mul_unit x y r hr hx

/-- Generalization of `is_integral_of_mem_closure` bootstrapped up from that lemma -/
lemma is_integral_of_mem_closure' (G : set A) (hG : ∀ x ∈ G, is_integral R x) :
  ∀ x ∈ (subring.closure G), is_integral R x :=
λ x hx, subring.closure_induction hx hG is_integral_zero is_integral_one
  (λ _ _, is_integral_add) (λ _, is_integral_neg) (λ _ _, is_integral_mul)

lemma is_integral_of_mem_closure'' {S : Type*} [comm_ring S] {f : R →+* S} (G : set S)
  (hG : ∀ x ∈ G, f.is_integral_elem x) : ∀ x ∈ (subring.closure G), f.is_integral_elem x :=
λ x hx, @is_integral_of_mem_closure' R S _ _ f.to_algebra G hG x hx

end

section algebra
open algebra
variables {R A B S T : Type*}
variables [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring S] [comm_ring T]
variables [algebra A B] [algebra R B] (f : R →+* S) (g : S →+* T)

lemma is_integral_trans_aux (x : B) {p : polynomial A} (pmonic : monic p) (hp : aeval x p = 0) :
  is_integral (adjoin R (↑(p.map $ algebra_map A B).frange : set B)) x :=
begin
  generalize hS : (↑(p.map $ algebra_map A B).frange : set B) = S,
  have coeffs_mem : ∀ i, (p.map $ algebra_map A B).coeff i ∈ adjoin R S,
  { intro i, by_cases hi : (p.map $ algebra_map A B).coeff i = 0,
    { rw hi, exact subalgebra.zero_mem _ },
    rw ← hS,
    exact subset_adjoin (coeff_mem_frange _ _ hi) },
  obtain ⟨q, hq⟩ : ∃ q : polynomial (adjoin R S), q.map (algebra_map (adjoin R S) B) =
      (p.map $ algebra_map A B),
  { rw ← set.mem_range, exact (polynomial.mem_map_range _).2 (λ i, ⟨⟨_, coeffs_mem i⟩, rfl⟩) },
  use q,
  split,
  { suffices h : (q.map (algebra_map (adjoin R S) B)).monic,
    { refine monic_of_injective _ h,
      exact subtype.val_injective },
    { rw hq, exact monic_map _ pmonic } },
  { convert hp using 1,
    replace hq := congr_arg (eval x) hq,
    convert hq using 1; symmetry; apply eval_map },
end

variables [algebra R A] [is_scalar_tower R A B]

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R.-/
lemma is_integral_trans (A_int : is_integral R A) (x : B) (hx : is_integral A x) :
  is_integral R x :=
begin
  rcases hx with ⟨p, pmonic, hp⟩,
  let S : set B := ↑(p.map $ algebra_map A B).frange,
  refine is_integral_of_mem_of_fg (adjoin R (S ∪ {x})) _ _ (subset_adjoin $ or.inr rfl),
  refine fg_trans (fg_adjoin_of_finite (finset.finite_to_set _) (λ x hx, _)) _,
  { rw [finset.mem_coe, frange, finset.mem_image] at hx,
    rcases hx with ⟨i, _, rfl⟩,
    rw coeff_map,
    exact is_integral_alg_hom (is_scalar_tower.to_alg_hom R A B) (A_int _) },
  { apply fg_adjoin_singleton_of_integral,
    exact is_integral_trans_aux _ pmonic hp }
end

/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.-/
lemma algebra.is_integral_trans (hA : is_integral R A) (hB : is_integral A B) : is_integral R B :=
λ x, is_integral_trans hA x (hB x)

lemma ring_hom.is_integral_trans (hf : f.is_integral) (hg : g.is_integral) :
  (g.comp f).is_integral :=
@algebra.is_integral_trans R S T _ _ _ g.to_algebra (g.comp f).to_algebra f.to_algebra
  (@is_scalar_tower.of_algebra_map_eq R S T _ _ _ f.to_algebra g.to_algebra (g.comp f).to_algebra
  (ring_hom.comp_apply g f)) hf hg

lemma ring_hom.is_integral_of_surjective (hf : function.surjective f) : f.is_integral :=
λ x, (hf x).rec_on (λ y hy, (hy ▸ f.is_integral_map : f.is_integral_elem x))

lemma is_integral_of_surjective (h : function.surjective (algebra_map R A)) : is_integral R A :=
(algebra_map R A).is_integral_of_surjective h

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
lemma is_integral_tower_bot_of_is_integral (H : function.injective (algebra_map A B))
  {x : A} (h : is_integral R (algebra_map A B x)) : is_integral R x :=
begin
  rcases h with ⟨p, ⟨hp, hp'⟩⟩,
  refine ⟨p, ⟨hp, _⟩⟩,
  rw [is_scalar_tower.algebra_map_eq R A B, ← eval₂_map,
      eval₂_hom, ← ring_hom.map_zero (algebra_map A B)] at hp',
  rw [eval₂_eq_eval_map],
  exact H hp',
end

lemma ring_hom.is_integral_tower_bot_of_is_integral (hg : function.injective g)
  (hfg : (g.comp f).is_integral) : f.is_integral :=
λ x,
  @is_integral_tower_bot_of_is_integral R S T _ _ _ g.to_algebra (g.comp f).to_algebra f.to_algebra
  (@is_scalar_tower.of_algebra_map_eq R S T _ _ _ f.to_algebra g.to_algebra (g.comp f).to_algebra
  (ring_hom.comp_apply g f))  hg x (hfg (g x))

lemma is_integral_tower_bot_of_is_integral_field {R A B : Type*} [comm_ring R] [field A]
  [comm_ring B] [nontrivial B] [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]
  {x : A} (h : is_integral R (algebra_map A B x)) : is_integral R x :=
is_integral_tower_bot_of_is_integral (algebra_map A B).injective h

lemma ring_hom.is_integral_elem_of_is_integral_elem_comp {x : T}
  (h : (g.comp f).is_integral_elem x) : g.is_integral_elem x :=
let ⟨p, ⟨hp, hp'⟩⟩ := h in ⟨p.map f, monic_map f hp, by rwa ← eval₂_map at hp'⟩

lemma ring_hom.is_integral_tower_top_of_is_integral (h : (g.comp f).is_integral) : g.is_integral :=
λ x, ring_hom.is_integral_elem_of_is_integral_elem_comp f g (h x)

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
lemma is_integral_tower_top_of_is_integral {x : B} (h : is_integral R x) : is_integral A x :=
begin
  rcases h with ⟨p, ⟨hp, hp'⟩⟩,
  refine ⟨p.map (algebra_map R A), ⟨monic_map (algebra_map R A) hp, _⟩⟩,
  rw [is_scalar_tower.algebra_map_eq R A B, ← eval₂_map] at hp',
  exact hp',
end

lemma ring_hom.is_integral_quotient_of_is_integral {I : ideal S} (hf : f.is_integral) :
  (ideal.quotient_map I f le_rfl).is_integral :=
begin
  rintros ⟨x⟩,
  obtain ⟨p, ⟨p_monic, hpx⟩⟩ := hf x,
  refine ⟨p.map (ideal.quotient.mk _), ⟨monic_map _ p_monic, _⟩⟩,
  simpa only [hom_eval₂, eval₂_map] using congr_arg (ideal.quotient.mk I) hpx
end

lemma is_integral_quotient_of_is_integral {I : ideal A} (hRA : is_integral R A) :
  is_integral (I.comap (algebra_map R A)).quotient I.quotient :=
(algebra_map R A).is_integral_quotient_of_is_integral hRA

lemma is_integral_quotient_map_iff {I : ideal S} :
  (ideal.quotient_map I f le_rfl).is_integral ↔
    ((ideal.quotient.mk I).comp f : R →+* I.quotient).is_integral :=
begin
  let g := ideal.quotient.mk (I.comap f),
  have := ideal.quotient_map_comp_mk le_rfl,
  refine ⟨λ h, _, λ h, ring_hom.is_integral_tower_top_of_is_integral g _ (this ▸ h)⟩,
  refine this ▸ ring_hom.is_integral_trans g (ideal.quotient_map I f le_rfl) _ h,
  exact ring_hom.is_integral_of_surjective g ideal.quotient.mk_surjective,
end

/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
lemma is_field_of_is_integral_of_is_field {R S : Type*} [integral_domain R] [integral_domain S]
  [algebra R S] (H : is_integral R S) (hRS : function.injective (algebra_map R S))
  (hS : is_field S) : is_field R :=
begin
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, λ a ha, _⟩,
  -- Let `a_inv` be the inverse of `algebra_map R S a`,
  -- then we need to show that `a_inv` is of the form `algebra_map R S b`.
  obtain ⟨a_inv, ha_inv⟩ := hS.mul_inv_cancel (λ h, ha (hRS (trans h (ring_hom.map_zero _).symm))),

  -- Let `p : polynomial R` be monic with root `a_inv`,
  -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
  -- We claim that `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
  obtain ⟨p, p_monic, hp⟩ := H a_inv,
  use -∑ (i : ℕ) in finset.range p.nat_degree, (p.coeff i) * a ^ (p.nat_degree - i - 1),

  -- `q(a) = 0`, because multiplying everything with `a_inv^n` gives `p(a_inv) = 0`.
  -- TODO: this could be a lemma for `polynomial.reverse`.
  have hq : ∑ (i : ℕ) in finset.range (p.nat_degree + 1), (p.coeff i) * a ^ (p.nat_degree - i) = 0,
  { apply (algebra_map R S).injective_iff.mp hRS,
    have a_inv_ne_zero : a_inv ≠ 0 := right_ne_zero_of_mul (mt ha_inv.symm.trans one_ne_zero),
    refine (mul_eq_zero.mp _).resolve_right (pow_ne_zero p.nat_degree a_inv_ne_zero),
    rw [eval₂_eq_sum_range] at hp,
    rw [ring_hom.map_sum, finset.sum_mul],
    refine (finset.sum_congr rfl (λ i hi, _)).trans hp,
    rw [ring_hom.map_mul, mul_assoc],
    congr,
    have : a_inv ^ p.nat_degree = a_inv ^ (p.nat_degree - i) * a_inv ^ i,
    { rw [← pow_add a_inv, nat.sub_add_cancel (nat.le_of_lt_succ (finset.mem_range.mp hi))] },
    rw [ring_hom.map_pow, this, ← mul_assoc, ← mul_pow, ha_inv, one_pow, one_mul] },

  -- Since `q(a) = 0` and `q(a) = q'(a) * a + 1`, we have `a * -q'(a) = 1`.
  -- TODO: we could use a lemma for `polynomial.div_X` here.
  rw [finset.sum_range_succ_comm, p_monic.coeff_nat_degree, one_mul, nat.sub_self, pow_zero,
      add_eq_zero_iff_eq_neg, eq_comm] at hq,
  rw [mul_comm, ← neg_mul_eq_neg_mul, finset.sum_mul],
  convert hq using 2,
  refine finset.sum_congr rfl (λ i hi, _),
  have : 1 ≤ p.nat_degree - i := nat.le_sub_left_of_add_le (finset.mem_range.mp hi),
  rw [mul_assoc, ← pow_succ', nat.sub_add_cancel this]
end

end algebra

section
local attribute [instance] subset.comm_ring algebra.of_is_subring
theorem integral_closure_idem {R : Type*} {A : Type*} [comm_ring R] [comm_ring A] [algebra R A] :
  integral_closure (integral_closure R A : set A) A = ⊥ :=
eq_bot_iff.2 $ λ x hx, algebra.mem_bot.2
⟨⟨x, @is_integral_trans _ _ _ _ _ _ _ _ (integral_closure R A).algebra
     _ integral_closure.is_integral x hx⟩, rfl⟩
end

section integral_domain
variables {R S : Type*} [comm_ring R] [integral_domain S] [algebra R S]

instance : integral_domain (integral_closure R S) :=
infer_instance

end integral_domain
