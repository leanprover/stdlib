/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.subalgebra
import analysis.special_functions.bernstein

/-!
# The Weierstrass approximation theorem for continuous functions on `[a,b]`

We've already proved the Weierstrass approximation theorem
in the sense that we've shown that the Bernstein approximations
to a continuous function on `[0,1]` converge uniformly.

Here we rephrase this more abstractly as
`polynomial_functions_closure_eq_top' : (polynomial_functions I).topological_closure = ⊤`
and then, by precomposing with suitable affine functions,
`polynomial_functions_closure_eq_top : (polynomial_functions (set.Icc a b)).topological_closure = ⊤`
-/

open continuous_map filter
open_locale unit_interval

/--
The special case of the Weierstrass approximation theorem for the interval `[0,1]`.
This is just a matter of unravelling definitions and using the Bernstein approximations.
-/
theorem polynomial_functions_closure_eq_top' :
  (polynomial_functions I).topological_closure = ⊤ :=
begin
  apply eq_top_iff.mpr,
  rintros f -,
  refine filter.frequently.mem_closure _,
  refine filter.tendsto.frequently (bernstein_approximation_uniform f) _,
  apply frequently_of_forall,
  intro n,
  simp only [set_like.mem_coe],
  apply subalgebra.sum_mem,
  rintro n -,
  apply subalgebra.smul_mem,
  dsimp [bernstein, polynomial_functions],
  simp,
end

/--
The **Weierstrass Approximation Theorem**:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`

(While we could deduce this as an application of the Stone-Weierstrass theorem,
our proof of that relies on the fact that `abs` is in the closure of polynomials on `[-M, M]`,
so we may as well get this done first.)
-/
theorem polynomial_functions_closure_eq_top (a b : ℝ) :
  (polynomial_functions (set.Icc a b)).topological_closure = ⊤ :=
begin
  by_cases h : a < b, -- (Otherwise it's easy; we'll deal with that later.)
  { -- We can pullback continuous functions on `[a,b]` to continuous functions on `[0,1]`,
    -- by precomposing with an affine map.
    let W : C(set.Icc a b, ℝ) →ₐ[ℝ] C(I, ℝ) :=
      comp_right_alg_hom ℝ (Icc_homeo_I a b h).symm.to_continuous_map,
    -- This operation is itself a homeomorphism
    -- (with respect to the norm topologies on continuous functions).
    let W' : C(set.Icc a b, ℝ) ≃ₜ C(I, ℝ) := comp_right_homeomorph ℝ (Icc_homeo_I a b h).symm,
    have w : (W : C(set.Icc a b, ℝ) → C(I, ℝ)) = W' := rfl,
    -- Thus we take the statement of the Weierstrass approximation theorem for `[0,1]`,
    have p := polynomial_functions_closure_eq_top',
    -- and pullback both sides, obtaining an equation between subalgebras of `C([a,b], ℝ)`.
    apply_fun (λ s, s.comap' W) at p,
    simp only [algebra.comap_top] at p,
    -- Since the pullback operation is continuous, it commutes with taking `topological_closure`,
    rw subalgebra.topological_closure_comap'_homeomorph _ W W' w at p,
    -- and precomposing with an affine map takes polynomial functions to polynomial functions.
    rw polynomial_functions.comap'_comp_right_alg_hom_Icc_homeo_I at p,
    -- 🎉
    exact p },
  { -- Otherwise, `b ≤ a`, and the interval is a subsingleton,
    -- so all subalgebras are the same anyway.
    haveI : subsingleton (set.Icc a b) := ⟨λ x y, le_antisymm
      ((x.2.2.trans (not_lt.mp h)).trans y.2.1) ((y.2.2.trans (not_lt.mp h)).trans x.2.1)⟩,
    haveI := (continuous_map.subsingleton_subalgebra (set.Icc a b) ℝ),
    apply subsingleton.elim, }
end

/--
An alternative statement of Weierstrass' theorem.

Every real-valued continuous function on `[a,b]` is a uniform limit of polynomials.
-/
theorem continuous_map_mem_polynomial_functions_closure (a b : ℝ) (f : C(set.Icc a b, ℝ)) :
  f ∈ (polynomial_functions (set.Icc a b)).topological_closure :=
begin
  rw polynomial_functions_closure_eq_top _ _,
  simp,
end

/--
An alternative statement of Weierstrass' theorem,
for those who like their epsilons.

Every real-valued continuous function on `[a,b]` is within any `ε > 0` of some polynomial.
-/
theorem exists_polynomial_near_continuous_map (a b : ℝ) (f : C(set.Icc a b, ℝ))
  (ε : ℝ) (pos : 0 < ε) :
  ∃ (p : polynomial ℝ), ∥p.to_continuous_map_on _ - f∥ < ε :=
begin
  have w := mem_closure_iff_frequently.mp (continuous_map_mem_polynomial_functions_closure _ _ f),
  rw metric.nhds_basis_ball.frequently_iff at w,
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos,
  rw [metric.mem_ball, dist_eq_norm] at H,
  exact ⟨m, H⟩,
end

/--
Another alternative statement of Weierstrass's theorem,
for those who like epsilons, but not bundled continuous functions.

Every real-valued function `ℝ → ℝ` which is continuous on `[a,b]`
can be approximated to within any `ε > 0` on `[a,b]` by some polynomial.
-/
theorem exists_polynomial_near_of_continuous_on
  (a b : ℝ) (f : ℝ → ℝ) (c : continuous_on f (set.Icc a b)) (ε : ℝ) (pos : 0 < ε) :
  ∃ (p : polynomial ℝ), ∀ x ∈ set.Icc a b, abs (p.eval x - f x) < ε :=
begin
  let f' : C(set.Icc a b, ℝ) := ⟨λ x, f x, continuous_on_iff_continuous_restrict.mp c⟩,
  obtain ⟨p, b⟩ := exists_polynomial_near_continuous_map a b f' ε pos,
  use p,
  rw norm_lt_iff _ pos at b,
  intros x m,
  exact b ⟨x, m⟩,
end
