/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Heather Macbeth
-/
import topology.continuous_function.weierstrass
import analysis.complex.basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/

noncomputable theory

namespace continuous_map

variables {X : Type*} [topological_space X] [compact_space X]

/--
Turn a function `f : C(X, ℝ)` into a continuous map into `set.Icc (-∥f∥) (∥f∥)`,
thereby explicitly attaching bounds.
-/
def attach_bound (f : C(X, ℝ)) : C(X, set.Icc (-∥f∥) (∥f∥)) :=
{ to_fun := λ x, ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩ }

@[simp] lemma attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attach_bound f) x : ℝ) = f x := rfl

lemma polynomial_comp_attach_bound (A : subalgebra ℝ C(X, ℝ)) (f : A) (g : polynomial ℝ) :
  (g.to_continuous_map_on (set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attach_bound =
    polynomial.aeval f g :=
begin
  ext,
  simp only [continuous_map.comp_coe, function.comp_app,
    continuous_map.attach_bound_apply_coe,
    polynomial.to_continuous_map_on_to_fun,
    polynomial.aeval_subalgebra_coe,
    polynomial.aeval_continuous_map_apply,
    polynomial.to_continuous_map_to_fun],
end

/--
Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `set.Icc (-∥f∥) ∥f∥)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
lemma polynomial_comp_attach_bound_mem (A : subalgebra ℝ C(X, ℝ)) (f : A) (g : polynomial ℝ) :
  (g.to_continuous_map_on (set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attach_bound ∈ A :=
begin
  rw polynomial_comp_attach_bound,
  apply set_like.coe_mem,
end

theorem comp_attach_bound_mem_closure
  (A : subalgebra ℝ C(X, ℝ)) (f : A) (p : C(set.Icc (-∥f∥) (∥f∥), ℝ)) :
  p.comp (attach_bound f) ∈ A.topological_closure :=
begin
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p ∈ (polynomial_functions (set.Icc (-∥f∥) (∥f∥))).topological_closure :=
    continuous_map_mem_polynomial_functions_closure _ _ p,
  -- and so there are polynomials arbitrarily close.
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure,
  -- To prove `p.comp (attached_bound f)` is in the closure of `A`,
  -- we show there are elements of `A` arbitrarily close.
  apply mem_closure_iff_frequently.mpr,
  -- To show that, we pull back the polynomials close to `p`,
  refine ((comp_right_continuous_map ℝ (attach_bound (f : C(X, ℝ)))).continuous_at p).tendsto
    .frequently_map _ _ frequently_mem_polynomials,
  -- but need to show that those pullbacks are actually in `A`.
  rintros _ ⟨g, ⟨-,rfl⟩⟩,
  simp only [set_like.mem_coe, alg_hom.coe_to_ring_hom, comp_right_continuous_map_apply,
    polynomial.to_continuous_map_on_alg_hom_apply],
  apply polynomial_comp_attach_bound_mem,
end

theorem abs_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f : A) :
  (f : C(X, ℝ)).abs ∈ A.topological_closure :=
begin
  let M := ∥f∥,
  let f' := attach_bound (f : C(X, ℝ)),
  let abs : C(set.Icc (-∥f∥) (∥f∥), ℝ) :=
  { to_fun := λ x : set.Icc (-∥f∥) (∥f∥), _root_.abs (x : ℝ) },
  change (abs.comp f') ∈ A.topological_closure,
  apply comp_attach_bound_mem_closure,
end

theorem inf_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A.topological_closure :=
begin
  rw inf_eq,
  refine A.topological_closure.smul_mem
    (A.topological_closure.sub_mem
      (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property)) _) _,
  exact_mod_cast abs_mem_subalgebra_closure A _,
end

theorem inf_mem_closed_subalgebra (A : subalgebra ℝ C(X, ℝ)) (h : is_closed (A : set C(X, ℝ)))
  (f g : A) : (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A :=
begin
  convert inf_mem_subalgebra_closure A f g,
  apply set_like.ext',
  symmetry,
  erw closure_eq_iff_is_closed,
  exact h,
end

theorem sup_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A.topological_closure :=
begin
  rw sup_eq,
  refine A.topological_closure.smul_mem
    (A.topological_closure.add_mem
      (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property)) _) _,
  exact_mod_cast abs_mem_subalgebra_closure A _,
end

theorem sup_mem_closed_subalgebra (A : subalgebra ℝ C(X, ℝ)) (h : is_closed (A : set C(X, ℝ)))
  (f g : A) : (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A :=
begin
  convert sup_mem_subalgebra_closure A f g,
  apply set_like.ext',
  symmetry,
  erw closure_eq_iff_is_closed,
  exact h,
end

open_locale topological_space

-- Here's the fun part of Stone-Weierstrass!
theorem sublattice_closure_eq_top
  (L : set C(X, ℝ)) (nA : L.nonempty)
  (inf_mem : ∀ f g ∈ L, f ⊓ g ∈ L) (sup_mem : ∀ f g ∈ L, f ⊔ g ∈ L)
  (sep : L.separates_points_strongly) :
  closure L = ⊤ :=
begin
  -- We start by boiling down to a statement about close approximation.
  apply eq_top_iff.mpr,
  rintros f -,
  refine filter.frequently.mem_closure
    ((filter.has_basis.frequently_iff metric.nhds_basis_ball).mpr (λ ε pos, _)),
  simp only [exists_prop, metric.mem_ball],

  -- It will be helpful to assume `X` is nonempty later,
  -- so we get that out of the way here.
  by_cases nX : nonempty X,
  swap,
  exact ⟨nA.some, (dist_lt_iff _ _ pos).mpr (λ x, false.elim (nX ⟨x⟩)), nA.some_spec⟩,

  /-
  The strategy now is to pick a family of continuous functions `g x y` in `A`
  with the property that `g x y x = f x` and `g x y y = f y`
  (this is immediate from `h : separates_points_strongly`)
  then use continuity to see that `g x y` is close to `f` near both `x` and `y`,
  and finally using compactness to produce the desired function `h`
  as a maximum over finitely many `x` of a minimum over finitely many `y` of the `g x y`.
  -/
  dsimp [set.separates_points_strongly] at sep,

  let g : X → X → L := λ x y, (sep f x y).some,
  have w₁ : ∀ x y, g x y x = f x := λ x y, (sep f x y).some_spec.1,
  have w₂ : ∀ x y, g x y y = f y := λ x y, (sep f x y).some_spec.2,

  -- For each `x y`, we define `U x y` to be `{z | f z - ε < g x y z}`,
  -- and observe this is a neighbourhood of `y`.
  let U : X → X → set X := λ x y, {z | f z - ε < g x y z},
  have U_nhd_y : ∀ x y, U x y ∈ 𝓝 y,
  { intros x y,
    refine is_open.mem_nhds _ _,
    { apply is_open_lt; continuity, },
    { rw [set.mem_set_of_eq, w₂],
      exact sub_lt_self _ pos, }, },

  -- Fixing `x` for a moment, we have a family of functions `λ y, g x y`
  -- which on different patches (the `U x y`) are greater than `f z - ε`.
  -- Taking the supremum of these functions
  -- indexed by a finite collection of patches which cover `X`
  -- will give us an element of `A` that is globally greater than `f z - ε`
  -- and still equal to `f x` at `x`.

  -- Since `X` is compact, for every `x` there is some finset `ys t`
  -- so the union of the `U x y` for `y ∈ ys x` still covers everything.
  let ys : Π x, finset X := λ x, (compact_space.elim_nhds_subcover (U x) (U_nhd_y x)).some,
  let ys_w : ∀ x, (⋃ y ∈ ys x, U x y) = ⊤ :=
    λ x, (compact_space.elim_nhds_subcover (U x) (U_nhd_y x)).some_spec,

  have ys_nonempty : ∀ x, (ys x).nonempty :=
    λ x, set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x),

  -- Thus for each `x` we have the desired `h x : A` so `f z - ε < h x z` everywhere
  -- and `h x x = f x`.
  let h : Π x, L := λ x,
    ⟨(ys x).sup' (ys_nonempty x) (λ y, (g x y : C(X, ℝ))),
      finset.sup'_mem _ sup_mem _ _ _ (λ y _, (g x y).2)⟩,
  have lt_h : ∀ x z, f z - ε < h x z,
  { intros x z,
    obtain ⟨y, ym, zm⟩ := set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z,
    dsimp [h],
    simp only [finset.lt_sup'_iff, continuous_map.sup'_apply],
    exact ⟨y, ym, zm⟩, },
  have h_eq : ∀ x, h x x = f x, by { intro x, simp only [coe_fn_coe_base] at w₁, simp [w₁], },

  -- For each `x`, we define `W x` to be `{z | h x z < f z + ε}`,
  let W : Π x, set X := λ x, {z | h x z < f z + ε},
  -- This is still a neighbourhood of `x`.
  have W_nhd : ∀ x, W x ∈ 𝓝 x,
  { intros x,
    refine is_open.mem_nhds _ _,
    { apply is_open_lt; continuity, },
    { dsimp only [W, set.mem_set_of_eq],
      rw h_eq,
      exact lt_add_of_pos_right _ pos}, },

  -- Since `X` is compact, there is some finset `ys t`
  -- so the union of the `W x` for `x ∈ xs` still covers everything.
  let xs : finset X := (compact_space.elim_nhds_subcover W W_nhd).some,
  let xs_w : (⋃ x ∈ xs, W x) = ⊤ :=
    (compact_space.elim_nhds_subcover W W_nhd).some_spec,
  have xs_nonempty : xs.nonempty := set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w,

  -- Finally our candidate function is the infimum over `x ∈ xs` of the `h x`.
  -- This function is then globally less than `f z + ε`.
  let k : (L : Type*) :=
    ⟨xs.inf' xs_nonempty (λ x, (h x : C(X, ℝ))),
      finset.inf'_mem _ inf_mem _ _ _ (λ x _, (h x).2)⟩,

  refine ⟨k.1, _, k.2⟩,

  -- We just need to verify the bound, which we do pointwise.
  rw dist_lt_iff _ _ pos,
  intro z,

  -- We rewrite into this particular form,
  -- so that simp lemmas about inequalities involving `finset.inf'` can fire.
  rw [(show ∀ a b ε : ℝ, dist a b < ε ↔ a < b + ε ∧ b - ε < a,
    by { intros, simp only [← metric.mem_ball, real.ball_eq_Ioo, set.mem_Ioo, and_comm], })],

  fsplit,
  { dsimp [k],
    simp only [finset.inf'_lt_iff, continuous_map.inf'_apply],
    exact set.exists_set_mem_of_union_eq_top _ _ xs_w z, },
  { dsimp [k],
    simp only [finset.lt_inf'_iff, continuous_map.inf'_apply],
    intros x xm,
    apply lt_h, },
end

/--
The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
theorem subalgebra_topological_closure_eq_top_of_separates_points
  (A : subalgebra ℝ C(X, ℝ)) (w : A.separates_points) :
  A.topological_closure = ⊤ :=
begin
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply set_like.ext',
  let L := A.topological_closure,
  have n : set.nonempty (L : set C(X, ℝ)) :=
    ⟨(1 : C(X, ℝ)), A.subalgebra_topological_closure A.one_mem⟩,
  convert sublattice_closure_eq_top
    (L : set C(X, ℝ)) n
    (λ f g fm gm, inf_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
    (λ f g fm gm, sup_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
    (subalgebra.separates_points.strongly
      (subalgebra.separates_points_monotone (A.subalgebra_topological_closure) w)),
  { simp, },
end

/--
An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `A`.
-/
theorem continuous_map_mem_subalgebra_closure_of_separates_points
  (A : subalgebra ℝ C(X, ℝ)) (w : A.separates_points)
  (f : C(X, ℝ)) :
  f ∈ A.topological_closure :=
begin
  rw subalgebra_topological_closure_eq_top_of_separates_points A w,
  simp,
end

/--
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_map_of_separates_points
  (A : subalgebra ℝ C(X, ℝ)) (w : A.separates_points)
  (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
  ∃ (g : A), ∥(g : C(X, ℝ)) - f∥ < ε :=
begin
  have w := mem_closure_iff_frequently.mp
    (continuous_map_mem_subalgebra_closure_of_separates_points A w f),
  rw metric.nhds_basis_ball.frequently_iff at w,
  obtain ⟨g, H, m⟩ := w ε pos,
  rw [metric.mem_ball, dist_eq_norm] at H,
  exact ⟨⟨g, m⟩, H⟩,
end

/--
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_of_separates_points
  (A : subalgebra ℝ C(X, ℝ)) (w : A.separates_points)
  (f : X → ℝ) (c : continuous f) (ε : ℝ) (pos : 0 < ε) :
  ∃ (g : A), ∀ x, ∥g x - f x∥ < ε :=
begin
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuous_map_of_separates_points A w ⟨f, c⟩ ε pos,
  use g,
  rwa norm_lt_iff _ pos at b,
end

end continuous_map

section complex
open complex

-- Redefine `X`, since for the next few lemmas it need not be compact
variables {X : Type*} [topological_space X]

namespace continuous_map

/-- A real subalgebra of `C(X, ℂ)` is `conj_invariant`, if it contains all its conjugates. -/
def conj_invariant_subalgebra (A : subalgebra ℝ C(X, ℂ)) : Prop :=
A.map (conj_ae.to_alg_hom.comp_left_continuous ℝ conj_cle.continuous) ≤ A

lemma mem_conj_invariant_subalgebra {A : subalgebra ℝ C(X, ℂ)} (hA : conj_invariant_subalgebra A)
  {f : C(X, ℂ)} (hf : f ∈ A) :
  (conj_ae.to_alg_hom.comp_left_continuous ℝ conj_cle.continuous) f ∈ A :=
hA ⟨f, hf, rfl⟩

end continuous_map

open continuous_map

/-- If a conjugation-invariant subalgebra of `C(X, ℂ)` separates points, then the real subalgebra
of its purely real-valued elements also separates points. -/
lemma subalgebra.separates_points.complex_to_real {A : subalgebra ℂ C(X, ℂ)}
  (hA : A.separates_points) (hA' : conj_invariant_subalgebra (A.restrict_scalars ℝ)) :
  ((A.restrict_scalars ℝ).comap'
    (of_real_am.comp_left_continuous ℝ continuous_of_real)).separates_points :=
begin
  intros x₁ x₂ hx,
  -- Let `f` in the subalgebra `A` separate the points `x₁`, `x₂`
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx,
  let F : C(X, ℂ) := f - const (f x₂),
  -- Subtract the constant `f x₂` from `f`; this is still an element of the subalgebra
  have hFA : F ∈ A,
  { refine A.sub_mem hfA _,
    convert A.smul_mem A.one_mem (f x₂),
    ext1,
    simp },
  -- Consider now the function `λ x, |f x - f x₂| ^ 2`
  refine ⟨_, ⟨(⟨complex.norm_sq, continuous_norm_sq⟩ : C(ℂ, ℝ)).comp F, _, rfl⟩, _⟩,
  { -- This is also an element of the subalgebra, and takes only real values
    rw [set_like.mem_coe, subalgebra.mem_comap],
    convert (A.restrict_scalars ℝ).mul_mem (mem_conj_invariant_subalgebra hA' hFA) hFA,
    ext1,
    exact complex.norm_sq_eq_conj_mul_self },
  { -- And it also separates the points `x₁`, `x₂`
    have : f x₁ - f x₂ ≠ 0 := sub_ne_zero.mpr hf,
    simpa using this },
end

variables [compact_space X]

/--
The Stone-Weierstrass approximation theorem, complex version,
that a subalgebra `A` of `C(X, ℂ)`, where `X` is a compact topological space,
is dense if it is conjugation-invariant and separates points.
-/
theorem continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
  (A : subalgebra ℂ C(X, ℂ)) (hA : A.separates_points)
  (hA' : conj_invariant_subalgebra (A.restrict_scalars ℝ)) :
  A.topological_closure = ⊤ :=
begin
  rw algebra.eq_top_iff,
  -- Let `I` be the natural inclusion of `C(X, ℝ)` into `C(X, ℂ)`
  let I : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) := of_real_clm.comp_left_continuous ℝ X,
  -- The main point of the proof is that its range (i.e., every real-valued function) is contained
  -- in the closure of `A`
  have key : I.range ≤ (A.to_submodule.restrict_scalars ℝ).topological_closure,
  { -- Let `A₀` be the subalgebra of `C(X, ℝ)` consisting of `A`'s purely real elements; it is the
    -- preimage of `A` under `I`.  In this argument we only need its submodule structure.
    let A₀ : submodule ℝ C(X, ℝ) := (A.to_submodule.restrict_scalars ℝ).comap I,
    -- By `subalgebra.separates_points.complex_to_real`, this subalgebra also separates points, so
    -- we may apply the real Stone-Weierstrass result to it.
    have SW : A₀.topological_closure = ⊤,
    { have := subalgebra_topological_closure_eq_top_of_separates_points _ (hA.complex_to_real hA'),
      exact congr_arg subalgebra.to_submodule this },
    rw [← submodule.map_top, ← SW],
    -- So it suffices to prove that the image under `I` of the closure of `A₀` is contained in the
    -- closure of `A`, which follows by abstract nonsense
    have h₁ := A₀.topological_closure_map (of_real_clm.comp_left_continuous_compact X),
    have h₂ := (A.to_submodule.restrict_scalars ℝ).map_comap_le I,
    exact h₁.trans (submodule.topological_closure_mono h₂) },
  -- In particular, for a function `f` in `C(X, ℂ)`, the real and imaginary parts of `f` are in the
  -- closure of `A`
  intros f,
  let f_re : C(X, ℝ) := (⟨complex.re, complex.re_clm.continuous⟩ : C(ℂ, ℝ)).comp f,
  let f_im : C(X, ℝ) := (⟨complex.im, complex.im_clm.continuous⟩ : C(ℂ, ℝ)).comp f,
  have h_f_re : I f_re ∈ A.topological_closure := key ⟨f_re, rfl⟩,
  have h_f_im : I f_im ∈ A.topological_closure := key ⟨f_im, rfl⟩,
  -- So `f_re + complex.I • f_im` is in the closure of `A`
  convert A.topological_closure.add_mem h_f_re (A.topological_closure.smul_mem h_f_im complex.I),
  -- And this, of course, is just `f`
  ext; simp [I]
end

end complex
