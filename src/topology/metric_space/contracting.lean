/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import analysis.specific_limits
import dynamics.fixed_points.topology

/-!
# Contracting maps

A Lipschitz continuous self-map with Lipschitz constant `K < 1` is called a *contracting map*.
In this file we prove the Banach fixed point theorem, some explicit estimates on the rate
of convergence, and some properties of the map sending a contracting map to its fixed point.

## Main definitions

* `contracting_with K f` : a Lipschitz continuous self-map with `K < 1`;
* `efixed_point` : given a contracting map `f` on a complete emetric space and a point `x`
  such that `edist x (f x) < ∞`, `efixed_point f hf x hx` is the unique fixed point of `f`
  in `emetric.ball x ∞`;
* `fixed_point` : the unique fixed point of a contracting map on a complete nonempty metric space.

## Tags

contracting map, fixed point, Banach fixed point theorem
-/

open_locale nnreal topological_space classical
open filter function

variables {α : Type*}

/-- A map is said to be `contracting_with K`, if `K < 1` and `f` is `lipschitz_with K`. -/
def contracting_with [emetric_space α] (K : ℝ≥0) (f : α → α) :=
(K < 1) ∧ lipschitz_with K f

namespace contracting_with

variables [emetric_space α] [cs : complete_space α] {K : ℝ≥0} {f : α → α}

open emetric set

lemma to_lipschitz_with (hf : contracting_with K f) : lipschitz_with K f := hf.2

lemma one_sub_K_pos' (hf : contracting_with K f) : (0:ennreal) < 1 - K := by simp [hf.1]

lemma one_sub_K_ne_zero (hf : contracting_with K f) : (1:ennreal) - K ≠ 0 :=
ne_of_gt hf.one_sub_K_pos'

lemma one_sub_K_ne_top : (1:ennreal) - K ≠ ⊤ :=
by { norm_cast, exact ennreal.coe_ne_top }

lemma edist_inequality (hf : contracting_with K f) {x y} (h : edist x y < ⊤) :
  edist x y ≤ (edist x (f x) + edist y (f y)) / (1 - K) :=
suffices edist x y ≤ edist x (f x) + edist y (f y) + K * edist x y,
  by rwa [ennreal.le_div_iff_mul_le (or.inl hf.one_sub_K_ne_zero) (or.inl one_sub_K_ne_top),
    mul_comm, ennreal.sub_mul (λ _ _, ne_of_lt h), one_mul, ennreal.sub_le_iff_le_add],
calc edist x y ≤ edist x (f x) + edist (f x) (f y) + edist (f y) y : edist_triangle4 _ _ _ _
  ... = edist x (f x) + edist y (f y) + edist (f x) (f y) : by rw [edist_comm y, add_right_comm]
  ... ≤ edist x (f x) + edist y (f y) + K * edist x y : add_le_add (le_refl _) (hf.2 _ _)

lemma edist_le_of_fixed_point (hf : contracting_with K f) {x y}
  (h : edist x y < ⊤) (hy : is_fixed_pt f y) :
  edist x y ≤ (edist x (f x)) / (1 - K) :=
by simpa only [hy.eq, edist_self, add_zero] using hf.edist_inequality h

lemma eq_or_edist_eq_top_of_fixed_points (hf : contracting_with K f) {x y}
  (hx : is_fixed_pt f x) (hy : is_fixed_pt f y) :
  x = y ∨ edist x y = ⊤ :=
begin
  cases eq_or_lt_of_le (le_top : edist x y ≤ ⊤), from or.inr h,
  refine or.inl (edist_le_zero.1 _),
  simpa only [hx.eq, edist_self, add_zero, ennreal.zero_div]
    using hf.edist_le_of_fixed_point h hy
end

/-- If a map `f` is `contracting_with K`, and `s` is a forward-invariant set, then
restriction of `f` to `s` is `contracting_with K` as well. -/
lemma restrict (hf : contracting_with K f) {s : set α} (hs : maps_to f s s) :
  contracting_with K (hs.restrict f s s) :=
⟨hf.1, λ x y, hf.2 x y⟩

include cs

/-- Banach fixed-point theorem, contraction mapping theorem, `emetric_space` version.
A contracting map on a complete metric space has a fixed point.
We include more conclusions in this theorem to avoid proving them again later.

The main API for this theorem are the functions `efixed_point` and `fixed_point`,
and lemmas about these functions. -/
theorem exists_fixed_point (hf : contracting_with K f) (x : α) (hx : edist x (f x) < ⊤) :
  ∃ y, is_fixed_pt f y ∧ tendsto (λ n, f^[n] x) at_top (𝓝 y) ∧
    ∀ n:ℕ, edist (f^[n] x) y ≤ (edist x (f x)) * K^n / (1 - K) :=
have cauchy_seq (λ n, f^[n] x),
from cauchy_seq_of_edist_le_geometric K (edist x (f x)) (ennreal.coe_lt_one_iff.2 hf.1)
  (ne_of_lt hx) (hf.to_lipschitz_with.edist_iterate_succ_le_geometric x),
let ⟨y, hy⟩ := cauchy_seq_tendsto_of_complete this in
⟨y, is_fixed_pt_of_tendsto_iterate hy hf.2.continuous.continuous_at, hy,
  edist_le_of_edist_le_geometric_of_tendsto K (edist x (f x))
    (hf.to_lipschitz_with.edist_iterate_succ_le_geometric x) hy⟩

variable (f) -- avoid `efixed_point _` in pretty printer

/-- Let `x` be a point of a complete emetric space. Suppose that `f` is a contracting map,
and `edist x (f x) < ∞`. Then `efixed_point` is the unique fixed point of `f`
in `emetric.ball x ∞`. -/
noncomputable def efixed_point (hf : contracting_with K f) (x : α) (hx : edist x (f x) < ⊤) :
  α :=
classical.some $ hf.exists_fixed_point x hx

variables {f}

lemma efixed_point_is_fixed_pt (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
  is_fixed_pt f (efixed_point f hf x hx) :=
(classical.some_spec $ hf.exists_fixed_point x hx).1

lemma tendsto_iterate_efixed_point (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
  tendsto (λn, f^[n] x) at_top (𝓝 $ efixed_point f hf x hx) :=
(classical.some_spec $ hf.exists_fixed_point x hx).2.1

lemma apriori_edist_iterate_efixed_point_le (hf : contracting_with K f)
  {x : α} (hx : edist x (f x) < ⊤) (n : ℕ) :
  edist (f^[n] x) (efixed_point f hf x hx) ≤ (edist x (f x)) * K^n / (1 - K) :=
(classical.some_spec $ hf.exists_fixed_point x hx).2.2 n

lemma edist_efixed_point_le (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
  edist x (efixed_point f hf x hx) ≤ (edist x (f x)) / (1 - K) :=
by { convert hf.apriori_edist_iterate_efixed_point_le hx 0, simp only [pow_zero, mul_one] }

lemma edist_efixed_point_lt_top (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
  edist x (efixed_point f hf x hx) < ⊤ :=
lt_of_le_of_lt (hf.edist_efixed_point_le hx) (ennreal.mul_lt_top hx $
  ennreal.lt_top_iff_ne_top.2 $ ennreal.inv_ne_top.2 hf.one_sub_K_ne_zero)

lemma efixed_point_eq_of_edist_lt_top (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤)
  {y : α} (hy : edist y (f y) < ⊤) (h : edist x y < ⊤) :
  efixed_point f hf x hx = efixed_point f hf y hy :=
begin
  refine (hf.eq_or_edist_eq_top_of_fixed_points _ _).elim id (λ h', false.elim (ne_of_lt _ h'));
    try { apply efixed_point_is_fixed_pt },
  change edist_lt_top_setoid.rel _ _,
  transitivity x, by { symmetry, exact hf.edist_efixed_point_lt_top hx },
  transitivity y,
  exacts [h, hf.edist_efixed_point_lt_top hy]
end

omit cs

/-- Banach fixed-point theorem for maps contracting on a complete subset. -/
theorem exists_fixed_point' {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hf : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) < ⊤) :
  ∃ y ∈ s, is_fixed_pt f y ∧ tendsto (λ n, f^[n] x) at_top (𝓝 y) ∧
    ∀ n:ℕ, edist (f^[n] x) y ≤ (edist x (f x)) * K^n / (1 - K) :=
begin
  haveI := hsc.complete_space_coe,
  rcases hf.exists_fixed_point ⟨x, hxs⟩ hx with ⟨y, hfy, h_tendsto, hle⟩,
  refine ⟨y, y.2, subtype.ext_iff_val.1 hfy, _, λ n, _⟩,
  { convert (continuous_subtype_coe.tendsto _).comp h_tendsto, ext n,
    simp only [(∘), maps_to.iterate_restrict, maps_to.coe_restrict_apply, subtype.coe_mk] },
  { convert hle n,
    rw [maps_to.iterate_restrict, eq_comm, maps_to.coe_restrict_apply, subtype.coe_mk] }
end

variable (f) -- avoid `efixed_point _` in pretty printer

/-- Let `s` be a complete forward-invariant set of a self-map `f`. If `f` contracts on `s`
and `x ∈ s` satisfies `edist x (f x) < ⊤`, then `efixed_point'` is the unique fixed point
of the restriction of `f` to `s ∩ emetric.ball x ⊤`. -/
noncomputable def efixed_point' {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hf : contracting_with K $ hsf.restrict f s s) (x : α) (hxs : x ∈ s) (hx : edist x (f x) < ⊤) :
  α :=
classical.some $ hf.exists_fixed_point' hsc hsf hxs hx

variables {f}

lemma efixed_point_mem' {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hf : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) < ⊤) :
  efixed_point' f hsc hsf hf x hxs hx ∈ s :=
(classical.some_spec $ hf.exists_fixed_point' hsc hsf hxs hx).fst

lemma efixed_point_is_fixed_pt' {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hf : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) < ⊤) :
  is_fixed_pt f (efixed_point' f hsc hsf hf x hxs hx) :=
(classical.some_spec $ hf.exists_fixed_point' hsc hsf hxs hx).snd.1

lemma tendsto_iterate_efixed_point' {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hf : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) < ⊤) :
  tendsto (λn, f^[n] x) at_top (𝓝 $ efixed_point' f hsc hsf hf x hxs hx) :=
(classical.some_spec $ hf.exists_fixed_point' hsc hsf hxs hx).snd.2.1

lemma apriori_edist_iterate_efixed_point_le' {s : set α} (hsc : is_complete s)
  (hsf : maps_to f s s) (hf : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s)
  (hx : edist x (f x) < ⊤) (n : ℕ) :
  edist (f^[n] x) (efixed_point' f hsc hsf hf x hxs hx) ≤ (edist x (f x)) * K^n / (1 - K) :=
(classical.some_spec $ hf.exists_fixed_point' hsc hsf hxs hx).snd.2.2 n

lemma edist_efixed_point_le' {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hf : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) < ⊤) :
  edist x (efixed_point' f hsc hsf hf x hxs hx) ≤ (edist x (f x)) / (1 - K) :=
by { convert hf.apriori_edist_iterate_efixed_point_le' hsc hsf hxs hx 0,
  rw [pow_zero, mul_one] }

lemma edist_efixed_point_lt_top' {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hf : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) < ⊤) :
  edist x (efixed_point' f hsc hsf hf x hxs hx) < ⊤ :=
lt_of_le_of_lt (hf.edist_efixed_point_le' hsc hsf hxs hx) (ennreal.mul_lt_top hx $
  ennreal.lt_top_iff_ne_top.2 $ ennreal.inv_ne_top.2 hf.one_sub_K_ne_zero)

/-- If a globally contracting map `f` has two complete forward-invariant sets `s`, `t`,
and `x ∈ s` is at a finite distance from `y ∈ t`, then the `efixed_point'` constructed by `x`
is the same as the `efixed_point'` constructed by `y`.

This lemma takes additional arguments stating that `f` contracts on `s` and `t` because this way
it can be used to prove the desired equality with non-trivial proofs of these facts. -/
lemma efixed_point_eq_of_edist_lt_top' (hf : contracting_with K f)
  {s : set α} (hsc : is_complete s) (hsf : maps_to f s s)
  (hfs : contracting_with K $ hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) < ⊤)
  {t : set α} (htc : is_complete t) (htf : maps_to f t t)
  (hft : contracting_with K $ htf.restrict f t t) {y : α} (hyt : y ∈ t) (hy : edist y (f y) < ⊤)
  (hxy : edist x y < ⊤) :
  efixed_point' f hsc hsf hfs x hxs hx = efixed_point' f htc htf hft y hyt hy :=
begin
  refine (hf.eq_or_edist_eq_top_of_fixed_points _ _).elim id (λ h', false.elim (ne_of_lt _ h'));
    try { apply efixed_point_is_fixed_pt' },
  change edist_lt_top_setoid.rel _ _,
  transitivity x, by { symmetry, apply edist_efixed_point_lt_top' },
  transitivity y,
  exact hxy,
  apply edist_efixed_point_lt_top'
end

end contracting_with

namespace contracting_with

variables [metric_space α] {K : ℝ≥0} {f : α → α} (hf : contracting_with K f)
include hf

lemma one_sub_K_pos (hf : contracting_with K f) : (0:ℝ) < 1 - K := sub_pos.2 hf.1

lemma dist_le_mul (x y : α) : dist (f x) (f y) ≤ K * dist x y :=
hf.to_lipschitz_with.dist_le_mul x y

lemma dist_inequality (x y) : dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y,
  by rwa [le_div_iff hf.one_sub_K_pos, mul_comm, sub_mul, one_mul, sub_le_iff_le_add],
calc dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) : dist_triangle4_right _ _ _ _
          ... ≤ dist x (f x) + dist y (f y) + K * dist x y :
  add_le_add_left (hf.dist_le_mul _ _) _

lemma dist_le_of_fixed_point (x) {y} (hy : is_fixed_pt f y) :
  dist x y ≤ (dist x (f x)) / (1 - K) :=
by simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y

theorem fixed_point_unique' {x y} (hx : is_fixed_pt f x) (hy : is_fixed_pt f y) : x = y :=
(hf.eq_or_edist_eq_top_of_fixed_points hx hy).resolve_right (edist_ne_top _ _)

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
lemma dist_fixed_point_fixed_point_of_dist_le' (g : α → α)
  {x y} (hx : is_fixed_pt f x) (hy : is_fixed_pt g y) {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) :
  dist x y ≤ C / (1 - K) :=
calc dist x y = dist y x                     : dist_comm x y
          ... ≤ (dist y (f y)) / (1 - K)     : hf.dist_le_of_fixed_point y hx
          ... = (dist (f y) (g y)) / (1 - K) : by rw [hy.eq, dist_comm]
          ... ≤ C / (1 - K)                  : (div_le_div_right hf.one_sub_K_pos).2 (hfg y)

noncomputable theory

variables [nonempty α] [complete_space α]

variable (f)
/-- The unique fixed point of a contracting map in a nonempty complete metric space. -/
def fixed_point : α :=
efixed_point f hf _ (edist_lt_top (classical.choice ‹nonempty α›) _)
variable {f}

/-- The point provided by `contracting_with.fixed_point` is actually a fixed point. -/
lemma fixed_point_is_fixed_pt : is_fixed_pt f (fixed_point f hf) :=
hf.efixed_point_is_fixed_pt _

lemma fixed_point_unique {x} (hx : is_fixed_pt f x) : x = fixed_point f hf :=
hf.fixed_point_unique' hx hf.fixed_point_is_fixed_pt

lemma dist_fixed_point_le (x) : dist x (fixed_point f hf) ≤ (dist x (f x)) / (1 - K) :=
hf.dist_le_of_fixed_point x hf.fixed_point_is_fixed_pt

/-- Aposteriori estimates on the convergence of iterates to the fixed point. -/
lemma aposteriori_dist_iterate_fixed_point_le (x n) :
  dist (f^[n] x) (fixed_point f hf) ≤ (dist (f^[n] x) (f^[n+1] x)) / (1 - K) :=
by { rw [iterate_succ'], apply hf.dist_fixed_point_le }

lemma apriori_dist_iterate_fixed_point_le (x n) :
  dist (f^[n] x) (fixed_point f hf) ≤ (dist x (f x)) * K^n / (1 - K) :=
le_trans (hf.aposteriori_dist_iterate_fixed_point_le x n) $
  (div_le_div_right hf.one_sub_K_pos).2 $
    hf.to_lipschitz_with.dist_iterate_succ_le_geometric x n

lemma tendsto_iterate_fixed_point (x) :
  tendsto (λn, f^[n] x) at_top (𝓝 $ fixed_point f hf) :=
begin
  convert tendsto_iterate_efixed_point hf (edist_lt_top x _),
  refine (fixed_point_unique _ _).symm,
  apply efixed_point_is_fixed_pt
end

lemma fixed_point_lipschitz_in_map {g : α → α} (hg : contracting_with K g)
  {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) :
  dist (fixed_point f hf) (fixed_point g hg) ≤ C / (1 - K) :=
hf.dist_fixed_point_fixed_point_of_dist_le' g hf.fixed_point_is_fixed_pt
  hg.fixed_point_is_fixed_pt hfg

end contracting_with
