/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import logic.function.iterate
import topology.metric_space.basic
import category_theory.endomorphism

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous.

## Main definitions and lemmas

* `lipschitz_with K f`: states that `f` is Lipschitz with constant `K : ℝ≥0`
* `lipschitz_on_with K f`: states that `f` is Lipschitz with constant `K : ℝ≥0` on a set `s`
* `lipschitz_with.uniform_continuous`: a Lipschitz function is uniformly continuous
* `lipschitz_on_with.uniform_continuous_on`: a function which is Lipschitz on a set is uniformly
  continuous on that set.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ennreal`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `lipschitz_with (nnreal.of_real K) f`.
-/

universes u v w x

open filter function set
open_locale topological_space nnreal

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def lipschitz_with [emetric_space α] [emetric_space β] (K : ℝ≥0) (f : α → β) :=
∀x y, edist (f x) (f y) ≤ K * edist x y

lemma lipschitz_with_iff_dist_le_mul [metric_space α] [metric_space β] {K : ℝ≥0} {f : α → β} :
  lipschitz_with K f ↔ ∀ x y, dist (f x) (f y) ≤ K * dist x y :=
by { simp only [lipschitz_with, edist_nndist, dist_nndist], norm_cast }

alias lipschitz_with_iff_dist_le_mul ↔ lipschitz_with.dist_le_mul lipschitz_with.of_dist_le_mul

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` on `s` if for all `x, y` in `s`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def lipschitz_on_with [emetric_space α] [emetric_space β] (K : ℝ≥0) (f : α → β) (s : set α) :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), edist (f x) (f y) ≤ K * edist x y

@[simp] lemma lipschitz_on_with_empty [emetric_space α] [emetric_space β] (K : ℝ≥0) (f : α → β) :
  lipschitz_on_with K f ∅ :=
λ x x_in y y_in, false.elim x_in

lemma lipschitz_on_with.mono [emetric_space α] [emetric_space β] {K : ℝ≥0} {s t : set α} {f : α → β}
  (hf : lipschitz_on_with K f t) (h : s ⊆ t) : lipschitz_on_with K f s :=
λ x x_in y y_in, hf (h x_in) (h y_in)

lemma lipschitz_on_with_iff_dist_le_mul [metric_space α] [metric_space β] {K : ℝ≥0} {s : set α}
  {f : α → β} : lipschitz_on_with K f s ↔ ∀ (x ∈ s) (y ∈ s), dist (f x) (f y) ≤ K * dist x y :=
by { simp only [lipschitz_on_with, edist_nndist, dist_nndist], norm_cast }

alias lipschitz_on_with_iff_dist_le_mul ↔ lipschitz_on_with.dist_le_mul lipschitz_on_with.of_dist_le_mul

@[simp] lemma lipschitz_on_univ [emetric_space α] [emetric_space β] {K : ℝ≥0} {f : α → β} :
  lipschitz_on_with K f univ ↔ lipschitz_with K f :=
by simp [lipschitz_on_with, lipschitz_with]

lemma lipschitz_on_with_iff_restrict [emetric_space α] [emetric_space β] {K : ℝ≥0}
  {f : α → β} {s : set α} : lipschitz_on_with K f s ↔ lipschitz_with K (s.restrict f) :=
by simp only [lipschitz_on_with, lipschitz_with, set_coe.forall', restrict, subtype.edist_eq]

namespace lipschitz_with

section emetric

variables [emetric_space α] [emetric_space β] [emetric_space γ] {K : ℝ≥0} {f : α → β}

lemma edist_le_mul (h : lipschitz_with K f) (x y : α) : edist (f x) (f y) ≤ K * edist x y := h x y

lemma edist_lt_top (hf : lipschitz_with K f) {x y : α} (h : edist x y < ⊤) :
  edist (f x) (f y) < ⊤ :=
lt_of_le_of_lt (hf x y) $ ennreal.mul_lt_top ennreal.coe_lt_top h

lemma mul_edist_le (h : lipschitz_with K f) (x y : α) :
  (K⁻¹ : ennreal) * edist (f x) (f y) ≤ edist x y :=
begin
  have := h x y,
  rw [mul_comm] at this,
  replace := ennreal.div_le_of_le_mul this,
  rwa [div_eq_mul_inv, mul_comm] at this
end

protected lemma of_edist_le (h : ∀ x y, edist (f x) (f y) ≤ edist x y) :
  lipschitz_with 1 f :=
λ x y, by simp only [ennreal.coe_one, one_mul, h]

protected lemma weaken (hf : lipschitz_with K f) {K' : ℝ≥0} (h : K ≤ K') :
  lipschitz_with K' f :=
assume x y, le_trans (hf x y) $ ennreal.mul_right_mono (ennreal.coe_le_coe.2 h)

lemma ediam_image_le (hf : lipschitz_with K f) (s : set α) :
  emetric.diam (f '' s) ≤ K * emetric.diam s :=
begin
  apply emetric.diam_le_of_forall_edist_le,
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
  calc edist (f x) (f y) ≤ ↑K * edist x y : hf.edist_le_mul x y
                     ... ≤ ↑K * emetric.diam s :
    ennreal.mul_left_mono (emetric.edist_le_diam_of_mem hx hy)
end

/-- A Lipschitz function is uniformly continuous -/
protected lemma uniform_continuous (hf : lipschitz_with K f) :
  uniform_continuous f :=
begin
  refine emetric.uniform_continuous_iff.2 (λε εpos, _),
  use [ε/K, canonically_ordered_semiring.mul_pos.2 ⟨εpos, ennreal.inv_pos.2 $ ennreal.coe_ne_top⟩],
  assume x y Dxy,
  apply lt_of_le_of_lt (hf.edist_le_mul x y),
  rw [mul_comm],
  exact ennreal.mul_lt_of_lt_div Dxy
end

/-- A Lipschitz function is continuous -/
protected lemma continuous (hf : lipschitz_with K f) :
  continuous f :=
hf.uniform_continuous.continuous

protected lemma const (b : β) : lipschitz_with 0 (λa:α, b) :=
assume x y, by simp only [edist_self, zero_le]

protected lemma id : lipschitz_with 1 (@id α) :=
lipschitz_with.of_edist_le $ assume x y, le_refl _

protected lemma subtype_val (s : set α) : lipschitz_with 1 (subtype.val : s → α) :=
lipschitz_with.of_edist_le $ assume x y, le_refl _

protected lemma subtype_coe (s : set α) : lipschitz_with 1 (coe : s → α) :=
lipschitz_with.subtype_val s

protected lemma restrict (hf : lipschitz_with K f) (s : set α) :
  lipschitz_with K (s.restrict f) :=
λ x y, hf x y

protected lemma comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) : lipschitz_with (Kf * Kg) (f ∘ g) :=
assume x y,
calc edist (f (g x)) (f (g y)) ≤ Kf * edist (g x) (g y) : hf _ _
... ≤ Kf * (Kg * edist x y) : ennreal.mul_left_mono (hg _ _)
... = (Kf * Kg : ℝ≥0) * edist x y : by rw [← mul_assoc, ennreal.coe_mul]

protected lemma prod_fst : lipschitz_with 1 (@prod.fst α β) :=
lipschitz_with.of_edist_le $ assume x y, le_max_left _ _

protected lemma prod_snd : lipschitz_with 1 (@prod.snd α β) :=
lipschitz_with.of_edist_le $ assume x y, le_max_right _ _

protected lemma prod {f : α → β} {Kf : ℝ≥0} (hf : lipschitz_with Kf f)
  {g : α → γ} {Kg : ℝ≥0} (hg : lipschitz_with Kg g) :
  lipschitz_with (max Kf Kg) (λ x, (f x, g x)) :=
begin
  assume x y,
  rw [ennreal.coe_mono.map_max, prod.edist_eq, ennreal.max_mul],
  exact max_le_max (hf x y) (hg x y)
end

protected lemma uncurry {f : α → β → γ} {Kα Kβ : ℝ≥0} (hα : ∀ b, lipschitz_with Kα (λ a, f a b))
  (hβ : ∀ a, lipschitz_with Kβ (f a)) :
  lipschitz_with (Kα + Kβ) (function.uncurry f) :=
begin
  rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
  simp only [function.uncurry, ennreal.coe_add, add_mul],
  apply le_trans (edist_triangle _ (f a₂ b₁) _),
  exact add_le_add (le_trans (hα _ _ _) $ ennreal.mul_left_mono $ le_max_left _ _)
    (le_trans (hβ _ _ _) $ ennreal.mul_left_mono $ le_max_right _ _)
end

protected lemma iterate {f : α → α} (hf : lipschitz_with K f) :
  ∀n, lipschitz_with (K ^ n) (f^[n])
| 0       := lipschitz_with.id
| (n + 1) := by rw [pow_succ']; exact (iterate n).comp hf

lemma edist_iterate_succ_le_geometric {f : α → α} (hf : lipschitz_with K f) (x n) :
  edist (f^[n] x) (f^[n + 1] x) ≤ edist x (f x) * K ^ n :=
begin
  rw [iterate_succ, mul_comm],
  simpa only [ennreal.coe_pow] using (hf.iterate n) x (f x)
end

open category_theory

protected lemma mul {f g : End α} {Kf Kg} (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf * Kg) (f * g : End α) :=
hf.comp hg

/-- The product of a list of Lipschitz continuous endomorphisms is a Lipschitz continuous
endomorphism. -/
protected lemma list_prod (f : ι → End α) (K : ι → ℝ≥0) (h : ∀ i, lipschitz_with (K i) (f i)) :
  ∀ l : list ι, lipschitz_with (l.map K).prod (l.map f).prod
| [] := by simp [types_id, lipschitz_with.id]
| (i :: l) := by { simp only [list.map_cons, list.prod_cons], exact (h i).mul (list_prod l) }

protected lemma pow {f : End α} {K} (h : lipschitz_with K f) :
  ∀ n : ℕ, lipschitz_with (K^n) (f^n : End α)
| 0       := lipschitz_with.id
| (n + 1) := h.mul (pow n)

end emetric

section metric

variables [metric_space α] [metric_space β] [metric_space γ] {K : ℝ≥0}

protected lemma of_dist_le' {f : α → β} {K : ℝ} (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
  lipschitz_with (nnreal.of_real K) f :=
of_dist_le_mul $ λ x y, le_trans (h x y) $
  mul_le_mul_of_nonneg_right (nnreal.le_coe_of_real K) dist_nonneg

protected lemma mk_one {f : α → β} (h : ∀ x y, dist (f x) (f y) ≤ dist x y) :
  lipschitz_with 1 f :=
of_dist_le_mul $ by simpa only [nnreal.coe_one, one_mul] using h

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected lemma of_le_add_mul' {f : α → ℝ} (K : ℝ) (h : ∀x y, f x ≤ f y + K * dist x y) :
  lipschitz_with (nnreal.of_real K) f :=
have I : ∀ x y, f x - f y ≤ K * dist x y,
  from assume x y, sub_le_iff_le_add'.2 (h x y),
lipschitz_with.of_dist_le' $
assume x y,
abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected lemma of_le_add_mul {f : α → ℝ} (K : ℝ≥0) (h : ∀x y, f x ≤ f y + K * dist x y) :
  lipschitz_with K f :=
by simpa only [nnreal.of_real_coe] using lipschitz_with.of_le_add_mul' K h

protected lemma of_le_add {f : α → ℝ} (h : ∀ x y, f x ≤ f y + dist x y) :
  lipschitz_with 1 f :=
lipschitz_with.of_le_add_mul 1 $ by simpa only [nnreal.coe_one, one_mul]

protected lemma le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : lipschitz_with K f) (x y) :
  f x ≤ f y + K * dist x y :=
sub_le_iff_le_add'.1 $ le_trans (le_abs_self _) $ h.dist_le_mul x y

protected lemma iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
  lipschitz_with K f ↔ ∀ x y, f x ≤ f y + K * dist x y :=
⟨lipschitz_with.le_add_mul, lipschitz_with.of_le_add_mul K⟩

lemma nndist_le {f : α → β} (hf : lipschitz_with K f) (x y : α) :
  nndist (f x) (f y) ≤ K * nndist x y :=
hf.dist_le_mul x y

lemma diam_image_le {f : α → β} (hf : lipschitz_with K f) (s : set α) (hs : metric.bounded s) :
  metric.diam (f '' s) ≤ K * metric.diam s :=
begin
  apply metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg metric.diam_nonneg),
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
  calc dist (f x) (f y) ≤ ↑K * dist x y      : hf.dist_le_mul x y
                    ... ≤ ↑K * metric.diam s :
    mul_le_mul_of_nonneg_left (metric.dist_le_diam_of_mem hs hx hy) K.2
end

protected lemma dist_left (y : α) : lipschitz_with 1 (λ x, dist x y) :=
lipschitz_with.of_le_add $ assume x z, by { rw [add_comm], apply dist_triangle }

protected lemma dist_right (x : α) : lipschitz_with 1 (dist x) :=
lipschitz_with.of_le_add $ assume y z, dist_triangle_right _ _ _

protected lemma dist : lipschitz_with 2 (function.uncurry $ @dist α _) :=
lipschitz_with.uncurry lipschitz_with.dist_left lipschitz_with.dist_right

lemma dist_iterate_succ_le_geometric {f : α → α} (hf : lipschitz_with K f) (x n) :
  dist (f^[n] x) (f^[n + 1] x) ≤ dist x (f x) * K ^ n :=
begin
  rw [iterate_succ, mul_comm],
  simpa only [nnreal.coe_pow] using (hf.iterate n).dist_le_mul x (f x)
end

end metric

end lipschitz_with

namespace lipschitz_on_with

variables [emetric_space α] [emetric_space β] [emetric_space γ] {K : ℝ≥0} {s : set α} {f : α → β}

protected lemma uniform_continuous_on (hf : lipschitz_on_with K f s) : uniform_continuous_on f s :=
uniform_continuous_on_iff_restrict.mpr (lipschitz_on_with_iff_restrict.mp hf).uniform_continuous

protected lemma continuous_on (hf : lipschitz_on_with K f s) : continuous_on f s :=
hf.uniform_continuous_on.continuous_on

end lipschitz_on_with

open metric

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
lemma continuous_at_of_locally_lipschitz [metric_space α] [metric_space β] {f : α → β} {x : α}
  {r : ℝ} (hr : 0 < r) (K : ℝ) (h : ∀y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) :
  continuous_at f x :=
begin
  refine (nhds_basis_ball.tendsto_iff nhds_basis_closed_ball).2
    (λε εpos, ⟨min r (ε / max K 1), _, λ y hy, _⟩),
  { simp [hr, div_pos εpos, zero_lt_one] },
  have A : max K 1 ≠ 0 := ne_of_gt (lt_max_iff.2 (or.inr zero_lt_one)),
  calc dist (f y) (f x)
    ≤ K * dist y x : h y (lt_of_lt_of_le hy (min_le_left _ _))
    ... ≤ max K 1 * dist y x : mul_le_mul_of_nonneg_right (le_max_left K 1) dist_nonneg
    ... ≤ max K 1 * (ε / max K 1) :
      mul_le_mul_of_nonneg_left (le_of_lt (lt_of_lt_of_le hy (min_le_right _ _)))
        (le_trans zero_le_one (le_max_right K 1))
    ... = ε : mul_div_cancel' _ A
end
