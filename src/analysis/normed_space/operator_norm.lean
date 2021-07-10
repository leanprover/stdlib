/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import linear_algebra.finite_dimensional
import analysis.normed_space.linear_isometry
import analysis.normed_space.riesz_lemma
import analysis.normed_space.normed_group_hom
import analysis.asymptotics.asymptotics
import algebra.algebra.tower
import data.equiv.transfer_instance

/-!
# Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous linear maps between normed spaces, and prove
its basic properties. In particular, show that this space is itself a normed space.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory for `semi_normed_space` and we specialize to `normed_space` at the end.
-/

noncomputable theory
open_locale classical nnreal topological_space

variables {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*}

section semi_normed

variables [semi_normed_group E] [semi_normed_group F] [semi_normed_group G]

open metric continuous_linear_map

section normed_field
/-! Most statements in this file require the field to be non-discrete,
as this is necessary to deduce an inequality `∥f x∥ ≤ C ∥x∥` from the continuity of f.
However, the other direction always holds.
In this section, we just assume that `𝕜` is a normed field.
In the remainder of the file, it will be non-discrete. -/

variables [normed_field 𝕜] [semi_normed_space 𝕜 E] [semi_normed_space 𝕜 F] (f : E →ₗ[𝕜] F)

lemma linear_map.lipschitz_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  lipschitz_with (real.to_nnreal C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

theorem linear_map.antilipschitz_of_bound {K : ℝ≥0} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  antilipschitz_with K f :=
antilipschitz_with.of_le_mul_dist $
λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

lemma linear_map.bound_of_antilipschitz {K : ℝ≥0} (h : antilipschitz_with K f) (x) :
  ∥x∥ ≤ K * ∥f x∥ :=
by simpa only [dist_zero_right, f.map_zero] using h.le_mul_dist x 0

lemma linear_map.uniform_continuous_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  uniform_continuous f :=
(f.lipschitz_of_bound C h).uniform_continuous

lemma linear_map.continuous_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  continuous f :=
(f.lipschitz_of_bound C h).continuous

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) : E →L[𝕜] F :=
⟨f, linear_map.continuous_of_bound f C h⟩

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `linear_map.to_continuous_linear_map`. -/
def linear_map.to_continuous_linear_map₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
f.mk_continuous (∥f 1∥) $ λ x, le_of_eq $
by { conv_lhs { rw ← mul_one x }, rw [← smul_eq_mul, f.map_smul, norm_smul, mul_comm] }

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous_of_exists_bound (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) : E →L[𝕜] F :=
⟨f, let ⟨C, hC⟩ := h in linear_map.continuous_of_bound f C hC⟩

lemma continuous_of_linear_of_bound {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
  (h_smul : ∀ (c : 𝕜) x, f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ∥f x∥ ≤ C*∥x∥) :
  continuous f :=
let φ : E →ₗ[𝕜] F := { to_fun := f, map_add' := h_add, map_smul' := h_smul } in
φ.continuous_of_bound C h_bound

@[simp, norm_cast] lemma linear_map.mk_continuous_coe (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ((f.mk_continuous C h) : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_apply (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) (x : E) :
  f.mk_continuous C h x = f x := rfl

@[simp, norm_cast] lemma linear_map.mk_continuous_of_exists_bound_coe
  (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ((f.mk_continuous_of_exists_bound h) : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_of_exists_bound_apply (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) (x : E) :
  f.mk_continuous_of_exists_bound h x = f x := rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_coe (f : 𝕜 →ₗ[𝕜] E) :
  (f.to_continuous_linear_map₁ : 𝕜 →ₗ[𝕜] E) = f :=
rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
  f.to_continuous_linear_map₁ x = f x :=
rfl

end normed_field

variables [nondiscrete_normed_field 𝕜] [semi_normed_space 𝕜 E] [semi_normed_space 𝕜 F]
[semi_normed_space 𝕜 G] (c : 𝕜) (f g : E →L[𝕜] F) (h : F →L[𝕜] G) (x y z : E)
include 𝕜

lemma linear_map.bound_of_shell_semi_normed (f : E →ₗ[𝕜] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
  (hc : 1 < ∥c∥) (hf : ∀ x, ε / ∥c∥ ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C * ∥x∥) {x : E} (hx : ∥x∥ ≠ 0) :
  ∥f x∥ ≤ C * ∥x∥ :=
begin
  rcases rescale_to_shell_semi_normed hc ε_pos hx with ⟨δ, hδ, δxle, leδx, δinv⟩,
  simpa only [f.map_smul, norm_smul, mul_left_comm C, mul_le_mul_left (norm_pos_iff.2 hδ)]
    using hf (δ • x) leδx δxle
end

/-- If `∥x∥ = 0` and `f` is continuous then `∥f x∥ = 0`. -/
lemma norm_image_of_norm_zero {f : E →ₗ[𝕜] F} (hf : continuous f) {x : E} (hx : ∥x∥ = 0) :
  ∥f x∥ = 0 :=
begin
  refine le_antisymm (le_of_forall_pos_le_add (λ ε hε, _)) (norm_nonneg (f x)),
  rcases normed_group.tendsto_nhds_nhds.1 (hf.tendsto 0) ε hε with ⟨δ, δ_pos, hδ⟩,
  replace hδ := hδ x,
  rw [sub_zero, hx] at hδ,
  replace hδ := le_of_lt (hδ δ_pos),
  rw [linear_map.map_zero, sub_zero] at hδ,
  rwa [zero_add]
end

/-- A continuous linear map between seminormed spaces is bounded when the field is nondiscrete. The
continuity ensures boundedness on a ball of some radius `ε`. The nondiscreteness is then used to
rescale any element into an element of norm in `[ε/C, ε]`, whose image has a controlled norm. The
norm control for the original element follows by rescaling. -/
lemma linear_map.bound_of_continuous (f : E →ₗ[𝕜] F) (hf : continuous f) :
  ∃ C, 0 < C ∧ (∀ x : E, ∥f x∥ ≤ C * ∥x∥) :=
begin
  rcases normed_group.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  simp only [sub_zero, f.map_zero] at hε,
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have : 0 < ∥c∥ / ε, from div_pos (zero_lt_one.trans hc) ε_pos,
  refine ⟨∥c∥ / ε, this, λ x, _⟩,
  by_cases hx : ∥x∥ = 0,
  { rw [hx, mul_zero],
    exact le_of_eq (norm_image_of_norm_zero hf hx) },
  refine f.bound_of_shell_semi_normed ε_pos hc (λ x hle hlt, _) hx,
  refine (hε _ hlt).le.trans _,
  rwa [← div_le_iff' this, one_div_div]
end

namespace continuous_linear_map

theorem bound : ∃ C, 0 < C ∧ (∀ x : E, ∥f x∥ ≤ C * ∥x∥) :=
f.to_linear_map.bound_of_continuous f.2

section
open asymptotics filter

theorem is_O_id (l : filter E) : is_O f (λ x, x) l :=
let ⟨M, hMp, hM⟩ := f.bound in is_O_of_le' l hM

theorem is_O_comp {α : Type*} (g : F →L[𝕜] G) (f : α → F) (l : filter α) :
  is_O (λ x', g (f x')) f l :=
(g.is_O_id ⊤).comp_tendsto le_top

theorem is_O_sub (f : E →L[𝕜] F) (l : filter E) (x : E) :
  is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
f.is_O_comp _ l

/-- A linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def of_homothety (f : E →ₗ[𝕜] F) (a : ℝ) (hf : ∀x, ∥f x∥ = a * ∥x∥) : E →L[𝕜] F :=
f.mk_continuous a (λ x, le_of_eq (hf x))

variable (𝕜)

lemma to_span_singleton_homothety (x : E) (c : 𝕜) :
  ∥linear_map.to_span_singleton 𝕜 E x c∥ = ∥x∥ * ∥c∥ :=
by {rw mul_comm, exact norm_smul _ _}

/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `E` to the span of `x`.-/
def to_span_singleton (x : E) : 𝕜 →L[𝕜] E :=
of_homothety (linear_map.to_span_singleton 𝕜 E x) ∥x∥ (to_span_singleton_homothety 𝕜 x)

end

section op_norm
open set real

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def op_norm := Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥}
instance has_op_norm : has_norm (E →L[𝕜] F) := ⟨op_norm⟩

lemma norm_def : ∥f∥ = Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥} := rfl

-- So that invocations of `real.Inf_le` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : E →L[𝕜] F} :
  ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : E →L[𝕜] F} :
  bdd_below { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
begin
  obtain ⟨C, Cpos, hC⟩ := f.bound,
  replace hC := hC x,
  by_cases h : ∥x∥ = 0,
  { rwa [h, mul_zero] at ⊢ hC },
  have hlt : 0 < ∥x∥ := lt_of_le_of_ne (norm_nonneg x) (ne.symm h),
  exact  (div_le_iff hlt).mp ((real.le_Inf _ bounds_nonempty bounds_bdd_below).2 (λ c ⟨_, hc⟩,
    (div_le_iff hlt).mpr $ by { apply hc })),
end

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥ * c :=
le_trans (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

theorem le_of_op_norm_le {c : ℝ} (h : ∥f∥ ≤ c) (x : E) : ∥f x∥ ≤ c * ∥x∥ :=
(f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : lipschitz_with ⟨∥f∥, op_norm_nonneg f⟩ f :=
lipschitz_with.of_dist_le_mul $ λ x y,
  by { rw [dist_eq_norm, dist_eq_norm, ←map_sub], apply le_op_norm }

lemma ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)

/-- The image of the unit ball under a continuous linear map is bounded. -/
lemma unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
mul_one ∥f∥ ▸ f.le_op_norm_of_le

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

theorem op_norm_le_of_lipschitz {f : E →L[𝕜] F} {K : ℝ≥0} (hf : lipschitz_with K f) :
  ∥f∥ ≤ K :=
f.op_norm_le_bound K.2 $ λ x, by simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

lemma op_norm_le_of_shell {f : E →L[𝕜] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  {c : 𝕜} (hc : 1 < ∥c∥) (hf : ∀ x, ε / ∥c∥ ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C * ∥x∥) :
  ∥f∥ ≤ C :=
begin
  refine f.op_norm_le_bound hC (λ x, _),
  by_cases hx : ∥x∥ = 0,
  { rw [hx, mul_zero],
    exact le_of_eq (norm_image_of_norm_zero f.2 hx) },
  exact linear_map.bound_of_shell_semi_normed f ε_pos hc hf hx
end

lemma op_norm_le_of_ball {f : E →L[𝕜] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  (hf : ∀ x ∈ ball (0 : E) ε, ∥f x∥ ≤ C * ∥x∥) : ∥f∥ ≤ C :=
begin
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  refine op_norm_le_of_shell ε_pos hC hc (λ x _ hx, hf x _),
  rwa ball_0_eq
end

lemma op_norm_le_of_nhds_zero {f : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
  (hf : ∀ᶠ x in 𝓝 (0 : E), ∥f x∥ ≤ C * ∥x∥) : ∥f∥ ≤ C :=
let ⟨ε, ε0, hε⟩ := metric.eventually_nhds_iff_ball.1 hf in op_norm_le_of_ball ε0 hC hε

lemma op_norm_le_of_shell' {f : E →L[𝕜] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  {c : 𝕜} (hc : ∥c∥ < 1) (hf : ∀ x, ε * ∥c∥ ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C * ∥x∥) :
  ∥f∥ ≤ C :=
begin
  by_cases h0 : c = 0,
  { refine op_norm_le_of_ball ε_pos hC (λ x hx, hf x _ _),
    { simp [h0] },
    { rwa ball_0_eq at hx } },
  { rw [← inv_inv' c, normed_field.norm_inv,
      inv_lt_one_iff_of_pos (norm_pos_iff.2 $ inv_ne_zero h0)] at hc,
    refine op_norm_le_of_shell ε_pos hC hc _,
    rwa [normed_field.norm_inv, div_eq_mul_inv, inv_inv'] }
end

lemma op_norm_eq_of_bounds {φ : E →L[𝕜] F} {M : ℝ} (M_nonneg : 0 ≤ M)
  (h_above : ∀ x, ∥φ x∥ ≤ M*∥x∥) (h_below : ∀ N ≥ 0, (∀ x, ∥φ x∥ ≤ N*∥x∥) → M ≤ N) :
  ∥φ∥ = M :=
le_antisymm (φ.op_norm_le_bound M_nonneg h_above)
  ((le_cInf_iff continuous_linear_map.bounds_bdd_below ⟨M, M_nonneg, h_above⟩).mpr $
   λ N ⟨N_nonneg, hN⟩, h_below N N_nonneg hN)

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
show ∥f + g∥ ≤ (coe : ℝ≥0 → ℝ) (⟨_, f.op_norm_nonneg⟩ + ⟨_, g.op_norm_nonneg⟩),
from op_norm_le_of_lipschitz (f.lipschitz.add g.lipschitz)

/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ∥(0 : E →L[𝕜] F)∥ = 0 :=
le_antisymm (real.Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul], exact norm_zero })⟩)
    (op_norm_nonneg _)

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
lemma norm_id_le : ∥id 𝕜 E∥ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λx, by simp)

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
lemma norm_id_of_nontrivial_seminorm (h : ∃ (x : E), ∥x∥ ≠ 0 ) : ∥id 𝕜 E∥ = 1 :=
le_antisymm norm_id_le $ let ⟨x, hx⟩ := h in
have _ := (id 𝕜 E).ratio_le_op_norm x,
by rwa [id_apply, div_self hx] at this

lemma op_norm_smul_le {𝕜' : Type*} [normed_field 𝕜'] [semi_normed_space 𝕜' F]
  [smul_comm_class 𝕜 𝕜' F] (c : 𝕜') (f : E →L[𝕜] F) : ∥c • f∥ ≤ ∥c∥ * ∥f∥ :=
((c • f).op_norm_le_bound
  (mul_nonneg (norm_nonneg _) (op_norm_nonneg _)) (λ _,
  begin
    erw [norm_smul, mul_assoc],
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
  end))

lemma op_norm_neg : ∥-f∥ = ∥f∥ := by simp only [norm_def, neg_apply, norm_neg]

/-- Continuous linear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance to_semi_normed_group : semi_normed_group (E →L[𝕜] F) :=
semi_normed_group.of_core _ ⟨op_norm_zero, op_norm_add_le, op_norm_neg⟩

instance to_semi_normed_space {𝕜' : Type*} [normed_field 𝕜'] [semi_normed_space 𝕜' F]
  [smul_comm_class 𝕜 𝕜' F] : semi_normed_space 𝕜' (E →L[𝕜] F) :=
⟨op_norm_smul_le⟩

/-- The operator norm is submultiplicative. -/
lemma op_norm_comp_le (f : E →L[𝕜] F) : ∥h.comp f∥ ≤ ∥h∥ * ∥f∥ :=
(Inf_le _ bounds_bdd_below
  ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x,
    by { rw mul_assoc, exact h.le_op_norm_of_le (f.le_op_norm x) } ⟩)

/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance to_semi_normed_ring : semi_normed_ring (E →L[𝕜] E) :=
{ norm_mul := op_norm_comp_le,
  .. continuous_linear_map.to_semi_normed_group }

theorem le_op_norm₂ (f : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
  ∥f x y∥ ≤ ∥f∥ * ∥x∥ * ∥y∥ :=
(f x).le_of_op_norm_le (f.le_op_norm x) y

theorem op_norm_le_bound₂ (f : E →L[𝕜] F →L[𝕜] G) {C : ℝ} (h0 : 0 ≤ C)
  (hC : ∀ x y, ∥f x y∥ ≤ C * ∥x∥ * ∥y∥) :
  ∥f∥ ≤ C :=
f.op_norm_le_bound h0 $ λ x,
  (f x).op_norm_le_bound (mul_nonneg h0 (norm_nonneg _)) $ hC x

@[simp] lemma op_norm_prod (f : E →L[𝕜] F) (g : E →L[𝕜] G) : ∥f.prod g∥ = ∥(f, g)∥ :=
le_antisymm
  (op_norm_le_bound _ (norm_nonneg _) $ λ x,
    by simpa only [prod_apply, prod.semi_norm_def, max_mul_of_nonneg, norm_nonneg]
      using max_le_max (le_op_norm f x) (le_op_norm g x)) $
  max_le
    (op_norm_le_bound _ (norm_nonneg _) $ λ x, (le_max_left _ _).trans ((f.prod g).le_op_norm x))
    (op_norm_le_bound _ (norm_nonneg _) $ λ x, (le_max_right _ _).trans ((f.prod g).le_op_norm x))

/-- `continuous_linear_map.prod` as a `linear_isometry_equiv`. -/
def prodₗᵢ (R : Type*) [ring R] [topological_space R] [module R F] [module R G]
  [has_continuous_smul R F] [has_continuous_smul R G]
  [smul_comm_class 𝕜 R F] [smul_comm_class 𝕜 R G] :
  (E →L[𝕜] F) × (E →L[𝕜] G) ≃ₗᵢ[R] (E →L[𝕜] F × G) :=
⟨prodₗ R, λ ⟨f, g⟩, op_norm_prod f g⟩

/-- A continuous linear map is automatically uniformly continuous. -/
protected theorem uniform_continuous : uniform_continuous f :=
f.lipschitz.uniform_continuous

@[simp, nontriviality] lemma op_norm_subsingleton [subsingleton E] : ∥f∥ = 0 :=
begin
  refine le_antisymm _ (norm_nonneg _),
  apply op_norm_le_bound _ rfl.ge,
  intros x,
  simp [subsingleton.elim x 0]
end

/-- A continuous linear map is an isometry if and only if it preserves the norm. -/
lemma isometry_iff_norm : isometry f ↔ ∀x, ∥f x∥ = ∥x∥ :=
f.to_linear_map.to_add_monoid_hom.isometry_iff_norm

end op_norm

end continuous_linear_map

namespace linear_isometry

lemma norm_to_continuous_linear_map_le (f : E →ₗᵢ[𝕜] F) :
  ∥f.to_continuous_linear_map∥ ≤ 1 :=
f.to_continuous_linear_map.op_norm_le_bound zero_le_one $ λ x, by simp

end linear_isometry

namespace linear_map

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
lemma mk_continuous_norm_le (f : E →ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_continuous C h∥ ≤ C :=
continuous_linear_map.op_norm_le_bound _ hC h

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
lemma mk_continuous_norm_le' (f : E →ₗ[𝕜] F) {C : ℝ} (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_continuous C h∥ ≤ max C 0 :=
continuous_linear_map.op_norm_le_bound _ (le_max_right _ _) $ λ x, (h x).trans $
  mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`linear_map.mk₂`. -/
def mk_continuous₂ (f : E →ₗ[𝕜] F →ₗ[𝕜] G) (C : ℝ)
  (hC : ∀ x y, ∥f x y∥ ≤ C * ∥x∥ * ∥y∥) :
  E →L[𝕜] F →L[𝕜] G :=
linear_map.mk_continuous
  { to_fun := λ x, (f x).mk_continuous (C * ∥x∥) (hC x),
    map_add' := λ x y, by { ext z, simp },
    map_smul' := λ c x, by { ext z, simp } }
  (max C 0) $ λ x, (mk_continuous_norm_le' _ _).trans_eq $
    by rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

@[simp] lemma mk_continuous₂_apply (f : E →ₗ[𝕜] F →ₗ[𝕜] G) {C : ℝ}
  (hC : ∀ x y, ∥f x y∥ ≤ C * ∥x∥ * ∥y∥) (x : E) (y : F) :
  f.mk_continuous₂ C hC x y = f x y :=
rfl

lemma mk_continuous₂_norm_le' (f : E →ₗ[𝕜] F →ₗ[𝕜] G) {C : ℝ}
  (hC : ∀ x y, ∥f x y∥ ≤ C * ∥x∥ * ∥y∥) :
  ∥f.mk_continuous₂ C hC∥ ≤ max C 0 :=
mk_continuous_norm_le _ (le_max_iff.2 $ or.inr le_rfl) _

lemma mk_continuous₂_norm_le (f : E →ₗ[𝕜] F →ₗ[𝕜] G) {C : ℝ} (h0 : 0 ≤ C)
  (hC : ∀ x y, ∥f x y∥ ≤ C * ∥x∥ * ∥y∥) :
  ∥f.mk_continuous₂ C hC∥ ≤ C :=
(f.mk_continuous₂_norm_le' hC).trans_eq $ max_eq_left h0

end linear_map

namespace continuous_linear_map

/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `linear_isometry_equiv`, see
`continuous_linear_map.flipL`. -/
def flip (f : E →L[𝕜] F →L[𝕜] G) : F →L[𝕜] E →L[𝕜] G :=
linear_map.mk_continuous₂
  (linear_map.mk₂ 𝕜 (λ y x, f x y) (λ x y z, (f z).map_add x y) (λ c y x, (f x).map_smul c y)
    (λ z x y, by rw [f.map_add, add_apply]) (λ c y x, by rw [map_smul, smul_apply]))
  ∥f∥ (λ y x, (f.le_op_norm₂ x y).trans_eq $ by rw mul_right_comm)

private lemma le_norm_flip (f : E →L[𝕜] F →L[𝕜] G) : ∥f∥ ≤ ∥flip f∥ :=
f.op_norm_le_bound₂ (norm_nonneg _) $ λ x y,
  by { rw mul_right_comm, exact (flip f).le_op_norm₂ y x }

@[simp] lemma flip_apply (f : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) : f.flip y x = f x y := rfl

@[simp] lemma flip_flip (f : E →L[𝕜] F →L[𝕜] G) :
  f.flip.flip = f :=
by { ext, refl }

@[simp] lemma op_norm_flip (f : E →L[𝕜] F →L[𝕜] G) :
  ∥f.flip∥ = ∥f∥ :=
le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)

@[simp] lemma flip_add (f g : E →L[𝕜] F →L[𝕜] G) :
  (f + g).flip = f.flip + g.flip :=
rfl

@[simp] lemma flip_smul (c : 𝕜) (f : E →L[𝕜] F →L[𝕜] G) :
  (c • f).flip = c • f.flip :=
rfl

variables (𝕜 E F G)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `linear_isometry_equiv`.
For an unbundled version see `continuous_linear_map.flip`. -/
def flipₗᵢ : (E →L[𝕜] F →L[𝕜] G) ≃ₗᵢ[𝕜] (F →L[𝕜] E →L[𝕜] G) :=
{ to_fun := flip,
  inv_fun := flip,
  map_add' := flip_add,
  map_smul' := flip_smul,
  left_inv := flip_flip,
  right_inv := flip_flip,
  norm_map' := op_norm_flip }

variables {𝕜 E F G}

@[simp] lemma flipₗᵢ_symm : (flipₗᵢ 𝕜 E F G).symm = flipₗᵢ 𝕜 F E G := rfl

@[simp] lemma coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E F G) = flip := rfl

variables (𝕜 F)

/-- The continuous linear map obtained by applying a continuous linear map at a given vector.

This is the continuous version of `linear_map.applyₗ`. -/
def apply : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F := flip (id 𝕜 (E →L[𝕜] F))

variables {𝕜 F}

@[simp] lemma apply_apply (v : E) (f : E →L[𝕜] F) : apply 𝕜 F v f = f v := rfl

variables (𝕜 E F G)

/-- Composition of continuous linear maps as a continuous bilinear map. -/
def compL : (F →L[𝕜] G) →L[𝕜] (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] G) :=
linear_map.mk_continuous₂
  (linear_map.mk₂ _ comp add_comp smul_comp comp_add (λ c f g, comp_smul _ _ _))
  1 $ λ f g, by simpa only [one_mul] using op_norm_comp_le f g

variables {𝕜 E F G}

@[simp] lemma compL_apply (f : F →L[𝕜] G) (g : E →L[𝕜] F) : compL 𝕜 E F G f g = f.comp g := rfl

section multiplication_linear
variables (𝕜) (𝕜' : Type*) [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜']

/-- Left multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps. -/
def lmulₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
{ to_linear_map := (algebra.lmul 𝕜 𝕜').to_linear_map.mk_continuous₂ 1 $
    λ x y, by simpa using norm_mul_le x y,
  norm_map' := λ x, le_antisymm
    (op_norm_le_bound _ (norm_nonneg x) (norm_mul_le x))
    (by { convert ratio_le_op_norm _ (1 : 𝕜'), simp [normed_algebra.norm_one 𝕜 𝕜'] }) }

/-- Left multiplication in a normed algebra as a continuous bilinear map. -/
def lmul : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
(lmulₗᵢ 𝕜 𝕜').to_continuous_linear_map

@[simp] lemma lmul_apply (x y : 𝕜') : lmul 𝕜 𝕜' x y = x * y := rfl

@[simp] lemma coe_lmulₗᵢ : ⇑(lmulₗᵢ 𝕜 𝕜') = lmul 𝕜 𝕜' := rfl

@[simp] lemma op_norm_lmul_apply (x : 𝕜') : ∥lmul 𝕜 𝕜' x∥ = ∥x∥ :=
(lmulₗᵢ 𝕜 𝕜').norm_map x

/-- Right-multiplication in a normed algebra, considered as a continuous linear map. -/
def lmul_right : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' := (lmul 𝕜 𝕜').flip

@[simp] lemma lmul_right_apply (x y : 𝕜') : lmul_right 𝕜 𝕜' x y = y * x := rfl

@[simp] lemma op_norm_lmul_right_apply (x : 𝕜') : ∥lmul_right 𝕜 𝕜' x∥ = ∥x∥ :=
le_antisymm
  (op_norm_le_bound _ (norm_nonneg x) (λ y, (norm_mul_le y x).trans_eq (mul_comm _ _)))
  (by { convert ratio_le_op_norm _ (1 : 𝕜'), simp [normed_algebra.norm_one 𝕜 𝕜'] })

/-- Right-multiplication in a normed algebra, considered as a linear isometry to the space of
continuous linear maps. -/
def lmul_rightₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
{ to_linear_map := lmul_right 𝕜 𝕜',
  norm_map' := op_norm_lmul_right_apply 𝕜 𝕜' }

@[simp] lemma coe_lmul_rightₗᵢ : ⇑(lmul_rightₗᵢ 𝕜 𝕜') = lmul_right 𝕜 𝕜' := rfl

/-- Simultaneous left- and right-multiplication in a normed algebra, considered as a continuous
trilinear map. -/
def lmul_left_right : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
((compL 𝕜 𝕜' 𝕜' 𝕜').comp (lmul_right 𝕜 𝕜')).flip.comp (lmul 𝕜 𝕜')

@[simp] lemma lmul_left_right_apply (x y z : 𝕜') :
  lmul_left_right 𝕜 𝕜' x y z = x * z * y := rfl

lemma op_norm_lmul_left_right_apply_apply_le (x y : 𝕜') :
  ∥lmul_left_right 𝕜 𝕜' x y∥ ≤ ∥x∥ * ∥y∥ :=
(op_norm_comp_le _ _).trans_eq $ by simp [mul_comm]

lemma op_norm_lmul_left_right_apply_le (x : 𝕜') :
  ∥lmul_left_right 𝕜 𝕜' x∥ ≤ ∥x∥ :=
op_norm_le_bound _ (norm_nonneg x) (op_norm_lmul_left_right_apply_apply_le 𝕜 𝕜' x)

lemma op_norm_lmul_left_right_le :
  ∥lmul_left_right 𝕜 𝕜'∥ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λ x, (one_mul ∥x∥).symm ▸ op_norm_lmul_left_right_apply_le 𝕜 𝕜' x)

end multiplication_linear

section smul_linear

variables (𝕜) (𝕜' : Type*) [normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [semi_normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E]

/-- Scalar multiplication as a continuous bilinear map. -/
def lsmul : 𝕜' →L[𝕜] E →L[𝕜] E :=
((algebra.lsmul 𝕜 E).to_linear_map : 𝕜' →ₗ[𝕜] E →ₗ[𝕜] E).mk_continuous₂ 1 $
  λ c x, by simpa only [one_mul] using (norm_smul c x).le

end smul_linear

section restrict_scalars

variables {𝕜' : Type*} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜' 𝕜]
variables [semi_normed_space 𝕜' E] [is_scalar_tower 𝕜' 𝕜 E]
variables [semi_normed_space 𝕜' F] [is_scalar_tower 𝕜' 𝕜 F]

@[simp] lemma norm_restrict_scalars (f : E →L[𝕜] F) : ∥f.restrict_scalars 𝕜'∥ = ∥f∥ :=
le_antisymm (op_norm_le_bound _ (norm_nonneg _) $ λ x, f.le_op_norm x)
  (op_norm_le_bound _ (norm_nonneg _) $ λ x, f.le_op_norm x)

variables (𝕜 E F 𝕜') (𝕜'' : Type*) [ring 𝕜''] [topological_space 𝕜''] [module 𝕜'' F]
  [has_continuous_smul 𝕜'' F] [smul_comm_class 𝕜 𝕜'' F] [smul_comm_class 𝕜' 𝕜'' F]

/-- `continuous_linear_map.restrict_scalars` as a `linear_isometry`. -/
def restrict_scalars_isometry : (E →L[𝕜] F) →ₗᵢ[𝕜''] (E →L[𝕜'] F) :=
⟨restrict_scalarsₗ 𝕜 E F 𝕜' 𝕜'', norm_restrict_scalars⟩

variables {𝕜 E F 𝕜' 𝕜''}

@[simp] lemma coe_restrict_scalars_isometry :
  ⇑(restrict_scalars_isometry 𝕜 E F 𝕜' 𝕜'') = restrict_scalars 𝕜' :=
rfl

@[simp] lemma restrict_scalars_isometry_to_linear_map :
  (restrict_scalars_isometry 𝕜 E F 𝕜' 𝕜'').to_linear_map = restrict_scalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
rfl

variables (𝕜 E F 𝕜' 𝕜'')

/-- `continuous_linear_map.restrict_scalars` as a `continuous_linear_map`. -/
def restrict_scalarsL : (E →L[𝕜] F) →L[𝕜''] (E →L[𝕜'] F) :=
(restrict_scalars_isometry 𝕜 E F 𝕜' 𝕜'').to_continuous_linear_map

variables {𝕜 E F 𝕜' 𝕜''}

@[simp] lemma coe_restrict_scalarsL :
  (restrict_scalarsL 𝕜 E F 𝕜' 𝕜'' : (E →L[𝕜] F) →ₗ[𝕜''] (E →L[𝕜'] F)) =
    restrict_scalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
rfl

@[simp] lemma coe_restrict_scalarsL' :
  ⇑(restrict_scalarsL 𝕜 E F 𝕜' 𝕜'') = restrict_scalars 𝕜' :=
rfl

end restrict_scalars

end continuous_linear_map

namespace submodule

lemma norm_subtypeL_le (K : submodule 𝕜 E) : ∥K.subtypeL∥ ≤ 1 :=
K.subtypeₗᵢ.norm_to_continuous_linear_map_le

end submodule

section has_sum

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we
-- don't have bundled continuous additive homomorphisms.

variables {ι R M M₂ : Type*} [semiring R] [add_comm_monoid M] [module R M]
  [add_comm_monoid M₂] [module R M₂] [topological_space M] [topological_space M₂]

omit 𝕜

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected lemma continuous_linear_map.has_sum {f : ι → M} (φ : M →L[R] M₂) {x : M}
  (hf : has_sum f x) :
  has_sum (λ (b:ι), φ (f b)) (φ x) :=
by simpa only using hf.map φ.to_linear_map.to_add_monoid_hom φ.continuous

alias continuous_linear_map.has_sum ← has_sum.mapL

protected lemma continuous_linear_map.summable {f : ι → M} (φ : M →L[R] M₂) (hf : summable f) :
  summable (λ b:ι, φ (f b)) :=
(hf.has_sum.mapL φ).summable

alias continuous_linear_map.summable ← summable.mapL

protected lemma continuous_linear_map.map_tsum [t2_space M₂] {f : ι → M}
  (φ : M →L[R] M₂) (hf : summable f) : φ (∑' z, f z) = ∑' z, φ (f z) :=
(hf.has_sum.mapL φ).tsum_eq.symm

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected lemma continuous_linear_equiv.has_sum {f : ι → M} (e : M ≃L[R] M₂) {y : M₂} :
  has_sum (λ (b:ι), e (f b)) y ↔ has_sum f (e.symm y) :=
⟨λ h, by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →L[R] M),
  λ h, by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →L[R] M₂).has_sum h⟩

protected lemma continuous_linear_equiv.summable {f : ι → M} (e : M ≃L[R] M₂) :
  summable (λ b:ι, e (f b)) ↔ summable f :=
⟨λ hf, (e.has_sum.1 hf.has_sum).summable, (e : M →L[R] M₂).summable⟩

lemma continuous_linear_equiv.tsum_eq_iff [t2_space M] [t2_space M₂] {f : ι → M}
  (e : M ≃L[R] M₂) {y : M₂} : ∑' z, e (f z) = y ↔ ∑' z, f z = e.symm y :=
begin
  by_cases hf : summable f,
  { exact ⟨λ h, (e.has_sum.mp ((e.summable.mpr hf).has_sum_iff.mpr h)).tsum_eq,
      λ h, (e.has_sum.mpr (hf.has_sum_iff.mpr h)).tsum_eq⟩ },
  { have hf' : ¬summable (λ z, e (f z)) := λ h, hf (e.summable.mp h),
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hf'],
    exact ⟨by { rintro rfl, simp }, λ H, by simpa using (congr_arg (λ z, e z) H)⟩ }
end

protected lemma continuous_linear_equiv.map_tsum [t2_space M] [t2_space M₂] {f : ι → M}
  (e : M ≃L[R] M₂) : e (∑' z, f z) = ∑' z, e (f z) :=
by { refine symm (e.tsum_eq_iff.mpr _), rw e.symm_apply_apply _ }

end has_sum

namespace continuous_linear_equiv

variables (e : E ≃L[𝕜] F)

protected lemma lipschitz : lipschitz_with (nnnorm (e : E →L[𝕜] F)) e :=
(e : E →L[𝕜] F).lipschitz

theorem is_O_comp {α : Type*} (f : α → E) (l : filter α) :
  asymptotics.is_O (λ x', e (f x')) f l :=
(e : E →L[𝕜] F).is_O_comp f l

theorem is_O_sub (l : filter E) (x : E) :
  asymptotics.is_O (λ x', e (x' - x)) (λ x', x' - x) l :=
(e : E →L[𝕜] F).is_O_sub l x

theorem is_O_comp_rev {α : Type*} (f : α → E) (l : filter α) :
  asymptotics.is_O f (λ x', e (f x')) l :=
(e.symm.is_O_comp _ l).congr_left $ λ _, e.symm_apply_apply _

theorem is_O_sub_rev (l : filter E) (x : E) :
  asymptotics.is_O (λ x', x' - x) (λ x', e (x' - x)) l :=
e.is_O_comp_rev _ _

lemma homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₗ[𝕜] F) :
  (∀ (x : E), ∥f x∥ = a * ∥x∥) → (∀ (y : F), ∥f.symm y∥ = a⁻¹ * ∥y∥) :=
begin
  intros hf y,
  calc ∥(f.symm) y∥ = a⁻¹ * (a * ∥ (f.symm) y∥) : _
  ... =  a⁻¹ * ∥f ((f.symm) y)∥ : by rw hf
  ... = a⁻¹ * ∥y∥ : by simp,
  rw [← mul_assoc, inv_mul_cancel (ne_of_lt ha).symm, one_mul],
end

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
def of_homothety (f : E ≃ₗ[𝕜] F) (a : ℝ) (ha : 0 < a) (hf : ∀x, ∥f x∥ = a * ∥x∥) : E ≃L[𝕜] F :=
{ to_linear_equiv := f,
  continuous_to_fun := f.to_linear_map.continuous_of_bound a (λ x, le_of_eq (hf x)),
  continuous_inv_fun := f.symm.to_linear_map.continuous_of_bound a⁻¹
    (λ x, le_of_eq (homothety_inverse a ha f hf x)) }

variable (𝕜)

lemma to_span_nonzero_singleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
  ∥linear_equiv.to_span_nonzero_singleton 𝕜 E x h c∥ = ∥x∥ * ∥c∥ :=
continuous_linear_map.to_span_singleton_homothety _ _ _

end continuous_linear_equiv

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def linear_equiv.to_continuous_linear_equiv_of_bounds (e : E ≃ₗ[𝕜] F) (C_to C_inv : ℝ)
  (h_to : ∀ x, ∥e x∥ ≤ C_to * ∥x∥) (h_inv : ∀ x : F, ∥e.symm x∥ ≤ C_inv * ∥x∥) : E ≃L[𝕜] F :=
{ to_linear_equiv := e,
  continuous_to_fun := e.to_linear_map.continuous_of_bound C_to h_to,
  continuous_inv_fun := e.symm.to_linear_map.continuous_of_bound C_inv h_inv }

namespace continuous_linear_map
variables (𝕜) (𝕜' : Type*) [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜']

variables {𝕜}

variables {E' F' : Type*} [semi_normed_group E'] [semi_normed_group F']
  [semi_normed_space 𝕜 E'] [semi_normed_space 𝕜 F']

/--
Compose a bilinear map `E →L[𝕜] F →L[𝕜] G` with two linear maps `E' →L[𝕜] E` and `F' →L[𝕜] F`.
-/
def bilinear_comp (f : E →L[𝕜] F →L[𝕜] G) (gE : E' →L[𝕜] E) (gF : F' →L[𝕜] F) :
  E' →L[𝕜] F' →L[𝕜] G :=
((f.comp gE).flip.comp gF).flip

@[simp] lemma bilinear_comp_apply (f : E →L[𝕜] F →L[𝕜] G) (gE : E' →L[𝕜] E) (gF : F' →L[𝕜] F)
  (x : E') (y : F') :
  f.bilinear_comp gE gF x y = f (gE x) (gF y) :=
rfl

/-- Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map. -/
def deriv₂ (f : E →L[𝕜] F →L[𝕜] G) : (E × F) →L[𝕜] (E × F) →L[𝕜] G :=
f.bilinear_comp (fst _ _ _) (snd _ _ _) + f.flip.bilinear_comp (snd _ _ _) (fst _ _ _)

@[simp] lemma coe_deriv₂ (f : E →L[𝕜] F →L[𝕜] G) (p : E × F) :
  ⇑(f.deriv₂ p) = λ q : E × F, f p.1 q.2 + f q.1 p.2 := rfl

lemma map_add₂ (f : E →L[𝕜] F →L[𝕜] G) (x x' : E) (y y' : F) :
  f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' :=
by simp only [map_add, add_apply, coe_deriv₂, add_assoc]

end continuous_linear_map

end semi_normed

section normed

variables [normed_group E] [normed_group F] [normed_group G]

open metric continuous_linear_map

section normed_field

variables [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (f : E →ₗ[𝕜] F)

lemma linear_map.continuous_iff_is_closed_ker {f : E →ₗ[𝕜] 𝕜} :
  continuous f ↔ is_closed (f.ker : set E) :=
begin
  -- the continuity of f obviously implies that its kernel is closed
  refine ⟨λh, (t1_space.t1 (0 : 𝕜)).preimage h, λh, _⟩,
  -- for the other direction, we assume that the kernel is closed
  by_cases hf : ∀x, x ∈ f.ker,
  { -- if `f = 0`, its continuity is obvious
    have : (f : E → 𝕜) = (λx, 0), by { ext x, simpa using hf x },
    rw this,
    exact continuous_const },
  { /- if `f` is not zero, we use an element `x₀ ∉ ker f` such that `∥x₀∥ ≤ 2 ∥x₀ - y∥` for all
    `y ∈ ker f`, given by Riesz's lemma, and prove that `2 ∥f x₀∥ / ∥x₀∥` gives a bound on the
    operator norm of `f`. For this, start from an arbitrary `x` and note that
    `y = x₀ - (f x₀ / f x) x` belongs to the kernel of `f`. Applying the above inequality to `x₀`
    and `y` readily gives the conclusion. -/
    push_neg at hf,
    let r : ℝ := (2 : ℝ)⁻¹,
    have : 0 ≤ r, by norm_num [r],
    have : r < 1, by norm_num [r],
    obtain ⟨x₀, x₀ker, h₀⟩ : ∃ (x₀ : E), x₀ ∉ f.ker ∧ ∀ y ∈ linear_map.ker f,
      r * ∥x₀∥ ≤ ∥x₀ - y∥, from riesz_lemma h hf this,
    have : x₀ ≠ 0,
    { assume h,
      have : x₀ ∈ f.ker, by { rw h, exact (linear_map.ker f).zero_mem },
      exact x₀ker this },
    have rx₀_ne_zero : r * ∥x₀∥ ≠ 0, by { simp [norm_eq_zero, this], },
    have : ∀x, ∥f x∥ ≤ (((r * ∥x₀∥)⁻¹) * ∥f x₀∥) * ∥x∥,
    { assume x,
      by_cases hx : f x = 0,
      { rw [hx, norm_zero],
        apply_rules [mul_nonneg, norm_nonneg, inv_nonneg.2] },
      { let y := x₀ - (f x₀ * (f x)⁻¹ ) • x,
        have fy_zero : f y = 0, by calc
          f y = f x₀ - (f x₀ * (f x)⁻¹ ) * f x : by simp [y]
          ... = 0 :
            by { rw [mul_assoc, inv_mul_cancel hx, mul_one, sub_eq_zero_of_eq], refl },
        have A : r * ∥x₀∥ ≤ ∥f x₀∥ * ∥f x∥⁻¹ * ∥x∥, from calc
          r * ∥x₀∥ ≤ ∥x₀ - y∥ : h₀ _ (linear_map.mem_ker.2 fy_zero)
          ... = ∥(f x₀ * (f x)⁻¹ ) • x∥ : by { dsimp [y], congr, abel }
          ... = ∥f x₀∥ * ∥f x∥⁻¹ * ∥x∥ :
            by rw [norm_smul, normed_field.norm_mul, normed_field.norm_inv],
        calc
          ∥f x∥ = (r * ∥x₀∥)⁻¹ * (r * ∥x₀∥) * ∥f x∥ : by rwa [inv_mul_cancel, one_mul]
          ... ≤ (r * ∥x₀∥)⁻¹ * (∥f x₀∥ * ∥f x∥⁻¹ * ∥x∥) * ∥f x∥ : begin
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left A _) (norm_nonneg _),
            exact inv_nonneg.2 (mul_nonneg (by norm_num) (norm_nonneg _))
          end
          ... = (∥f x∥ ⁻¹ * ∥f x∥) * (((r * ∥x₀∥)⁻¹) * ∥f x₀∥) * ∥x∥ : by ring
          ... = (((r * ∥x₀∥)⁻¹) * ∥f x₀∥) * ∥x∥ :
            by { rw [inv_mul_cancel, one_mul], simp [norm_eq_zero, hx] } } },
    exact linear_map.continuous_of_bound f _ this }
end

end normed_field

variables [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
[normed_space 𝕜 G] (c : 𝕜) (f g : E →L[𝕜] F) (h : F →L[𝕜] G) (x y z : E)
include 𝕜

lemma linear_map.bound_of_shell (f : E →ₗ[𝕜] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
  (hc : 1 < ∥c∥) (hf : ∀ x, ε / ∥c∥ ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C * ∥x∥) (x : E) :
  ∥f x∥ ≤ C * ∥x∥ :=
begin
  by_cases hx : x = 0, { simp [hx] },
  exact linear_map.bound_of_shell_semi_normed f ε_pos hc hf (ne_of_lt (norm_pos_iff.2 hx)).symm
end

namespace continuous_linear_map

section op_norm
open set real

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, continuous_linear_map.ext (λ x, norm_le_zero_iff.1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, le_antisymm (Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul, hf], exact norm_zero })⟩)
    (op_norm_nonneg _))

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
lemma norm_id [nontrivial E] : ∥id 𝕜 E∥ = 1 :=
begin
  refine norm_id_of_nontrivial_seminorm _,
  obtain ⟨x, hx⟩ := exists_ne (0 : E),
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩,
end

@[simp] lemma norm_id_field : ∥id 𝕜 𝕜∥ = 1 :=
norm_id

@[simp] lemma norm_id_field' : ∥(1 : 𝕜 →L[𝕜] 𝕜)∥ = 1 :=
norm_id_field

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : normed_group (E →L[𝕜] F) :=
normed_group.of_core _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

instance to_normed_space {𝕜' : Type*} [normed_field 𝕜'] [normed_space 𝕜' F]
  [smul_comm_class 𝕜 𝕜' F] : normed_space 𝕜' (E →L[𝕜] F) :=
⟨op_norm_smul_le⟩

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance to_normed_ring : normed_ring (E →L[𝕜] E) :=
{ norm_mul := op_norm_comp_le,
  .. continuous_linear_map.to_normed_group }

/-- For a nonzero normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance to_normed_algebra [nontrivial E] : normed_algebra 𝕜 (E →L[𝕜] E) :=
{ norm_algebra_map_eq := λ c, show ∥c • id 𝕜 E∥ = ∥c∥,
    by {rw [norm_smul, norm_id], simp},
  .. continuous_linear_map.algebra }

variable {f}

lemma homothety_norm [nontrivial E] (f : E →L[𝕜] F) {a : ℝ} (hf : ∀x, ∥f x∥ = a * ∥x∥) :
  ∥f∥ = a :=
begin
  obtain ⟨x, hx⟩ : ∃ (x : E), x ≠ 0 := exists_ne 0,
  rw ← norm_pos_iff at hx,
  have ha : 0 ≤ a, by simpa only [hf, hx, zero_le_mul_right] using norm_nonneg (f x),
  apply le_antisymm (f.op_norm_le_bound ha (λ y, le_of_eq (hf y))),
  simpa only [hf, hx, mul_le_mul_right] using f.le_op_norm x,
end

lemma to_span_singleton_norm (x : E) : ∥to_span_singleton 𝕜 x∥ = ∥x∥ :=
homothety_norm _ (to_span_singleton_homothety 𝕜 x)

variable (f)

theorem uniform_embedding_of_bound {K : ℝ≥0} (hf : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  uniform_embedding f :=
(f.to_linear_map.antilipschitz_of_bound hf).uniform_embedding f.uniform_continuous

/-- If a continuous linear map is a uniform embedding, then it is expands the distances
by a positive factor.-/
theorem antilipschitz_of_uniform_embedding (hf : uniform_embedding f) :
  ∃ K, antilipschitz_with K f :=
begin
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), ∀ {x y : E}, dist (f x) (f y) < ε → dist x y < 1,
    from (uniform_embedding_iff.1 hf).2.2 1 zero_lt_one,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos εpos,
  have H : ∀{x}, ∥f x∥ ≤ δ → ∥x∥ ≤ 1,
  { assume x hx,
    have : dist x 0 ≤ 1,
    { refine (hε _).le,
      rw [f.map_zero, dist_zero_right],
      exact hx.trans_lt (half_lt_self εpos) },
    simpa using this },
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  refine ⟨⟨δ⁻¹, _⟩ * nnnorm c, f.to_linear_map.antilipschitz_of_bound $ λx, _⟩,
  exact inv_nonneg.2 (le_of_lt δ_pos),
  by_cases hx : f x = 0,
  { have : f x = f 0, by { simp [hx] },
    have : x = 0 := (uniform_embedding_iff.1 hf).1 this,
    simp [this] },
  { rcases rescale_to_shell hc δ_pos hx with ⟨d, hd, dxlt, ledx, dinv⟩,
    rw [← f.map_smul d] at dxlt,
    have : ∥d • x∥ ≤ 1 := H dxlt.le,
    calc ∥x∥ = ∥d∥⁻¹ * ∥d • x∥ :
      by rwa [← normed_field.norm_inv, ← norm_smul, ← mul_smul, inv_mul_cancel, one_smul]
    ... ≤ ∥d∥⁻¹ * 1 :
      mul_le_mul_of_nonneg_left this (inv_nonneg.2 (norm_nonneg _))
    ... ≤ δ⁻¹ * ∥c∥ * ∥f x∥ :
      by rwa [mul_one] }
end

section completeness

open_locale topological_space
open filter

/-- If the target space is complete, the space of continuous linear maps with its norm is also
complete. This works also if the source space is seminormed. -/
instance {E : Type*} [semi_normed_group E] [semi_normed_space 𝕜 E] [complete_space F] :
  complete_space (E →L[𝕜] F) :=
begin
  -- We show that every Cauchy sequence converges.
  refine metric.complete_of_cauchy_seq_tendsto (λ f hf, _),
  -- We now expand out the definition of a Cauchy sequence,
  rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩, clear hf,
  -- and establish that the evaluation at any point `v : E` is Cauchy.
  have cau : ∀ v, cauchy_seq (λ n, f n v),
  { assume v,
    apply cauchy_seq_iff_le_tendsto_0.2 ⟨λ n, b n * ∥v∥, λ n, _, _, _⟩,
    { exact mul_nonneg (b0 n) (norm_nonneg _) },
    { assume n m N hn hm,
      rw dist_eq_norm,
      apply le_trans ((f n - f m).le_op_norm v) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m N hn hm) (norm_nonneg v) },
    { simpa using b_lim.mul tendsto_const_nhds } },
  -- We assemble the limits points of those Cauchy sequences
  -- (which exist as `F` is complete)
  -- into a function which we call `G`.
  choose G hG using λv, cauchy_seq_tendsto_of_complete (cau v),
  -- Next, we show that this `G` is linear,
  let Glin : E →ₗ[𝕜] F :=
  { to_fun := G,
    map_add' := λ v w, begin
      have A := hG (v + w),
      have B := (hG v).add (hG w),
      simp only [map_add] at A B,
      exact tendsto_nhds_unique A B,
    end,
    map_smul' := λ c v, begin
      have A := hG (c • v),
      have B := filter.tendsto.smul (@tendsto_const_nhds _ ℕ _ c _) (hG v),
      simp only [map_smul] at A B,
      exact tendsto_nhds_unique A B
    end },
  -- and that `G` has norm at most `(b 0 + ∥f 0∥)`.
  have Gnorm : ∀ v, ∥G v∥ ≤ (b 0 + ∥f 0∥) * ∥v∥,
  { assume v,
    have A : ∀ n, ∥f n v∥ ≤ (b 0 + ∥f 0∥) * ∥v∥,
    { assume n,
      apply le_trans ((f n).le_op_norm _) _,
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v),
      calc ∥f n∥ = ∥(f n - f 0) + f 0∥ : by { congr' 1, abel }
      ... ≤ ∥f n - f 0∥ + ∥f 0∥ : norm_add_le _ _
      ... ≤ b 0 + ∥f 0∥ : begin
        apply add_le_add_right,
        simpa [dist_eq_norm] using b_bound n 0 0 (zero_le _) (zero_le _)
      end },
    exact le_of_tendsto (hG v).norm (eventually_of_forall A) },
  -- Thus `G` is continuous, and we propose that as the limit point of our original Cauchy sequence.
  let Gcont := Glin.mk_continuous _ Gnorm,
  use Gcont,
  -- Our last task is to establish convergence to `G` in norm.
  have : ∀ n, ∥f n - Gcont∥ ≤ b n,
  { assume n,
    apply op_norm_le_bound _ (b0 n) (λ v, _),
    have A : ∀ᶠ m in at_top, ∥(f n - f m) v∥ ≤ b n * ∥v∥,
    { refine eventually_at_top.2 ⟨n, λ m hm, _⟩,
      apply le_trans ((f n - f m).le_op_norm _) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m n (le_refl _) hm) (norm_nonneg v) },
    have B : tendsto (λ m, ∥(f n - f m) v∥) at_top (𝓝 (∥(f n - Gcont) v∥)) :=
      tendsto.norm (tendsto_const_nhds.sub (hG v)),
    exact le_of_tendsto B A },
  erw tendsto_iff_norm_tendsto_zero,
  exact squeeze_zero (λ n, norm_nonneg _) this b_lim,
end

end completeness

section uniformly_extend

variables [complete_space F] (e : E →L[𝕜] G) (h_dense : dense_range e)

section
variables (h_e : uniform_inducing e)

/-- Extension of a continuous linear map `f : E →L[𝕜] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] G`.  -/
def extend : G →L[𝕜] F :=
/- extension of `f` is continuous -/
have cont : _ := (uniform_continuous_uniformly_extend h_e h_dense f.uniform_continuous).continuous,
/- extension of `f` agrees with `f` on the domain of the embedding `e` -/
have eq : _ := uniformly_extend_of_ind h_e h_dense f.uniform_continuous,
{ to_fun := (h_e.dense_inducing h_dense).extend f,
  map_add' :=
  begin
    refine h_dense.induction_on₂ _ _,
    { exact is_closed_eq (cont.comp continuous_add)
        ((cont.comp continuous_fst).add (cont.comp continuous_snd)) },
    { assume x y, simp only [eq, ← e.map_add], exact f.map_add _ _  },
  end,
  map_smul' := λk,
  begin
    refine (λ b, h_dense.induction_on b _ _),
    { exact is_closed_eq (cont.comp (continuous_const.smul continuous_id))
        ((continuous_const.smul continuous_id).comp cont) },
    { assume x, rw ← map_smul, simp only [eq], exact map_smul _ _ _  },
  end,
  cont := cont
}

lemma extend_unique (g : G →L[𝕜] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
continuous_linear_map.coe_fn_injective $
  uniformly_extend_unique h_e h_dense (continuous_linear_map.ext_iff.1 H) g.continuous

@[simp] lemma extend_zero : extend (0 : E →L[𝕜] F) e h_dense h_e = 0 :=
extend_unique _ _ _ _ _ (zero_comp _)

end

section
variables {N : ℝ≥0} (h_e : ∀x, ∥x∥ ≤ N * ∥e x∥)

local notation `ψ` := f.extend e h_dense (uniform_embedding_of_bound _ h_e).to_uniform_inducing

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ∥f∥`. -/
lemma op_norm_extend_le : ∥ψ∥ ≤ N * ∥f∥ :=
begin
  have uni : uniform_inducing e := (uniform_embedding_of_bound _ h_e).to_uniform_inducing,
  have eq : ∀x, ψ (e x) = f x := uniformly_extend_of_ind uni h_dense f.uniform_continuous,
  by_cases N0 : 0 ≤ N,
  { refine op_norm_le_bound ψ _ (is_closed_property h_dense (is_closed_le _ _) _),
    { exact mul_nonneg N0 (norm_nonneg _) },
    { exact continuous_norm.comp (cont ψ) },
    { exact continuous_const.mul continuous_norm },
    { assume x,
      rw eq,
      calc ∥f x∥ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
        ... ≤ ∥f∥ * (N * ∥e x∥) : mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)
        ... ≤ N * ∥f∥ * ∥e x∥ : by rw [mul_comm ↑N ∥f∥, mul_assoc] } },
  { have he : ∀ x : E, x = 0,
    { assume x,
      have N0 : N ≤ 0 := le_of_lt (lt_of_not_ge N0),
      rw ← norm_le_zero_iff,
      exact le_trans (h_e x) (mul_nonpos_of_nonpos_of_nonneg N0 (norm_nonneg _)) },
    have hf : f = 0, { ext, simp only [he x, zero_apply, map_zero] },
    have hψ : ψ = 0, { rw hf, apply extend_zero },
    rw [hψ, hf, norm_zero, norm_zero, mul_zero] }
end

end

end uniformly_extend

end op_norm

end continuous_linear_map

namespace linear_isometry

@[simp] lemma norm_to_continuous_linear_map [nontrivial E] (f : E →ₗᵢ[𝕜] F) :
  ∥f.to_continuous_linear_map∥ = 1 :=
f.to_continuous_linear_map.homothety_norm $ by simp

end linear_isometry

namespace continuous_linear_map

/-- Precomposition with a linear isometry preserves the operator norm. -/
lemma op_norm_comp_linear_isometry_equiv {G : Type*} [semi_normed_group G] [semi_normed_space 𝕜 G]
  (f : F →L[𝕜] G) (g : E ≃ₗᵢ[𝕜] F) :
  ∥f.comp g.to_linear_isometry.to_continuous_linear_map∥ = ∥f∥ :=
begin
  casesI subsingleton_or_nontrivial E,
  { haveI := g.symm.to_linear_equiv.to_equiv.subsingleton,
    simp },
  refine le_antisymm _ _,
  { convert f.op_norm_comp_le g.to_linear_isometry.to_continuous_linear_map,
    simp [g.to_linear_isometry.norm_to_continuous_linear_map] },
  { convert (f.comp g.to_linear_isometry.to_continuous_linear_map).op_norm_comp_le
      g.symm.to_linear_isometry.to_continuous_linear_map,
    { ext,
      simp },
    haveI := g.symm.to_linear_equiv.to_equiv.nontrivial,
    simp [g.symm.to_linear_isometry.norm_to_continuous_linear_map] },
end

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp] lemma norm_smul_right_apply (c : E →L[𝕜] 𝕜) (f : F) :
  ∥smul_right c f∥ = ∥c∥ * ∥f∥ :=
begin
  refine le_antisymm _ _,
  { apply op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (λx, _),
    calc
     ∥(c x) • f∥ = ∥c x∥ * ∥f∥ : norm_smul _ _
     ... ≤ (∥c∥ * ∥x∥) * ∥f∥ :
       mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _)
     ... = ∥c∥ * ∥f∥ * ∥x∥ : by ring },
  { by_cases h : f = 0,
    { simp [h] },
    { have : 0 < ∥f∥ := norm_pos_iff.2 h,
      rw ← le_div_iff this,
      apply op_norm_le_bound _ (div_nonneg (norm_nonneg _) (norm_nonneg f)) (λx, _),
      rw [div_mul_eq_mul_div, le_div_iff this],
      calc ∥c x∥ * ∥f∥ = ∥c x • f∥ : (norm_smul _ _).symm
      ... = ∥smul_right c f x∥ : rfl
      ... ≤ ∥smul_right c f∥ * ∥x∥ : le_op_norm _ _ } },
end

variables (𝕜 E F)

/-- `continuous_linear_map.smul_right` as a continuous trilinear map:
`smul_rightL (c : E →L[𝕜] 𝕜) (f : F) (x : E) = c x • f`. -/
def smul_rightL : (E →L[𝕜] 𝕜) →L[𝕜] F →L[𝕜] E →L[𝕜] F :=
linear_map.mk_continuous₂
  { to_fun := smul_rightₗ,
    map_add' := λ c₁ c₂, by { ext x, simp [add_smul] },
    map_smul' := λ m c, by { ext x, simp [smul_smul] } }
  1 $ λ c x, by simp

variables {𝕜 E F}

@[simp] lemma norm_smul_rightL_apply (c : E →L[𝕜] 𝕜) (f : F) :
  ∥smul_rightL 𝕜 E F c f∥ = ∥c∥ * ∥f∥ :=
norm_smul_right_apply c f

@[simp] lemma norm_smul_rightL (c : E →L[𝕜] 𝕜) [nontrivial F] :
  ∥smul_rightL 𝕜 E F c∥ = ∥c∥ :=
continuous_linear_map.homothety_norm _ c.norm_smul_right_apply

variables (𝕜) (𝕜' : Type*) [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜']

@[simp] lemma op_norm_lmul : ∥lmul 𝕜 𝕜'∥ = 1 :=
by haveI := normed_algebra.nontrivial 𝕜 𝕜'; exact (lmulₗᵢ 𝕜 𝕜').norm_to_continuous_linear_map

@[simp] lemma op_norm_lmul_right : ∥lmul_right 𝕜 𝕜'∥ = 1 :=
(op_norm_flip (@lmul 𝕜 _ 𝕜' _ _)).trans (op_norm_lmul _ _)

end continuous_linear_map

namespace submodule

lemma norm_subtypeL (K : submodule 𝕜 E) [nontrivial K] : ∥K.subtypeL∥ = 1 :=
K.subtypeₗᵢ.norm_to_continuous_linear_map

end submodule

namespace continuous_linear_equiv

variables (e : E ≃L[𝕜] F)

protected lemma antilipschitz : antilipschitz_with (nnnorm (e.symm : F →L[𝕜] E)) e :=
e.symm.lipschitz.to_right_inverse e.left_inv

/-- A continuous linear equiv is a uniform embedding. -/
lemma uniform_embedding : uniform_embedding e :=
e.antilipschitz.uniform_embedding e.lipschitz.uniform_continuous

lemma one_le_norm_mul_norm_symm [nontrivial E] :
  1 ≤ ∥(e : E →L[𝕜] F)∥ * ∥(e.symm : F →L[𝕜] E)∥ :=
begin
  rw [mul_comm],
  convert (e.symm : F →L[𝕜] E).op_norm_comp_le (e : E →L[𝕜] F),
  rw [e.coe_symm_comp_coe, continuous_linear_map.norm_id]
end

lemma norm_pos [nontrivial E] : 0 < ∥(e : E →L[𝕜] F)∥ :=
pos_of_mul_pos_right (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

lemma norm_symm_pos [nontrivial E] : 0 < ∥(e.symm : F →L[𝕜] E)∥ :=
pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

lemma nnnorm_symm_pos [nontrivial E] : 0 < nnnorm (e.symm : F →L[𝕜] E) :=
e.norm_symm_pos

lemma subsingleton_or_norm_symm_pos : subsingleton E ∨ 0 < ∥(e.symm : F →L[𝕜] E)∥ :=
begin
  rcases subsingleton_or_nontrivial E with _i|_i; resetI,
  { left, apply_instance },
  { right, exact e.norm_symm_pos }
end

lemma subsingleton_or_nnnorm_symm_pos : subsingleton E ∨ 0 < (nnnorm $ (e.symm : F →L[𝕜] E)) :=
subsingleton_or_norm_symm_pos e

variable (𝕜)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
    continuous linear equivalence from `E₁` to the span of `x`.-/
def to_span_nonzero_singleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] (𝕜 ∙ x) :=
of_homothety
  (linear_equiv.to_span_nonzero_singleton 𝕜 E x h)
  ∥x∥
  (norm_pos_iff.mpr h)
  (to_span_nonzero_singleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
def coord (x : E) (h : x ≠ 0) : (𝕜 ∙ x) →L[𝕜] 𝕜 := (to_span_nonzero_singleton 𝕜 x h).symm

@[simp] lemma coe_to_span_nonzero_singleton_symm {x : E} (h : x ≠ 0) :
  ⇑(to_span_nonzero_singleton 𝕜 x h).symm = coord 𝕜 x h := rfl

@[simp] lemma coord_to_span_nonzero_singleton {x : E} (h : x ≠ 0) (c : 𝕜) :
  coord 𝕜 x h (to_span_nonzero_singleton 𝕜 x h c) = c :=
(to_span_nonzero_singleton 𝕜 x h).symm_apply_apply c

@[simp] lemma to_span_nonzero_singleton_coord {x : E} (h : x ≠ 0) (y : 𝕜 ∙ x) :
  to_span_nonzero_singleton 𝕜 x h (coord 𝕜 x h y) = y :=
(to_span_nonzero_singleton 𝕜 x h).apply_symm_apply y

@[simp] lemma coord_norm (x : E) (h : x ≠ 0) : ∥coord 𝕜 x h∥ = ∥x∥⁻¹ :=
begin
  have hx : 0 < ∥x∥ := (norm_pos_iff.mpr h),
  haveI : nontrivial (𝕜 ∙ x) := submodule.nontrivial_span_singleton h,
  exact continuous_linear_map.homothety_norm _
        (λ y, homothety_inverse _ hx _ (to_span_nonzero_singleton_homothety 𝕜 x h) _)
end

@[simp] lemma coord_self (x : E) (h : x ≠ 0) :
  (coord 𝕜 x h) (⟨x, submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
linear_equiv.coord_self 𝕜 E x h

end continuous_linear_equiv

lemma linear_equiv.uniform_embedding (e : E ≃ₗ[𝕜] F) (h₁ : continuous e)
  (h₂ : continuous e.symm) : uniform_embedding e :=
continuous_linear_equiv.uniform_embedding
{ continuous_to_fun := h₁,
  continuous_inv_fun := h₂,
  .. e }

end normed
