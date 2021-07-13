/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import linear_algebra.affine_space.midpoint
import analysis.normed_space.basic
import topology.instances.real_vector_space

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.

-/

noncomputable theory
open_locale nnreal topological_space
open filter

/-- A `semi_normed_add_torsor V P` is a torsor of an additive seminormed group
action by a `semi_normed_group V` on points `P`. We bundle the pseudometric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems). -/
class semi_normed_add_torsor (V : out_param $ Type*) (P : Type*)
  [out_param $ semi_normed_group V] [pseudo_metric_space P]
  extends add_torsor V P :=
(dist_eq_norm' : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)

/-- A `normed_add_torsor V P` is a torsor of an additive normed group
action by a `normed_group V` on points `P`. We bundle the metric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a metric space, but
bundling just the distance and using an instance for the metric space
results in type class problems). -/
class normed_add_torsor (V : out_param $ Type*) (P : Type*)
  [out_param $ normed_group V] [metric_space P]
  extends add_torsor V P :=
(dist_eq_norm' : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)

/-- A `normed_add_torsor` is a `semi_normed_add_torsor`. -/
@[priority 100]
instance normed_add_torsor.to_semi_normed_add_torsor {V P : Type*} [normed_group V] [metric_space P]
  [β : normed_add_torsor V P] : semi_normed_add_torsor V P := { ..β }

variables {α V P : Type*} [semi_normed_group V] [pseudo_metric_space P] [semi_normed_add_torsor V P]
variables {W Q : Type*} [normed_group W] [metric_space Q] [normed_add_torsor W Q]

/-- A `semi_normed_group` is a `semi_normed_add_torsor` over itself. -/
@[priority 100]
instance semi_normed_group.normed_add_torsor : semi_normed_add_torsor V V :=
{ dist_eq_norm' := dist_eq_norm }

/-- A `normed_group` is a `normed_add_torsor` over itself. -/
@[priority 100]
instance normed_group.normed_add_torsor : normed_add_torsor W W :=
{ dist_eq_norm' := dist_eq_norm }

include V

section

variables (V W)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
lemma dist_eq_norm_vsub (x y : P) :
  dist x y = ∥(x -ᵥ y)∥ :=
semi_normed_add_torsor.dist_eq_norm' x y

end

@[simp] lemma dist_vadd_cancel_left (v : V) (x y : P) :
  dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
by rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, vadd_vsub_vadd_cancel_left]

@[simp] lemma dist_vadd_cancel_right (v₁ v₂ : V) (x : P) :
  dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ :=
by rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]

@[simp] lemma dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ∥v∥ :=
by simp [dist_eq_norm_vsub V _ x]

@[simp] lemma dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ∥v∥ :=
by rw [dist_comm, dist_vadd_left]

@[simp] lemma dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z :=
by rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]

@[simp] lemma dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
by rw [dist_eq_norm, vsub_sub_vsub_cancel_right, dist_eq_norm_vsub V]

lemma dist_vadd_vadd_le (v v' : V) (p p' : P) :
  dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v' + dist p p' :=
by simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')

lemma dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
  dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃ + dist p₂ p₄ :=
by { rw [dist_eq_norm, vsub_sub_vsub_comm, dist_eq_norm_vsub V, dist_eq_norm_vsub V],
 exact norm_sub_le _ _ }

lemma nndist_vadd_vadd_le (v v' : V) (p p' : P) :
  nndist (v +ᵥ p) (v' +ᵥ p') ≤ nndist v v' + nndist p p' :=
by simp only [← nnreal.coe_le_coe, nnreal.coe_add, ← dist_nndist, dist_vadd_vadd_le]

lemma nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
  nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ nndist p₁ p₃ + nndist p₂ p₄ :=
by simp only [← nnreal.coe_le_coe, nnreal.coe_add, ← dist_nndist, dist_vsub_vsub_le]

lemma edist_vadd_vadd_le (v v' : V) (p p' : P) :
  edist (v +ᵥ p) (v' +ᵥ p') ≤ edist v v' + edist p p' :=
by { simp only [edist_nndist], apply_mod_cast nndist_vadd_vadd_le }

lemma edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
  edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ edist p₁ p₃ + edist p₂ p₄ :=
by { simp only [edist_nndist], apply_mod_cast nndist_vsub_vsub_le }

omit V

/-- The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def pseudo_metric_space_of_normed_group_of_add_torsor (V P : Type*) [semi_normed_group V]
  [add_torsor V P] : pseudo_metric_space P :=
{ dist := λ x y, ∥(x -ᵥ y : V)∥,
  dist_self := λ x, by simp,
  dist_comm := λ x y, by simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
  dist_triangle := begin
    intros x y z,
    change ∥x -ᵥ z∥ ≤ ∥x -ᵥ y∥ + ∥y -ᵥ z∥,
    rw ←vsub_add_vsub_cancel,
    apply norm_add_le
  end }

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metric_space_of_normed_group_of_add_torsor (V P : Type*) [normed_group V] [add_torsor V P] :
  metric_space P :=
{ dist := λ x y, ∥(x -ᵥ y : V)∥,
  dist_self := λ x, by simp,
  eq_of_dist_eq_zero := λ x y h, by simpa using h,
  dist_comm := λ x y, by simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
  dist_triangle := begin
    intros x y z,
    change ∥x -ᵥ z∥ ≤ ∥x -ᵥ y∥ + ∥y -ᵥ z∥,
    rw ←vsub_add_vsub_cancel,
    apply norm_add_le
  end }

include V

namespace isometric

/-- The map `v ↦ v +ᵥ p` as an isometric equivalence between `V` and `P`. -/
def vadd_const (p : P) : V ≃ᵢ P :=
⟨equiv.vadd_const p, isometry_emetric_iff_metric.2 $ λ x₁ x₂, dist_vadd_cancel_right x₁ x₂ p⟩

@[simp] lemma coe_vadd_const (p : P) : ⇑(vadd_const p) = λ v, v +ᵥ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : ⇑(vadd_const p).symm = λ p', p' -ᵥ p := rfl

@[simp] lemma vadd_const_to_equiv (p : P) : (vadd_const p).to_equiv = equiv.vadd_const p := rfl

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def const_vsub (p : P) : P ≃ᵢ V :=
⟨equiv.const_vsub p, isometry_emetric_iff_metric.2 $ λ p₁ p₂, dist_vsub_cancel_left _ _ _⟩

@[simp] lemma coe_const_vsub (p : P) : ⇑(const_vsub p) = (-ᵥ) p := rfl

@[simp] lemma coe_const_vsub_symm (p : P) : ⇑(const_vsub p).symm = λ v, -v +ᵥ p := rfl

variables (P)

/-- The map `p ↦ v +ᵥ p` as an isometric automorphism of `P`. -/
def const_vadd (v : V) : P ≃ᵢ P :=
⟨equiv.const_vadd P v, isometry_emetric_iff_metric.2 $ dist_vadd_cancel_left v⟩

@[simp] lemma coe_const_vadd (v : V) : ⇑(const_vadd P v) = (+ᵥ) v := rfl

variable (V)

@[simp] lemma const_vadd_zero : const_vadd P (0:V) = isometric.refl P :=
isometric.to_equiv_inj $ equiv.const_vadd_zero V P

variables {P V}

/-- Point reflection in `x` as an `isometric` homeomorphism. -/
def point_reflection (x : P) : P ≃ᵢ P :=
(const_vsub x).trans (vadd_const x)

lemma point_reflection_apply (x y : P) : point_reflection x y = x -ᵥ y +ᵥ x := rfl

@[simp] lemma point_reflection_to_equiv (x : P) :
  (point_reflection x).to_equiv = equiv.point_reflection x := rfl

@[simp] lemma point_reflection_self (x : P) : point_reflection x x = x :=
equiv.point_reflection_self x

lemma point_reflection_involutive (x : P) : function.involutive (point_reflection x : P → P) :=
equiv.point_reflection_involutive x

@[simp] lemma point_reflection_symm (x : P) : (point_reflection x).symm = point_reflection x :=
to_equiv_inj $ equiv.point_reflection_symm x

@[simp] lemma dist_point_reflection_fixed (x y : P) :
  dist (point_reflection x y) x = dist y x :=
by rw [← (point_reflection x).dist_eq y x, point_reflection_self]

lemma dist_point_reflection_self' (x y : P) :
  dist (point_reflection x y) y = ∥bit0 (x -ᵥ y)∥ :=
by rw [point_reflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]

lemma dist_point_reflection_self (𝕜 : Type*) [normed_field 𝕜] [normed_space 𝕜 V] (x y : P) :
  dist (point_reflection x y) y = ∥(2:𝕜)∥ * dist x y :=
by rw [dist_point_reflection_self', ← two_smul' 𝕜 (x -ᵥ y), norm_smul, ← dist_eq_norm_vsub V]

lemma point_reflection_fixed_iff (𝕜 : Type*) [normed_field 𝕜] [normed_space 𝕜 V]
  [invertible (2:𝕜)] {x y : P} : point_reflection x y = y ↔ y = x :=
affine_equiv.point_reflection_fixed_iff_of_module 𝕜

variables [normed_space ℝ V]

lemma dist_point_reflection_self_real (x y : P) :
  dist (point_reflection x y) y = 2 * dist x y :=
by { rw [dist_point_reflection_self ℝ, real.norm_two], apply_instance }

@[simp] lemma point_reflection_midpoint_left (x y : P) :
  point_reflection (midpoint ℝ x y) x = y :=
affine_equiv.point_reflection_midpoint_left x y

@[simp] lemma point_reflection_midpoint_right (x y : P) :
  point_reflection (midpoint ℝ x y) y = x :=
affine_equiv.point_reflection_midpoint_right x y

end isometric

lemma lipschitz_with.vadd [pseudo_emetric_space α] {f : α → V} {g : α → P} {Kf Kg : ℝ≥0}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (f +ᵥ g) :=
λ x y,
calc edist (f x +ᵥ g x) (f y +ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_vadd_vadd_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma lipschitz_with.vsub [pseudo_emetric_space α] {f g : α → P} {Kf Kg : ℝ≥0}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (f -ᵥ g) :=
λ x y,
calc edist (f x -ᵥ g x) (f y -ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_vsub_vsub_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma uniform_continuous_vadd : uniform_continuous (λ x : V × P, x.1 +ᵥ x.2) :=
(lipschitz_with.prod_fst.vadd lipschitz_with.prod_snd).uniform_continuous

lemma uniform_continuous_vsub : uniform_continuous (λ x : P × P, x.1 -ᵥ x.2) :=
(lipschitz_with.prod_fst.vsub lipschitz_with.prod_snd).uniform_continuous

lemma continuous_vadd : continuous (λ x : V × P, x.1 +ᵥ x.2) :=
uniform_continuous_vadd.continuous

lemma continuous_vsub : continuous (λ x : P × P, x.1 -ᵥ x.2) :=
uniform_continuous_vsub.continuous

lemma filter.tendsto.vadd {l : filter α} {f : α → V} {g : α → P} {v : V} {p : P}
  (hf : tendsto f l (𝓝 v)) (hg : tendsto g l (𝓝 p)) :
  tendsto (f +ᵥ g) l (𝓝 (v +ᵥ p)) :=
(continuous_vadd.tendsto (v, p)).comp (hf.prod_mk_nhds hg)

lemma filter.tendsto.vsub {l : filter α} {f g : α → P} {x y : P}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
(continuous_vsub.tendsto (x, y)).comp (hf.prod_mk_nhds hg)

section

variables [topological_space α]

lemma continuous.vadd {f : α → V} {g : α → P} (hf : continuous f) (hg : continuous g) :
  continuous (f +ᵥ g) :=
continuous_vadd.comp (hf.prod_mk hg)

lemma continuous.vsub {f g : α → P} (hf : continuous f) (hg : continuous g) :
  continuous (f -ᵥ g) :=
continuous_vsub.comp (hf.prod_mk hg : _)

lemma continuous_at.vadd {f : α → V} {g : α → P} {x : α} (hf : continuous_at f x)
  (hg : continuous_at g x) :
  continuous_at (f +ᵥ g) x :=
hf.vadd hg

lemma continuous_at.vsub {f g : α → P}  {x : α} (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (f -ᵥ g) x :=
hf.vsub hg

lemma continuous_within_at.vadd {f : α → V} {g : α → P} {x : α} {s : set α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (f +ᵥ g) s x :=
hf.vadd hg

lemma continuous_within_at.vsub {f g : α → P} {x : α} {s : set α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (f -ᵥ g) s x :=
hf.vsub hg

end

section

variables {R : Type*} [ring R] [topological_space R] [module R V] [has_continuous_smul R V]

lemma filter.tendsto.line_map {l : filter α} {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (h₂ : tendsto f₂ l (𝓝 p₂)) (hg : tendsto g l (𝓝 c)) :
  tendsto (λ x, affine_map.line_map (f₁ x) (f₂ x) (g x)) l (𝓝 $ affine_map.line_map p₁ p₂ c) :=
(hg.smul (h₂.vsub h₁)).vadd h₁

lemma filter.tendsto.midpoint [invertible (2:R)] {l : filter α} {f₁ f₂ : α → P} {p₁ p₂ : P}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (h₂ : tendsto f₂ l (𝓝 p₂)) :
  tendsto (λ x, midpoint R (f₁ x) (f₂ x)) l (𝓝 $ midpoint R p₁ p₂) :=
h₁.line_map h₂ tendsto_const_nhds

end

variables {V' : Type*} {P' : Type*} [semi_normed_group V'] [pseudo_metric_space P']
  [semi_normed_add_torsor V' P']

/-- The map `g` from `V1` to `V2` corresponding to a map `f` from `P1`
to `P2`, at a base point `p`, is an isometry if `f` is one. -/
lemma isometry.vadd_vsub {f : P → P'} (hf : isometry f) {p : P} {g : V → V'}
  (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) : isometry g :=
begin
  convert (isometric.vadd_const (f p)).symm.isometry.comp
    (hf.comp (isometric.vadd_const p).isometry),
  exact funext hg
end

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 V]

open affine_map

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
lemma affine_map.continuous_linear_iff [normed_space 𝕜 V'] {f : P →ᵃ[𝕜] P'} :
  continuous f.linear ↔ continuous f :=
begin
  inhabit P,
  have : (f.linear : V → V') =
    (isometric.vadd_const $ f $ default P).to_homeomorph.symm ∘ f ∘
      (isometric.vadd_const $ default P).to_homeomorph,
  { ext v, simp },
  rw this,
  simp only [homeomorph.comp_continuous_iff, homeomorph.comp_continuous_iff'],
end

@[simp] lemma dist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
  dist p₁ (homothety p₁ c p₂) = ∥c∥ * dist p₁ p₂ :=
by simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp] lemma dist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
  dist (homothety p₁ c p₂) p₁ = ∥c∥ * dist p₁ p₂ :=
by rw [dist_comm, dist_center_homothety]

@[simp] lemma dist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
  dist (homothety p₁ c p₂) p₂ = ∥1 - c∥ * dist p₁ p₂ :=
by rw [homothety_eq_line_map, ← line_map_apply_one_sub, ← homothety_eq_line_map,
  dist_homothety_center, dist_comm]

@[simp] lemma dist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
  dist p₂ (homothety p₁ c p₂) = ∥1 - c∥ * dist p₁ p₂ :=
by rw [dist_comm, dist_homothety_self]

variables [invertible (2:𝕜)]

@[simp] lemma dist_left_midpoint (p₁ p₂ : P) :
  dist p₁ (midpoint 𝕜 p₁ p₂) = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [midpoint, ← homothety_eq_line_map, dist_center_homothety, inv_of_eq_inv,
  ← normed_field.norm_inv]

@[simp] lemma dist_midpoint_left (p₁ p₂ : P) :
  dist (midpoint 𝕜 p₁ p₂) p₁ = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [dist_comm, dist_left_midpoint]

@[simp] lemma dist_midpoint_right (p₁ p₂ : P) :
  dist (midpoint 𝕜 p₁ p₂) p₂ = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp] lemma dist_right_midpoint (p₁ p₂ : P) :
  dist p₂ (midpoint 𝕜 p₁ p₂) = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [dist_comm, dist_midpoint_right]

lemma dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
  dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / ∥(2 : 𝕜)∥ :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint];
    try { apply_instance },
  rw [midpoint_eq_smul_add, norm_smul, inv_of_eq_inv, normed_field.norm_inv, ← div_eq_inv_mul],
  exact div_le_div_of_le_of_nonneg (norm_add_le _ _) (norm_nonneg _),
end

end normed_space

variables [normed_space ℝ V] [normed_space ℝ W]

lemma dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
  dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / 2 :=
by simpa using dist_midpoint_midpoint_le' p₁ p₂ p₃ p₄

include W

/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def affine_map.of_map_midpoint (f : P → Q)
  (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y))
  (hfc : continuous f) :
  P →ᵃ[ℝ] Q :=
affine_map.mk' f
  ↑((add_monoid_hom.of_map_midpoint ℝ ℝ
    ((affine_equiv.vadd_const ℝ (f $ classical.arbitrary P)).symm ∘ f ∘
      (affine_equiv.vadd_const ℝ (classical.arbitrary P))) (by simp)
      (λ x y, by simp [h])).to_real_linear_map $ by apply_rules [continuous.vadd, continuous.vsub,
        continuous_const, hfc.comp, continuous_id])
  (classical.arbitrary P)
  (λ p, by simp)
