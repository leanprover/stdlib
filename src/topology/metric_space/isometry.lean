/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
-/
import topology.metric_space.antilipschitz

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `pseudo_metric_space` and we specialize to `metric_space` when needed.
-/

noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function set

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between pseudoemetric spaces, or equivalently the distance between pseudometric space.  -/
def isometry [pseudo_emetric_space α] [pseudo_emetric_space β] (f : α → β) : Prop :=
∀x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

/-- On pseudometric spaces, a map is an isometry if and only if it preserves distances. -/
lemma isometry_emetric_iff_metric [pseudo_metric_space α] [pseudo_metric_space β] {f : α → β} :
  isometry f ↔ (∀x y, dist (f x) (f y) = dist x y) :=
⟨assume H x y, by simp [dist_edist, H x y],
assume H x y, by simp [edist_dist, H x y]⟩

/-- An isometry preserves edistances. -/
theorem isometry.edist_eq [pseudo_emetric_space α] [pseudo_emetric_space β] {f : α → β}
  (hf : isometry f) (x y : α) : edist (f x) (f y) = edist x y :=
hf x y

/-- An isometry preserves distances. -/
theorem isometry.dist_eq [pseudo_metric_space α] [pseudo_metric_space β] {f : α → β}
  (hf : isometry f) (x y : α) : dist (f x) (f y) = dist x y :=
by rw [dist_edist, dist_edist, hf]

section emetric_isometry

variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]
variables {f : α → β} {x y z : α}  {s : set α}

lemma isometry.lipschitz (h : isometry f) : lipschitz_with 1 f :=
lipschitz_with.of_edist_le $ λ x y, le_of_eq (h x y)

lemma isometry.antilipschitz (h : isometry f) : antilipschitz_with 1 f :=
λ x y, by simp only [h x y, ennreal.coe_one, one_mul, le_refl]

/-- An isometry from an emetric space is injective -/
lemma isometry.injective {α : Type u} [emetric_space α] {f : α → β} (h : isometry f) :
  injective f := h.antilipschitz.injective

/-- Any map on a subsingleton is an isometry -/
theorem isometry_subsingleton [subsingleton α] : isometry f :=
λx y, by rw subsingleton.elim x y; simp

/-- The identity is an isometry -/
lemma isometry_id : isometry (id : α → α) :=
λx y, rfl

/-- The composition of isometries is an isometry -/
theorem isometry.comp {g : β → γ} {f : α → β} (hg : isometry g) (hf : isometry f) :
  isometry (g ∘ f) :=
assume x y, calc
  edist ((g ∘ f) x) ((g ∘ f) y) = edist (f x) (f y) : hg _ _
                            ... = edist x y : hf _ _

/-- An isometry from a metric space is a uniform inducing map -/
theorem isometry.uniform_inducing (hf : isometry f) :
  uniform_inducing f :=
hf.antilipschitz.uniform_inducing hf.lipschitz.uniform_continuous

/-- An isometry from a metric space is a uniform embedding -/
theorem isometry.uniform_embedding {α : Type u} {β : Type v} [emetric_space α]
  [pseudo_emetric_space β] {f : α → β} (hf : isometry f) :
  uniform_embedding f :=
hf.antilipschitz.uniform_embedding hf.lipschitz.uniform_continuous

/-- An isometry from a complete emetric space is a closed embedding -/
theorem isometry.closed_embedding {α : Type u} {β : Type v} [emetric_space α] [complete_space α]
  [emetric_space β] {f : α → β} (hf : isometry f) : closed_embedding f :=
hf.antilipschitz.closed_embedding hf.lipschitz.uniform_continuous

/-- An isometry is continuous. -/
lemma isometry.continuous (hf : isometry f) : continuous f :=
hf.lipschitz.continuous

/-- The right inverse of an isometry is an isometry. -/
lemma isometry.right_inv {f : α → β} {g : β → α} (h : isometry f) (hg : right_inverse g f) :
  isometry g :=
λ x y, by rw [← h, hg _, hg _]

/-- Isometries preserve the diameter in pseudoemetric spaces. -/
lemma isometry.ediam_image (hf : isometry f) (s : set α) :
  emetric.diam (f '' s) = emetric.diam s :=
eq_of_forall_ge_iff $ λ d,
by simp only [emetric.diam_le_iff, ball_image_iff, hf.edist_eq]

lemma isometry.ediam_range (hf : isometry f) :
  emetric.diam (range f) = emetric.diam (univ : set α) :=
by { rw ← image_univ, exact hf.ediam_image univ }

/-- The injection from a subtype is an isometry -/
lemma isometry_subtype_coe {s : set α} : isometry (coe : s → α) :=
λx y, rfl

lemma isometry.comp_continuous_on_iff {γ} [topological_space γ] (hf : isometry f) {g : γ → α}
  {s : set γ} :
  continuous_on (f ∘ g) s ↔ continuous_on g s :=
hf.uniform_inducing.inducing.continuous_on_iff.symm

lemma isometry.comp_continuous_iff {γ} [topological_space γ] (hf : isometry f) {g : γ → α} :
  continuous (f ∘ g) ↔ continuous g :=
hf.uniform_inducing.inducing.continuous_iff.symm

end emetric_isometry --section

/-- An isometry preserves the diameter in pseudometric spaces. -/
lemma isometry.diam_image [pseudo_metric_space α] [pseudo_metric_space β]
  {f : α → β} (hf : isometry f) (s : set α) : metric.diam (f '' s) = metric.diam s :=
by rw [metric.diam, metric.diam, hf.ediam_image]

lemma isometry.diam_range [pseudo_metric_space α] [pseudo_metric_space β] {f : α → β}
  (hf : isometry f) : metric.diam (range f) = metric.diam (univ : set α) :=
by { rw ← image_univ, exact hf.diam_image univ }

/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
@[nolint has_inhabited_instance] -- such a bijection need not exist
structure isometric (α : Type*) (β : Type*) [pseudo_emetric_space α] [pseudo_emetric_space β]
  extends α ≃ β :=
(isometry_to_fun  : isometry to_fun)

infix ` ≃ᵢ `:25 := isometric

namespace isometric

section pseudo_emetric_space
variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]

instance : has_coe_to_fun (α ≃ᵢ β) := ⟨λ_, α → β, λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : α ≃ᵢ β) (a : α) : h a = h.to_equiv a := rfl

@[simp] lemma coe_to_equiv (h : α ≃ᵢ β) : ⇑h.to_equiv = h := rfl

protected lemma isometry (h : α ≃ᵢ β) : isometry h := h.isometry_to_fun

protected lemma bijective (h : α ≃ᵢ β) : bijective h := h.to_equiv.bijective
protected lemma injective (h : α ≃ᵢ β) : injective h := h.to_equiv.injective
protected lemma surjective (h : α ≃ᵢ β) : surjective h := h.to_equiv.surjective

protected lemma edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
h.isometry.edist_eq x y

protected lemma dist_eq {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β] (h : α ≃ᵢ β)
  (x y : α) : dist (h x) (h y) = dist x y :=
h.isometry.dist_eq x y

protected lemma continuous (h : α ≃ᵢ β) : continuous h := h.isometry.continuous

@[simp] lemma ediam_image (h : α ≃ᵢ β) (s : set α) : emetric.diam (h '' s) = emetric.diam s :=
h.isometry.ediam_image s

lemma to_equiv_inj : ∀ ⦃h₁ h₂ : α ≃ᵢ β⦄, (h₁.to_equiv = h₂.to_equiv) → h₁ = h₂
| ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ H := by { dsimp at H, subst e₁ }

@[ext] lemma ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
to_equiv_inj $ equiv.ext H

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
def mk' {α : Type u} [emetric_space α] (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x)
  (hf : isometry f) : α ≃ᵢ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ x, hf.injective $ hfg _,
  right_inv := hfg,
  isometry_to_fun := hf }

/-- The identity isometry of a space. -/
protected def refl (α : Type*) [pseudo_emetric_space α] : α ≃ᵢ α :=
{ isometry_to_fun := isometry_id, .. equiv.refl α }

/-- The composition of two isometric isomorphisms, as an isometric isomorphism. -/
protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
{ isometry_to_fun  := h₂.isometry_to_fun.comp h₁.isometry_to_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

@[simp] lemma trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x) := rfl

/-- The inverse of an isometric isomorphism, as an isometric isomorphism. -/
protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α :=
{ isometry_to_fun  := h.isometry.right_inv h.right_inv,
  to_equiv := h.to_equiv.symm }

@[simp] lemma symm_symm (h : α ≃ᵢ β) : h.symm.symm = h := to_equiv_inj h.to_equiv.symm_symm

@[simp] lemma apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y :=
h.to_equiv.apply_symm_apply y

@[simp] lemma symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x :=
h.to_equiv.symm_apply_apply x

lemma symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} :
  h.symm y = x ↔ y = h x :=
h.to_equiv.symm_apply_eq

lemma eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} :
  x = h.symm y ↔ h x = y :=
h.to_equiv.eq_symm_apply

lemma symm_comp_self (h : α ≃ᵢ β) : ⇑h.symm ∘ ⇑h = id :=
funext $ assume a, h.to_equiv.left_inv a

lemma self_comp_symm (h : α ≃ᵢ β) : ⇑h ∘ ⇑h.symm = id :=
funext $ assume a, h.to_equiv.right_inv a

@[simp] lemma range_eq_univ (h : α ≃ᵢ β) : range h = univ :=
h.to_equiv.range_eq_univ

lemma image_symm (h : α ≃ᵢ β) : image h.symm = preimage h :=
image_eq_preimage_of_inverse h.symm.to_equiv.left_inv h.symm.to_equiv.right_inv

lemma preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h :=
(image_eq_preimage_of_inverse h.to_equiv.left_inv h.to_equiv.right_inv).symm

@[simp] lemma symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
  (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) := rfl

lemma ediam_univ (h : α ≃ᵢ β) : emetric.diam (univ : set α) = emetric.diam (univ : set β) :=
by rw [← h.range_eq_univ, h.isometry.ediam_range]

@[simp] lemma ediam_preimage (h : α ≃ᵢ β) (s : set β) : emetric.diam (h ⁻¹' s) = emetric.diam s :=
by rw [← image_symm, ediam_image]

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
protected def to_homeomorph (h : α ≃ᵢ β) : α ≃ₜ β :=
{ continuous_to_fun  := h.continuous,
  continuous_inv_fun := h.symm.continuous,
  to_equiv := h.to_equiv }

@[simp] lemma coe_to_homeomorph (h : α ≃ᵢ β) : ⇑(h.to_homeomorph) = h := rfl

@[simp] lemma coe_to_homeomorph_symm (h : α ≃ᵢ β) : ⇑(h.to_homeomorph.symm) = h.symm := rfl

@[simp] lemma to_homeomorph_to_equiv (h : α ≃ᵢ β) :
  h.to_homeomorph.to_equiv = h.to_equiv :=
rfl

@[simp] lemma comp_continuous_on_iff {γ} [topological_space γ] (h : α ≃ᵢ β)
  {f : γ → α} {s : set γ} :
  continuous_on (h ∘ f) s ↔ continuous_on f s :=
h.to_homeomorph.comp_continuous_on_iff _ _

@[simp] lemma comp_continuous_iff {γ} [topological_space γ] (h : α ≃ᵢ β) {f : γ → α} :
  continuous (h ∘ f) ↔ continuous f :=
h.to_homeomorph.comp_continuous_iff

@[simp] lemma comp_continuous_iff' {γ} [topological_space γ] (h : α ≃ᵢ β) {f : β → γ} :
  continuous (f ∘ h) ↔ continuous f :=
h.to_homeomorph.comp_continuous_iff'

/-- The group of isometries. -/
instance : group (α ≃ᵢ α) :=
  { one := isometric.refl _,
    mul := λ e₁ e₂, e₂.trans e₁,
    inv := isometric.symm,
    mul_assoc := λ e₁ e₂ e₃, rfl,
    one_mul := λ e, ext $ λ _, rfl,
    mul_one := λ e, ext $ λ _, rfl,
    mul_left_inv := λ e, ext e.symm_apply_apply }

@[simp] lemma coe_one : ⇑(1 : α ≃ᵢ α) = id := rfl

@[simp] lemma coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl

lemma mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp] lemma inv_apply_self (e : α ≃ᵢ α) (x: α) : e⁻¹ (e x) = x := e.symm_apply_apply x

@[simp] lemma apply_inv_self (e : α ≃ᵢ α) (x: α) : e (e⁻¹ x) = x := e.apply_symm_apply x

protected lemma complete_space (e : α ≃ᵢ β) (hF : complete_space β) : complete_space α :=
complete_space_of_is_complete_univ $ is_complete_of_complete_image e.isometry.uniform_inducing $
  by rwa [set.image_univ, isometric.range_eq_univ, ← complete_space_iff_is_complete_univ]

lemma complete_space_iff (e : α ≃ᵢ β) : complete_space α ↔ complete_space β :=
⟨λ h, e.symm.complete_space h, λ h, e.complete_space h⟩

end pseudo_emetric_space

section pseudo_metric_space

variables [pseudo_metric_space α] [pseudo_metric_space β] (h : α ≃ᵢ β)

@[simp] lemma diam_image (s : set α) : metric.diam (h '' s) = metric.diam s :=
h.isometry.diam_image s

@[simp] lemma diam_preimage (s : set β) : metric.diam (h ⁻¹' s) = metric.diam s :=
by rw [← image_symm, diam_image]

lemma diam_univ : metric.diam (univ : set α) = metric.diam (univ : set β) :=
congr_arg ennreal.to_real h.ediam_univ

end pseudo_metric_space

end isometric

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
def isometry.isometric_on_range [emetric_space α] [pseudo_emetric_space β] {f : α → β}
  (h : isometry f) : α ≃ᵢ range f :=
{ isometry_to_fun := λx y, by simpa [subtype.edist_eq] using h x y,
  .. equiv.of_injective f h.injective }

@[simp] lemma isometry.isometric_on_range_apply [emetric_space α] [pseudo_emetric_space β]
  {f : α → β} (h : isometry f) (x : α) : h.isometric_on_range x = ⟨f x, mem_range_self _⟩ :=
rfl
