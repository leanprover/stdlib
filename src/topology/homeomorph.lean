/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import topology.dense_embedding

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions

* `homeomorph α β`: The type of homeomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ₜ β`.

# Main results

* Pretty much every topological property is preserved under homeomorphisms.
* `homeomorph.homeomorph_of_continuous_open`: A continuous bijection that is
  an open map is a homeomorphism.

-/

open set filter
open_locale topological_space

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- Homeomorphism between `α` and `β`, also called topological isomorphism -/
@[nolint has_inhabited_instance] -- not all spaces are homeomorphic to each other
structure homeomorph (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  extends α ≃ β :=
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')
(continuous_inv_fun : continuous inv_fun . tactic.interactive.continuity')

infix ` ≃ₜ `:25 := homeomorph

namespace homeomorph
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

instance : has_coe_to_fun (α ≃ₜ β) := ⟨λ_, α → β, λe, e.to_equiv⟩

@[simp] lemma homeomorph_mk_coe (a : equiv α β) (b c) :
  ((homeomorph.mk a b c) : α → β) = a :=
rfl

@[simp] lemma coe_to_equiv (h : α ≃ₜ β) : ⇑h.to_equiv = h := rfl

/-- Inverse of a homeomorphism. -/
protected def symm (h : α ≃ₜ β) : β ≃ₜ α :=
{ continuous_to_fun  := h.continuous_inv_fun,
  continuous_inv_fun := h.continuous_to_fun,
  to_equiv := h.to_equiv.symm }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : α ≃ₜ β) : α → β := h
/-- See Note [custom simps projection] -/
def simps.symm_apply (h : α ≃ₜ β) : β → α := h.symm

initialize_simps_projections homeomorph
  (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply, -to_equiv)

lemma to_equiv_injective : function.injective (to_equiv : α ≃ₜ β → α ≃ β)
| ⟨e, h₁, h₂⟩ ⟨e', h₁', h₂'⟩ rfl := rfl

@[ext] lemma ext {h h' : α ≃ₜ β} (H : ∀ x, h x = h' x) : h = h' :=
to_equiv_injective $ equiv.ext H

/-- Identity map as a homeomorphism. -/
@[simps apply {fully_applied := ff}]
protected def refl (α : Type*) [topological_space α] : α ≃ₜ α :=
{ continuous_to_fun := continuous_id,
  continuous_inv_fun := continuous_id,
  to_equiv := equiv.refl α }

/-- Composition of two homeomorphisms. -/
protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ :=
{ continuous_to_fun  := h₂.continuous_to_fun.comp h₁.continuous_to_fun,
  continuous_inv_fun := h₁.continuous_inv_fun.comp h₂.continuous_inv_fun,
  to_equiv := equiv.trans h₁.to_equiv h₂.to_equiv }

@[simp] lemma homeomorph_mk_coe_symm (a : equiv α β) (b c) :
  ((homeomorph.mk a b c).symm : β → α) = a.symm :=
rfl

@[simp] lemma refl_symm : (homeomorph.refl α).symm = homeomorph.refl α := rfl

@[continuity]
protected lemma continuous (h : α ≃ₜ β) : continuous h := h.continuous_to_fun

@[continuity] -- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
protected lemma continuous_symm (h : α ≃ₜ β) : continuous (h.symm) := h.continuous_inv_fun

@[simp] lemma apply_symm_apply (h : α ≃ₜ β) (x : β) : h (h.symm x) = x :=
h.to_equiv.apply_symm_apply x

@[simp] lemma symm_apply_apply (h : α ≃ₜ β) (x : α) : h.symm (h x) = x :=
h.to_equiv.symm_apply_apply x

protected lemma bijective (h : α ≃ₜ β) : function.bijective h := h.to_equiv.bijective
protected lemma injective (h : α ≃ₜ β) : function.injective h := h.to_equiv.injective
protected lemma surjective (h : α ≃ₜ β) : function.surjective h := h.to_equiv.surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def change_inv (f : α ≃ₜ β) (g : β → α) (hg : function.right_inverse g f) : α ≃ₜ β :=
have g = f.symm, from funext (λ x, calc g x = f.symm (f (g x)) : (f.left_inv (g x)).symm
                                        ... = f.symm x : by rw hg x),
{ to_fun := f,
  inv_fun := g,
  left_inv := by convert f.left_inv,
  right_inv := by convert f.right_inv,
  continuous_to_fun := f.continuous,
  continuous_inv_fun := by convert f.symm.continuous }

@[simp] lemma symm_comp_self (h : α ≃ₜ β) : ⇑h.symm ∘ ⇑h = id :=
funext h.symm_apply_apply

@[simp] lemma self_comp_symm (h : α ≃ₜ β) : ⇑h ∘ ⇑h.symm = id :=
funext h.apply_symm_apply

@[simp] lemma range_coe (h : α ≃ₜ β) : range h = univ :=
h.surjective.range_eq

lemma image_symm (h : α ≃ₜ β) : image h.symm = preimage h :=
funext h.symm.to_equiv.image_eq_preimage

lemma preimage_symm (h : α ≃ₜ β) : preimage h.symm = image h :=
(funext h.to_equiv.image_eq_preimage).symm

@[simp] lemma image_preimage (h : α ≃ₜ β) (s : set β) : h '' (h ⁻¹' s) = s :=
h.to_equiv.image_preimage s

@[simp] lemma preimage_image (h : α ≃ₜ β) (s : set α) : h ⁻¹' (h '' s) = s :=
h.to_equiv.preimage_image s

protected lemma inducing (h : α ≃ₜ β) : inducing h :=
inducing_of_inducing_compose h.continuous h.symm.continuous $
  by simp only [symm_comp_self, inducing_id]

lemma induced_eq (h : α ≃ₜ β) : topological_space.induced h ‹_› = ‹_› := h.inducing.1.symm

protected lemma quotient_map (h : α ≃ₜ β) : quotient_map h :=
quotient_map.of_quotient_map_compose h.symm.continuous h.continuous $
  by simp only [self_comp_symm, quotient_map.id]

lemma coinduced_eq (h : α ≃ₜ β) : topological_space.coinduced h ‹_› = ‹_› :=
h.quotient_map.2.symm

protected lemma embedding (h : α ≃ₜ β) : embedding h :=
⟨h.inducing, h.injective⟩

/-- Homeomorphism given an embedding. -/
noncomputable def of_embedding (f : α → β) (hf : embedding f) : α ≃ₜ (set.range f) :=
{ continuous_to_fun := continuous_subtype_mk _ hf.continuous,
  continuous_inv_fun := by simp [hf.continuous_iff, continuous_subtype_coe],
  .. equiv.of_injective f hf.inj }

protected lemma second_countable_topology [topological_space.second_countable_topology β]
  (h : α ≃ₜ β) :
  topological_space.second_countable_topology α :=
h.inducing.second_countable_topology

lemma compact_image {s : set α} (h : α ≃ₜ β) : is_compact (h '' s) ↔ is_compact s :=
h.embedding.is_compact_iff_is_compact_image.symm

lemma compact_preimage {s : set β} (h : α ≃ₜ β) : is_compact (h ⁻¹' s) ↔ is_compact s :=
by rw ← image_symm; exact h.symm.compact_image

protected lemma dense_embedding (h : α ≃ₜ β) : dense_embedding h :=
{ dense   := h.surjective.dense_range,
  .. h.embedding }

@[simp] lemma is_open_preimage (h : α ≃ₜ β) {s : set β} : is_open (h ⁻¹' s) ↔ is_open s :=
h.quotient_map.is_open_preimage

@[simp] lemma is_open_image (h : α ≃ₜ β) {s : set α} : is_open (h '' s) ↔ is_open s :=
by rw [← preimage_symm, is_open_preimage]

@[simp] lemma is_closed_preimage (h : α ≃ₜ β) {s : set β} : is_closed (h ⁻¹' s) ↔ is_closed s :=
by simp only [← is_open_compl_iff, ← preimage_compl, is_open_preimage]

@[simp] lemma is_closed_image (h : α ≃ₜ β) {s : set α} : is_closed (h '' s) ↔ is_closed s :=
by rw [← preimage_symm, is_closed_preimage]

lemma preimage_closure (h : α ≃ₜ β) (s : set β) : h ⁻¹' (closure s) = closure (h ⁻¹' s) :=
by rw [h.embedding.closure_eq_preimage_closure_image, h.image_preimage]

lemma image_closure (h : α ≃ₜ β) (s : set α) : h '' (closure s) = closure (h '' s) :=
by rw [← preimage_symm, preimage_closure]

protected lemma is_open_map (h : α ≃ₜ β) : is_open_map h := λ s, h.is_open_image.2

protected lemma is_closed_map (h : α ≃ₜ β) : is_closed_map h := λ s, h.is_closed_image.2

protected lemma closed_embedding (h : α ≃ₜ β) : closed_embedding h :=
closed_embedding_of_embedding_closed h.embedding h.is_closed_map

@[simp] lemma map_nhds_eq (h : α ≃ₜ β) (x : α) : map h (𝓝 x) = 𝓝 (h x) :=
h.embedding.map_nhds_of_mem _ (by simp)

lemma symm_map_nhds_eq (h : α ≃ₜ β) (x : α) : map h.symm (𝓝 (h x)) = 𝓝 x :=
by rw [h.symm.map_nhds_eq, h.symm_apply_apply]

lemma nhds_eq_comap (h : α ≃ₜ β) (x : α) : 𝓝 x = comap h (𝓝 (h x)) :=
h.embedding.to_inducing.nhds_eq_comap x

@[simp] lemma comap_nhds_eq (h : α ≃ₜ β) (y : β) : comap h (𝓝 y) = 𝓝 (h.symm y) :=
by rw [h.nhds_eq_comap, h.apply_symm_apply]

/-- If an bijective map `e : α ≃ β` is continuous and open, then it is a homeomorphism. -/
def homeomorph_of_continuous_open (e : α ≃ β) (h₁ : continuous e) (h₂ : is_open_map e) :
  α ≃ₜ β :=
{ continuous_to_fun := h₁,
  continuous_inv_fun := begin
    rw continuous_def,
    intros s hs,
    convert ← h₂ s hs using 1,
    apply e.image_eq_preimage
  end,
  to_equiv := e }

@[simp] lemma comp_continuous_on_iff (h : α ≃ₜ β) (f : γ → α) (s : set γ) :
  continuous_on (h ∘ f) s ↔ continuous_on f s :=
h.inducing.continuous_on_iff.symm

@[simp] lemma comp_continuous_iff (h : α ≃ₜ β) {f : γ → α} :
  continuous (h ∘ f) ↔ continuous f :=
h.inducing.continuous_iff.symm

@[simp] lemma comp_continuous_iff' (h : α ≃ₜ β) {f : β → γ} :
  continuous (f ∘ h) ↔ continuous f :=
h.quotient_map.continuous_iff.symm

/-- If two sets are equal, then they are homeomorphic. -/
def set_congr {s t : set α} (h : s = t) : s ≃ₜ t :=
{ continuous_to_fun := continuous_subtype_mk _ continuous_subtype_val,
  continuous_inv_fun := continuous_subtype_mk _ continuous_subtype_val,
  to_equiv := equiv.set_congr h }

/-- Sum of two homeomorphisms. -/
def sum_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α ⊕ γ ≃ₜ β ⊕ δ :=
{ continuous_to_fun  :=
  begin
    convert continuous_sum_rec (continuous_inl.comp h₁.continuous)
      (continuous_inr.comp h₂.continuous),
    ext x, cases x; refl,
  end,
  continuous_inv_fun :=
  begin
    convert continuous_sum_rec (continuous_inl.comp h₁.symm.continuous)
      (continuous_inr.comp h₂.symm.continuous),
    ext x, cases x; refl
  end,
  to_equiv := h₁.to_equiv.sum_congr h₂.to_equiv }

/-- Product of two homeomorphisms. -/
def prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ :=
{ continuous_to_fun  := (h₁.continuous.comp continuous_fst).prod_mk
    (h₂.continuous.comp continuous_snd),
  continuous_inv_fun := (h₁.symm.continuous.comp continuous_fst).prod_mk
    (h₂.symm.continuous.comp continuous_snd),
  to_equiv := h₁.to_equiv.prod_congr h₂.to_equiv }

@[simp] lemma prod_congr_symm (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) :
  (h₁.prod_congr h₂).symm = h₁.symm.prod_congr h₂.symm := rfl

@[simp] lemma coe_prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) :
  ⇑(h₁.prod_congr h₂) = prod.map h₁ h₂ := rfl

section
variables (α β γ)

/-- `α × β` is homeomorphic to `β × α`. -/
def prod_comm : α × β ≃ₜ β × α :=
{ continuous_to_fun  := continuous_snd.prod_mk continuous_fst,
  continuous_inv_fun := continuous_snd.prod_mk continuous_fst,
  to_equiv := equiv.prod_comm α β }

@[simp] lemma prod_comm_symm : (prod_comm α β).symm = prod_comm β α := rfl
@[simp] lemma coe_prod_comm : ⇑(prod_comm α β) = prod.swap := rfl

/-- `(α × β) × γ` is homeomorphic to `α × (β × γ)`. -/
def prod_assoc : (α × β) × γ ≃ₜ α × (β × γ) :=
{ continuous_to_fun  := (continuous_fst.comp continuous_fst).prod_mk
    ((continuous_snd.comp continuous_fst).prod_mk continuous_snd),
  continuous_inv_fun := (continuous_fst.prod_mk (continuous_fst.comp continuous_snd)).prod_mk
    (continuous_snd.comp continuous_snd),
  to_equiv := equiv.prod_assoc α β γ }

/-- `α × {*}` is homeomorphic to `α`. -/
@[simps apply {fully_applied := ff}]
def prod_punit : α × punit ≃ₜ α :=
{ to_equiv := equiv.prod_punit α,
  continuous_to_fun := continuous_fst,
  continuous_inv_fun := continuous_id.prod_mk continuous_const }

/-- `{*} × α` is homeomorphic to `α`. -/
def punit_prod : punit × α ≃ₜ α :=
(prod_comm _ _).trans (prod_punit _)

@[simp] lemma coe_punit_prod : ⇑(punit_prod α) = prod.snd := rfl

end

/-- `ulift α` is homeomorphic to `α`. -/
def {u v} ulift {α : Type u} [topological_space α] : ulift.{v u} α ≃ₜ α :=
{ continuous_to_fun := continuous_ulift_down,
  continuous_inv_fun := continuous_ulift_up,
  to_equiv := equiv.ulift }

section distrib

/-- `(α ⊕ β) × γ` is homeomorphic to `α × γ ⊕ β × γ`. -/
def sum_prod_distrib : (α ⊕ β) × γ ≃ₜ α × γ ⊕ β × γ :=
begin
  refine (homeomorph.homeomorph_of_continuous_open (equiv.sum_prod_distrib α β γ).symm _ _).symm,
  { convert continuous_sum_rec
      ((continuous_inl.comp continuous_fst).prod_mk continuous_snd)
      ((continuous_inr.comp continuous_fst).prod_mk continuous_snd),
    ext1 x, cases x; refl, },
  { exact (is_open_map_sum
    (open_embedding_inl.prod open_embedding_id).is_open_map
    (open_embedding_inr.prod open_embedding_id).is_open_map) }
end

/-- `α × (β ⊕ γ)` is homeomorphic to `α × β ⊕ α × γ`. -/
def prod_sum_distrib : α × (β ⊕ γ) ≃ₜ α × β ⊕ α × γ :=
(prod_comm _ _).trans $
sum_prod_distrib.trans $
sum_congr (prod_comm _ _) (prod_comm _ _)

variables {ι : Type*} {σ : ι → Type*} [Π i, topological_space (σ i)]

/-- `(Σ i, σ i) × β` is homeomorphic to `Σ i, (σ i × β)`. -/
def sigma_prod_distrib : ((Σ i, σ i) × β) ≃ₜ (Σ i, (σ i × β)) :=
homeomorph.symm $
homeomorph_of_continuous_open (equiv.sigma_prod_distrib σ β).symm
  (continuous_sigma $ λ i,
    (continuous_sigma_mk.comp continuous_fst).prod_mk continuous_snd)
  (is_open_map_sigma $ λ i,
    (open_embedding_sigma_mk.prod open_embedding_id).is_open_map)

end distrib

/--
A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
def image (e : α ≃ₜ β) (s : set α) : s ≃ₜ e '' s :=
{ continuous_to_fun := by continuity!,
  continuous_inv_fun := by continuity!,
  ..e.to_equiv.image s, }

end homeomorph
