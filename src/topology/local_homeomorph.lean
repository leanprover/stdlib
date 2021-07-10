/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.equiv.local_equiv
import topology.opens

/-!
# Local homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`local_homeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.to_fun x` and `e.inv_fun x`.

## Main definitions

`homeomorph.to_local_homeomorph`: associating a local homeomorphism to a homeomorphism, with
                                  source = target = univ
`local_homeomorph.symm`  : the inverse of a local homeomorphism
`local_homeomorph.trans` : the composition of two local homeomorphisms
`local_homeomorph.refl`  : the identity local homeomorphism
`local_homeomorph.of_set`: the identity on a set `s`
`eq_on_source`           : equivalence relation describing the "right" notion of equality for local
                           homeomorphisms

## Implementation notes

Most statements are copied from their local_equiv versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `local_equiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `local_equiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

open function set filter topological_space (second_countable_topology)
open_locale topological_space

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
[topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

/-- local homeomorphisms, defined on open subsets of the space -/
@[nolint has_inhabited_instance]
structure local_homeomorph (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  extends local_equiv α β :=
(open_source        : is_open source)
(open_target        : is_open target)
(continuous_to_fun  : continuous_on to_fun source)
(continuous_inv_fun : continuous_on inv_fun target)

/-- A homeomorphism induces a local homeomorphism on the whole space -/
def homeomorph.to_local_homeomorph (e : α ≃ₜ β) :
  local_homeomorph α β :=
{ open_source        := is_open_univ,
  open_target        := is_open_univ,
  continuous_to_fun  := by { erw ← continuous_iff_continuous_on_univ, exact e.continuous_to_fun },
  continuous_inv_fun := by { erw ← continuous_iff_continuous_on_univ, exact e.continuous_inv_fun },
  ..e.to_equiv.to_local_equiv }

namespace local_homeomorph

variables (e : local_homeomorph α β) (e' : local_homeomorph β γ)

instance : has_coe_to_fun (local_homeomorph α β) := ⟨_, λ e, e.to_local_equiv.to_fun⟩

/-- The inverse of a local homeomorphism -/
protected def symm : local_homeomorph β α :=
{ open_source        := e.open_target,
  open_target        := e.open_source,
  continuous_to_fun  := e.continuous_inv_fun,
  continuous_inv_fun := e.continuous_to_fun,
  ..e.to_local_equiv.symm }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (e : local_homeomorph α β) : α → β := e
/-- See Note [custom simps projection] -/
def simps.symm_apply (e : local_homeomorph α β) : β → α := e.symm

initialize_simps_projections local_homeomorph
  (to_local_equiv_to_fun → apply, to_local_equiv_inv_fun → symm_apply,
   to_local_equiv_source → source, to_local_equiv_target → target, -to_local_equiv)

protected lemma continuous_on : continuous_on e e.source := e.continuous_to_fun

lemma continuous_on_symm : continuous_on e.symm e.target := e.continuous_inv_fun

@[simp, mfld_simps] lemma mk_coe (e : local_equiv α β) (a b c d) :
  (local_homeomorph.mk e a b c d : α → β) = e := rfl

@[simp, mfld_simps] lemma mk_coe_symm (e : local_equiv α β) (a b c d) :
  ((local_homeomorph.mk e a b c d).symm : β → α) = e.symm := rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp, mfld_simps] lemma to_fun_eq_coe (e : local_homeomorph α β) : e.to_fun = e := rfl

@[simp, mfld_simps] lemma inv_fun_eq_coe (e : local_homeomorph α β) : e.inv_fun = e.symm := rfl

@[simp, mfld_simps] lemma coe_coe : (e.to_local_equiv : α → β) = e := rfl

@[simp, mfld_simps] lemma coe_coe_symm : (e.to_local_equiv.symm : β → α) = e.symm := rfl

@[simp, mfld_simps] lemma map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
e.map_source' h

@[simp, mfld_simps] lemma map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
e.map_target' h

@[simp, mfld_simps] lemma left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
e.left_inv' h

@[simp, mfld_simps] lemma right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
e.right_inv' h

protected lemma maps_to : maps_to e e.source e.target := λ x, e.map_source
protected lemma symm_maps_to : maps_to e.symm e.target e.source := e.symm.maps_to
protected lemma left_inv_on : left_inv_on e.symm e e.source := λ x, e.left_inv
protected lemma right_inv_on : right_inv_on e.symm e e.target := λ x, e.right_inv
protected lemma inv_on : inv_on e.symm e e.source e.target := ⟨e.left_inv_on, e.right_inv_on⟩
protected lemma inj_on : inj_on e e.source := e.left_inv_on.inj_on
protected lemma bij_on : bij_on e e.source e.target := e.inv_on.bij_on e.maps_to e.symm_maps_to
protected lemma surj_on : surj_on e e.source e.target := e.bij_on.surj_on

/-- Replace `to_local_equiv` field to provide better definitional equalities. -/
def replace_equiv (e : local_homeomorph α β) (e' : local_equiv α β) (h : e.to_local_equiv = e') :
  local_homeomorph α β :=
{ to_local_equiv := e',
  open_source := h ▸ e.open_source,
  open_target := h ▸ e.open_target,
  continuous_to_fun := h ▸ e.continuous_to_fun,
  continuous_inv_fun := h ▸ e.continuous_inv_fun }

lemma replace_equiv_eq_self (e : local_homeomorph α β) (e' : local_equiv α β)
  (h : e.to_local_equiv = e') :
  e.replace_equiv e' h = e :=
by { cases e, subst e', refl }

lemma source_preimage_target : e.source ⊆ e ⁻¹' e.target := e.maps_to

lemma eq_of_local_equiv_eq {e e' : local_homeomorph α β}
  (h : e.to_local_equiv = e'.to_local_equiv) : e = e' :=
by { cases e, cases e', cases h, refl }

lemma eventually_left_inverse (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
(e.open_source.eventually_mem hx).mono e.left_inv'

lemma eventually_left_inverse' (e : local_homeomorph α β) {x} (hx : x ∈ e.target) :
  ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
e.eventually_left_inverse (e.map_target hx)

lemma eventually_right_inverse (e : local_homeomorph α β) {x} (hx : x ∈ e.target) :
  ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
(e.open_target.eventually_mem hx).mono e.right_inv'

lemma eventually_right_inverse' (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
e.eventually_right_inverse (e.map_source hx)

lemma eventually_ne_nhds_within (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  ∀ᶠ x' in 𝓝[{x}ᶜ] x, e x' ≠ e x :=
eventually_nhds_within_iff.2 $ (e.eventually_left_inverse hx).mono $
  λ x' hx', mt $ λ h, by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']

lemma nhds_within_source_inter {x} (hx : x ∈ e.source) (s : set α) :
  𝓝[e.source ∩ s] x = 𝓝[s] x :=
nhds_within_inter_of_mem (mem_nhds_within_of_mem_nhds $ is_open.mem_nhds e.open_source hx)

lemma nhds_within_target_inter {x} (hx : x ∈ e.target) (s : set β) :
  𝓝[e.target ∩ s] x = 𝓝[s] x :=
e.symm.nhds_within_source_inter hx s

lemma image_eq_target_inter_inv_preimage {s : set α} (h : s ⊆ e.source) :
  e '' s = e.target ∩ e.symm ⁻¹' s :=
e.to_local_equiv.image_eq_target_inter_inv_preimage h

lemma image_source_inter_eq' (s : set α) :
  e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
e.to_local_equiv.image_source_inter_eq' s

lemma image_source_inter_eq (s : set α) :
  e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
e.to_local_equiv.image_source_inter_eq s

lemma symm_image_eq_source_inter_preimage {s : set β} (h : s ⊆ e.target) :
  e.symm '' s = e.source ∩ e ⁻¹' s :=
e.symm.image_eq_target_inter_inv_preimage h

lemma symm_image_target_inter_eq (s : set β) :
  e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
e.symm.image_source_inter_eq _

lemma source_inter_preimage_inv_preimage (s : set α) :
  e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
e.to_local_equiv.source_inter_preimage_inv_preimage s

lemma target_inter_inv_preimage_preimage (s : set β) :
  e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
e.symm.source_inter_preimage_inv_preimage _

lemma source_inter_preimage_target_inter (s : set β) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_local_equiv.source_inter_preimage_target_inter s

/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected lemma ext (e' : local_homeomorph α β) (h : ∀x, e x = e' x)
  (hinv : ∀x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
eq_of_local_equiv_eq (local_equiv.ext h hinv hs)

@[simp, mfld_simps] lemma symm_to_local_equiv : e.symm.to_local_equiv = e.to_local_equiv.symm := rfl
-- The following lemmas are already simp via local_equiv
lemma symm_source : e.symm.source = e.target := rfl
lemma symm_target : e.symm.target = e.source := rfl
@[simp, mfld_simps] lemma symm_symm : e.symm.symm = e := eq_of_local_equiv_eq $ by simp

/-- A local homeomorphism is continuous at any point of its source -/
protected lemma continuous_at {x : α} (h : x ∈ e.source) : continuous_at e x :=
(e.continuous_on x h).continuous_at (is_open.mem_nhds e.open_source h)

/-- A local homeomorphism inverse is continuous at any point of its target -/
lemma continuous_at_symm {x : β} (h : x ∈ e.target) : continuous_at e.symm x :=
e.symm.continuous_at h

lemma tendsto_symm {x} (hx : x ∈ e.source) :
  tendsto e.symm (𝓝 (e x)) (𝓝 x) :=
by simpa only [continuous_at, e.left_inv hx] using e.continuous_at_symm (e.map_source hx)

lemma map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
le_antisymm (e.continuous_at hx) $
  le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)

lemma symm_map_nhds_eq {x} (hx : x ∈ e.source) :
  map e.symm (𝓝 (e x)) = 𝓝 x :=
(e.symm.map_nhds_eq $ e.map_source hx).trans $ by rw e.left_inv hx

lemma image_mem_nhds {x} (hx : x ∈ e.source) {s : set α} (hs : s ∈ 𝓝 x) :
  e '' s ∈ 𝓝 (e x) :=
e.map_nhds_eq hx ▸ filter.image_mem_map hs

lemma map_nhds_within_eq (e : local_homeomorph α β) {x} (hx : x ∈ e.source) (s : set α) :
  map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] (e x) :=
calc map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :
  congr_arg (map e) (e.nhds_within_source_inter hx _).symm
... = 𝓝[e '' (e.source ∩ s)] (e x) :
  (e.left_inv_on.mono $ inter_subset_left _ _).map_nhds_within_eq (e.left_inv hx)
    (e.continuous_at_symm (e.map_source hx)).continuous_within_at
    (e.continuous_at hx).continuous_within_at

lemma map_nhds_within_preimage_eq (e : local_homeomorph α β) {x} (hx : x ∈ e.source) (s : set β) :
  map e (𝓝[e ⁻¹' s] x) = 𝓝[s] (e x) :=
by rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
  e.nhds_within_target_inter (e.map_source hx)]

lemma preimage_open_of_open {s : set β} (hs : is_open s) : is_open (e.source ∩ e ⁻¹' s) :=
e.continuous_on.preimage_open_of_open e.open_source hs

/-!
### `local_homeomorph.is_image` relation

We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `local_equiv.is_image` for local homeomorphisms. In this section
we transfer API about `local_equiv.is_image` to local homeomorphisms and add a few
`local_homeomorph`-specific lemmas like `local_homeomorph.is_image.closure`.
-/

/-- We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def is_image (s : set α) (t : set β) : Prop := ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace is_image

variables {e} {s : set α} {t : set β} {x : α} {y : β}

lemma to_local_equiv (h : e.is_image s t) : e.to_local_equiv.is_image s t := h

lemma apply_mem_iff (h : e.is_image s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s := h hx

protected lemma symm (h : e.is_image s t) : e.symm.is_image t s := h.to_local_equiv.symm

lemma symm_apply_mem_iff (h : e.is_image s t) (hy : y ∈ e.target) : (e.symm y ∈ s ↔ y ∈ t) :=
h.symm hy

@[simp] lemma symm_iff : e.symm.is_image t s ↔ e.is_image s t := ⟨λ h, h.symm, λ h, h.symm⟩

protected lemma maps_to (h : e.is_image s t) : maps_to e (e.source ∩ s) (e.target ∩ t) :=
h.to_local_equiv.maps_to

lemma symm_maps_to (h : e.is_image s t) : maps_to e.symm (e.target ∩ t) (e.source ∩ s) :=
h.symm.maps_to

lemma image_eq (h : e.is_image s t) : e '' (e.source ∩ s) = e.target ∩ t :=
h.to_local_equiv.image_eq

lemma symm_image_eq (h : e.is_image s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
h.symm.image_eq

lemma iff_preimage_eq : e.is_image s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
local_equiv.is_image.iff_preimage_eq

alias iff_preimage_eq ↔ local_homeomorph.is_image.preimage_eq
  local_homeomorph.is_image.of_preimage_eq

lemma iff_symm_preimage_eq : e.is_image s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
symm_iff.symm.trans iff_preimage_eq

alias iff_symm_preimage_eq ↔ local_homeomorph.is_image.symm_preimage_eq
  local_homeomorph.is_image.of_symm_preimage_eq

lemma iff_symm_preimage_eq' :
  e.is_image s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t :=
by rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']

alias iff_symm_preimage_eq' ↔ local_homeomorph.is_image.symm_preimage_eq'
  local_homeomorph.is_image.of_symm_preimage_eq'

lemma iff_preimage_eq' : e.is_image s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
symm_iff.symm.trans iff_symm_preimage_eq'

alias iff_preimage_eq' ↔ local_homeomorph.is_image.preimage_eq'
  local_homeomorph.is_image.of_preimage_eq'

lemma of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.is_image s t :=
local_equiv.is_image.of_image_eq h

lemma of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.is_image s t :=
local_equiv.is_image.of_symm_image_eq h

protected lemma compl (h : e.is_image s t) : e.is_image sᶜ tᶜ :=
λ x hx, not_congr (h hx)

protected lemma inter {s' t'} (h : e.is_image s t) (h' : e.is_image s' t') :
  e.is_image (s ∩ s') (t ∩ t') :=
λ x hx, and_congr (h hx) (h' hx)

protected lemma union {s' t'} (h : e.is_image s t) (h' : e.is_image s' t') :
  e.is_image (s ∪ s') (t ∪ t') :=
λ x hx, or_congr (h hx) (h' hx)

protected lemma diff {s' t'} (h : e.is_image s t) (h' : e.is_image s' t') :
  e.is_image (s \ s') (t \ t') :=
h.inter h'.compl

lemma left_inv_on_piecewise {e' : local_homeomorph α β} [∀ i, decidable (i ∈ s)]
  [∀ i, decidable (i ∈ t)] (h : e.is_image s t) (h' : e'.is_image s t) :
  left_inv_on (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
h.to_local_equiv.left_inv_on_piecewise h'

lemma inter_eq_of_inter_eq_of_eq_on {e' : local_homeomorph α β} (h : e.is_image s t)
  (h' : e'.is_image s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : eq_on e e' (e.source ∩ s)) :
  e.target ∩ t = e'.target ∩ t :=
h.to_local_equiv.inter_eq_of_inter_eq_of_eq_on h' hs Heq

lemma symm_eq_on_of_inter_eq_of_eq_on {e' : local_homeomorph α β} (h : e.is_image s t)
  (hs : e.source ∩ s = e'.source ∩ s) (Heq : eq_on e e' (e.source ∩ s)) :
  eq_on e.symm e'.symm (e.target ∩ t) :=
h.to_local_equiv.symm_eq_on_of_inter_eq_of_eq_on hs Heq

lemma map_nhds_within_eq (h : e.is_image s t) (hx : x ∈ e.source) :
  map e (𝓝[s] x) = 𝓝[t] (e x) :=
by rw [e.map_nhds_within_eq hx, h.image_eq, e.nhds_within_target_inter (e.map_source hx)]

protected lemma closure (h : e.is_image s t) : e.is_image (closure s) (closure t) :=
λ x hx, by simp only [mem_closure_iff_nhds_within_ne_bot, ← h.map_nhds_within_eq hx, map_ne_bot_iff]

protected lemma interior (h : e.is_image s t) : e.is_image (interior s) (interior t) :=
by simpa only [closure_compl, compl_compl] using h.compl.closure.compl

protected lemma frontier (h : e.is_image s t) :
  e.is_image (frontier s) (frontier t) :=
h.closure.diff h.interior

lemma is_open_iff (h : e.is_image s t) :
  is_open (e.source ∩ s) ↔ is_open (e.target ∩ t) :=
⟨λ hs, h.symm_preimage_eq' ▸ e.symm.preimage_open_of_open hs,
  λ hs, h.preimage_eq' ▸ e.preimage_open_of_open hs⟩

/-- Restrict a `local_homeomorph` to a pair of corresponding open sets. -/
@[simps to_local_equiv] def restr (h : e.is_image s t) (hs : is_open (e.source ∩ s)) :
  local_homeomorph α β :=
{ to_local_equiv := h.to_local_equiv.restr,
  open_source := hs,
  open_target := h.is_open_iff.1 hs,
  continuous_to_fun := e.continuous_on.mono (inter_subset_left _ _),
  continuous_inv_fun := e.symm.continuous_on.mono (inter_subset_left _ _) }

end is_image

lemma is_image_source_target : e.is_image e.source e.target :=
e.to_local_equiv.is_image_source_target

lemma is_image_source_target_of_disjoint (e' : local_homeomorph α β)
  (hs : disjoint e.source e'.source) (ht : disjoint e.target e'.target) :
  e.is_image e'.source e'.target :=
e.to_local_equiv.is_image_source_target_of_disjoint e'.to_local_equiv hs ht

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
lemma preimage_interior (s : set β) :
  e.source ∩ e ⁻¹' (interior s) = e.source ∩ interior (e ⁻¹' s) :=
(is_image.of_preimage_eq rfl).interior.preimage_eq

lemma preimage_closure (s : set β) :
  e.source ∩ e ⁻¹' (closure s) = e.source ∩ closure (e ⁻¹' s) :=
(is_image.of_preimage_eq rfl).closure.preimage_eq

lemma preimage_frontier (s : set β) :
  e.source ∩ e ⁻¹' (frontier s) = e.source ∩ frontier (e ⁻¹' s) :=
(is_image.of_preimage_eq rfl).frontier.preimage_eq

lemma preimage_open_of_open_symm {s : set α} (hs : is_open s) :
  is_open (e.target ∩ e.symm ⁻¹' s) :=
e.symm.continuous_on.preimage_open_of_open e.open_target hs

/-- The image of an open set in the source is open. -/
lemma image_open_of_open {s : set α} (hs : is_open s) (h : s ⊆ e.source) : is_open (e '' s) :=
begin
  have : e '' s = e.target ∩ e.symm ⁻¹' s :=
    e.to_local_equiv.image_eq_target_inter_inv_preimage h,
  rw this,
  exact e.continuous_on_symm.preimage_open_of_open e.open_target hs
end

/-- The image of the restriction of an open set to the source is open. -/
lemma image_open_of_open' {s : set α} (hs : is_open s) : is_open (e '' (e.source ∩ s)) :=
image_open_of_open _ (is_open.inter e.open_source hs) (inter_subset_left _ _)

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def of_continuous_open_restrict (e : local_equiv α β) (hc : continuous_on e e.source)
  (ho : is_open_map (e.source.restrict e)) (hs : is_open e.source) :
  local_homeomorph α β :=
{ to_local_equiv := e,
  open_source := hs,
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.is_open_range,
  continuous_to_fun := hc,
  continuous_inv_fun := e.image_source_eq_target ▸
    ho.continuous_on_image_of_left_inv_on e.left_inv_on }

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def of_continuous_open (e : local_equiv α β) (hc : continuous_on e e.source)
  (ho : is_open_map e) (hs : is_open e.source) :
  local_homeomorph α β :=
of_continuous_open_restrict e hc (ho.restrict hs) hs

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restr_open (s : set α) (hs : is_open s) :
  local_homeomorph α β :=
(@is_image.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr
  (is_open.inter e.open_source hs)

@[simp, mfld_simps] lemma restr_open_to_local_equiv (s : set α) (hs : is_open s) :
  (e.restr_open s hs).to_local_equiv = e.to_local_equiv.restr s := rfl

-- Already simp via local_equiv
lemma restr_open_source (s : set α) (hs : is_open s) :
  (e.restr_open s hs).source = e.source ∩ s := rfl

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
@[simps apply symm_apply (mfld_cfg), simps source target {attrs := []}]
protected def restr (s : set α) : local_homeomorph α β :=
e.restr_open (interior s) is_open_interior

@[simp, mfld_simps] lemma restr_to_local_equiv (s : set α) :
  (e.restr s).to_local_equiv = (e.to_local_equiv).restr (interior s) := rfl

lemma restr_source' (s : set α) (hs : is_open s) : (e.restr s).source = e.source ∩ s :=
by rw [e.restr_source, hs.interior_eq]

lemma restr_to_local_equiv' (s : set α) (hs : is_open s):
  (e.restr s).to_local_equiv = e.to_local_equiv.restr s :=
by rw [e.restr_to_local_equiv, hs.interior_eq]

lemma restr_eq_of_source_subset {e : local_homeomorph α β} {s : set α} (h : e.source ⊆ s) :
  e.restr s = e :=
begin
  apply eq_of_local_equiv_eq,
  rw restr_to_local_equiv,
  apply local_equiv.restr_eq_of_source_subset,
  exact interior_maximal h e.open_source
end

@[simp, mfld_simps] lemma restr_univ {e : local_homeomorph α β} : e.restr univ = e :=
restr_eq_of_source_subset (subset_univ _)

lemma restr_source_inter (s : set α) : e.restr (e.source ∩ s) = e.restr s :=
begin
  refine local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) _,
  simp [e.open_source.interior_eq, ← inter_assoc]
end

/-- The identity on the whole space as a local homeomorphism. -/
@[simps apply (mfld_cfg), simps source target {attrs := []}]
protected def refl (α : Type*) [topological_space α] : local_homeomorph α α :=
(homeomorph.refl α).to_local_homeomorph

@[simp, mfld_simps] lemma refl_local_equiv :
  (local_homeomorph.refl α).to_local_equiv = local_equiv.refl α := rfl
@[simp, mfld_simps] lemma refl_symm : (local_homeomorph.refl α).symm = local_homeomorph.refl α :=
rfl

section
variables {s : set α} (hs : is_open s)

/-- The identity local equiv on a set `s` -/
@[simps apply (mfld_cfg), simps source target {attrs := []}]
def of_set (s : set α) (hs : is_open s) : local_homeomorph α α :=
{ open_source        := hs,
  open_target        := hs,
  continuous_to_fun  := continuous_id.continuous_on,
  continuous_inv_fun := continuous_id.continuous_on,
  ..local_equiv.of_set s }

@[simp, mfld_simps] lemma of_set_to_local_equiv :
  (of_set s hs).to_local_equiv = local_equiv.of_set s := rfl
@[simp, mfld_simps] lemma of_set_symm : (of_set s hs).symm = of_set s hs := rfl

@[simp, mfld_simps] lemma of_set_univ_eq_refl :
  of_set univ is_open_univ = local_homeomorph.refl α :=
by ext; simp

end

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : local_homeomorph α γ :=
{ open_source       := e.open_source,
  open_target       := e'.open_target,
  continuous_to_fun := begin
    apply continuous_on.comp e'.continuous_to_fun e.continuous_to_fun,
    rw ← h,
    exact e.to_local_equiv.source_subset_preimage_target
  end,
  continuous_inv_fun := begin
    apply continuous_on.comp e.continuous_inv_fun e'.continuous_inv_fun,
    rw h,
    exact e'.to_local_equiv.target_subset_preimage_source
  end,
  ..local_equiv.trans' e.to_local_equiv e'.to_local_equiv h }

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : local_homeomorph α γ :=
  local_homeomorph.trans' (e.symm.restr_open e'.source e'.open_source).symm
    (e'.restr_open e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps] lemma trans_to_local_equiv :
  (e.trans e').to_local_equiv = e.to_local_equiv.trans e'.to_local_equiv := rfl
@[simp, mfld_simps] lemma coe_trans : (e.trans e' : α → γ) = e' ∘ e := rfl
@[simp, mfld_simps] lemma coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm := rfl

lemma trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm :=
by cases e; cases e'; refl

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
lemma trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
local_equiv.trans_source e.to_local_equiv e'.to_local_equiv

lemma trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
local_equiv.trans_source' e.to_local_equiv e'.to_local_equiv

lemma trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
local_equiv.trans_source'' e.to_local_equiv e'.to_local_equiv

lemma image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
local_equiv.image_trans_source e.to_local_equiv e'.to_local_equiv

lemma trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target := rfl

lemma trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
trans_source' e'.symm e.symm

lemma trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
trans_source'' e'.symm e.symm

lemma inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
image_trans_source e'.symm e.symm

lemma trans_assoc (e'' : local_homeomorph γ δ) :
  (e.trans e').trans e'' = e.trans (e'.trans e'') :=
eq_of_local_equiv_eq $ local_equiv.trans_assoc e.to_local_equiv e'.to_local_equiv e''.to_local_equiv

@[simp, mfld_simps] lemma trans_refl : e.trans (local_homeomorph.refl β) = e :=
eq_of_local_equiv_eq $ local_equiv.trans_refl e.to_local_equiv

@[simp, mfld_simps] lemma refl_trans : (local_homeomorph.refl α).trans e = e :=
eq_of_local_equiv_eq $ local_equiv.refl_trans e.to_local_equiv

lemma trans_of_set {s : set β} (hs : is_open s) :
  e.trans (of_set s hs) = e.restr (e ⁻¹' s) :=
local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) $
  by simp [local_equiv.trans_source, (e.preimage_interior _).symm, hs.interior_eq]

lemma trans_of_set' {s : set β} (hs : is_open s) :
  e.trans (of_set s hs) = e.restr (e.source ∩ e ⁻¹' s) :=
by rw [trans_of_set, restr_source_inter]

lemma of_set_trans {s : set α} (hs : is_open s) :
  (of_set s hs).trans e = e.restr s :=
local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) $
  by simp [local_equiv.trans_source, hs.interior_eq, inter_comm]

lemma of_set_trans' {s : set α} (hs : is_open s) :
  (of_set s hs).trans e = e.restr (e.source ∩ s) :=
by rw [of_set_trans, restr_source_inter]

@[simp, mfld_simps] lemma of_set_trans_of_set
  {s : set α} (hs : is_open s) {s' : set α} (hs' : is_open s') :
  (of_set s hs).trans (of_set s' hs') = of_set (s ∩ s') (is_open.inter hs hs')  :=
begin
  rw (of_set s hs).trans_of_set hs',
  ext; simp [hs'.interior_eq]
end

lemma restr_trans (s : set α) :
  (e.restr s).trans e' = (e.trans e').restr s :=
eq_of_local_equiv_eq $ local_equiv.restr_trans e.to_local_equiv e'.to_local_equiv (interior s)

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def eq_on_source (e e' : local_homeomorph α β) : Prop :=
e.source = e'.source ∧ (eq_on e e' e.source)

lemma eq_on_source_iff (e e' : local_homeomorph α β) :
eq_on_source e e' ↔ local_equiv.eq_on_source e.to_local_equiv e'.to_local_equiv :=
iff.rfl

/-- `eq_on_source` is an equivalence relation -/
instance : setoid (local_homeomorph α β) :=
{ r     := eq_on_source,
  iseqv := ⟨
    λe, (@local_equiv.eq_on_source_setoid α β).iseqv.1 e.to_local_equiv,
    λe e' h, (@local_equiv.eq_on_source_setoid α β).iseqv.2.1 ((eq_on_source_iff e e').1 h),
    λe e' e'' h h', (@local_equiv.eq_on_source_setoid α β).iseqv.2.2
      ((eq_on_source_iff e e').1 h) ((eq_on_source_iff e' e'').1 h')⟩ }

lemma eq_on_source_refl : e ≈ e := setoid.refl _

/-- If two local homeomorphisms are equivalent, so are their inverses -/
lemma eq_on_source.symm' {e e' : local_homeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
local_equiv.eq_on_source.symm' h

/-- Two equivalent local homeomorphisms have the same source -/
lemma eq_on_source.source_eq {e e' : local_homeomorph α β} (h : e ≈ e') : e.source = e'.source :=
h.1

/-- Two equivalent local homeomorphisms have the same target -/
lemma eq_on_source.target_eq {e e' : local_homeomorph α β} (h : e ≈ e') : e.target = e'.target :=
h.symm'.1

/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
lemma eq_on_source.eq_on {e e' : local_homeomorph α β} (h : e ≈ e') :
  eq_on e e' e.source :=
h.2

/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
lemma eq_on_source.symm_eq_on_target {e e' : local_homeomorph α β} (h : e ≈ e') :
  eq_on e.symm e'.symm e.target :=
h.symm'.2

/-- Composition of local homeomorphisms respects equivalence -/
lemma eq_on_source.trans' {e e' : local_homeomorph α β} {f f' : local_homeomorph β γ}
  (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
local_equiv.eq_on_source.trans' he hf

/-- Restriction of local homeomorphisms respects equivalence -/
lemma eq_on_source.restr {e e' : local_homeomorph α β} (he : e ≈ e') (s : set α) :
  e.restr s ≈ e'.restr s :=
local_equiv.eq_on_source.restr he _

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
lemma trans_self_symm :
  e.trans e.symm ≈ local_homeomorph.of_set e.source e.open_source :=
local_equiv.trans_self_symm _

lemma trans_symm_self :
  e.symm.trans e ≈ local_homeomorph.of_set e.target e.open_target :=
e.symm.trans_self_symm

lemma eq_of_eq_on_source_univ {e e' : local_homeomorph α β} (h : e ≈ e')
  (s : e.source = univ) (t : e.target = univ) : e = e' :=
eq_of_local_equiv_eq $ local_equiv.eq_of_eq_on_source_univ _ _ h s t

section prod

/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
@[simps to_local_equiv apply (mfld_cfg), simps source target symm_apply {attrs := []}]
def prod (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  local_homeomorph (α × γ) (β × δ) :=
{ open_source := e.open_source.prod e'.open_source,
  open_target := e.open_target.prod e'.open_target,
  continuous_to_fun := e.continuous_on.prod_map e'.continuous_on,
  continuous_inv_fun := e.continuous_on_symm.prod_map e'.continuous_on_symm,
  to_local_equiv := e.to_local_equiv.prod e'.to_local_equiv }

@[simp, mfld_simps] lemma prod_symm (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').symm = (e.symm.prod e'.symm) :=
rfl

@[simp, mfld_simps] lemma prod_trans
  {η : Type*} {ε : Type*} [topological_space η] [topological_space ε]
  (e : local_homeomorph α β) (f : local_homeomorph β γ)
  (e' : local_homeomorph δ η) (f' : local_homeomorph η ε) :
  (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
local_homeomorph.eq_of_local_equiv_eq $
  by dsimp only [trans_to_local_equiv, prod_to_local_equiv]; apply local_equiv.prod_trans

end prod

section piecewise

/-- Combine two `local_homeomorph`s using `set.piecewise`. The source of the new `local_homeomorph`
is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The
function sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t`
using `e'`, and similarly for the inverse function. To ensure that the maps `to_fun` and `inv_fun`
are inverse of each other on the new `source` and `target`, the definition assumes that the sets `s`
and `t` are related both by `e.is_image` and `e'.is_image`. To ensure that the new maps are
continuous on `source`/`target`, it also assumes that `e.source` and `e'.source` meet `frontier s`
on the same set and `e x = e' x` on this intersection. -/
@[simps to_local_equiv apply {fully_applied := ff}]
def piecewise (e e' : local_homeomorph α β) (s : set α) (t : set β)
  [∀ x, decidable (x ∈ s)] [∀ y, decidable (y ∈ t)] (H : e.is_image s t) (H' : e'.is_image s t)
  (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
  (Heq : eq_on e e' (e.source ∩ frontier s)) :
  local_homeomorph α β :=
{ to_local_equiv := e.to_local_equiv.piecewise e'.to_local_equiv s t H H',
  open_source := e.open_source.ite e'.open_source Hs,
  open_target := e.open_target.ite e'.open_target $
    H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq,
  continuous_to_fun := continuous_on_piecewise_ite e.continuous_on e'.continuous_on Hs Heq,
  continuous_inv_fun := continuous_on_piecewise_ite e.continuous_on_symm e'.continuous_on_symm
    (H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq)
    (H.frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq) }

@[simp] lemma symm_piecewise (e e' : local_homeomorph α β) {s : set α} {t : set β}
  [∀ x, decidable (x ∈ s)] [∀ y, decidable (y ∈ t)] (H : e.is_image s t) (H' : e'.is_image s t)
  (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
  (Heq : eq_on e e' (e.source ∩ frontier s)) :
  (e.piecewise e' s t H H' Hs Heq).symm =
    e.symm.piecewise e'.symm t s H.symm H'.symm
      (H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq)
      (H.frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq) :=
rfl

/-- Combine two `local_homeomorph`s with disjoint sources and disjoint targets. We reuse
`local_homeomorph.piecewise` then override `to_local_equiv` to `local_equiv.disjoint_union`.
This way we have better definitional equalities for `source` and `target`. -/
def disjoint_union (e e' : local_homeomorph α β)
  [∀ x, decidable (x ∈ e.source)] [∀ y, decidable (y ∈ e.target)]
  (Hs : disjoint e.source e'.source) (Ht : disjoint e.target e'.target) :
  local_homeomorph α β :=
(e.piecewise e' e.source e.target e.is_image_source_target
  (e'.is_image_source_target_of_disjoint e Hs.symm Ht.symm)
  (by rw [e.open_source.inter_frontier_eq, e'.open_source.inter_frontier_eq_empty_of_disjoint Hs])
  (by { rw e.open_source.inter_frontier_eq, exact eq_on_empty _ _ })).replace_equiv
    (e.to_local_equiv.disjoint_union e'.to_local_equiv Hs Ht)
    (local_equiv.disjoint_union_eq_piecewise _ _ _ _).symm

end piecewise

section pi

variables {ι : Type*} [fintype ι] {Xi Yi : ι → Type*} [Π i, topological_space (Xi i)]
  [Π i, topological_space (Yi i)] (ei : Π i, local_homeomorph (Xi i) (Yi i))

/-- The product of a finite family of `local_homeomorph`s. -/
@[simps to_local_equiv] def pi : local_homeomorph (Π i, Xi i) (Π i, Yi i) :=
{ to_local_equiv := local_equiv.pi (λ i, (ei i).to_local_equiv),
  open_source := is_open_set_pi finite_univ $ λ i hi, (ei i).open_source,
  open_target := is_open_set_pi finite_univ $ λ i hi, (ei i).open_target,
  continuous_to_fun := continuous_on_pi.2 $ λ i, (ei i).continuous_on.comp
    (continuous_apply _).continuous_on (λ f hf, hf i trivial),
  continuous_inv_fun := continuous_on_pi.2 $ λ i, (ei i).continuous_on_symm.comp
    (continuous_apply _).continuous_on (λ f hf, hf i trivial) }

end pi

section continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
lemma continuous_within_at_iff_continuous_within_at_comp_right
  {f : β → γ} {s : set β} {x : β} (h : x ∈ e.target) :
  continuous_within_at f s x ↔ continuous_within_at (f ∘ e) (e ⁻¹' s) (e.symm x) :=
by simp_rw [continuous_within_at, ← @tendsto_map'_iff _ _ _ _ e,
  e.map_nhds_within_preimage_eq (e.map_target h), (∘), e.right_inv h]

/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
lemma continuous_at_iff_continuous_at_comp_right
  {f : β → γ} {x : β} (h : x ∈ e.target) :
  continuous_at f x ↔ continuous_at (f ∘ e) (e.symm x) :=
by rw [← continuous_within_at_univ, e.continuous_within_at_iff_continuous_within_at_comp_right h,
       preimage_univ, continuous_within_at_univ]

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
lemma continuous_on_iff_continuous_on_comp_right {f : β → γ} {s : set β} (h : s ⊆ e.target) :
  continuous_on f s ↔ continuous_on (f ∘ e) (e.source ∩ e ⁻¹' s) :=
begin
  simp only [← e.symm_image_eq_source_inter_preimage h, continuous_on, ball_image_iff],
  refine forall_congr (λ x, forall_congr $ λ hx, _),
  rw [e.continuous_within_at_iff_continuous_within_at_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuous_within_at_inter],
  exact is_open.mem_nhds e.open_source (e.map_target (h hx))
end

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
lemma continuous_within_at_iff_continuous_within_at_comp_left
  {f : γ → α} {s : set γ} {x : γ} (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
  continuous_within_at f s x ↔ continuous_within_at (e ∘ f) s x :=
begin
  refine ⟨(e.continuous_at hx).tendsto.comp, λ fe_cont, _⟩,
  rw [← continuous_within_at_inter' h] at fe_cont ⊢,
  have : continuous_within_at (e.symm ∘ (e ∘ f)) (s ∩ f ⁻¹' e.source) x,
  { have : continuous_within_at e.symm univ (e (f x))
      := (e.continuous_at_symm (e.map_source hx)).continuous_within_at,
    exact continuous_within_at.comp this fe_cont (subset_univ _) },
  exact this.congr (λy hy, by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])
end

/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
lemma continuous_at_iff_continuous_at_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
  continuous_at f x ↔ continuous_at (e ∘ f) x :=
begin
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _),
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x, by rwa nhds_within_univ,
  rw [← continuous_within_at_univ, ← continuous_within_at_univ,
      e.continuous_within_at_iff_continuous_within_at_comp_left hx h']
end

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
lemma continuous_on_iff_continuous_on_comp_left {f : γ → α} {s : set γ} (h : s ⊆ f ⁻¹' e.source) :
  continuous_on f s ↔ continuous_on (e ∘ f) s :=
forall_congr $ λ x, forall_congr $ λ hx, e.continuous_within_at_iff_continuous_within_at_comp_left
  (h hx) (mem_sets_of_superset self_mem_nhds_within h)

end continuity

/-- A local homeomrphism defines a homeomorphism between its source and target. -/
def to_homeomorph_source_target : e.source ≃ₜ e.target :=
{ to_fun := e.maps_to.restrict _ _ _,
  inv_fun := e.symm_maps_to.restrict _ _ _,
  left_inv := λ x, subtype.eq $ e.left_inv x.2,
  right_inv := λ x, subtype.eq $ e.right_inv x.2,
  continuous_to_fun := continuous_subtype_mk _ $
    continuous_on_iff_continuous_restrict.1 e.continuous_on,
  continuous_inv_fun := continuous_subtype_mk _ $
    continuous_on_iff_continuous_restrict.1 e.symm.continuous_on }

lemma second_countable_topology_source [second_countable_topology β]
  (e : local_homeomorph α β) :
  second_countable_topology e.source :=
e.to_homeomorph_source_target.second_countable_topology

/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps apply symm_apply (mfld_cfg)]
def to_homeomorph_of_source_eq_univ_target_eq_univ (h : e.source = (univ : set α))
  (h' : e.target = univ) : α ≃ₜ β :=
{ to_fun := e,
  inv_fun := e.symm,
  left_inv := λx, e.left_inv $ by { rw h, exact mem_univ _ },
  right_inv := λx, e.right_inv $ by { rw h', exact mem_univ _ },
  continuous_to_fun := begin
    rw [continuous_iff_continuous_on_univ],
    convert e.continuous_to_fun,
    rw h
  end,
  continuous_inv_fun := begin
    rw [continuous_iff_continuous_on_univ],
    convert e.continuous_inv_fun,
    rw h'
  end }

/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
lemma to_open_embedding (h : e.source = set.univ) : open_embedding e :=
begin
  apply open_embedding_of_continuous_injective_open,
  { apply continuous_iff_continuous_on_univ.mpr,
    rw ← h,
    exact e.continuous_to_fun },
  { apply set.injective_iff_inj_on_univ.mpr,
    rw ← h,
    exact e.inj_on },
  { intros U hU,
    simpa only [h, subset_univ] with mfld_simps using e.image_open_of_open hU}
end

end local_homeomorph

namespace homeomorph
variables (e : α ≃ₜ β) (e' : β ≃ₜ γ)
/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/

attribute [simps apply source target {simp_rhs := tt, .. mfld_cfg}] to_local_homeomorph

@[simp, mfld_simps] lemma to_local_homeomorph_coe_symm :
  (e.to_local_homeomorph.symm : β → α) = e.symm := rfl
@[simp, mfld_simps] lemma refl_to_local_homeomorph :
  (homeomorph.refl α).to_local_homeomorph = local_homeomorph.refl α := rfl
@[simp, mfld_simps] lemma symm_to_local_homeomorph :
  e.symm.to_local_homeomorph = e.to_local_homeomorph.symm := rfl
@[simp, mfld_simps] lemma trans_to_local_homeomorph :
  (e.trans e').to_local_homeomorph = e.to_local_homeomorph.trans e'.to_local_homeomorph :=
local_homeomorph.eq_of_local_equiv_eq $ equiv.trans_to_local_equiv _ _

end homeomorph

namespace open_embedding
variables (f : α → β) (h : open_embedding f)

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
@[simps apply source target (mfld_cfg)]
noncomputable def to_local_homeomorph [nonempty α] : local_homeomorph α β :=
local_homeomorph.of_continuous_open
  ((h.to_embedding.inj.inj_on univ).to_local_equiv _ _)
  h.continuous.continuous_on h.is_open_map is_open_univ

lemma continuous_at_iff
  {f : α → β} {g : β → γ} (hf : open_embedding f) {x : α} :
  continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
begin
  haveI : nonempty α := ⟨x⟩,
  convert (((hf.to_local_homeomorph f).continuous_at_iff_continuous_at_comp_right) _).symm,
  { apply (local_homeomorph.left_inv _ _).symm,
    simp, },
  { simp, },
end

end open_embedding

namespace topological_space.opens

open topological_space
variables (s : opens α) [nonempty s]

/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def local_homeomorph_subtype_coe : local_homeomorph s α :=
open_embedding.to_local_homeomorph _ s.2.open_embedding_subtype_coe

@[simp, mfld_simps] lemma local_homeomorph_subtype_coe_coe :
  (s.local_homeomorph_subtype_coe : s → α) = coe := rfl

@[simp, mfld_simps] lemma local_homeomorph_subtype_coe_source :
  s.local_homeomorph_subtype_coe.source = set.univ := rfl

@[simp, mfld_simps] lemma local_homeomorph_subtype_coe_target :
  s.local_homeomorph_subtype_coe.target = s :=
by { simp only [local_homeomorph_subtype_coe, subtype.range_coe_subtype] with mfld_simps, refl }

end topological_space.opens

namespace local_homeomorph

open topological_space
variables (e : local_homeomorph α β)
variables (s : opens α) [nonempty s]

/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtype_restr : local_homeomorph s β := s.local_homeomorph_subtype_coe.trans e

lemma subtype_restr_def : e.subtype_restr s = s.local_homeomorph_subtype_coe.trans e := rfl

@[simp, mfld_simps] lemma subtype_restr_coe : ((e.subtype_restr s : local_homeomorph s β) : s → β)
  = set.restrict (e : α → β) s := rfl

@[simp, mfld_simps] lemma subtype_restr_source : (e.subtype_restr s).source = coe ⁻¹' e.source :=
by simp only [subtype_restr_def] with mfld_simps

/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
lemma subtype_restr_symm_trans_subtype_restr (f f' : local_homeomorph α β) :
  (f.subtype_restr s).symm.trans (f'.subtype_restr s)
  ≈ (f.symm.trans f').restr (f.target ∩ (f.symm) ⁻¹' s) :=
begin
  simp only [subtype_restr_def, trans_symm_eq_symm_trans_symm],
  have openness₁ : is_open (f.target ∩ f.symm ⁻¹' s) := f.preimage_open_of_open_symm s.2,
  rw [← of_set_trans _ openness₁, ← trans_assoc, ← trans_assoc],
  refine eq_on_source.trans' _ (eq_on_source_refl _),
  -- f' has been eliminated !!!
  have sets_identity : f.symm.source ∩ (f.target ∩ (f.symm) ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s,
  { mfld_set_tac },
  have openness₂ : is_open (s : set α) := s.2,
  rw [of_set_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc],
  refine eq_on_source.trans' (eq_on_source_refl _) _,
  -- f has been eliminated !!!
  refine setoid.trans (trans_symm_self s.local_homeomorph_subtype_coe) _,
  simp only with mfld_simps,
end

end local_homeomorph
