/-
Copyright (c) 2019 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.filter.lift
import topology.opens
import topology.algebra.ring

open topological_space
open_locale topological_space

set_option old_structure_cmd true

/-- The type of open subgroups of a topological additive group. -/
@[ancestor add_subgroup]
structure open_add_subgroup  (G : Type*) [add_group G] [topological_space G]
  extends add_subgroup G :=
(is_open' : is_open carrier)

/-- The type of open subgroups of a topological group. -/
@[ancestor subgroup, to_additive]
structure open_subgroup (G : Type*) [group G] [topological_space G] extends subgroup G :=
(is_open' : is_open carrier)

/-- Reinterpret an `open_subgroup` as a `subgroup`. -/
add_decl_doc open_subgroup.to_subgroup

/-- Reinterpret an `open_add_subgroup` as an `add_subgroup`. -/
add_decl_doc open_add_subgroup.to_add_subgroup

-- Tell Lean that `open_add_subgroup` is a namespace
namespace open_add_subgroup
end open_add_subgroup

namespace open_subgroup
open function topological_space
variables {G : Type*} [group G] [topological_space G]
variables {U V : open_subgroup G} {g : G}

@[to_additive]
instance has_coe_set : has_coe_t (open_subgroup G) (set G) := ⟨λ U, U.1⟩

@[to_additive]
instance : has_mem G (open_subgroup G) := ⟨λ g U, g ∈ (U : set G)⟩

@[to_additive]
instance has_coe_subgroup : has_coe_t (open_subgroup G) (subgroup G) := ⟨to_subgroup⟩

@[to_additive]
instance has_coe_opens : has_coe_t (open_subgroup G) (opens G) := ⟨λ U, ⟨U, U.is_open'⟩⟩

@[simp, norm_cast, to_additive] lemma mem_coe : g ∈ (U : set G) ↔ g ∈ U := iff.rfl
@[simp, norm_cast, to_additive] lemma mem_coe_opens : g ∈ (U : opens G) ↔ g ∈ U := iff.rfl
@[simp, norm_cast, to_additive]
lemma mem_coe_subgroup : g ∈ (U : subgroup G) ↔ g ∈ U := iff.rfl

@[to_additive] lemma coe_injective : injective (coe : open_subgroup G → set G) :=
λ U V h, by cases U; cases V; congr; assumption

@[ext, to_additive]
lemma ext (h : ∀ x, x ∈ U ↔ x ∈ V) : (U = V) := coe_injective $ set.ext h

@[to_additive]
lemma ext_iff : (U = V) ↔ (∀ x, x ∈ U ↔ x ∈ V) := ⟨λ h x, h ▸ iff.rfl, ext⟩

variable (U)
@[to_additive]
protected lemma is_open : is_open (U : set G) := U.is_open'

@[to_additive]
protected lemma one_mem : (1 : G) ∈ U := U.one_mem'

@[to_additive]
protected lemma inv_mem {g : G} (h : g ∈ U) : g⁻¹ ∈ U := U.inv_mem' h

@[to_additive]
protected lemma mul_mem {g₁ g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : g₁ * g₂ ∈ U := U.mul_mem' h₁ h₂

@[to_additive]
lemma mem_nhds_one : (U : set G) ∈ 𝓝 (1 : G) :=
is_open.mem_nhds U.is_open U.one_mem
variable {U}

@[to_additive]
instance : has_top (open_subgroup G) := ⟨{ is_open' := is_open_univ, .. (⊤ : subgroup G) }⟩

@[to_additive]
instance : inhabited (open_subgroup G) := ⟨⊤⟩

@[to_additive]
lemma is_closed [has_continuous_mul G] (U : open_subgroup G) : is_closed (U : set G) :=
begin
  apply is_open_compl_iff.1,
  refine is_open_iff_forall_mem_open.2 (λ x hx, ⟨(λ y, y * x⁻¹) ⁻¹' U, _, _, _⟩),
  { intros u hux,
    simp only [set.mem_preimage, set.mem_compl_iff, mem_coe] at hux hx ⊢,
    refine mt (λ hu, _) hx,
    convert U.mul_mem (U.inv_mem hux) hu,
    simp },
  { exact U.is_open.preimage (continuous_mul_right _) },
  { simp [U.one_mem] }
end

section
variables {H : Type*} [group H] [topological_space H]

/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive "The product of two open subgroups as an open subgroup of the product group."]
def prod (U : open_subgroup G) (V : open_subgroup H) : open_subgroup (G × H) :=
{ carrier := (U : set G).prod (V : set H),
  is_open' := U.is_open.prod V.is_open,
  .. (U : subgroup G).prod (V : subgroup H) }

end

@[to_additive]
instance : partial_order (open_subgroup G) :=
{ le := λ U V, ∀ ⦃x⦄, x ∈ U → x ∈ V,
  .. partial_order.lift (coe : open_subgroup G → set G) coe_injective }

@[to_additive]
instance : semilattice_inf_top (open_subgroup G) :=
{ inf := λ U V, { is_open' := is_open.inter U.is_open V.is_open, .. (U : subgroup G) ⊓ V },
  inf_le_left := λ U V, set.inter_subset_left _ _,
  inf_le_right := λ U V, set.inter_subset_right _ _,
  le_inf := λ U V W hV hW, set.subset_inter hV hW,
  top := ⊤,
  le_top := λ U, set.subset_univ _,
  ..open_subgroup.partial_order }

@[simp, norm_cast, to_additive] lemma coe_inf : (↑(U ⊓ V) : set G) = (U : set G) ∩ V := rfl

@[simp, norm_cast, to_additive] lemma coe_subset : (U : set G) ⊆ V ↔ U ≤ V := iff.rfl

@[simp, norm_cast, to_additive] lemma coe_subgroup_le :
(U : subgroup G) ≤ (V : subgroup G) ↔ U ≤ V := iff.rfl

variables {N : Type*} [group N] [topological_space N]

/-- The preimage of an `open_subgroup` along a continuous `monoid` homomorphism
  is an `open_subgroup`. -/
@[to_additive "The preimage of an `open_add_subgroup` along a continuous `add_monoid` homomorphism
is an `open_add_subgroup`."]
def comap (f : G →* N)
  (hf : continuous f) (H : open_subgroup N) : open_subgroup G :=
{ is_open' := H.is_open.preimage hf,
  .. (H : subgroup N).comap f }

@[simp, to_additive]
lemma coe_comap (H : open_subgroup N) (f : G →* N) (hf : continuous f) :
  (H.comap f hf : set G) = f ⁻¹' H := rfl

@[simp, to_additive]
lemma mem_comap {H : open_subgroup N} {f : G →* N} {hf : continuous f} {x : G} :
  x ∈ H.comap f hf ↔ f x ∈ H := iff.rfl

@[to_additive]
lemma comap_comap {P : Type*} [group P] [topological_space P]
  (K : open_subgroup P) (f₂ : N →* P) (hf₂ : continuous f₂) (f₁ : G →* N) (hf₁ : continuous f₁) :
  (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
rfl

end open_subgroup

namespace subgroup

variables {G : Type*} [group G] [topological_space G] [has_continuous_mul G] (H : subgroup G)

@[to_additive]
lemma is_open_of_mem_nhds {g : G} (hg : (H : set G) ∈ 𝓝 g) :
  is_open (H : set G) :=
begin
  simp only [is_open_iff_mem_nhds, set_like.mem_coe] at hg ⊢,
  intros x hx,
  have : filter.tendsto (λ y, y * (x⁻¹ * g)) (𝓝 x) (𝓝 $ x * (x⁻¹ * g)) :=
    (continuous_id.mul continuous_const).tendsto _,
  rw [mul_inv_cancel_left] at this,
  have := filter.mem_map.1 (this hg),
  replace hg : g ∈ H := set_like.mem_coe.1 (mem_of_mem_nhds hg),
  simp only [set_like.mem_coe, H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg)] at this,
  exact this
end

@[to_additive]
lemma is_open_of_open_subgroup {U : open_subgroup G} (h : U.1 ≤ H) :
  is_open (H : set G) :=
H.is_open_of_mem_nhds (filter.mem_sets_of_superset U.mem_nhds_one h)

@[to_additive]
lemma is_open_mono {H₁ H₂ : subgroup G} (h : H₁ ≤ H₂) (h₁ : is_open (H₁  :set G)) :
  is_open (H₂ : set G) :=
@is_open_of_open_subgroup _ _ _ _ H₂ { is_open' := h₁, .. H₁ } h

end subgroup

namespace open_subgroup

variables {G : Type*} [group G] [topological_space G] [has_continuous_mul G]

@[to_additive]
instance : semilattice_sup_top (open_subgroup G) :=
{ sup := λ U V,
  { is_open' := show is_open (((U : subgroup G) ⊔ V : subgroup G) : set G),
    from subgroup.is_open_mono le_sup_left U.is_open,
    .. ((U : subgroup G) ⊔ V) },
  le_sup_left := λ U V, coe_subgroup_le.1 le_sup_left,
  le_sup_right := λ U V, coe_subgroup_le.1 le_sup_right,
  sup_le := λ U V W hU hV, coe_subgroup_le.1 (sup_le hU hV),
  ..open_subgroup.semilattice_inf_top }

end open_subgroup

namespace submodule
open open_add_subgroup
variables {R : Type*} {M : Type*} [comm_ring R]
variables [add_comm_group M] [topological_space M] [topological_add_group M] [module R M]

lemma is_open_mono {U P : submodule R M} (h : U ≤ P) (hU : is_open (U : set M)) :
  is_open (P : set M) :=
@add_subgroup.is_open_mono M _ _ _ U.to_add_subgroup P.to_add_subgroup h hU

end submodule

namespace ideal
variables {R : Type*} [comm_ring R]
variables [topological_space R] [topological_ring R]

lemma is_open_of_open_subideal {U I : ideal R} (h : U ≤ I) (hU : is_open (U : set R)) :
  is_open (I : set R) :=
submodule.is_open_mono h hU

end ideal
