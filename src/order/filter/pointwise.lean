/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import algebra.pointwise
import order.filter.basic
/-!
# Pointwise operations on filters.

The pointwise operations on filters have nice properties, such as
  • `map m (f₁ * f₂) = map m f₁ * map m f₂`
  • `𝓝 x * 𝓝 y = 𝓝 (x * y)`

-/

open classical set

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open_locale classical

namespace filter
open set

@[to_additive]
instance [has_one α] : has_one (filter α) := ⟨principal 1⟩

@[simp, to_additive]
lemma mem_one [has_one α] (s : set α) : s ∈ (1 : filter α) ↔ (1:α) ∈ s :=
calc
  s ∈ (1:filter α) ↔ 1 ⊆ s : iff.rfl
  ... ↔ (1 : α) ∈ s : by simp

@[to_additive]
instance [monoid α] : has_mul (filter α) := ⟨λf g,
{ sets             := { s | ∃t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ * t₂ ⊆ s },
  univ_sets        :=
  begin
    have h₁ : (∃x, x ∈ f) := ⟨univ, univ_sets f⟩,
    have h₂ : (∃x, x ∈ g) := ⟨univ, univ_sets g⟩,
    simpa using and.intro h₁ h₂
  end,
  sets_of_superset := λx y hx hxy,
  begin
   rcases hx with ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
   exact ⟨t₁, ht₁, t₂, ht₂, subset.trans t₁t₂ hxy⟩
  end,
  inter_sets       := λx y,
  begin
    simp only [exists_prop, mem_set_of_eq, subset_inter_iff],
    rintros ⟨s₁, s₂, hs₁, hs₂, s₁s₂⟩ ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩,
    exact ⟨s₁ ∩ t₁, s₂ ∩ t₂, inter_sets f hs₁ ht₁, inter_sets g hs₂ ht₂,
    subset.trans (mul_subset_mul (inter_subset_left _ _) (inter_subset_left _ _)) s₁s₂,
    subset.trans (mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _)) t₁t₂⟩,
  end }⟩

@[to_additive]
lemma mem_mul [monoid α] {f g : filter α} {s : set α} :
  s ∈ f * g ↔ ∃t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ * t₂  ⊆ s := iff.rfl

@[to_additive]
lemma mul_mem_mul [monoid α] {f g : filter α} {s t : set α} (hs : s ∈ f) (ht : t ∈ g) :
  s * t ∈ f * g := ⟨_, _, hs, ht, subset.refl _⟩

@[to_additive]
protected lemma mul_le_mul [monoid α] {f₁ f₂ g₁ g₂ : filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁ * g₁ ≤ f₂ * g₂ := assume _ ⟨s, t, hs, ht, hst⟩, ⟨s, t, hf hs, hg ht, hst⟩

@[to_additive]
lemma ne_bot.mul [monoid α] {f g : filter α} : ne_bot f → ne_bot g → ne_bot (f * g) :=
begin
  simp only [forall_sets_nonempty_iff_ne_bot.symm],
  rintros hf hg s ⟨a, b, ha, hb, ab⟩,
  exact ((hf a ha).mul (hg b hb)).mono ab
end

@[to_additive]
protected lemma mul_assoc [monoid α] (f g h : filter α) : f * g * h = f * (g * h) :=
begin
  ext s, split,
  { rintros ⟨a, b, ⟨a₁, a₂, ha₁, ha₂, a₁a₂⟩, hb, ab⟩,
    refine ⟨a₁, a₂ * b, ha₁, mul_mem_mul ha₂ hb, _⟩, rw [← mul_assoc],
    exact calc
      a₁ * a₂ * b ⊆ a * b : mul_subset_mul a₁a₂ (subset.refl _)
      ...         ⊆ s     : ab },
  { rintros ⟨a, b, ha, ⟨b₁, b₂, hb₁, hb₂, b₁b₂⟩, ab⟩,
    refine ⟨a * b₁, b₂, mul_mem_mul ha hb₁, hb₂, _⟩, rw [mul_assoc],
    exact calc
      a * (b₁ * b₂) ⊆ a * b : mul_subset_mul (subset.refl _) b₁b₂
      ...           ⊆ s     : ab }
end

@[to_additive]
protected lemma one_mul [monoid α] (f : filter α) : 1 * f = f :=
begin
  ext s, split,
  { rintros ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩,
    refine mem_sets_of_superset (mem_sets_of_superset ht₂ _) t₁t₂,
    assume x hx,
    exact ⟨1, x, by rwa [← mem_one], hx, one_mul _⟩ },
  { assume hs, refine ⟨(1:set α), s, mem_principal_self _, hs, by simp only [one_mul]⟩ }
end

@[to_additive]
protected lemma mul_one [monoid α] (f : filter α) : f * 1 = f :=
begin
  ext s, split,
  { rintros ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩,
    refine mem_sets_of_superset (mem_sets_of_superset ht₁ _) t₁t₂,
    assume x hx,
    exact ⟨x, 1, hx, by rwa [← mem_one], mul_one _⟩ },
  { assume hs,
    refine ⟨s, (1:set α), hs, mem_principal_self _, by simp only [mul_one]⟩ }
end

@[to_additive filter.add_monoid]
instance [monoid α] : monoid (filter α) :=
{ mul_assoc := filter.mul_assoc,
  one_mul := filter.one_mul,
  mul_one := filter.mul_one,
  .. filter.has_mul,
  .. filter.has_one }

section map
open is_mul_hom

variables [monoid α] [monoid β] {f : filter α} {m : α → β}

@[to_additive]
protected lemma map_mul (hm : is_mul_hom m) {f₁ f₂ : filter α} :
  map m (f₁ * f₂) = map m f₁ * map m f₂ :=
begin
  ext s,
  simp only [mem_mul], split,
  { rintro ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩,
    have : m '' (t₁ * t₂) ⊆ s := subset.trans (image_subset m t₁t₂) (image_preimage_subset _ _),
    refine ⟨m '' t₁, m '' t₂, image_mem_map ht₁, image_mem_map ht₂, _⟩,
    rwa ← image_mul hm },
  { rintro ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩,
    refine ⟨m ⁻¹' t₁, m ⁻¹' t₂, ht₁, ht₂, image_subset_iff.1 _⟩,
    rw image_mul hm,
    exact subset.trans
      (mul_subset_mul (image_preimage_subset _ _) (image_preimage_subset _ _)) t₁t₂ },
end

@[to_additive]
protected lemma map_one (hm : is_monoid_hom m) : map m (1:filter α) = 1 :=
le_antisymm
  (le_principal_iff.2 $ mem_map_sets_iff.2 ⟨(1:set α), by simp,
    by { assume x, simp [hm.map_one] }⟩)
  (le_map $ assume s hs,
   begin
     simp only [mem_one],
     exact ⟨(1:α), (mem_one s).1 hs, hm.map_one⟩
   end)

-- TODO: prove similar statements when `m` is group homomorphism etc.
@[to_additive map.is_add_monoid_hom]
lemma map.is_monoid_hom (hm : is_monoid_hom m) : is_monoid_hom (map m) :=
{ map_one := filter.map_one hm,
  map_mul := λ _ _, filter.map_mul hm.to_is_mul_hom }

-- The other direction does not hold in general.
@[to_additive]
lemma comap_mul_comap_le (hm : is_mul_hom m) {f₁ f₂ : filter β} :
  comap m f₁ * comap m f₂ ≤ comap m (f₁ * f₂) :=
begin
  rintros s ⟨t, ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩, mt⟩,
  refine ⟨m ⁻¹' t₁, m ⁻¹' t₂, ⟨t₁, ht₁, subset.refl _⟩, ⟨t₂, ht₂, subset.refl _⟩, _⟩,
  have := subset.trans (preimage_mono t₁t₂) mt,
  exact subset.trans (preimage_mul_preimage_subset hm) this
end

@[to_additive]
lemma tendsto.mul_mul (hm : is_mul_hom m) {f₁ g₁ : filter α} {f₂ g₂ : filter β} :
  tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ * g₁) (f₂ * g₂) :=
assume hf hg, by { rw [tendsto, filter.map_mul hm], exact filter.mul_le_mul hf hg }

end map

end filter
