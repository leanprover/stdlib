/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import deprecated.subring
import algebra.group_with_zero.power

variables {F : Type*} [field F] (S : set F)

class is_subfield extends is_subring S : Prop :=
(inv_mem : ∀ {x : F}, x ∈ S → x⁻¹ ∈ S)

instance is_subfield.field [is_subfield S] : field S :=
by letI cr_inst : comm_ring S := subset.comm_ring; exact
{ inv := λ x, ⟨x⁻¹, is_subfield.inv_mem x.2⟩,
  exists_pair_ne := ⟨0, 1, λ h, zero_ne_one (subtype.ext_iff_val.1 h)⟩,
  mul_inv_cancel := λ a ha, subtype.ext_iff_val.2 (mul_inv_cancel
    (λ h, ha $ subtype.ext_iff_val.2 h)),
  inv_zero := subtype.ext_iff_val.2 inv_zero,
  .. cr_inst }

lemma is_subfield.pow_mem {a : F} {n : ℤ} {s : set F} [is_subfield s] (h : a ∈ s) :
  a ^ n ∈ s :=
begin
  cases n,
  { exact is_submonoid.pow_mem h },
  { exact is_subfield.inv_mem (is_submonoid.pow_mem h) },
end

instance univ.is_subfield : is_subfield (@set.univ F) :=
{ inv_mem := by intros; trivial }

/- note: in the next two declarations, if we let type-class inference figure out the instance
  `ring_hom.is_subring_preimage` then that instance only applies when particular instances of
  `is_add_subgroup _` and `is_submonoid _` are chosen (which are not the default ones).
  If we specify it explicitly, then it doesn't complain. -/
instance preimage.is_subfield {K : Type*} [field K]
  (f : F →+* K) (s : set K) [is_subfield s] : is_subfield (f ⁻¹' s) :=
{ inv_mem := λ a (ha : f a ∈ s), show f a⁻¹ ∈ s,
    by { rw [f.map_inv],
         exact is_subfield.inv_mem ha },
  ..f.is_subring_preimage s }

instance image.is_subfield {K : Type*} [field K]
  (f : F →+* K) (s : set F) [is_subfield s] : is_subfield (f '' s) :=
{ inv_mem := λ a ⟨x, xmem, ha⟩, ⟨x⁻¹, is_subfield.inv_mem xmem, ha ▸ f.map_inv _⟩,
  ..f.is_subring_image s }

instance range.is_subfield {K : Type*} [field K]
  (f : F →+* K) : is_subfield (set.range f) :=
by { rw ← set.image_univ, apply_instance }

namespace field

/-- `field.closure s` is the minimal subfield that includes `s`. -/
def closure : set F :=
{ x | ∃ y ∈ ring.closure S, ∃ z ∈ ring.closure S, y / z = x }

variables {S}

theorem ring_closure_subset : ring.closure S ⊆ closure S :=
λ x hx, ⟨x, hx, 1, is_submonoid.one_mem, div_one x⟩

instance closure.is_submonoid : is_submonoid (closure S) :=
{ mul_mem := by rintros _  _ ⟨p, hp, q, hq, hq0, rfl⟩ ⟨r, hr, s, hs, hs0, rfl⟩;
    exact ⟨p * r,
          is_submonoid.mul_mem hp hr,
          q * s,
          is_submonoid.mul_mem hq hs,
          (div_mul_div _ _ _ _).symm⟩,
  one_mem := ring_closure_subset $ is_submonoid.one_mem }

instance closure.is_subfield : is_subfield (closure S) :=
have h0 : (0:F) ∈ closure S, from ring_closure_subset $ is_add_submonoid.zero_mem,
{ add_mem := begin
    intros a b ha hb,
    rcases (id ha) with ⟨p, hp, q, hq, rfl⟩,
    rcases (id hb) with ⟨r, hr, s, hs, rfl⟩,
    classical, by_cases hq0 : q = 0, by simp [hb, hq0], by_cases hs0 : s = 0, by simp [ha, hs0],
    exact ⟨p * s + q * r, is_add_submonoid.add_mem (is_submonoid.mul_mem hp hs)
      (is_submonoid.mul_mem hq hr), q * s, is_submonoid.mul_mem hq hs,
      (div_add_div p r hq0 hs0).symm⟩
  end,
  zero_mem := h0,
  neg_mem := begin
    rintros _ ⟨p, hp, q, hq, rfl⟩,
    exact ⟨-p, is_add_subgroup.neg_mem hp, q, hq, neg_div q p⟩
  end,
  inv_mem := begin
    rintros _ ⟨p, hp, q, hq, rfl⟩,
    classical, by_cases hp0 : p = 0, by simp [hp0, h0],
    exact ⟨q, hq, p, hp, inv_div.symm⟩
  end }

theorem mem_closure {a : F} (ha : a ∈ S) : a ∈ closure S :=
ring_closure_subset $ ring.mem_closure ha

theorem subset_closure : S ⊆ closure S :=
λ _, mem_closure

theorem closure_subset {T : set F} [is_subfield T] (H : S ⊆ T) : closure S ⊆ T :=
begin
  rintros _ ⟨p, hp, q, hq, rfl⟩,
  simp only [field.div, div_eq_mul_inv p q],
  exact is_submonoid.mul_mem (ring.closure_subset H hp)
  (is_subfield.inv_mem $ ring.closure_subset H hq)
end

theorem closure_subset_iff (s t : set F) [is_subfield t] : closure s ⊆ t ↔ s ⊆ t :=
⟨set.subset.trans subset_closure, closure_subset⟩

theorem closure_mono {s t : set F} (H : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans H subset_closure

end field

lemma is_subfield_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set F) [∀ i, is_subfield (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_subfield (⋃i, s i) :=
{ inv_mem := λ x hx, let ⟨i, hi⟩ := set.mem_Union.1 hx in
    set.mem_Union.2 ⟨i, is_subfield.inv_mem hi⟩,
  to_is_subring := is_subring_Union_of_directed s directed }

instance is_subfield.inter (S₁ S₂ : set F) [is_subfield S₁] [is_subfield S₂] :
  is_subfield (S₁ ∩ S₂) :=
{ inv_mem := λ x hx, ⟨is_subfield.inv_mem hx.1, is_subfield.inv_mem hx.2⟩ }

instance is_subfield.Inter {ι : Sort*} (S : ι → set F) [h : ∀ y : ι, is_subfield (S y)] :
  is_subfield (set.Inter S) :=
{ inv_mem := λ x hx, set.mem_Inter.2 $ λ y, is_subfield.inv_mem $ set.mem_Inter.1 hx y }
