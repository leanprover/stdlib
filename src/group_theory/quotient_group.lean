/-
Copyright (c) 2018 Kevin Buzzard and Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot.

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import group_theory.coset

universes u v

namespace quotient_group

variables {G : Type u} [group G] (N : set G) [normal_subgroup N] {H : Type v} [group H]

@[to_additive quotient_add_group.add_group]
instance : group (quotient N) :=
{ one := (1 : G),
  mul := quotient.map₂' (*)
  (λ a₁ b₁ hab₁ a₂ b₂ hab₂,
    ((is_subgroup.mul_mem_cancel_left N (is_subgroup.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact normal_subgroup.normal _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c
    (λ a b c, congr_arg mk (mul_assoc a b c)),
  one_mul := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (one_mul a)),
  inv := λ a, quotient.lift_on' a (λ a, ((a⁻¹ : G) : quotient N))
    (λ a b hab, quotient.sound' begin
      show a⁻¹⁻¹ * b⁻¹ ∈ N,
      rw ← mul_inv_rev,
      exact is_subgroup.inv_mem (is_subgroup.mem_norm_comm hab)
    end),
  mul_left_inv := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_left_inv a)) }

@[to_additive quotient_add_group.is_add_group_hom]
instance : is_group_hom (mk : G → quotient N) := { map_mul := λ _ _, rfl }

@[simp, to_additive quotient_add_group.ker_mk]
lemma ker_mk :
  is_group_hom.ker (quotient_group.mk : G → quotient_group.quotient N) = N :=
begin
  ext g,
  rw [is_group_hom.mem_ker, eq_comm],
  show (((1 : G) : quotient_group.quotient N)) = g ↔ _,
  rw [quotient_group.eq, one_inv, one_mul],
end

@[to_additive quotient_add_group.add_comm_group]
instance {G : Type*} [comm_group G] (s : set G) [is_subgroup s] : comm_group (quotient s) :=
{ mul_comm := λ a b, quotient.induction_on₂' a b
    (λ a b, congr_arg mk (mul_comm a b)),
  ..@quotient_group.group _ _ s (normal_subgroup_of_comm_group s) }

@[simp, to_additive quotient_add_group.coe_zero]
lemma coe_one : ((1 : G) : quotient N) = 1 := rfl

@[simp, to_additive quotient_add_group.coe_add]
lemma coe_mul (a b : G) : ((a * b : G) : quotient N) = a * b := rfl

@[simp, to_additive quotient_add_group.coe_neg]
lemma coe_inv (a : G) : ((a⁻¹ : G) : quotient N) = a⁻¹ := rfl

@[simp] lemma coe_pow (a : G) (n : ℕ) : ((a ^ n : G) : quotient N) = a ^ n :=
(monoid_hom.of mk).map_pow a n

@[simp] lemma coe_gpow (a : G) (n : ℤ) : ((a ^ n : G) : quotient N) = a ^ n :=
(monoid_hom.of mk).map_gpow a n

local notation ` Q ` := quotient N

@[to_additive quotient_add_group.lift]
def lift (φ : G → H) [is_group_hom φ] (HN : ∀x∈N, φ x = 1) (q : Q) : H :=
q.lift_on' φ $ assume a b (hab : a⁻¹ * b ∈ N),
(calc φ a = φ a * 1           : (mul_one _).symm
...       = φ a * φ (a⁻¹ * b) : HN (a⁻¹ * b) hab ▸ rfl
...       = φ (a * (a⁻¹ * b)) : (is_mul_hom.map_mul φ a (a⁻¹ * b)).symm
...       = φ b               : by rw mul_inv_cancel_left)

@[simp, to_additive quotient_add_group.lift_mk]
lemma lift_mk {φ : G → H} [is_group_hom φ] (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_mk']
lemma lift_mk' {φ : G → H} [is_group_hom φ] (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (mk g : Q) = φ g := rfl

@[to_additive quotient_add_group.map]
def map (M : set H) [normal_subgroup M] (f : G → H) [is_group_hom f] (h : N ⊆ f ⁻¹' M) :
  quotient N → quotient M :=
begin
  haveI : is_group_hom ((mk : H → quotient M) ∘ f) := is_group_hom.comp _ _,
  refine quotient_group.lift N (mk ∘ f) _,
  assume x hx,
  refine quotient_group.eq.2 _,
  rw [mul_one, is_subgroup.inv_mem_iff],
  exact h hx,
end

variables (φ : G → H) [is_group_hom φ] (HN : ∀x∈N, φ x = 1)

@[to_additive quotient_add_group.is_add_group_hom_quotient_lift]
instance is_group_hom_quotient_lift  :
  is_group_hom (lift N φ HN) :=
{ map_mul := λ q r, quotient.induction_on₂' q r $ is_mul_hom.map_mul φ }

@[to_additive quotient_add_group.map_is_add_group_hom]
instance map_is_group_hom (M : set H) [normal_subgroup M]
(f : G → H) [is_group_hom f] (h : N ⊆ f ⁻¹' M) : is_group_hom (map N M f h) :=
@quotient_group.is_group_hom_quotient_lift _ _ _ _ _ _ _ (is_group_hom.comp _ _) _

open function is_group_hom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive quotient_add_group.ker_lift]
def ker_lift : quotient (ker φ) → H :=
lift _ φ $ λ g, (mem_ker φ).mp

@[simp, to_additive quotient_add_group.ker_lift_mk]
lemma ker_lift_mk (g : G) : (ker_lift φ) g = φ g :=
lift_mk _ _ _

@[simp, to_additive quotient_add_group.ker_lift_mk']
lemma ker_lift_mk' (g : G) : (ker_lift φ) (mk g) = φ g :=
lift_mk' _ _ _

@[to_additive quotient_add_group.ker_lift_is_add_group_hom]
instance ker_lift_is_group_hom : is_group_hom (ker_lift φ) :=
quotient_group.is_group_hom_quotient_lift _ _ _

@[to_additive quotient_add_group.injective_ker_lift]
lemma injective_ker_lift : injective (ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $ assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [mem_ker φ,
  is_mul_hom.map_mul φ, ← h, is_group_hom.map_inv φ, inv_mul_self]

--@[to_additive quotient_add_group.quotient_ker_equiv_range]
noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃ set.range φ :=
@equiv.of_bijective _ (set.range φ) (λ x, ⟨lift (ker φ) φ
  (by simp [mem_ker]) x, by exact quotient.induction_on' x (λ x, ⟨x, rfl⟩)⟩)
⟨λ a b h, injective_ker_lift _ (subtype.mk.inj h),
  λ ⟨x, y, hy⟩, ⟨mk y, subtype.eq hy⟩⟩

noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  (quotient (ker φ)) ≃ H :=
calc (quotient_group.quotient (is_group_hom.ker φ)) ≃ set.range φ : quotient_ker_equiv_range _
... ≃ H : ⟨λ a, a.1, λ b, ⟨b, hφ b⟩, λ ⟨_, _⟩, rfl, λ _, rfl⟩

end quotient_group

namespace quotient_add_group
open is_add_group_hom

variables {G : Type u} [_root_.add_group G] (N : set G) [normal_add_subgroup N] {H : Type v} [_root_.add_group H]
variables (φ : G → H) [_root_.is_add_group_hom φ]

noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃ set.range φ :=
@quotient_group.quotient_ker_equiv_range (multiplicative G) _ (multiplicative H) _ φ
  (multiplicative.is_group_hom _)

noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  (quotient (ker φ)) ≃ H :=
@quotient_group.quotient_ker_equiv_of_surjective (multiplicative G) _ (multiplicative H) _ φ
  (multiplicative.is_group_hom _) hφ

attribute [to_additive quotient_add_group.quotient_ker_equiv_range] quotient_group.quotient_ker_equiv_range
attribute [to_additive quotient_add_group.quotient_ker_equiv_of_surjective] quotient_group.quotient_ker_equiv_of_surjective

end quotient_add_group
