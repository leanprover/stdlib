/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.equiv.mul_add_aut
import group_theory.subgroup

/-!
# Semidirect product

This file defines semidirect products of groups, and the canonical maps in and out of the
semidirect product. The semidirect product of `N` and `G` given a hom `φ` from
`φ` from `G` to the automorphism group of `N` is the product of sets with the group
`⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`

## Key definitions

There are two homs into the semidirect product `inl : N →* N ⋊[φ] G` and
`inr : G →* N ⋊[φ] G`, and `lift` can be used to define maps `N ⋊[φ] G →* H`
out of the semidirect product given maps `f₁ : N →* H` and `f₂ : G →* H` that satisfy the
condition `∀ n g, f₁ (φ g n) = f₂ g * f₁ n * f₂ g⁻¹`

## Notation

This file introduces the global notation `N ⋊[φ] G` for `semidirect_product N G φ`

## Tags
group, semidirect product
-/
variables (N : Type*) (G : Type*) {H : Type*} [group N] [group G] [group H]

/-- The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the automorphism
  group of `N`. It the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
@[ext, derive decidable_eq]
structure semidirect_product (φ : G →* mul_aut N) :=
(left : N) (right : G)

attribute [pp_using_anonymous_constructor] semidirect_product

notation N` ⋊[`:35 φ:35`] `:0 G :35 := semidirect_product N G φ

namespace semidirect_product

variables {N G} {φ : G →* mul_aut N}

private def one_aux : N ⋊[φ] G := ⟨1, 1⟩
private def mul_aux (a b : N ⋊[φ] G) : N ⋊[φ] G := ⟨a.1 * φ a.2 b.1, a.right * b.right⟩
private def inv_aux (a : N ⋊[φ] G) : N ⋊[φ] G := let i := a.2⁻¹ in ⟨φ i a.1⁻¹, i⟩
private lemma mul_assoc_aux (a b c : N ⋊[φ] G) : mul_aux (mul_aux a b) c = mul_aux a (mul_aux b c) :=
by simp [mul_aux, mul_assoc, mul_equiv.map_mul]
private lemma mul_one_aux (a : N ⋊[φ] G) : mul_aux a one_aux = a :=
by cases a; simp [mul_aux, one_aux]
private lemma one_mul_aux (a : N ⋊[φ] G) : mul_aux one_aux a = a :=
by cases a; simp [mul_aux, one_aux]
private lemma mul_left_inv_aux (a : N ⋊[φ] G) : mul_aux (inv_aux a) a = one_aux :=
by simp only [mul_aux, inv_aux, one_aux, ← mul_equiv.map_mul, mul_left_inv]; simp

instance : group (N ⋊[φ] G) :=
{ one := one_aux,
  inv := inv_aux,
  mul := mul_aux,
  mul_assoc := mul_assoc_aux,
  one_mul := one_mul_aux,
  mul_one := mul_one_aux,
  mul_left_inv := mul_left_inv_aux }

instance : inhabited (N ⋊[φ] G) := ⟨1⟩

@[simp] lemma one_left : (1 : N ⋊[φ] G).left = 1 := rfl
@[simp] lemma one_right : (1 : N ⋊[φ] G).right = 1 := rfl
@[simp] lemma inv_left (a : N ⋊[φ] G) : (a⁻¹).left = φ a.right⁻¹ a.left⁻¹ := rfl
@[simp] lemma inv_right (a : N ⋊[φ] G) : (a⁻¹).right = a.right⁻¹ := rfl
@[simp] lemma mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left := rfl
@[simp] lemma mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right := rfl

/-- The canonical map `N →* N ⋊[φ] G` sending `n` to `⟨n, 1⟩` -/
def inl : N →* N ⋊[φ] G :=
{ to_fun := λ n, ⟨n, 1⟩,
  map_one' := rfl,
  map_mul' := by intros; ext; simp }

@[simp] lemma left_inl (n : N) : (inl n : N ⋊[φ] G).left = n := rfl
@[simp] lemma right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1 := rfl

lemma inl_injective : function.injective (inl : N → N ⋊[φ] G) :=
function.injective_iff_has_left_inverse.2 ⟨left, left_inl⟩

@[simp] lemma inl_inj {n₁ n₂ : N} : (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂ :=
inl_injective.eq_iff

/-- The canonical map `G →* N ⋊[φ] G` sending `g` to `⟨1, g⟩` -/
def inr : G →* N ⋊[φ] G :=
{ to_fun := λ g, ⟨1, g⟩,
  map_one' := rfl,
  map_mul' := by intros; ext; simp }

@[simp] lemma left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1 := rfl
@[simp] lemma right_inr (g : G) : (inr g : N ⋊[φ] G).right = g := rfl

lemma inr_injective : function.injective (inr : G → N ⋊[φ] G) :=
function.injective_iff_has_left_inverse.2 ⟨right, right_inr⟩

@[simp] lemma inr_inj {g₁ g₂ : G} : (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂ :=
inr_injective.eq_iff

lemma inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹ :=
by ext; simp

lemma inl_aut_inv (g : G) (n : N) : (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl n * inr g :=
by rw [← monoid_hom.map_inv, inl_aut, inv_inv]

@[simp] lemma mk_eq_inl_mul_inr (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g :=
by ext; simp

@[simp] lemma inl_left_mul_inr_right (x : N ⋊[φ] G) : inl x.left * inr x.right = x :=

by ext; simp

/-- The canonical projection map `N ⋊[φ] G →* G`, as a group hom. -/
def right_hom : N ⋊[φ] G →* G :=
{ to_fun := semidirect_product.right,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

@[simp] lemma right_hom_eq_right : (right_hom :  N ⋊[φ] G → G) = right := rfl

@[simp] lemma right_hom_comp_inl : (right_hom : N ⋊[φ] G →* G).comp inl = 1 :=
by ext; simp [right_hom]

@[simp] lemma right_hom_comp_inr : (right_hom : N ⋊[φ] G →* G).comp inr = monoid_hom.id _ :=
by ext; simp [right_hom]

@[simp] lemma right_hom_inl (n : N) : right_hom (inl n : N ⋊[φ] G) = 1 :=
by simp [right_hom]

@[simp] lemma right_hom_inr (g : G) : right_hom (inr g : N ⋊[φ] G) = g :=
by simp [right_hom]

lemma right_hom_surjective : function.surjective (right_hom : N ⋊[φ] G → G) :=
function.surjective_iff_has_right_inverse.2 ⟨inr, right_hom_inr⟩

lemma range_inl_eq_ker_right_hom : (inl : N →* N ⋊[φ] G).range = right_hom.ker :=
le_antisymm
  (λ _, by simp [monoid_hom.mem_ker, eq_comm] {contextual := tt})
  (λ x hx, ⟨x.left, by ext; simp [*, monoid_hom.mem_ker] at *⟩)

section lift
variables (f₁ : N →* H) (f₂ : G →* H)
  (h : ∀ g, f₁.comp (φ g).to_monoid_hom = (mul_aut.conj (f₂ g)).to_monoid_hom.comp f₁)

/-- Define a group hom `N ⋊[φ] G →* H`, by defining maps `N →* H` and `G →* H`  -/
def lift (f₁ : N →* H) (f₂ : G →* H)
  (h : ∀ g, f₁.comp (φ g).to_monoid_hom = (mul_aut.conj (f₂ g)).to_monoid_hom.comp f₁) :
  N ⋊[φ] G →* H :=
{ to_fun := λ a, f₁ a.1 * f₂ a.2,
  map_one' := by simp,
  map_mul' := λ a b, begin
    have := λ n g, monoid_hom.ext_iff.1 (h n) g,
    simp only [mul_aut.conj_apply, monoid_hom.comp_apply, mul_equiv.to_monoid_hom_apply] at this,
    simp [this, mul_assoc]
  end }

@[simp] lemma lift_inl (n : N) : lift f₁ f₂ h (inl n) = f₁ n := by simp [lift]
@[simp] lemma lift_comp_inl : (lift f₁ f₂ h).comp inl = f₁ := by ext; simp

@[simp] lemma lift_inr (g : G) : lift f₁ f₂ h (inr g) = f₂ g := by simp [lift]
@[simp] lemma lift_comp_inr : (lift f₁ f₂ h).comp inr = f₂ := by ext; simp

lemma lift_unique (F : N ⋊[φ] G →* H) :
  F = lift (F.comp inl) (F.comp inr) (λ _, by ext; simp [inl_aut]) :=
begin
  ext,
  simp only [lift, monoid_hom.comp_apply, monoid_hom.coe_mk],
  rw [← F.map_mul, inl_left_mul_inr_right],
end

/-- Two maps out of the semidirect product are equal if they're equal after composition
  with both `inl` and `inr` -/
lemma hom_ext {f g : (N ⋊[φ] G) →* H} (hl : f.comp inl = g.comp inl)
  (hr : f.comp inr = g.comp inr) : f = g :=
by { rw [lift_unique f, lift_unique g], simp only * }

end lift

section map

variables {N₁ : Type*} {G₁ : Type*} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁}

/-- Define a map from `N ⋊[φ] G` to `N₁ ⋊[φ₁] G₁` given maps `N →* N₁` and `G →* G₁` that
  satisfy a commutativity condition `∀ n g, f₁ (φ g n) = φ₁ (f₂ g) (f₁ n)`.  -/
def map (f₁ : N →* N₁) (f₂ : G →* G₁)
  (h : ∀ g : G, f₁.comp (φ g).to_monoid_hom = (φ₁ (f₂ g)).to_monoid_hom.comp f₁) :
  N ⋊[φ] G →* N₁ ⋊[φ₁] G₁ :=
{ to_fun := λ x, ⟨f₁ x.1, f₂ x.2⟩,
  map_one' := by simp,
  map_mul' := λ x y, begin
    replace h := monoid_hom.ext_iff.1 (h x.right) y.left,
    ext; simp * at *,
  end  }

variables (f₁ : N →* N₁) (f₂ : G →* G₁)
  (h : ∀ g : G, f₁.comp (φ g).to_monoid_hom = (φ₁ (f₂ g)).to_monoid_hom.comp f₁)

@[simp] lemma map_left (g : N ⋊[φ] G) : (map f₁ f₂ h g).left = f₁ g.left := rfl

@[simp] lemma map_right (g : N ⋊[φ] G) : (map f₁ f₂ h g).right = f₂ g.right := rfl

@[simp] lemma right_hom_comp_map : right_hom.comp (map f₁ f₂ h) = f₂.comp right_hom := rfl

@[simp] lemma map_inl (n : N) : map f₁ f₂ h (inl n) = inl (f₁ n) :=
by simp [map]

@[simp] lemma map_comp_inl : (map f₁ f₂ h).comp inl = inl.comp f₁ :=
by ext; simp

@[simp] lemma map_inr (g : G) : map f₁ f₂ h (inr g) = inr (f₂ g) :=
by simp [map]

@[simp] lemma map_comp_inr : (map f₁ f₂ h).comp inr = inr.comp f₂ :=
by ext; simp [map]

end map

end semidirect_product
