/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.bracket
import algebra.algebra.basic
import tactic.noncomm_ring

/-!
# Lie algebras

This file defines Lie rings and Lie algebras over a commutative ring together with their
modules, morphisms and equivalences, as well as various lemmas to make these definitions usable.

## Main definitions

  * `lie_ring`
  * `lie_algebra`
  * `lie_ring_module`
  * `lie_module`
  * `lie_hom`
  * `lie_equiv`
  * `lie_module_hom`
  * `lie_module_equiv`

## Notation

Working over a fixed commutative ring `R`, we introduce the notations:
 * `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
 * `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
 * `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
 * `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

## Tags

lie bracket, jacobi identity, lie ring, lie algebra, lie module
-/

universes u v w w₁ w₂

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. -/
@[protect_proj] class lie_ring (L : Type v) extends add_comm_group L, has_bracket L L :=
(add_lie  : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add  : ∀ (x y z : L), ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(leibniz_lie : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆)

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[protect_proj] class lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L]
  extends module R L :=
(lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)

/-- A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endomorphisms.
(For representations of Lie *algebras* see `lie_module`.) -/
@[protect_proj] class lie_ring_module (L : Type v) (M : Type w)
  [lie_ring L] [add_comm_group M] extends has_bracket L M :=
(add_lie     : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆)
(lie_add     : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆)
(leibniz_lie : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆)

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
@[protect_proj] class lie_module (R : Type u) (L : Type v) (M : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
  [lie_ring_module L M] :=
(smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆)
(lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆)

section basic_properties

variables {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variables [comm_ring R] [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group N] [module R N] [lie_ring_module L N] [lie_module R L N]
variables (t : R) (x y z : L) (m n : M)

@[simp] lemma add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ := lie_ring_module.add_lie x y m

@[simp] lemma lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ := lie_ring_module.lie_add x m n

@[simp] lemma smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆ := lie_module.smul_lie t x m

@[simp] lemma lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆ := lie_module.lie_smul t x m

lemma leibniz_lie : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := lie_ring_module.leibniz_lie x y m

@[simp] lemma lie_zero : ⁅x, 0⁆ = (0 : M) := (add_monoid_hom.mk' _ (lie_add x)).map_zero

@[simp] lemma zero_lie : ⁅(0 : L), m⁆ = 0 :=
(add_monoid_hom.mk' (λ (x : L), ⁅x, m⁆) (λ x y, add_lie x y m)).map_zero

@[simp] lemma lie_self : ⁅x, x⁆ = 0 := lie_ring.lie_self x

instance lie_ring_self_module : lie_ring_module L L := { ..(infer_instance : lie_ring L) }

@[simp] lemma lie_skew : -⁅y, x⁆ = ⁅x, y⁆ :=
have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0, { rw ← lie_add, apply lie_self, },
by simpa [neg_eq_iff_add_eq_zero] using h

/-- Every Lie algebra is a module over itself. -/
instance lie_algebra_self_module : lie_module R L L :=
{ smul_lie := λ t x m, by rw [←lie_skew, ←lie_skew x m, lie_algebra.lie_smul, smul_neg],
  lie_smul := by apply lie_algebra.lie_smul, }

@[simp] lemma neg_lie : ⁅-x, m⁆ = -⁅x, m⁆ :=
by { rw [←sub_eq_zero, sub_neg_eq_add, ←add_lie], simp, }

@[simp] lemma lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ :=
by { rw [←sub_eq_zero, sub_neg_eq_add, ←lie_add], simp, }

@[simp] lemma sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ :=
by simp [sub_eq_add_neg]

@[simp] lemma lie_sub : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ :=
by simp [sub_eq_add_neg]

@[simp] lemma nsmul_lie (n : ℕ) : ⁅n • x, m⁆ = n • ⁅x, m⁆ :=
add_monoid_hom.map_nsmul ⟨λ (x : L), ⁅x, m⁆, zero_lie m, λ _ _, add_lie _ _ _⟩ _ _

@[simp] lemma lie_nsmul (n : ℕ) : ⁅x, n • m⁆ = n • ⁅x, m⁆ :=
add_monoid_hom.map_nsmul ⟨λ (m : M), ⁅x, m⁆, lie_zero x, λ _ _, lie_add _ _ _⟩ _ _

@[simp] lemma gsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (x : L), ⁅x, m⁆, zero_lie m, λ _ _, add_lie _ _ _⟩ _ _

@[simp] lemma lie_gsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (m : M), ⁅x, m⁆, lie_zero x, λ _ _, lie_add _ _ _⟩ _ _

@[simp] lemma lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ :=
by rw [leibniz_lie, add_sub_cancel]

lemma lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
by { rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie], abel, }

instance lie_ring.int_lie_algebra : lie_algebra ℤ L :=
{ lie_smul := λ n x y, lie_gsmul x y n, }

instance : lie_ring_module L (M →ₗ[R] N) :=
{ bracket     := λ x f,
  { to_fun    := λ m, ⁅x, f m⁆ - f ⁅x, m⁆,
    map_add'  := λ m n, by { simp only [lie_add, linear_map.map_add], abel, },
    map_smul' := λ t m, by simp only [smul_sub, linear_map.map_smul, lie_smul], },
  add_lie     := λ x y f, by
    { ext n, simp only [add_lie, linear_map.coe_mk, linear_map.add_apply, linear_map.map_add],
      abel, },
  lie_add     := λ x f g, by
    { ext n, simp only [linear_map.coe_mk, lie_add, linear_map.add_apply], abel, },
  leibniz_lie := λ x y f, by
    { ext n,
      simp only [lie_lie, linear_map.coe_mk, linear_map.map_sub, linear_map.add_apply, lie_sub],
      abel, }, }

@[simp] lemma lie_hom.lie_apply (f : M →ₗ[R] N) (x : L) (m : M) :
  ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆ :=
rfl

instance : lie_module R L (M →ₗ[R] N) :=
{ smul_lie := λ t x f, by
    { ext n,
      simp only [smul_sub, smul_lie, linear_map.smul_apply, lie_hom.lie_apply,
        linear_map.map_smul], },
  lie_smul := λ t x f, by
    { ext n, simp only [smul_sub, linear_map.smul_apply, lie_hom.lie_apply, lie_smul], }, }

end basic_properties

set_option old_structure_cmd true
/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure lie_hom (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends L →ₗ[R] L' :=
(map_lie' : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆)

attribute [nolint doc_blame] lie_hom.to_linear_map

notation L ` →ₗ⁅`:25 R:25 `⁆ `:0 L':0 := lie_hom R L L'

namespace lie_hom

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance : has_coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) := ⟨lie_hom.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ →ₗ⁅R⁆ L₂) := ⟨_, lie_hom.to_fun⟩

initialize_simps_projections lie_hom (to_fun → apply)

@[simp, norm_cast] lemma coe_to_linear_map (f : L₁ →ₗ⁅R⁆ L₂) : ((f : L₁ →ₗ[R] L₂) : L₁ → L₂) = f :=
rfl

@[simp] lemma to_fun_eq_coe (f : L₁ →ₗ⁅R⁆ L₂) : f.to_fun = ⇑f := rfl

@[simp] lemma map_smul (f : L₁ →ₗ⁅R⁆ L₂) (c : R) (x : L₁) : f (c • x) = c • f x :=
linear_map.map_smul (f : L₁ →ₗ[R] L₂) c x

@[simp] lemma map_add (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x + y) = (f x) + (f y) :=
linear_map.map_add (f : L₁ →ₗ[R] L₂) x y

@[simp] lemma map_sub (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x - y) = (f x) - (f y) :=
linear_map.map_sub (f : L₁ →ₗ[R] L₂) x y

@[simp] lemma map_neg (f : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f (-x) = -(f x) :=
linear_map.map_neg (f : L₁ →ₗ[R] L₂) x

@[simp] lemma map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ := lie_hom.map_lie' f

@[simp] lemma map_zero (f : L₁ →ₗ⁅R⁆ L₂) : f 0 = 0 := (f : L₁ →ₗ[R] L₂).map_zero

/-- The identity map is a morphism of Lie algebras. -/
def id : L₁ →ₗ⁅R⁆ L₁ :=
{ map_lie' := λ x y, rfl,
  .. (linear_map.id : L₁ →ₗ[R] L₁) }

@[simp] lemma coe_id : ((id : L₁ →ₗ⁅R⁆ L₁) : L₁ → L₁) = _root_.id := rfl

lemma id_apply (x : L₁) : (id : L₁ →ₗ⁅R⁆ L₁) x = x := rfl

/-- The constant 0 map is a Lie algebra morphism. -/
instance : has_zero (L₁ →ₗ⁅R⁆ L₂) := ⟨{ map_lie' := by simp, ..(0 : L₁ →ₗ[R] L₂)}⟩

@[norm_cast, simp] lemma coe_zero : ((0 : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = 0 := rfl

lemma zero_apply (x : L₁) : (0 : L₁ →ₗ⁅R⁆ L₂) x = 0 := rfl

/-- The identity map is a Lie algebra morphism. -/
instance : has_one (L₁ →ₗ⁅R⁆ L₁) := ⟨id⟩

@[simp] lemma coe_one : ((1 : (L₁ →ₗ⁅R⁆ L₁)) : L₁ → L₁) = _root_.id := rfl

lemma one_apply (x : L₁) : (1 : (L₁ →ₗ⁅R⁆ L₁)) x = x := rfl

instance : inhabited (L₁ →ₗ⁅R⁆ L₂) := ⟨0⟩

lemma coe_injective : function.injective (λ f : L₁ →ₗ⁅R⁆ L₂, show L₁ → L₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : L₁ →ₗ⁅R⁆ L₂} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

lemma congr_fun {f g : L₁ →ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : f x = g x := h ▸ rfl

@[simp] lemma mk_coe (f : L₁ →ₗ⁅R⁆ L₂) (h₁ h₂ h₃ h₄) :
  (⟨f, h₁, h₂, h₃, h₄⟩ : L₁ →ₗ⁅R⁆ L₂) = f :=
by { ext, refl, }

@[simp] lemma coe_mk (f : L₁ → L₂) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f := rfl

@[norm_cast, simp] lemma coe_linear_mk (f : L₁ →ₗ[R] L₂) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ[R] L₂) = ⟨f, h₁, h₂, h₃⟩ :=
by { ext, refl, }

/-- The composition of morphisms is a morphism. -/
def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
{ map_lie' := λ x y, by { change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

lemma comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) :
  f.comp g x = f (g x) := rfl

@[norm_cast, simp]
lemma coe_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
  (f.comp g : L₁ → L₃) = f ∘ g :=
rfl

@[norm_cast, simp]
lemma coe_linear_map_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
  (f.comp g : L₁ →ₗ[R] L₃) = (f : L₂ →ₗ[R] L₃).comp (g : L₁ →ₗ[R] L₂) :=
rfl

@[simp] lemma comp_id (f : L₁ →ₗ⁅R⁆ L₂) : f.comp (id : L₁ →ₗ⁅R⁆ L₁) = f :=
by { ext, refl, }

@[simp] lemma id_comp (f : L₁ →ₗ⁅R⁆ L₂) : (id : L₂ →ₗ⁅R⁆ L₂).comp f = f :=
by { ext, refl, }

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
{ map_lie' := λ x y,
  calc g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ : by { conv_lhs { rw [←h₂ x, ←h₂ y], }, }
            ... = g (f ⁅g x, g y⁆) : by rw map_lie
            ... = ⁅g x, g y⁆ : (h₁ _),
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

end lie_hom

/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.to_linear_equiv` for free. -/
structure lie_equiv (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends L →ₗ⁅R⁆ L', L ≃ₗ[R] L'

attribute [nolint doc_blame] lie_equiv.to_lie_hom
attribute [nolint doc_blame] lie_equiv.to_linear_equiv

notation L ` ≃ₗ⁅`:50 R `⁆ ` L' := lie_equiv R L L'

namespace lie_equiv

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance has_coe_to_lie_hom : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) := ⟨to_lie_hom⟩
instance has_coe_to_linear_equiv : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ ≃ₗ⁅R⁆ L₂) := ⟨_, to_fun⟩

@[simp, norm_cast] lemma coe_to_lie_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = e :=
  rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) :
  ((e : L₁ ≃ₗ[R] L₂) : L₁ → L₂) = e := rfl

instance : has_one (L₁ ≃ₗ⁅R⁆ L₁) :=
⟨{ map_lie' := λ x y,
    by { change ((1 : L₁→ₗ[R] L₁) ⁅x, y⁆) = ⁅(1 : L₁→ₗ[R] L₁) x, (1 : L₁→ₗ[R] L₁) y⁆, simp, },
  ..(1 : L₁ ≃ₗ[R] L₁)}⟩

@[simp] lemma one_apply (x : L₁) : (1 : (L₁ ≃ₗ⁅R⁆ L₁)) x = x := rfl

instance : inhabited (L₁ ≃ₗ⁅R⁆ L₁) := ⟨1⟩

/-- Lie algebra equivalences are reflexive. -/
@[refl]
def refl : L₁ ≃ₗ⁅R⁆ L₁ := 1

@[simp] lemma refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x := rfl

/-- Lie algebra equivalences are symmetric. -/
@[symm]
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
{ ..lie_hom.inverse e.to_lie_hom e.inv_fun e.left_inv e.right_inv,
  ..e.to_linear_equiv.symm }

@[simp] lemma symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e :=
by { cases e, refl, }

@[simp] lemma apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e (e.symm x) = x :=
  e.to_linear_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x :=
  e.to_linear_equiv.symm_apply_apply

/-- Lie algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
{ ..lie_hom.comp e₂.to_lie_hom e₁.to_lie_hom,
  ..linear_equiv.trans e₁.to_linear_equiv e₂.to_linear_equiv }

@[simp] lemma trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma symm_trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₃) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

lemma bijective (e : L₁ ≃ₗ⁅R⁆ L₂) : function.bijective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
e.to_linear_equiv.bijective

lemma injective (e : L₁ ≃ₗ⁅R⁆ L₂) : function.injective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
e.to_linear_equiv.injective

lemma surjective (e : L₁ ≃ₗ⁅R⁆ L₂) : function.surjective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
e.to_linear_equiv.surjective

end lie_equiv

section lie_module_morphisms

variables (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)
variables [comm_ring R] [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [add_comm_group N] [add_comm_group P]
variables [module R M] [module R N] [module R P]
variables [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P]
variables [lie_module R L M] [lie_module R L N] [lie_module R L P]

set_option old_structure_cmd true

/-- A morphism of Lie algebra modules is a linear map which commutes with the action of the Lie
algebra. -/
structure lie_module_hom extends M →ₗ[R] N :=
(map_lie' : ∀ {x : L} {m : M}, to_fun ⁅x, m⁆ = ⁅x, to_fun m⁆)

attribute [nolint doc_blame] lie_module_hom.to_linear_map

notation M ` →ₗ⁅`:25 R,L:25 `⁆ `:0 N:0 := lie_module_hom R L M N

namespace lie_module_hom

variables {R L M N P}

instance : has_coe (M →ₗ⁅R,L⁆ N) (M →ₗ[R] N) := ⟨lie_module_hom.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (M →ₗ⁅R,L⁆ N) := ⟨_, lie_module_hom.to_fun⟩

@[simp, norm_cast] lemma coe_to_linear_map (f : M →ₗ⁅R,L⁆ N) : ((f : M →ₗ[R] N) : M → N) = f :=
rfl

@[simp] lemma map_smul (f : M →ₗ⁅R,L⁆ N) (c : R) (x : M) : f (c • x) = c • f x :=
linear_map.map_smul (f : M →ₗ[R] N) c x

@[simp] lemma map_add (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x + y) = (f x) + (f y) :=
linear_map.map_add (f : M →ₗ[R] N) x y

@[simp] lemma map_sub (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x - y) = (f x) - (f y) :=
linear_map.map_sub (f : M →ₗ[R] N) x y

@[simp] lemma map_neg (f : M →ₗ⁅R,L⁆ N) (x : M) : f (-x) = -(f x) :=
linear_map.map_neg (f : M →ₗ[R] N) x

@[simp] lemma map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
lie_module_hom.map_lie' f

lemma map_lie₂ (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (x : L) (m : M) (n : N) :
  ⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆ :=
by simp only [sub_add_cancel, map_lie, lie_hom.lie_apply]

@[simp] lemma map_zero (f : M →ₗ⁅R,L⁆ N) : f 0 = 0 :=
linear_map.map_zero (f : M →ₗ[R] N)

/-- The constant 0 map is a Lie module morphism. -/
instance : has_zero (M →ₗ⁅R,L⁆ N) := ⟨{ map_lie' := by simp, ..(0 : M →ₗ[R] N) }⟩

@[norm_cast, simp] lemma coe_zero : ((0 : M →ₗ⁅R,L⁆ N) : M → N) = 0 := rfl

lemma zero_apply (m : M) : (0 : M →ₗ⁅R,L⁆ N) m = 0 := rfl

/-- The identity map is a Lie module morphism. -/
instance : has_one (M →ₗ⁅R,L⁆ M) := ⟨{ map_lie' := by simp, ..(1 : M →ₗ[R] M) }⟩

instance : inhabited (M →ₗ⁅R,L⁆ N) := ⟨0⟩

lemma coe_injective : function.injective (λ f : M →ₗ⁅R,L⁆ N, show M → N, from f) :=
by { rintros ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩, congr, }

@[ext] lemma ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : M →ₗ⁅R,L⁆ N} : f = g ↔ ∀ m, f m = g m :=
⟨by { rintro rfl m, refl, }, ext⟩

@[simp] lemma mk_coe (f : M →ₗ⁅R,L⁆ N) (h₁ h₂ h₃ h₄) :
  (⟨f, h₁, h₂, h₃, h₄⟩ : M →ₗ⁅R,L⁆ N) = f :=
by { ext, refl, }

@[simp] lemma coe_mk (f : M → N) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : M →ₗ⁅R,L⁆ N) : M → N) = f := rfl

@[norm_cast, simp] lemma coe_linear_mk (f : M →ₗ[R] N) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : M →ₗ⁅R,L⁆ N) : M →ₗ[R] N) = ⟨f, h₁, h₂, h₃⟩ :=
by { ext, refl, }

/-- The composition of Lie module morphisms is a morphism. -/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
{ map_lie' := λ x m, by { change f (g ⁅x, m⁆) = ⁅x, f (g m)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

lemma comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) :
  f.comp g m = f (g m) := rfl

@[norm_cast, simp] lemma coe_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
  (f.comp g : M → P) = f ∘ g :=
rfl

@[norm_cast, simp] lemma coe_linear_map_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
  (f.comp g : M →ₗ[R] P) = (f : N →ₗ[R] P).comp (g : M →ₗ[R] N) :=
rfl

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : N →ₗ⁅R,L⁆ M :=
{ map_lie' := λ x n,
    calc g ⁅x, n⁆ = g ⁅x, f (g n)⁆ : by rw h₂
              ... = g (f ⁅x, g n⁆) : by rw map_lie
              ... = ⁅x, g n⁆ : (h₁ _),
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

instance : has_add (M →ₗ⁅R,L⁆ N) :=
{ add := λ f g, { map_lie' := by simp, ..((f : M →ₗ[R] N) + (g : M →ₗ[R] N)) }, }

instance : has_sub (M →ₗ⁅R,L⁆ N) :=
{ sub := λ f g, { map_lie' := by simp, ..((f : M →ₗ[R] N) - (g : M →ₗ[R] N)) }, }

instance : has_neg (M →ₗ⁅R,L⁆ N) :=
{ neg := λ f, { map_lie' := by simp, ..(-(f : (M →ₗ[R] N))) }, }

@[norm_cast, simp] lemma coe_add (f g : M →ₗ⁅R,L⁆ N) : ⇑(f + g) = f + g := rfl

lemma add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m := rfl

@[norm_cast, simp] lemma coe_sub (f g : M →ₗ⁅R,L⁆ N) : ⇑(f - g) = f - g := rfl

lemma sub_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m := rfl

@[norm_cast, simp] lemma coe_neg (f : M →ₗ⁅R,L⁆ N) : ⇑(-f) = -f := rfl

lemma neg_apply (f : M →ₗ⁅R,L⁆ N) (m : M) : (-f) m = -(f m) := rfl

instance : add_comm_group (M →ₗ⁅R,L⁆ N) :=
{ zero           := 0,
  add            := (+),
  neg            := has_neg.neg,
  sub            := has_sub.sub,
  nsmul          := λ n f, { map_lie' := λ x m, by simp, ..(n • (f : M →ₗ[R] N)) },
  nsmul_zero'    := λ f, by { ext, simp, },
  nsmul_succ'    := λ n f, by { ext, simp [nat.succ_eq_one_add, add_nsmul], },
  ..(coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub :
    add_comm_group (M →ₗ⁅R,L⁆ N)) }

instance : has_scalar R (M →ₗ⁅R,L⁆ N) :=
{ smul := λ t f, { map_lie' := by simp, ..(t • (f : M →ₗ[R] N)) }, }

@[norm_cast, simp] lemma coe_smul (t : R) (f : M →ₗ⁅R,L⁆ N) : ⇑(t • f) = t • f := rfl

lemma smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • (f m) := rfl

instance : module R (M →ₗ⁅R,L⁆ N) :=
function.injective.module R ⟨to_fun, rfl, coe_add⟩ coe_injective coe_smul

end lie_module_hom

/-- An equivalence of Lie algebra modules is a linear equivalence which is also a morphism of
Lie algebra modules. -/
structure lie_module_equiv extends M ≃ₗ[R] N, M →ₗ⁅R,L⁆ N, M ≃ N

attribute [nolint doc_blame] lie_module_equiv.to_equiv
attribute [nolint doc_blame] lie_module_equiv.to_lie_module_hom
attribute [nolint doc_blame] lie_module_equiv.to_linear_equiv

notation M ` ≃ₗ⁅`:25 R,L:25 `⁆ `:0 N:0 := lie_module_equiv R L M N

namespace lie_module_equiv

variables {R L M N P}

instance has_coe_to_equiv : has_coe (M ≃ₗ⁅R,L⁆ N) (M ≃ N) := ⟨to_equiv⟩
instance has_coe_to_lie_module_hom : has_coe (M ≃ₗ⁅R,L⁆ N) (M →ₗ⁅R,L⁆ N) := ⟨to_lie_module_hom⟩
instance has_coe_to_linear_equiv : has_coe (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (M ≃ₗ⁅R,L⁆ N) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (f : M → N) (h₁ h₂ h₃ F h₄ h₅ h₆) :
  ((⟨f, h₁, h₂, h₃, F, h₄, h₅, h₆⟩ : M ≃ₗ⁅R,L⁆ N) : M → N) = f := rfl

@[simp, norm_cast] lemma coe_to_lie_module_hom (e : M ≃ₗ⁅R,L⁆ N) :
  ((e : M →ₗ⁅R,L⁆ N) : M → N) = e := rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
rfl

lemma to_equiv_injective : function.injective (to_equiv : (M ≃ₗ⁅R,L⁆ N) → M ≃ N) :=
λ ⟨_, _, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _, _⟩ h,
  lie_module_equiv.mk.inj_eq.mpr (equiv.mk.inj h)

@[ext] lemma ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : ∀ m, e₁ m = e₂ m) : e₁ = e₂ :=
to_equiv_injective (equiv.ext h)

instance : has_one (M ≃ₗ⁅R,L⁆ M) := ⟨{ map_lie' := λ x m, rfl, ..(1 : M ≃ₗ[R] M) }⟩

@[simp] lemma one_apply (m : M) : (1 : (M ≃ₗ⁅R,L⁆ M)) m = m := rfl

instance : inhabited (M ≃ₗ⁅R,L⁆ M) := ⟨1⟩

/-- Lie module equivalences are reflexive. -/
@[refl] def refl : M ≃ₗ⁅R,L⁆ M := 1

@[simp] lemma refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m := rfl

/-- Lie module equivalences are syemmtric. -/
@[symm] def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
{ ..lie_module_hom.inverse e.to_lie_module_hom e.inv_fun e.left_inv e.right_inv,
  ..(e : M ≃ₗ[R] N).symm }

@[simp] lemma symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e :=
by { cases e, refl, }

@[simp] lemma apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e (e.symm x) = x :=
  e.to_linear_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e.symm (e x) = x :=
  e.to_linear_equiv.symm_apply_apply

/-- Lie module equivalences are transitive. -/
@[trans] def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
{ ..lie_module_hom.comp e₂.to_lie_module_hom e₁.to_lie_module_hom,
  ..linear_equiv.trans e₁.to_linear_equiv e₂.to_linear_equiv }

@[simp] lemma trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) :
  (e₁.trans e₂) m = e₂ (e₁ m) := rfl

@[simp] lemma symm_trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (p : P) :
  (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl

end lie_module_equiv

end lie_module_morphisms
