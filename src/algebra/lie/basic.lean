/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.bracket
import linear_algebra.bilinear_form
import tactic.noncomm_ring

/-!
# Lie algebras

This file defines Lie rings, and Lie algebras over a commutative ring. It shows how these arise from
associative rings and algebras via the ring commutator. In particular it defines the Lie algebra
of endomorphisms of a module as well as of the algebra of square matrices over a commutative ring.

It also includes definitions of morphisms of Lie algebras, Lie subalgebras, Lie modules, Lie
submodules, and the quotient of a Lie algebra by an ideal.

## Notations

We introduce the notation ⁅x, y⁆ for the Lie bracket. Note that these are the Unicode "square with
quill" brackets rather than the usual square brackets.

Working over a fixed commutative ring `R`, we introduce the notations:
 * `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
 * `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
 * `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
 * `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975]

## Tags

lie bracket, ring commutator, jacobi identity, lie ring, lie algebra
-/

universes u v w w₁ w₂

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero. -/
@[protect_proj] class lie_ring (L : Type v) extends add_comm_group L, has_bracket L L :=
(add_lie : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add : ∀ (x y z : L), ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(leibniz_lie : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆)

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[protect_proj] class lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L]
  extends semimodule R L :=
(lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)

/-- A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endomorphisms.
(For representations of Lie *algebras* see `lie_module`.) -/
@[protect_proj] class lie_ring_module (L : Type v) (M : Type w)
  [lie_ring L] [add_comm_group M] extends has_bracket L M :=
(add_lie : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆)
(lie_add : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆)
(leibniz_lie : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆)

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
@[protect_proj] class lie_module (R : Type u) (L : Type v) (M : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
  [lie_ring_module L M] :=
(smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆)
(lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆)

section basic_properties

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
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
by { rw [←sub_eq_zero_iff_eq, sub_neg_eq_add, ←add_lie], simp, }

@[simp] lemma lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ :=
by { rw [←sub_eq_zero_iff_eq, sub_neg_eq_add, ←lie_add], simp, }

@[simp] lemma gsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (x : L), ⁅x, m⁆, zero_lie m, λ _ _, add_lie _ _ _⟩ _ _

@[simp] lemma lie_gsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (m : M), ⁅x, m⁆, lie_zero x, λ _ _, lie_add _ _ _⟩ _ _

@[simp] lemma lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ :=
by rw [leibniz_lie, add_sub_cancel]

lemma lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
by { rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie], abel, }

end basic_properties

namespace lie_algebra

set_option old_structure_cmd true
/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure morphism (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends linear_map R L L' :=
(map_lie : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆)

attribute [nolint doc_blame] lie_algebra.morphism.to_linear_map

notation L ` →ₗ⁅`:25 R:25 `⁆ `:0 L':0 := morphism R L L'

section morphism_properties

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance : has_coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) := ⟨morphism.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ →ₗ⁅R⁆ L₂) := ⟨_, morphism.to_fun⟩

@[simp] lemma coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : L₁ →ₗ⁅R⁆ L₂) : ((f : L₁ →ₗ[R] L₂) : L₁ → L₂) = f :=
rfl

@[simp] lemma morphism.map_smul (f : L₁ →ₗ⁅R⁆ L₂) (c : R) (x : L₁) : f (c • x) = c • f x :=
linear_map.map_smul (f : L₁ →ₗ[R] L₂) c x

@[simp] lemma morphism.map_add (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x + y) = (f x) + (f y) :=
linear_map.map_add (f : L₁ →ₗ[R] L₂) x y

@[simp] lemma map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ := morphism.map_lie f

@[simp] lemma map_zero (f : L₁ →ₗ⁅R⁆ L₂) : f 0 = 0 := (f : L₁ →ₗ[R] L₂).map_zero

/-- The constant 0 map is a Lie algebra morphism. -/
instance : has_zero (L₁ →ₗ⁅R⁆ L₂) := ⟨{ map_lie := by simp, ..(0 : L₁ →ₗ[R] L₂)}⟩

/-- The identity map is a Lie algebra morphism. -/
instance : has_one (L₁ →ₗ⁅R⁆ L₁) := ⟨{ map_lie := by simp, ..(1 : L₁ →ₗ[R] L₁)}⟩

instance : inhabited (L₁ →ₗ⁅R⁆ L₂) := ⟨0⟩

lemma morphism.coe_injective : function.injective (λ f : L₁ →ₗ⁅R⁆ L₂, show L₁ → L₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma morphism.ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
morphism.coe_injective $ funext h

lemma morphism.ext_iff {f g : L₁ →ₗ⁅R⁆ L₂} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, morphism.ext⟩

/-- The composition of morphisms is a morphism. -/
def morphism.comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
{ map_lie := λ x y, by { change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

@[simp] lemma morphism.comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) :
  f.comp g x = f (g x) := rfl

@[norm_cast]
lemma morphism.comp_coe (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
  (f : L₂ → L₃) ∘ (g : L₁ → L₂) = f.comp g := rfl

/-- The inverse of a bijective morphism is a morphism. -/
def morphism.inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
{ map_lie := λ x y,
  calc g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ : by { conv_lhs { rw [←h₂ x, ←h₂ y], }, }
            ... = g (f ⁅g x, g y⁆) : by rw map_lie
            ... = ⁅g x, g y⁆ : (h₁ _),
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

end morphism_properties

/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.to_linear_equiv` for free. -/
structure equiv (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends L →ₗ⁅R⁆ L', L ≃ₗ[R] L'

attribute [nolint doc_blame] lie_algebra.equiv.to_morphism
attribute [nolint doc_blame] lie_algebra.equiv.to_linear_equiv

notation L ` ≃ₗ⁅`:50 R `⁆ ` L' := equiv R L L'

namespace equiv

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance has_coe_to_lie_hom : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) := ⟨to_morphism⟩
instance has_coe_to_linear_equiv : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ ≃ₗ⁅R⁆ L₂) := ⟨_, to_fun⟩

@[simp, norm_cast] lemma coe_to_lie_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = e :=
  rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) :
  ((e : L₁ ≃ₗ[R] L₂) : L₁ → L₂) = e := rfl

instance : has_one (L₁ ≃ₗ⁅R⁆ L₁) :=
⟨{ map_lie := λ x y,
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
{ ..morphism.inverse e.to_morphism e.inv_fun e.left_inv e.right_inv,
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
{ ..morphism.comp e₂.to_morphism e₁.to_morphism,
  ..linear_equiv.trans e₁.to_linear_equiv e₂.to_linear_equiv }

@[simp] lemma trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma symm_trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₃) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

end equiv

end lie_algebra

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
(map_lie : ∀ {x : L} {m : M}, to_fun ⁅x, m⁆ = ⁅x, to_fun m⁆)

attribute [nolint doc_blame] lie_module_hom.to_linear_map

notation M ` →ₗ⁅`:25 R,L:25 `⁆ `:0 N:0 := lie_module_hom R L M N

namespace lie_module_hom

variables {R L M N P}

instance : has_coe (M →ₗ⁅R,L⁆ N) (M →ₗ[R] N) := ⟨lie_module_hom.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (M →ₗ⁅R,L⁆ N) := ⟨_, lie_module_hom.to_fun⟩

@[simp] lemma coe_mk (f : M → N) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : M →ₗ⁅R,L⁆ N) : M → N) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : M →ₗ⁅R,L⁆ N) : ((f : M →ₗ[R] N) : M → N) = f :=
rfl

@[simp] lemma map_lie' (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
lie_module_hom.map_lie f

/-- The constant 0 map is a Lie module morphism. -/
instance : has_zero (M →ₗ⁅R,L⁆ N) := ⟨{ map_lie := by simp, ..(0 : M →ₗ[R] N) }⟩

/-- The identity map is a Lie module morphism. -/
instance : has_one (M →ₗ⁅R,L⁆ M) := ⟨{ map_lie := by simp, ..(1 : M →ₗ[R] M) }⟩

instance : inhabited (M →ₗ⁅R,L⁆ N) := ⟨0⟩

lemma coe_injective : function.injective (λ f : M →ₗ⁅R,L⁆ N, show M → N, from f) :=
by { rintros ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩, congr, }

@[ext] lemma ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : M →ₗ⁅R,L⁆ N} : f = g ↔ ∀ m, f m = g m :=
⟨by { rintro rfl m, refl, }, ext⟩

/-- The composition of Lie module morphisms is a morphism. -/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
{ map_lie := λ x m, by { change f (g ⁅x, m⁆) = ⁅x, f (g m)⁆, rw [map_lie', map_lie'], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

@[simp] lemma comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) :
  f.comp g m = f (g m) := rfl

@[norm_cast] lemma comp_coe (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
  (f : N → P) ∘ (g : M → N) = f.comp g := rfl

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : N →ₗ⁅R,L⁆ M :=
{ map_lie := λ x n,
    calc g ⁅x, n⁆ = g ⁅x, f (g n)⁆ : by rw h₂
              ... = g (f ⁅x, g n⁆) : by rw map_lie'
              ... = ⁅x, g n⁆ : (h₁ _),
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

end lie_module_hom

/-- An equivalence of Lie algebra modules is a linear equivalence which is also a morphism of
Lie algebra modules. -/
structure lie_module_equiv extends M ≃ₗ[R] N, M →ₗ⁅R,L⁆ N

attribute [nolint doc_blame] lie_module_equiv.to_lie_module_hom
attribute [nolint doc_blame] lie_module_equiv.to_linear_equiv

notation M ` ≃ₗ⁅`:25 R,L:25 `⁆ `:0 N:0 := lie_module_equiv R L M N

namespace lie_module_equiv

variables {R L M N P}

instance has_coe_to_lie_module_hom : has_coe (M ≃ₗ⁅R,L⁆ N) (M →ₗ⁅R,L⁆ N) := ⟨to_lie_module_hom⟩
instance has_coe_to_linear_equiv : has_coe (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (M ≃ₗ⁅R,L⁆ N) := ⟨_, to_fun⟩

@[simp, norm_cast] lemma coe_to_lie_module_hom (e : M ≃ₗ⁅R,L⁆ N) :
  ((e : M →ₗ⁅R,L⁆ N) : M → N) = e := rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
rfl

instance : has_one (M ≃ₗ⁅R,L⁆ M) := ⟨{ map_lie := λ x m, rfl, ..(1 : M ≃ₗ[R] M) }⟩

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

section of_associative

variables {A : Type v} [ring A]

namespace ring_commutator

/-- The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
@[priority 100]
instance : has_bracket A A := ⟨λ x y, x*y - y*x⟩

lemma commutator (x y : A) : ⁅x, y⁆ = x*y - y*x := rfl

end ring_commutator

namespace lie_ring

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
@[priority 100]
instance of_associative_ring : lie_ring A :=
{ add_lie      := by simp only [ring_commutator.commutator, right_distrib, left_distrib,
    sub_eq_add_neg, add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_add      := by simp only [ring_commutator.commutator, right_distrib, left_distrib,
    sub_eq_add_neg, add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_self     := by simp only [ring_commutator.commutator, forall_const, sub_self],
  leibniz_lie  := λ x y z, by { repeat {rw ring_commutator.commutator}, noncomm_ring, } }

lemma of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x*y - y*x := rfl

end lie_ring

/-- A Lie (ring) module is trivial iff all brackets vanish. -/
class lie_module.is_trivial (L : Type v) (M : Type w) [has_bracket L M] [has_zero M] : Prop :=
(trivial : ∀ (x : L) (m : M), ⁅x, m⁆ = 0)

@[simp] lemma trivial_lie_zero (L : Type v) (M : Type w)
  [has_bracket L M] [has_zero M] [lie_module.is_trivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0 :=
lie_module.is_trivial.trivial x m

/-- A Lie algebra is Abelian iff it is trivial as a Lie module over itself. -/
abbreviation is_lie_abelian (L : Type v) [has_bracket L L] [has_zero L] : Prop :=
lie_module.is_trivial L L

lemma commutative_ring_iff_abelian_lie_ring : is_commutative A (*) ↔ is_lie_abelian A :=
begin
  have h₁ : is_commutative A (*) ↔ ∀ (a b : A), a * b = b * a := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  have h₂ : is_lie_abelian A ↔ ∀ (a b : A), ⁅a, b⁆ = 0 := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  simp only [h₁, h₂, lie_ring.of_associative_ring_bracket, sub_eq_zero],
end

namespace lie_algebra

variables {R : Type u} [comm_ring R] [algebra R A]

/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
@[priority 100]
instance of_associative_algebra : lie_algebra R A :=
{ lie_smul := λ t x y,
    by rw [lie_ring.of_associative_ring_bracket, lie_ring.of_associative_ring_bracket,
           algebra.mul_smul_comm, algebra.smul_mul_assoc, smul_sub], }

/-- The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def of_associative_algebra_hom {B : Type w} [ring B] [algebra R B] (f : A →ₐ[R] B) : A →ₗ⁅R⁆ B :=
 { map_lie := λ x y, show f ⁅x,y⁆ = ⁅f x,f y⁆,
     by simp only [lie_ring.of_associative_ring_bracket, alg_hom.map_sub, alg_hom.map_mul],
  ..f.to_linear_map, }

@[simp] lemma of_associative_algebra_hom_id : of_associative_algebra_hom (alg_hom.id R A) = 1 := rfl

@[simp] lemma of_associative_algebra_hom_apply {B : Type w} [ring B] [algebra R B]
  (f : A →ₐ[R] B) (x : A) : of_associative_algebra_hom f x = f x := rfl

@[simp] lemma of_associative_algebra_hom_comp {B : Type w} {C : Type w₁}
  [ring B] [ring C] [algebra R B] [algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  of_associative_algebra_hom (g.comp f) =
  (of_associative_algebra_hom g).comp (of_associative_algebra_hom f) := rfl

end lie_algebra

end of_associative

section adjoint_action

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module. -/
def lie_module.to_endo_morphism : L →ₗ⁅R⁆ module.End R M :=
{ to_fun    := λ x,
  { to_fun    := λ m, ⁅x, m⁆,
    map_add'  := lie_add x,
    map_smul' := λ t, lie_smul t x, },
  map_add'  := λ x y, by { ext m, apply add_lie, },
  map_smul' := λ t x, by { ext m, apply smul_lie, },
  map_lie   := λ x y, by { ext m, apply lie_lie, }, }

/-- The adjoint action of a Lie algebra on itself. -/
def lie_algebra.ad : L →ₗ⁅R⁆ module.End R L := lie_module.to_endo_morphism R L L

@[simp] lemma lie_algebra.ad_apply (x y : L) : lie_algebra.ad R L x y = ⁅x, y⁆ := rfl

end adjoint_action

section lie_subalgebra

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

set_option old_structure_cmd true
/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
structure lie_subalgebra extends submodule R L :=
(lie_mem' : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier)

attribute [nolint doc_blame] lie_subalgebra.to_submodule

/-- The zero algebra is a subalgebra of any Lie algebra. -/
instance : has_zero (lie_subalgebra R L) :=
⟨{ lie_mem' := λ x y hx hy, by { rw [((submodule.mem_bot R).1 hx), zero_lie],
                                exact submodule.zero_mem (0 : submodule R L), },
   ..(0 : submodule R L) }⟩

instance : inhabited (lie_subalgebra R L) := ⟨0⟩
instance : has_coe (lie_subalgebra R L) (set L) := ⟨lie_subalgebra.carrier⟩
instance : has_mem L (lie_subalgebra R L) := ⟨λ x L', x ∈ (L' : set L)⟩

instance lie_subalgebra_coe_submodule : has_coe (lie_subalgebra R L) (submodule R L) :=
⟨lie_subalgebra.to_submodule⟩

/-- A Lie subalgebra forms a new Lie ring. -/
instance lie_subalgebra_lie_ring (L' : lie_subalgebra R L) : lie_ring L' :=
{ bracket      := λ x y, ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩,
  lie_add      := by { intros, apply set_coe.ext, apply lie_add, },
  add_lie      := by { intros, apply set_coe.ext, apply add_lie, },
  lie_self     := by { intros, apply set_coe.ext, apply lie_self, },
  leibniz_lie  := by { intros, apply set_coe.ext, apply leibniz_lie, } }

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lie_subalgebra_lie_algebra (L' : lie_subalgebra R L) : lie_algebra R L' :=
{ lie_smul := by { intros, apply set_coe.ext, apply lie_smul } }

namespace lie_subalgebra

variables {R L} (L' : lie_subalgebra R L)

@[simp] lemma zero_mem : (0 : L) ∈ L' := (L' : submodule R L).zero_mem

lemma smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' := (L' : submodule R L).smul_mem t h

lemma add_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (x + y : L) ∈ L' :=
(L' : submodule R L).add_mem hx hy

lemma lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' := L'.lie_mem' hx hy

@[simp] lemma mem_coe {x : L} : x ∈ (L' : set L) ↔ x ∈ L' := iff.rfl

@[simp] lemma mem_coe' {x : L} : x ∈ (L' : submodule R L) ↔ x ∈ L' := iff.rfl

@[simp, norm_cast] lemma coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ := rfl

@[ext] lemma ext (L₁' L₂' : lie_subalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') :
  L₁' = L₂' :=
by { cases L₁', cases L₂', simp only [], ext x, exact h x, }

lemma ext_iff (L₁' L₂' : lie_subalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
⟨λ h x, by rw h, ext L₁' L₂'⟩

@[simp] lemma mk_coe (S : set L) (h₁ h₂ h₃ h₄) :
  ((⟨S, h₁, h₂, h₃, h₄⟩ : lie_subalgebra R L) : set L) = S := rfl

lemma coe_injective : function.injective (coe : lie_subalgebra R L → set L) :=
λ L₁' L₂' h, by cases L₁'; cases L₂'; congr'

@[simp, norm_cast] theorem coe_set_eq (L₁' L₂' : lie_subalgebra R L) :
  (L₁' : set L) = L₂' ↔ L₁' = L₂' := coe_injective.eq_iff

lemma to_submodule_injective :
  function.injective (coe : lie_subalgebra R L → submodule R L) :=
λ L₁' L₂' h, by { rw submodule.ext'_iff at h, rw ← coe_set_eq, exact h, }

@[simp] lemma coe_to_submodule_eq (L₁' L₂' : lie_subalgebra R L) :
  (L₁' : submodule R L) = (L₂' : submodule R L) ↔ L₁' = L₂' :=
to_submodule_injective.eq_iff

end lie_subalgebra

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lie_subalgebra_of_subalgebra (A : Type v) [ring A] [algebra R A]
  (A' : subalgebra R A) : lie_subalgebra R A :=
{ lie_mem' := λ x y hx hy, by {
    change ⁅x, y⁆ ∈ A', change x ∈ A' at hx, change y ∈ A' at hy,
    rw lie_ring.of_associative_ring_bracket,
    have hxy := A'.mul_mem hx hy,
    have hyx := A'.mul_mem hy hx,
    exact submodule.sub_mem A'.to_submodule hxy hyx, },
  ..A'.to_submodule }

variables {R L} {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂]
variables (f : L →ₗ⁅R⁆ L₂)

/-- The embedding of a Lie subalgebra into the ambient space as a Lie morphism. -/
def lie_subalgebra.incl (L' : lie_subalgebra R L) : L' →ₗ⁅R⁆ L :=
{ map_lie := λ x y, by { rw [linear_map.to_fun_eq_coe, submodule.subtype_apply], refl, },
  ..L'.to_submodule.subtype }

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def lie_algebra.morphism.range : lie_subalgebra R L₂ :=
{ lie_mem' := λ x y,
    show x ∈ f.to_linear_map.range → y ∈ f.to_linear_map.range → ⁅x, y⁆ ∈ f.to_linear_map.range,
    by { repeat { rw linear_map.mem_range }, rintros ⟨x', hx⟩ ⟨y', hy⟩, refine ⟨⁅x', y'⁆, _⟩,
         rw [←hx, ←hy], change f ⁅x', y'⁆ = ⁅f x', f y'⁆, rw lie_algebra.map_lie, },
  ..f.to_linear_map.range }

@[simp] lemma lie_algebra.morphism.range_bracket (x y : f.range) :
  (↑⁅x, y⁆ : L₂) = ⁅(↑x : L₂), ↑y⁆ := rfl

@[simp] lemma lie_algebra.morphism.range_coe : (f.range : set L₂) = set.range f :=
linear_map.range_coe ↑f

@[simp] lemma lie_subalgebra.range_incl (L' : lie_subalgebra R L) : L'.incl.range = L' :=
by { rw ← lie_subalgebra.coe_to_submodule_eq, exact (L' : submodule R L).range_subtype, }

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def lie_subalgebra.map (L' : lie_subalgebra R L) : lie_subalgebra R L₂ :=
{ lie_mem' := λ x y hx hy, by {
    erw submodule.mem_map at hx, rcases hx with ⟨x', hx', hx⟩, rw ←hx,
    erw submodule.mem_map at hy, rcases hy with ⟨y', hy', hy⟩, rw ←hy,
    erw submodule.mem_map,
    exact ⟨⁅x', y'⁆, L'.lie_mem hx' hy', lie_algebra.map_lie f x' y'⟩, },
..((L' : submodule R L).map (f : L →ₗ[R] L₂))}

@[simp] lemma lie_subalgebra.mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (L' : lie_subalgebra R L) (x : L₂) :
  x ∈ L'.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (L' : submodule R L).map (e : L →ₗ[R] L₂) :=
iff.rfl

end lie_subalgebra

namespace lie_algebra

variables {R : Type u} {L₁ : Type v} {L₂ : Type w}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]

namespace equiv

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
noncomputable def of_injective (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) :
  L₁ ≃ₗ⁅R⁆ f.range :=
have h' : (f : L₁ →ₗ[R] L₂).ker = ⊥ := linear_map.ker_eq_bot_of_injective h,
{ map_lie := λ x y, by { apply set_coe.ext,
    simp only [linear_equiv.of_injective_apply, lie_algebra.morphism.range_bracket],
    apply f.map_lie, },
..(linear_equiv.of_injective ↑f h')}

@[simp] lemma of_injective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) (x : L₁) :
  ↑(of_injective f h x) = f x := rfl

variables (L₁' L₁'' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def of_eq (h : (L₁' : set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
{ map_lie := λ x y, by { apply set_coe.ext, simp, },
  ..(linear_equiv.of_eq ↑L₁' ↑L₁''
      (by {ext x, change x ∈ (L₁' : set L₁) ↔ x ∈ (L₁'' : set L₁), rw h, } )) }

@[simp] lemma of_eq_apply (L L' : lie_subalgebra R L₁) (h : (L : set L₁) = L') (x : L) :
  (↑(of_eq L L' h x) : L₁) = x := rfl

variables (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebra : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : lie_subalgebra R L₂) :=
{ map_lie := λ x y, by { apply set_coe.ext, exact lie_algebra.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, }
  ..(linear_equiv.of_submodule (e : L₁ ≃ₗ[R] L₂) ↑L₁'') }

@[simp] lemma of_subalgebra_apply (x : L₁'') : ↑(e.of_subalgebra _  x) = e x := rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
{ map_lie := λ x y, by { apply set_coe.ext, exact lie_algebra.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, },
  ..(linear_equiv.of_submodules (e : L₁ ≃ₗ[R] L₂) ↑L₁' ↑L₂' (by { rw ←h, refl, })) }

@[simp] lemma of_subalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') :
  ↑(e.of_subalgebras _ _ h x) = e x := rfl

@[simp] lemma of_subalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
  ↑((e.of_subalgebras _ _ h).symm x) = e.symm x := rfl

end equiv

end lie_algebra

section lie_submodule

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

set_option old_structure_cmd true
/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure lie_submodule extends submodule R M :=
(lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier)

attribute [nolint doc_blame] lie_submodule.to_submodule

namespace lie_submodule

/-- The zero module is a Lie submodule of any Lie module. -/
instance : has_zero (lie_submodule R L M) :=
⟨{ lie_mem := λ x m h, by { rw ((submodule.mem_bot R).1 h), apply lie_zero, },
   ..(0 : submodule R M)}⟩

instance : inhabited (lie_submodule R L M) := ⟨0⟩

instance coe_submodule : has_coe (lie_submodule R L M) (submodule R M) := ⟨to_submodule⟩

@[norm_cast]
lemma coe_to_submodule (N : lie_submodule R L M) : ((N : submodule R M) : set M) = N := rfl

instance has_mem : has_mem M (lie_submodule R L M) := ⟨λ x N, x ∈ (N : set M)⟩

@[simp] lemma mem_carrier (N : lie_submodule R L M) {x : M} : x ∈ N.carrier ↔ x ∈ (N : set M) :=
iff.rfl

@[simp] lemma mem_coe_submodule (N : lie_submodule R L M) {x : M} :
  x ∈ (N : submodule R M) ↔ x ∈ N := iff.rfl

lemma mem_coe (N : lie_submodule R L M) {x : M} : x ∈ (N : set M) ↔ x ∈ N := iff.rfl

@[simp] lemma coe_to_set_mk (S : set M) (h₁ h₂ h₃ h₄) :
  ((⟨S, h₁, h₂, h₃, h₄⟩ : lie_submodule R L M) : set M) = S := rfl

@[simp] lemma coe_to_submodule_mk (p : submodule R M) (h) :
  (({lie_mem := h, ..p} : lie_submodule R L M) : submodule R M) = p :=
by { cases p, refl, }

@[ext] lemma ext (N N' : lie_submodule R L M) (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
by { cases N, cases N', simp only [], ext m, exact h m, }

@[simp] lemma coe_to_submodule_eq_iff (N N' : lie_submodule R L M) :
  (N : submodule R M) = (N' : submodule R M) ↔ N = N' :=
begin
  split; intros h,
  { ext, rw [← mem_coe_submodule, h], simp, },
  { rw h, },
end

instance (N : lie_submodule R L M) : lie_ring_module L N :=
{ bracket     := λ (x : L) (m : N), ⟨⁅x, m.val⁆, N.lie_mem m.property⟩,
  add_lie     := by { intros x y m, apply set_coe.ext, apply add_lie, },
  lie_add     := by { intros x m n, apply set_coe.ext, apply lie_add, },
  leibniz_lie := by { intros x y m, apply set_coe.ext, apply leibniz_lie, }, }

instance (N : lie_submodule R L M) : lie_module R L N :=
{ lie_smul := by { intros t x y, apply set_coe.ext, apply lie_smul, },
  smul_lie := by { intros t x y, apply set_coe.ext, apply smul_lie, }, }

end lie_submodule

section lie_ideal

variables (L)

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbreviation lie_ideal := lie_submodule R L L

lemma lie_mem_right (I : lie_ideal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I := I.lie_mem h

lemma lie_mem_left (I : lie_ideal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I :=
 by { rw [←lie_skew, ←neg_lie], apply lie_mem_right, assumption, }

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def lie_ideal_subalgebra (I : lie_ideal R L) : lie_subalgebra R L :=
{ lie_mem' := by { intros x y hx hy, apply lie_mem_right, exact hy, },
  ..I.to_submodule, }

instance : has_coe (lie_ideal R L) (lie_subalgebra R L) := ⟨λ I, lie_ideal_subalgebra R L I⟩

@[norm_cast] lemma lie_ideal.coe_to_subalgebra (I : lie_ideal R L) :
  ((I : lie_subalgebra R L) : set L) = I := rfl

end lie_ideal

end lie_submodule

namespace lie_submodule

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (N N' : lie_submodule R L M) (I J : lie_ideal R L)

section lattice_structure

open set

lemma coe_injective : function.injective (coe : lie_submodule R L M → set M) :=
λ N N' h, by { cases N, cases N', simp only, exact h, }

lemma coe_submodule_injective : function.injective (coe : lie_submodule R L M → submodule R M) :=
λ N N' h, by { ext, rw [← mem_coe_submodule, h], refl, }

instance : partial_order (lie_submodule R L M) :=
{ le := λ N N', ∀ ⦃x⦄, x ∈ N → x ∈ N', -- Overriding `le` like this gives a better defeq.
  ..partial_order.lift (coe : lie_submodule R L M → set M) coe_injective }

lemma le_def : N ≤ N' ↔ (N : set M) ⊆ N' := iff.rfl

@[simp, norm_cast] lemma coe_submodule_le_coe_submodule : (N : submodule R M) ≤ N' ↔ N ≤ N' :=
iff.rfl

instance : has_bot (lie_submodule R L M) := ⟨0⟩

@[simp] lemma bot_coe : ((⊥ : lie_submodule R L M) : set M) = {0} := rfl

@[simp] lemma bot_coe_submodule : ((⊥ : lie_submodule R L M) : submodule R M) = ⊥ := rfl

@[simp] lemma mem_bot (x : M) : x ∈ (⊥ : lie_submodule R L M) ↔ x = 0 := mem_singleton_iff

instance : has_top (lie_submodule R L M) :=
⟨{ lie_mem := λ x m h, mem_univ ⁅x, m⁆,
   ..(⊤ : submodule R M) }⟩

@[simp] lemma top_coe : ((⊤ : lie_submodule R L M) : set M) = univ := rfl

@[simp] lemma top_coe_submodule : ((⊤ : lie_submodule R L M) : submodule R M) = ⊤ := rfl

lemma mem_top (x : M) : x ∈ (⊤ : lie_submodule R L M) := mem_univ x

instance : has_inf (lie_submodule R L M) :=
⟨λ N N', { lie_mem := λ x m h, mem_inter (N.lie_mem h.1) (N'.lie_mem h.2),
            ..(N ⊓ N' : submodule R M) }⟩

instance : has_Inf (lie_submodule R L M) :=
⟨λ S, { lie_mem := λ x m h, by
        { simp only [submodule.mem_carrier, mem_Inter, submodule.Inf_coe, mem_set_of_eq,
            forall_apply_eq_imp_iff₂, exists_imp_distrib] at *,
          intros N hN, apply N.lie_mem (h N hN), },
        ..Inf {(s : submodule R M) | s ∈ S} }⟩

@[simp] theorem inf_coe : (↑(N ⊓ N') : set M) = N ∩ N' := rfl

@[simp] lemma Inf_coe_to_submodule (S : set (lie_submodule R L M)) :
  (↑(Inf S) : submodule R M) = Inf {(s : submodule R M) | s ∈ S} := rfl

@[simp] lemma Inf_coe (S : set (lie_submodule R L M)) : (↑(Inf S) : set M) = ⋂ s ∈ S, (s : set M) :=
begin
  rw [← lie_submodule.coe_to_submodule, Inf_coe_to_submodule, submodule.Inf_coe],
  ext m,
  simpa only [mem_Inter, mem_set_of_eq, forall_apply_eq_imp_iff₂, exists_imp_distrib],
end

lemma Inf_glb (S : set (lie_submodule R L M)) : is_glb S (Inf S) :=
begin
  have h : ∀ (N N' : lie_submodule R L M), (N : set M) ≤ N' ↔ N ≤ N', { intros, apply iff.rfl, },
  simp only [is_glb.of_image h, Inf_coe, is_glb_binfi],
end

/-- The set of Lie submodules of a Lie module form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `complete_lattice_of_Inf`.  -/
instance : complete_lattice (lie_submodule R L M) :=
{ bot          := ⊥,
  bot_le       := λ N _ h, by { rw mem_bot at h, rw h, exact N.zero_mem', },
  top          := ⊤,
  le_top       := λ _ _ _, trivial,
  inf          := (⊓),
  le_inf       := λ N₁ N₂ N₃ h₁₂ h₁₃ m hm, ⟨h₁₂ hm, h₁₃ hm⟩,
  inf_le_left  := λ _ _ _, and.left,
  inf_le_right := λ _ _ _, and.right,
  ..complete_lattice_of_Inf _ Inf_glb }

instance : add_comm_monoid (lie_submodule R L M) :=
{ add       := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero      := ⊥,
  zero_add  := λ _, bot_sup_eq,
  add_zero  := λ _, sup_bot_eq,
  add_comm  := λ _ _, sup_comm, }

@[simp] lemma add_eq_sup : N + N' = N ⊔ N' := rfl

@[norm_cast, simp] lemma sup_coe_to_submodule :
  (↑(N ⊔ N') : submodule R M) = (N : submodule R M) ⊔ (N' : submodule R M) :=
begin
  have aux : ∀ (x : L) m, m ∈ (N ⊔ N' : submodule R M) → ⁅x,m⁆ ∈ (N ⊔ N' : submodule R M),
  { simp only [submodule.mem_sup],
    rintro x m ⟨y, hy, z, hz, rfl⟩,
    refine ⟨⁅x, y⁆, N.lie_mem hy, ⁅x, z⁆, N'.lie_mem hz, (lie_add _ _ _).symm⟩ },
  refine le_antisymm (Inf_le ⟨{ lie_mem := aux, ..(N ⊔ N' : submodule R M) }, _⟩) _,
  { simp only [exists_prop, and_true, mem_set_of_eq, eq_self_iff_true, coe_to_submodule_mk,
      ← coe_submodule_le_coe_submodule, and_self, le_sup_left, le_sup_right] },
  { simp, },
end

@[norm_cast, simp] lemma inf_coe_to_submodule :
  (↑(N ⊓ N') : submodule R M) = (N : submodule R M) ⊓ (N' : submodule R M) := rfl

@[simp] lemma mem_inf (x : M) : x ∈ N ⊓ N' ↔ x ∈ N ∧ x ∈ N' :=
by rw [← mem_coe_submodule, ← mem_coe_submodule, ← mem_coe_submodule, inf_coe_to_submodule,
  submodule.mem_inf]

lemma mem_sup (x : M) : x ∈ N ⊔ N' ↔ ∃ (y ∈ N) (z ∈ N'), y + z = x :=
by { rw [← mem_coe_submodule, sup_coe_to_submodule, submodule.mem_sup], exact iff.rfl, }

lemma eq_bot_iff : N = ⊥ ↔ ∀ (m : M), m ∈ N → m = 0 :=
by { rw eq_bot_iff, exact iff.rfl, }

section inclusion_maps

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
def incl : N →ₗ⁅R,L⁆ M :=
{ map_lie := λ x m, rfl,
  ..submodule.subtype (N : submodule R M) }

@[simp] lemma incl_apply (m : N) : N.incl m = m := rfl

lemma incl_eq_val : (N.incl : N → M) = subtype.val := rfl

variables {N N'} (h : N ≤ N')

/-- Given two nested Lie submodules `N ⊆ N'`, the inclusion `N ↪ N'` is a morphism of Lie modules.-/
def hom_of_le : N →ₗ⁅R,L⁆ N' :=
{ map_lie := λ x m, rfl,
  ..submodule.of_le h }

@[simp] lemma coe_hom_of_le (m : N) : (hom_of_le h m : M) = m := rfl

lemma hom_of_le_apply (m : N) : hom_of_le h m = ⟨m.1, h m.2⟩ := rfl

end inclusion_maps

section lie_span

variables (R L) (s : set M)
/-- The `lie_span` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
def lie_span : lie_submodule R L M := Inf {N | s ⊆ N}

variables {R L s}

lemma mem_lie_span {x : M} : x ∈ lie_span R L s ↔ ∀ N : lie_submodule R L M, s ⊆ N → x ∈ N :=
by { change x ∈ (lie_span R L s : set M) ↔ _, erw Inf_coe, exact mem_bInter_iff, }

lemma subset_lie_span : s ⊆ lie_span R L s :=
by { intros m hm, erw mem_lie_span, intros N hN, exact hN hm, }

lemma submodule_span_le_lie_span : submodule.span R s ≤ lie_span R L s :=
by { rw [submodule.span_le, coe_to_submodule], apply subset_lie_span, }

lemma lie_span_le {N} : lie_span R L s ≤ N ↔ s ⊆ N :=
begin
  split,
  { exact subset.trans subset_lie_span, },
  { intros hs m hm, rw mem_lie_span at hm, exact hm _ hs, },
end

lemma lie_span_mono {t : set M} (h : s ⊆ t) : lie_span R L s ≤ lie_span R L t :=
by { rw lie_span_le, exact subset.trans h subset_lie_span, }

lemma lie_span_eq : lie_span R L (N : set M) = N :=
le_antisymm (lie_span_le.mpr rfl.subset) subset_lie_span

end lie_span

lemma well_founded_of_noetherian [is_noetherian R M] :
  well_founded ((>) : lie_submodule R L M → lie_submodule R L M → Prop) :=
begin
  let f : ((>) : lie_submodule R L M → lie_submodule R L M → Prop) →r
          ((>) : submodule R M → submodule R M → Prop) :=
  { to_fun       := coe,
    map_rel' := λ N N' h, h, },
  apply f.well_founded, rw ← is_noetherian_iff_well_founded, apply_instance,
end

end lattice_structure

section lie_ideal_operations

/-- Given a Lie module `M` over a Lie algebra `L`, the set of Lie ideals of `L` acts on the set
of submodules of `M`. -/
instance : has_bracket (lie_ideal R L) (lie_submodule R L M) :=
⟨λ I N, lie_span R L { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m }⟩

lemma lie_ideal_oper_eq_span :
  ⁅I, N⁆ = lie_span R L { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m } := rfl

lemma lie_ideal_oper_eq_linear_span :
  (↑⁅I, N⁆ : submodule R M) = submodule.span R { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m } :=
begin
  apply le_antisymm,
  { let s := {m : M | ∃ (x : ↥I) (n : ↥N), ⁅(x : L), (n : M)⁆ = m},
    have aux : ∀ (y : L) (m' ∈ submodule.span R s), ⁅y, m'⁆ ∈ submodule.span R s,
    { intros y m' hm', apply submodule.span_induction hm',
      { rintros m'' ⟨x, n, hm''⟩, rw [← hm'', leibniz_lie],
        refine submodule.add_mem _ _ _; apply submodule.subset_span,
        { use [⟨⁅y, ↑x⁆, I.lie_mem x.property⟩, n], refl, },
        { use [x, ⟨⁅y, ↑n⁆, N.lie_mem n.property⟩], refl, }, },
      { simp only [lie_zero, submodule.zero_mem], },
      { intros m₁ m₂ hm₁ hm₂, rw lie_add, exact submodule.add_mem _ hm₁ hm₂, },
      { intros t m'' hm'', rw lie_smul, exact submodule.smul_mem _ t hm'', }, },
    change _ ≤ ↑({ lie_mem := aux, ..submodule.span R s } : lie_submodule R L M),
    rw [coe_submodule_le_coe_submodule, lie_ideal_oper_eq_span, lie_span_le],
    exact submodule.subset_span, },
  { rw lie_ideal_oper_eq_span, apply submodule_span_le_lie_span, },
end

lemma lie_mem_lie (x : I) (m : N) : ⁅(x : L), (m : M)⁆ ∈ ⁅I, N⁆ :=
by { rw lie_ideal_oper_eq_span, apply subset_lie_span, use [x, m], }

lemma lie_comm : ⁅I, J⁆ = ⁅J, I⁆ :=
begin
  suffices : ∀ (I J : lie_ideal R L), ⁅I, J⁆ ≤ ⁅J, I⁆, { exact le_antisymm (this I J) (this J I), },
  clear I J, intros I J,
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros x ⟨y, z, h⟩, rw ← h,
  rw [← lie_skew, ← lie_neg, ← submodule.coe_neg],
  apply lie_mem_lie,
end

lemma lie_le_right : ⁅I, N⁆ ≤ N :=
begin
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨x, n, hn⟩, rw ← hn,
  exact N.lie_mem n.property,
end

lemma lie_le_left : ⁅I, J⁆ ≤ I :=
by { rw lie_comm, exact lie_le_right I J, }

lemma lie_le_inf : ⁅I, J⁆ ≤ I ⊓ J :=
by { rw le_inf_iff, exact ⟨lie_le_left I J, lie_le_right J I⟩, }

@[simp] lemma lie_bot : ⁅I, (⊥ : lie_submodule R L M)⁆ = ⊥ :=
by { rw eq_bot_iff, apply lie_le_right, }

@[simp] lemma bot_lie : ⁅(⊥ : lie_ideal R L), N⁆ = ⊥ :=
begin
  suffices : ⁅(⊥ : lie_ideal R L), N⁆ ≤ ⊥, { exact le_bot_iff.mp this, },
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨⟨x, hx⟩, n, hn⟩, rw ← hn,
  change x ∈ (⊥ : lie_ideal R L) at hx, rw mem_bot at hx, simp [hx],
end

lemma mono_lie (h₁ : I ≤ J) (h₂ : N ≤ N') : ⁅I, N⁆ ≤ ⁅J, N'⁆ :=
begin
  intros m h,
  rw [lie_ideal_oper_eq_span, mem_lie_span] at h, rw [lie_ideal_oper_eq_span, mem_lie_span],
  intros N hN, apply h, rintros m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩, rw ← hm, apply hN,
  use [⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩], refl,
end

lemma mono_lie_left (h : I ≤ J) : ⁅I, N⁆ ≤ ⁅J, N⁆ := mono_lie _ _ _ _ h (le_refl N)

lemma mono_lie_right (h : N ≤ N') : ⁅I, N⁆ ≤ ⁅I, N'⁆ := mono_lie _ _ _ _ (le_refl I) h

@[simp] lemma lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆ :=
begin
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ ≤ ⁅I, N ⊔ N'⁆,
  { rw sup_le_iff, split; apply mono_lie_right; [exact le_sup_left, exact le_sup_right], },
  suffices : ⁅I, N ⊔ N'⁆ ≤ ⁅I, N⁆ ⊔ ⁅I, N'⁆, { exact le_antisymm this h, }, clear h,
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨x, ⟨n, hn⟩, h⟩, erw lie_submodule.mem_sup,
  erw lie_submodule.mem_sup at hn, rcases hn with ⟨n₁, hn₁, n₂, hn₂, hn'⟩,
  use ⁅(x : L), (⟨n₁, hn₁⟩ : N)⁆, split, { apply lie_mem_lie, },
  use ⁅(x : L), (⟨n₂, hn₂⟩ : N')⁆, split, { apply lie_mem_lie, },
  simp [← h, ← hn'],
end

@[simp] lemma sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆ :=
begin
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ ≤ ⁅I ⊔ J, N⁆,
  { rw sup_le_iff, split; apply mono_lie_left; [exact le_sup_left, exact le_sup_right], },
  suffices : ⁅I ⊔ J, N⁆ ≤ ⁅I, N⁆ ⊔ ⁅J, N⁆, { exact le_antisymm this h, }, clear h,
  rw [lie_ideal_oper_eq_span, lie_span_le], rintros m ⟨⟨x, hx⟩, n, h⟩, erw lie_submodule.mem_sup,
  erw lie_submodule.mem_sup at hx, rcases hx with ⟨x₁, hx₁, x₂, hx₂, hx'⟩,
  use ⁅((⟨x₁, hx₁⟩ : I) : L), (n : N)⁆, split, { apply lie_mem_lie, },
  use ⁅((⟨x₂, hx₂⟩ : J) : L), (n : N)⁆, split, { apply lie_mem_lie, },
  simp [← h, ← hx'],
end

@[simp] lemma lie_inf : ⁅I, N ⊓ N'⁆ ≤ ⁅I, N⁆ ⊓ ⁅I, N'⁆ :=
by { rw le_inf_iff, split; apply mono_lie_right; [exact inf_le_left, exact inf_le_right], }

@[simp] lemma inf_lie : ⁅I ⊓ J, N⁆ ≤ ⁅I, N⁆ ⊓ ⁅J, N⁆ :=
by { rw le_inf_iff, split; apply mono_lie_left; [exact inf_le_left, exact inf_le_right], }

@[simp] lemma trivial_lie_oper_zero [lie_module.is_trivial L M] : ⁅I, N⁆ = ⊥ :=
begin
  suffices : ⁅I, N⁆ ≤ ⊥, { exact le_bot_iff.mp this, },
  rw [lie_ideal_oper_eq_span, lie_span_le],
  rintros m ⟨x, n, h⟩, rw trivial_lie_zero at h, simp [← h],
end

end lie_ideal_operations

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
abbreviation quotient := N.to_submodule.quotient

namespace quotient

variables {N I}

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbreviation mk : M → N.quotient := submodule.quotient.mk

lemma is_quotient_mk (m : M) :
  quotient.mk' m = (mk m : N.quotient) := rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant : L →ₗ[R] submodule.compatible_maps N.to_submodule N.to_submodule :=
  linear_map.cod_restrict _ (lie_module.to_endo_morphism R L M) N.lie_mem

variables (N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def action_as_endo_map : L →ₗ⁅R⁆ module.End R N.quotient :=
{ map_lie := λ x y, by { ext n, apply quotient.induction_on' n, intros m,
                         change mk ⁅⁅x, y⁆, m⁆ = mk (⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆),
                         congr, apply lie_lie, },
  ..linear_map.comp (submodule.mapq_linear (N : submodule R M) ↑N) lie_submodule_invariant }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
def action_as_endo_map_bracket : has_bracket L N.quotient := ⟨λ x n, action_as_endo_map N x n⟩

instance lie_quotient_lie_ring_module : lie_ring_module L N.quotient :=
{ bracket     := λ x n, (action_as_endo_map N : L →ₗ[R] module.End R N.quotient) x n,
  add_lie     := λ x y n, by { simp only [linear_map.map_add, linear_map.add_apply], },
  lie_add     := λ x m n, by { simp only [linear_map.map_add, linear_map.add_apply], },
  leibniz_lie := λ x y m, show action_as_endo_map _ _ _ = _,
  { simp only [lie_algebra.map_lie, lie_ring.of_associative_ring_bracket, sub_add_cancel,
      lie_algebra.coe_to_linear_map, linear_map.mul_app, linear_map.sub_apply], } }

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lie_quotient_lie_module : lie_module R L N.quotient :=
{ smul_lie := λ t x m, show (_ : L →ₗ[R] module.End R N.quotient) _ _ = _,
  { simp only [linear_map.map_smul], refl, },
  lie_smul := λ x t m, show (_ : L →ₗ[R] module.End R N.quotient) _ _ = _,
  { simp only [linear_map.map_smul], refl, }, }

instance lie_quotient_has_bracket : has_bracket (quotient I) (quotient I) :=
⟨begin
  intros x y,
  apply quotient.lift_on₂' x y (λ x' y', mk ⁅x', y'⁆),
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  apply (submodule.quotient.eq I.to_submodule).2,
  have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆,
    by simp [-lie_skew, sub_eq_add_neg, add_assoc],
  rw h,
  apply submodule.add_mem,
  { apply lie_mem_right R L I x₁ (x₂ - y₂) h₂, },
  { apply lie_mem_left R L I (x₁ - y₁) y₂ h₁, },
end⟩

@[simp] lemma mk_bracket (x y : L) :
  mk ⁅x, y⁆ = ⁅(mk x : quotient I), (mk y : quotient I)⁆ := rfl

instance lie_quotient_lie_ring : lie_ring (quotient I) :=
{ add_lie  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply add_lie, },
  lie_add  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply lie_add, },
  lie_self := by { intros x', apply quotient.induction_on' x', intros x,
                   rw [is_quotient_mk, ←mk_bracket],
                   apply congr_arg, apply lie_self, },
  leibniz_lie := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply leibniz_lie, } }

instance lie_quotient_lie_algebra : lie_algebra R (quotient I) :=
{ lie_smul := by { intros t x' y', apply quotient.induction_on₂' x' y', intros x y,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_smul, },
                   apply congr_arg, apply lie_smul, } }

end quotient

end lie_submodule

section lie_module

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

namespace lie_algebra

variables (I : lie_ideal R L)

/-- A generalisation of the derived series of a Lie algebra, whose zeroth term is a specified ideal.

It can be more convenient to work with this generalisation when considering the derived series of
an ideal since it provides a type-theoretic expression of the fact that the terms of the ideal's
derived series are also ideals of the enclosing algebra.

See also `lie_ideal.derived_series_eq_derived_series_of_ideal_comap` and
`lie_ideal.derived_series_eq_derived_series_of_ideal_map` below. -/
def derived_series_of_ideal : ℕ → lie_ideal R L
| 0       := I
| (k + 1) := ⁅derived_series_of_ideal k, derived_series_of_ideal k⁆

@[simp] lemma derived_series_of_ideal_zero :
  derived_series_of_ideal R L I 0 = I := rfl

@[simp] lemma derived_series_of_ideal_succ (k : ℕ) :
  derived_series_of_ideal R L I (k + 1) =
  ⁅derived_series_of_ideal R L I k, derived_series_of_ideal R L I k⁆ := rfl

/-- The derived series of Lie ideals of a Lie algebra. -/
abbreviation derived_series : ℕ → lie_ideal R L := derived_series_of_ideal R L ⊤

lemma derived_series_def (k : ℕ) :
  derived_series R L k = derived_series_of_ideal R L ⊤ k := rfl

variables {R L}

local notation `D` := derived_series_of_ideal R L

lemma derived_series_of_ideal_add (k l : ℕ) : D I (k + l) = D (D I l) k :=
begin
  induction k with k ih,
  { rw [zero_add, derived_series_of_ideal_zero], },
  { rw [nat.succ_add k l, derived_series_of_ideal_succ, derived_series_of_ideal_succ, ih], },
end

lemma derived_series_of_ideal_le {I J : lie_ideal R L} {k l : ℕ} (h₁ : I ≤ J) (h₂ : l ≤ k) :
  D I k ≤ D J l :=
begin
  revert l, induction k with k ih; intros l h₂,
  { rw nat.le_zero_iff at h₂, rw [h₂, derived_series_of_ideal_zero], exact h₁, },
  { have h : l = k.succ ∨ l ≤ k, { omega, },
    cases h,
    { rw h, exact lie_submodule.mono_lie _ _ _ _ (ih (le_refl k)) (ih (le_refl k)), },
    { exact le_trans (lie_submodule.lie_le_left _ _) (ih h), }, },
end

lemma derived_series_of_ideal_succ_le (k : ℕ) : D I (k + 1) ≤ D I k :=
derived_series_of_ideal_le (le_refl I) k.le_succ

lemma derived_series_of_ideal_le_self (k : ℕ) : D I k ≤ I :=
derived_series_of_ideal_le (le_refl I) (zero_le k)

lemma derived_series_of_ideal_mono {I J : lie_ideal R L} (h : I ≤ J) (k : ℕ) : D I k ≤ D J k :=
derived_series_of_ideal_le h (le_refl k)

lemma derived_series_of_ideal_antimono {k l : ℕ} (h : l ≤ k) : D I k ≤ D I l :=
derived_series_of_ideal_le (le_refl I) h

end lie_algebra

namespace lie_module

/-- The lower central series of Lie submodules of a Lie module. -/
def lower_central_series : ℕ → lie_submodule R L M
| 0       := ⊤
| (k + 1) := ⁅(⊤ : lie_ideal R L), lower_central_series k⁆

lemma trivial_iff_derived_eq_bot : is_trivial L M ↔ lower_central_series R L M 1 = ⊥ :=
begin
  split; intros h,
  { erw [eq_bot_iff, lie_submodule.lie_span_le], rintros m ⟨x, n, hn⟩, rw [← hn, h.trivial], simp,},
  { rw lie_submodule.eq_bot_iff at h, apply is_trivial.mk, intros x m, apply h,
    apply lie_submodule.subset_lie_span, use [x, m], refl, },
end

open lie_algebra

lemma derived_series_le_lower_central_series (k : ℕ) :
  derived_series R L k ≤ lower_central_series R L L k :=
begin
  induction k with k h,
  { exact le_refl _, },
  { have h' : derived_series R L k ≤ ⊤, { by simp only [le_top], },
    exact lie_submodule.mono_lie _ _ _ _ h' h, },
end

end lie_module

end lie_module

section lie_submodule_map_and_comap

variables {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group M'] [module R M'] [lie_ring_module L M'] [lie_module R L M']

namespace lie_submodule

/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
def map (f : M →ₗ⁅R,L⁆ M') (N : lie_submodule R L M) : lie_submodule R L M' :=
{ lie_mem := λ x m' h, by
  { rcases h with ⟨m, hm, hfm⟩, use ⁅x, m⁆, split,
    { apply N.lie_mem hm, },
    { norm_cast at hfm, simp [hfm], }, },
  ..(N : submodule R M).map (f : M →ₗ[R] M') }

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
def comap (f : M →ₗ⁅R,L⁆ M') (N : lie_submodule R L M') : lie_submodule R L M :=
{ lie_mem := λ x m h, by { suffices : ⁅x, f m⁆ ∈ N, { simp [this], }, apply N.lie_mem h, },
  ..(N : submodule R M').comap (f : M →ₗ[R] M') }

lemma map_le_iff_le_comap {f : M →ₗ⁅R,L⁆ M'} {N : lie_submodule R L M} {N' : lie_submodule R L M'} :
  map f N ≤ N' ↔ N ≤ comap f N' := set.image_subset_iff

lemma gc_map_comap (f : M →ₗ⁅R,L⁆ M') : galois_connection (map f) (comap f) :=
λ N N', map_le_iff_le_comap

end lie_submodule

namespace lie_ideal

variables (f : L →ₗ⁅R⁆ L') (I : lie_ideal R L) (J : lie_ideal R L')

/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `lie_submodule.map`, we must take the `lie_span` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
def map : lie_ideal R L' := lie_submodule.lie_span R L' (f '' I)

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `lie_submodule.comap` but we do not exploit this fact. -/
def comap : lie_ideal R L :=
{ lie_mem := λ x y h, by { suffices : ⁅f x, f y⁆ ∈ J, { simp [this], }, apply J.lie_mem h, },
  ..(J : submodule R L').comap (f : L →ₗ[R] L') }

@[simp] lemma map_coe_submodule (h : ↑(map f I) = f '' I) :
  (map f I : submodule R L') = (I : submodule R L).map f :=
by { rw [submodule.ext'_iff, lie_submodule.coe_to_submodule, h, submodule.map_coe], refl, }

@[simp] lemma comap_coe_submodule : (comap f J : submodule R L) = (J : submodule R L').comap f :=
rfl

lemma map_le : map f I ≤ J ↔ f '' I ⊆ J := lie_submodule.lie_span_le

variables {f I J}

lemma mem_map {x : L} (hx : x ∈ I) : f x ∈ map f I :=
by { apply lie_submodule.subset_lie_span, use x, exact ⟨hx, rfl⟩, }

@[simp] lemma mem_comap {x : L} : x ∈ comap f J ↔ f x ∈ J := iff.rfl

lemma map_le_iff_le_comap : map f I ≤ J ↔ I ≤ comap f J :=
by { rw map_le, exact set.image_subset_iff, }

lemma gc_map_comap : galois_connection (map f) (comap f) :=
λ I I', map_le_iff_le_comap

lemma map_comap_le : map f (comap f J) ≤ J :=
by { rw map_le_iff_le_comap, apply le_refl _, }

/-- See also `map_comap_eq` below. -/
lemma comap_map_le : I ≤ comap f (map f I) :=
by { rw ← map_le_iff_le_comap, apply le_refl _, }

@[mono] lemma map_mono : monotone (map f) :=
λ I₁ I₂ h,
by { rw lie_submodule.le_def at h, apply lie_submodule.lie_span_mono (set.image_subset ⇑f h), }

@[mono] lemma comap_mono : monotone (comap f) :=
λ J₁ J₂ h, by { rw lie_submodule.le_def at h ⊢, exact set.preimage_mono h, }

lemma map_of_image (h : f '' I = J) : I.map f = J :=
begin
  apply le_antisymm,
  { erw [lie_submodule.lie_span_le, h], },
  { rw [lie_submodule.le_def, ← h], exact lie_submodule.subset_lie_span, },
end

end lie_ideal

namespace lie_algebra.morphism

variables (f : L →ₗ⁅R⁆ L') (I : lie_ideal R L) (J : lie_ideal R L')

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : lie_ideal R L := lie_ideal.comap f ⊥

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
def ideal_range : lie_ideal R L' := lie_ideal.map f ⊤

/-- The condition that the image of a morphism of Lie algebras is an ideal. -/
def is_ideal_morphism : Prop := (f.ideal_range : lie_subalgebra R L') = f.range

@[simp] lemma is_ideal_morphism_def :
  f.is_ideal_morphism ↔ (f.ideal_range : lie_subalgebra R L') = f.range := iff.rfl

lemma range_subset_ideal_range : (f.range : set L') ⊆ f.ideal_range := lie_submodule.subset_lie_span

lemma map_le_ideal_range : I.map f ≤ f.ideal_range := lie_ideal.map_mono le_top

lemma ker_le_comap : f.ker ≤ J.comap f := lie_ideal.comap_mono bot_le

@[simp] lemma ker_coe_submodule : (ker f : submodule R L) = (f : L →ₗ[R] L').ker := rfl

@[simp] lemma mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
show x ∈ (f.ker : submodule R L) ↔ _,
by simp only [ker_coe_submodule, linear_map.mem_ker, lie_algebra.coe_to_linear_map]

lemma mem_ideal_range {x : L} : f x ∈ ideal_range f := lie_ideal.mem_map (lie_submodule.mem_top x)

@[simp] lemma mem_ideal_range_iff (h : is_ideal_morphism f) {y : L'} :
  y ∈ ideal_range f ↔ ∃ (x : L), f x = y :=
begin
  rw f.is_ideal_morphism_def at h,
  rw [← lie_submodule.mem_coe, ← lie_ideal.coe_to_subalgebra, h, f.range_coe, set.mem_range],
end

lemma le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 :=
begin
  split; intros h x hx,
  { specialize h hx, rw mem_ker at h, exact h, },
  { rw mem_ker, apply h x hx, },
end

@[simp] lemma map_bot_iff : I.map f = ⊥ ↔ I ≤ f.ker :=
begin
  rw le_ker_iff, unfold lie_ideal.map, split; intros h,
  { rwa [eq_bot_iff, lie_submodule.lie_span_le, set.image_subset_iff, lie_submodule.bot_coe] at h,},
  { suffices : f '' I = ↑(⊥ : lie_ideal R L'), { rw [this, lie_submodule.lie_span_eq], },
    ext x, rw [lie_submodule.bot_coe, set.mem_singleton_iff, set.mem_image],
    split,
    { rintros ⟨y, hy, hx⟩, rw ← hx, exact h y hy, },
    { intros hx, use 0, simp [hx], }, },
end

end lie_algebra.morphism

namespace lie_ideal

variables {f : L →ₗ⁅R⁆ L'} {I : lie_ideal R L} {J : lie_ideal R L'}

lemma map_sup_ker_eq_map : lie_ideal.map f (I ⊔ f.ker) = lie_ideal.map f I :=
begin
  suffices : lie_ideal.map f (I ⊔ f.ker) ≤ lie_ideal.map f I,
  { exact le_antisymm this (lie_ideal.map_mono le_sup_left), },
  apply lie_submodule.lie_span_mono,
  rintros x ⟨y, hy₁, hy₂⟩, rw ← hy₂,
  erw lie_submodule.mem_sup at hy₁, obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁, rw ← hy,
  rw [f.map_add, f.mem_ker.mp hz₂, add_zero], exact ⟨z₁, hz₁, rfl⟩,
end

@[simp] lemma map_comap_eq (h : f.is_ideal_morphism) : map f (comap f J) = f.ideal_range ⊓ J :=
begin
  apply le_antisymm,
  { rw le_inf_iff, exact ⟨f.map_le_ideal_range _, map_comap_le⟩, },
  { rw f.is_ideal_morphism_def at h,
    rw [lie_submodule.le_def, lie_submodule.inf_coe, ← coe_to_subalgebra, h],
    rintros y ⟨⟨x, h₁, h₂⟩, h₃⟩, rw ← h₂ at h₃ ⊢, exact mem_map h₃, },
end

@[simp] lemma comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I ⊔ f.ker :=
by rw [← lie_submodule.coe_to_submodule_eq_iff, comap_coe_submodule, I.map_coe_submodule f h,
  lie_submodule.sup_coe_to_submodule, f.ker_coe_submodule, linear_map.comap_map_eq]

variables (f I J)

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
def incl : I →ₗ⁅R⁆ L := (I : lie_subalgebra R L).incl

@[simp] lemma incl_apply (x : I) : I.incl x = x := rfl

@[simp] lemma incl_coe : (I.incl : I →ₗ[R] L) = (I : submodule R L).subtype := rfl

@[simp] lemma comap_incl_self : comap I.incl I = ⊤ :=
by { rw ← lie_submodule.coe_to_submodule_eq_iff, exact submodule.comap_subtype_self _, }

@[simp] lemma ker_incl : I.incl.ker = ⊥ :=
by rw [← lie_submodule.coe_to_submodule_eq_iff, I.incl.ker_coe_submodule,
  lie_submodule.bot_coe_submodule, incl_coe, submodule.ker_subtype]

@[simp] lemma incl_ideal_range : I.incl.ideal_range = I :=
begin
  apply le_antisymm,
  { erw lie_submodule.lie_span_le, intros x hx,
    simp only [true_and, set.mem_image, incl_apply, set.mem_univ, lie_submodule.top_coe] at hx,
    obtain ⟨y, hy⟩ := hx, rw ← hy, exact y.property, },
  { rw [lie_submodule.le_def, ← lie_ideal.coe_to_subalgebra, ← (I : lie_subalgebra R L).range_incl],
    exact I.incl.range_subset_ideal_range, },
end

lemma incl_is_ideal_morphism : I.incl.is_ideal_morphism :=
begin
  rw [I.incl.is_ideal_morphism_def, incl_ideal_range],
  exact (I : lie_subalgebra R L).range_incl.symm,
end

open lie_algebra

/-- Note that the inequality can be strict; e.g., the inclusion of an Abelian subalgebra of a
simple algebra. -/
lemma map_bracket_le {I₁ I₂ : lie_ideal R L} : map f ⁅I₁, I₂⁆ ≤ ⁅map f I₁, map f I₂⁆ :=
begin
  rw map_le_iff_le_comap, erw lie_submodule.lie_span_le,
  intros x hx, obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx, rw ← hx,
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩,
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩,
  change _ ∈ comap f ⁅map f I₁, map f I₂⁆,
  simp only [submodule.coe_mk, mem_comap, map_lie],
  exact lie_submodule.lie_mem_lie _ _ fy₁ fy₂,
end

lemma comap_bracket_le {J₁ J₂ : lie_ideal R L'} : ⁅comap f J₁, comap f J₂⁆ ≤ comap f ⁅J₁, J₂⁆ :=
begin
  rw ← map_le_iff_le_comap,
  exact le_trans (map_bracket_le f) (lie_submodule.mono_lie _ _ _ _ map_comap_le map_comap_le),
end

variables {f}

lemma map_comap_incl {I₁ I₂ : lie_ideal R L} : map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂ :=
by { conv_rhs { rw ← I₁.incl_ideal_range, }, rw ← map_comap_eq, exact I₁.incl_is_ideal_morphism, }

lemma comap_bracket_eq {J₁ J₂ : lie_ideal R L'} (h : f.is_ideal_morphism) :
  comap f ⁅f.ideal_range ⊓ J₁, f.ideal_range ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker :=
begin
  rw [← lie_submodule.coe_to_submodule_eq_iff, comap_coe_submodule,
    lie_submodule.sup_coe_to_submodule, f.ker_coe_submodule, ← linear_map.comap_map_eq,
    lie_submodule.lie_ideal_oper_eq_linear_span, lie_submodule.lie_ideal_oper_eq_linear_span,
    submodule.map_span],
  congr, simp only [coe_to_linear_map, set.mem_set_of_eq], ext y,
  split,
  { rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hy⟩, rw ← hy,
    erw [lie_submodule.mem_inf, f.mem_ideal_range_iff h] at hx₁ hx₂,
    obtain ⟨⟨z₁, hz₁⟩, hz₁'⟩ := hx₁, rw ← hz₁ at hz₁',
    obtain ⟨⟨z₂, hz₂⟩, hz₂'⟩ := hx₂, rw ← hz₂ at hz₂',
    use [⁅z₁, z₂⁆, ⟨z₁, hz₁'⟩, ⟨z₂, hz₂'⟩, rfl],
    simp only [hz₁, hz₂, submodule.coe_mk, map_lie], },
  { rintros ⟨x, ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩, hx⟩, hy⟩, rw [← hy, ← hx],
    have hz₁' : f z₁ ∈ f.ideal_range ⊓ J₁,
    { rw lie_submodule.mem_inf, exact ⟨f.mem_ideal_range, hz₁⟩, },
    have hz₂' : f z₂ ∈ f.ideal_range ⊓ J₂,
    { rw lie_submodule.mem_inf, exact ⟨f.mem_ideal_range, hz₂⟩, },
    use [⟨f z₁, hz₁'⟩, ⟨f z₂, hz₂'⟩], simp only [submodule.coe_mk, map_lie], },
end

lemma map_comap_bracket_eq {J₁ J₂ : lie_ideal R L'} (h : f.is_ideal_morphism) :
  map f ⁅comap f J₁, comap f J₂⁆ = ⁅f.ideal_range ⊓ J₁, f.ideal_range ⊓ J₂⁆ :=
by { rw [← map_sup_ker_eq_map, ← comap_bracket_eq h, map_comap_eq h, inf_eq_right],
     exact le_trans (lie_submodule.lie_le_left _ _) inf_le_left, }

lemma comap_bracket_incl {I₁ I₂ : lie_ideal R L} :
  ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆ :=
begin
  conv_rhs { congr, skip, rw ← I.incl_ideal_range, }, rw comap_bracket_eq,
  simp only [ker_incl, sup_bot_eq], exact I.incl_is_ideal_morphism,
end

/-- This is a very useful result; it allows us to use the fact that inclusion distributes over the
Lie bracket operation on ideals, subject to the conditions shown. -/
lemma comap_bracket_incl_of_le {I₁ I₂ : lie_ideal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) :
  ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆ :=
by { rw comap_bracket_incl, rw ← inf_eq_right at h₁ h₂, rw [h₁, h₂], }

lemma derived_series_eq_derived_series_of_ideal_comap (k : ℕ) :
  derived_series R I k = (derived_series_of_ideal R L I k).comap I.incl :=
begin
  induction k with k ih,
  { simp only [derived_series_def, comap_incl_self, derived_series_of_ideal_zero], },
  { simp only [derived_series_def, derived_series_of_ideal_succ] at ⊢ ih, rw ih,
    exact comap_bracket_incl_of_le I
      (derived_series_of_ideal_le_self I k) (derived_series_of_ideal_le_self I k), },
end

lemma derived_series_eq_derived_series_of_ideal_map (k : ℕ) :
  (derived_series R I k).map I.incl = derived_series_of_ideal R L I k :=
by { rw [derived_series_eq_derived_series_of_ideal_comap, map_comap_incl, inf_eq_right],
     apply derived_series_of_ideal_le_self, }

lemma derived_series_eq_bot_iff (k : ℕ) :
  derived_series R I k = ⊥ ↔ derived_series_of_ideal R L I k = ⊥ :=
by rw [← derived_series_eq_derived_series_of_ideal_map, I.incl.map_bot_iff, ker_incl, eq_bot_iff]

end lie_ideal

end lie_submodule_map_and_comap

section lie_algebra_properties

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

/-- A Lie module is irreducible if it is zero or its only non-trivial Lie submodule is itself. -/
class lie_module.is_irreducible : Prop :=
(irreducible : ∀ (N : lie_submodule R L M), N ≠ ⊥ → N = ⊤)

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of steps).-/
class lie_module.is_nilpotent : Prop :=
(nilpotent : ∃ k, lie_module.lower_central_series R L M k = ⊥)

@[priority 100]
instance trivial_is_nilpotent [lie_module.is_trivial L M] : lie_module.is_nilpotent R L M :=
⟨by { use 1, change ⁅⊤, ⊤⁆ = ⊥, simp, }⟩

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class lie_algebra.is_simple extends lie_module.is_irreducible R L L : Prop :=
(non_abelian : ¬is_lie_abelian L)

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
class lie_algebra.is_solvable : Prop :=
(solvable : ∃ k, lie_algebra.derived_series R L k = ⊥)

@[priority 100]
instance is_solvable_of_is_nilpotent [hL : lie_module.is_nilpotent R L L] :
  lie_algebra.is_solvable R L :=
begin
  obtain ⟨k, h⟩ : ∃ k, lie_module.lower_central_series R L L k = ⊥ := hL.nilpotent,
  use k, rw ← le_bot_iff at h ⊢,
  exact le_trans (lie_module.derived_series_le_lower_central_series R L k) h,
end

end lie_algebra_properties

namespace linear_equiv

variables {R : Type u} {M₁ : Type v} {M₂ : Type w}
variables [comm_ring R] [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]
variables (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lie_conj : module.End R M₁ ≃ₗ⁅R⁆ module.End R M₂ :=
{ map_lie := λ f g, show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆,
    by simp only [lie_ring.of_associative_ring_bracket, linear_map.mul_eq_comp, e.conj_comp,
                  linear_equiv.map_sub],
  ..e.conj }

@[simp] lemma lie_conj_apply (f : module.End R M₁) : e.lie_conj f = e.conj f := rfl

@[simp] lemma lie_conj_symm : e.lie_conj.symm = e.symm.lie_conj := rfl

end linear_equiv

namespace alg_equiv

variables {R : Type u} {A₁ : Type v} {A₂ : Type w}
variables [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂]
variables (e : A₁ ≃ₐ[R] A₂)

/-- An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
def to_lie_equiv : A₁ ≃ₗ⁅R⁆ A₂ :=
{ to_fun  := e.to_fun,
  map_lie := λ x y, by simp [lie_ring.of_associative_ring_bracket],
  ..e.to_linear_equiv }

@[simp] lemma to_lie_equiv_apply (x : A₁) : e.to_lie_equiv x = e x := rfl

@[simp] lemma to_lie_equiv_symm_apply (x : A₂) : e.to_lie_equiv.symm x = e.symm x := rfl

end alg_equiv

section matrices
open_locale matrix

variables {R : Type u} [comm_ring R]
variables {n : Type w} [decidable_eq n] [fintype n]

/-! ### Matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring.
-/

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lie_equiv_matrix' : module.End R (n → R) ≃ₗ⁅R⁆ matrix n n R :=
{ map_lie := λ T S,
  begin
    let f := @linear_map.to_matrix' R _ n n _ _ _,
    change f (T.comp S - S.comp T) = (f T) * (f S) - (f S) * (f T),
    have h : ∀ (T S : module.End R _), f (T.comp S) = (f T) ⬝ (f S) := linear_map.to_matrix'_comp,
    rw [linear_equiv.map_sub, h, h, matrix.mul_eq_mul, matrix.mul_eq_mul],
  end,
  ..linear_map.to_matrix' }

@[simp] lemma lie_equiv_matrix'_apply (f : module.End R (n → R)) :
  lie_equiv_matrix' f = f.to_matrix' := rfl

@[simp] lemma lie_equiv_matrix'_symm_apply (A : matrix n n R) :
  (@lie_equiv_matrix' R _ n _ _).symm A = A.to_lin' := rfl

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
noncomputable def matrix.lie_conj (P : matrix n n R) (h : is_unit P) :
  matrix n n R ≃ₗ⁅R⁆ matrix n n R :=
((@lie_equiv_matrix' R _ n _ _).symm.trans (P.to_linear_equiv h).lie_conj).trans lie_equiv_matrix'

@[simp] lemma matrix.lie_conj_apply (P A : matrix n n R) (h : is_unit P) :
  P.lie_conj h A = P ⬝ A ⬝ P⁻¹ :=
by simp [linear_equiv.conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

@[simp] lemma matrix.lie_conj_symm_apply (P A : matrix n n R) (h : is_unit P) :
  (P.lie_conj h).symm A = P⁻¹ ⬝ A ⬝ P :=
by simp [linear_equiv.symm_conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types is an equivalence of Lie algebras. -/
def matrix.reindex_lie_equiv {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) : matrix n n R ≃ₗ⁅R⁆ matrix m m R :=
{ map_lie := λ M N, by simp only [lie_ring.of_associative_ring_bracket, matrix.reindex_mul,
    matrix.mul_eq_mul, linear_equiv.map_sub, linear_equiv.to_fun_apply],
..(matrix.reindex_linear_equiv e e) }

@[simp] lemma matrix.reindex_lie_equiv_apply {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) (M : matrix n n R) :
  matrix.reindex_lie_equiv e M = λ i j, M (e.symm i) (e.symm j) :=
rfl

@[simp] lemma matrix.reindex_lie_equiv_symm_apply {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) (M : matrix m m R) :
  (matrix.reindex_lie_equiv e).symm M = λ i j, M (e i) (e j) :=
rfl

end matrices
