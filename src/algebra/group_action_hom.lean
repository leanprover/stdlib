/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.group_ring_action
import group_theory.group_action

/-!
# Equivariant homomorphisms

## Main definitions

* `mul_action_hom M X Y`, the type of equivariant functions from `X` to `Y`, where `M` is a monoid
  that acts on the types `X` and `Y`.
* `distrib_mul_action_hom M A B`, the type of equivariant additive monoid homomorphisms
  from `A` to `B`, where `M` is a monoid that acts on the additive monoids `A` and `B`.
* `mul_semiring_action_hom M R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `M` is a monoid that acts on the rings `R` and `S`.

## Notations

* `X →[M] Y` is `mul_action_hom M X Y`.
* `A →+[M] B` is `distrib_mul_action_hom M X Y`.
* `R →+*[M] S` is `mul_semiring_action_hom M X Y`.

-/

variables (M' : Type*)
variables (X : Type*) [has_scalar M' X]
variables (Y : Type*) [has_scalar M' Y]
variables (Z : Type*) [has_scalar M' Z]
variables (M : Type*) [monoid M]
variables (A : Type*) [add_monoid A] [distrib_mul_action M A]
variables (A' : Type*) [add_group A'] [distrib_mul_action M A']
variables (B : Type*) [add_monoid B] [distrib_mul_action M B]
variables (B' : Type*) [add_group B'] [distrib_mul_action M B']
variables (C : Type*) [add_monoid C] [distrib_mul_action M C]
variables (R : Type*) [semiring R] [mul_semiring_action M R]
variables (R' : Type*) [ring R'] [mul_semiring_action M R']
variables (S : Type*) [semiring S] [mul_semiring_action M S]
variables (S' : Type*) [ring S'] [mul_semiring_action M S']
variables (T : Type*) [semiring T] [mul_semiring_action M T]
variables (G : Type*) [group G] (H : subgroup G)

set_option old_structure_cmd true

/-- Equivariant functions. -/
@[nolint has_inhabited_instance]
structure mul_action_hom :=
(to_fun : X → Y)
(map_smul' : ∀ (m : M') (x : X), to_fun (m • x) = m • to_fun x)

notation X ` →[`:25 M:25 `] `:0 Y:0 := mul_action_hom M X Y

namespace mul_action_hom

instance : has_coe_to_fun (X →[M'] Y) :=
⟨_, λ c, c.to_fun⟩

variables {M M' X Y}

@[simp] lemma map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
f.map_smul' m x

@[ext] theorem ext : ∀ {f g : X →[M'] Y}, (∀ x, f x = g x) → f = g
| ⟨f, _⟩ ⟨g, _⟩ H := by { congr' 1 with x, exact H x }

theorem ext_iff {f g : X →[M'] Y} : f = g ↔ ∀ x, f x = g x :=
⟨λ H x, by rw H, ext⟩

protected lemma congr_fun {f g : X →[M'] Y} (h : f = g) (x : X) : f x = g x := h ▸ rfl

variables (M M') {X}

/-- The identity map as an equivariant map. -/
protected def id : X →[M'] X :=
⟨id, λ _ _, rfl⟩

@[simp] lemma id_apply (x : X) : mul_action_hom.id M' x = x := rfl

variables {M M' X Y Z}

/-- Composition of two equivariant maps. -/
def comp (g : Y →[M'] Z) (f : X →[M'] Y) : X →[M'] Z :=
⟨g ∘ f, λ m x, calc
g (f (m • x)) = g (m • f x) : by rw f.map_smul
          ... = m • g (f x) : g.map_smul _ _⟩

@[simp] lemma comp_apply (g : Y →[M'] Z) (f : X →[M'] Y) (x : X) : g.comp f x = g (f x) := rfl

@[simp] lemma id_comp (f : X →[M'] Y) : (mul_action_hom.id M').comp f = f :=
ext $ λ x, by rw [comp_apply, id_apply]

@[simp] lemma comp_id (f : X →[M'] Y) : f.comp (mul_action_hom.id M') = f :=
ext $ λ x, by rw [comp_apply, id_apply]

variables {A B}

/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps] def inverse (f : A →[M] B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  B →[M] A :=
{ to_fun    := g,
  map_smul' := λ m x,
    calc g (m • x) = g (m • (f (g x))) : by rw h₂
               ... = g (f (m • (g x))) : by rw f.map_smul
               ... = m • g x : by rw h₁, }

variables {G} (H)

/-- The canonical map to the left cosets. -/
def to_quotient : G →[G] quotient_group.quotient H :=
⟨coe, λ g x, rfl⟩

@[simp] lemma to_quotient_apply (g : G) : to_quotient H g = g := rfl

end mul_action_hom

/-- Equivariant additive monoid homomorphisms. -/
structure distrib_mul_action_hom extends A →+ B, A →[M] B.

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc distrib_mul_action_hom.to_add_monoid_hom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc distrib_mul_action_hom.to_mul_action_hom

notation A ` →+[`:25 M:25 `] `:0 B:0 := distrib_mul_action_hom M A B

namespace distrib_mul_action_hom

instance has_coe : has_coe (A →+[M] B) (A →+ B) :=
⟨to_add_monoid_hom⟩

instance has_coe' : has_coe (A →+[M] B) (A →[M] B) :=
⟨to_mul_action_hom⟩

instance : has_coe_to_fun (A →+[M] B) :=
⟨_, to_fun⟩

variables {M A B}

@[simp] lemma to_fun_eq_coe (f : A →+[M] B) : f.to_fun = ⇑f := rfl

@[norm_cast] lemma coe_fn_coe (f : A →+[M] B) : ((f : A →+ B) : A → B) = f := rfl
@[norm_cast] lemma coe_fn_coe' (f : A →+[M] B) : ((f : A →[M] B) : A → B) = f := rfl

@[ext] theorem ext : ∀ {f g : A →+[M] B}, (∀ x, f x = g x) → f = g
| ⟨f, _, _, _⟩ ⟨g, _, _, _⟩ H := by { congr' 1 with x, exact H x }

theorem ext_iff {f g : A →+[M] B} : f = g ↔ ∀ x, f x = g x :=
⟨λ H x, by rw H, ext⟩

protected lemma congr_fun {f g : A →+[M] B} (h : f = g) (x : A) : f x = g x := h ▸ rfl

lemma to_mul_action_hom_injective {f g : A →+[M] B}
  (h : (f : A →[M] B) = (g : A →[M] B)) : f = g :=
by { ext a, exact mul_action_hom.congr_fun h a, }

lemma to_add_monoid_hom_injective {f g : A →+[M] B}
  (h : (f : A →+ B) = (g : A →+ B)) : f = g :=
by { ext a, exact add_monoid_hom.congr_fun h a, }

@[simp] lemma map_zero (f : A →+[M] B) : f 0 = 0 :=
f.map_zero'

@[simp] lemma map_add (f : A →+[M] B) (x y : A) : f (x + y) = f x + f y :=
f.map_add' x y

@[simp] lemma map_neg (f : A' →+[M] B') (x : A') : f (-x) = -f x :=
(f : A' →+ B').map_neg x

@[simp] lemma map_sub (f : A' →+[M] B') (x y : A') : f (x - y) = f x - f y :=
(f : A' →+ B').map_sub x y

@[simp] lemma map_smul (f : A →+[M] B) (m : M) (x : A) : f (m • x) = m • f x :=
f.map_smul' m x

variables (M) {A}

/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id : A →+[M] A :=
{ to_fun := id, .. add_monoid_hom.id _, .. mul_action_hom.id _ }

@[simp] lemma id_apply (x : A) : distrib_mul_action_hom.id M x = x := rfl

variables {M A B C}

instance : has_zero (A →+[M] B) :=
⟨{ map_smul' := by simp,
   .. (0 : A →+ B) }⟩

instance : has_one (A →+[M] A) := ⟨distrib_mul_action_hom.id M⟩

@[simp] lemma coe_zero : ((0 : A →+[M] B) : A → B) = 0 := rfl

@[simp] lemma coe_one : ((1 : A →+[M] A) : A → A) = id := rfl

lemma zero_apply (a : A) : (0 : A →+[M] B) a = 0 := rfl

lemma one_apply (a : A) : (1 : A →+[M] A) a = a := rfl

instance : inhabited (A →+[M] B) := ⟨0⟩

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : B →+[M] C) (f : A →+[M] B) : A →+[M] C :=
{ .. mul_action_hom.comp (g : B →[M] C) (f : A →[M] B),
  .. add_monoid_hom.comp (g : B →+ C) (f : A →+ B), }

@[simp] lemma comp_apply (g : B →+[M] C) (f : A →+[M] B) (x : A) : g.comp f x = g (f x) := rfl

@[simp] lemma id_comp (f : A →+[M] B) : (distrib_mul_action_hom.id M).comp f = f :=
ext $ λ x, by rw [comp_apply, id_apply]

@[simp] lemma comp_id (f : A →+[M] B) : f.comp (distrib_mul_action_hom.id M) = f :=
ext $ λ x, by rw [comp_apply, id_apply]

/-- The inverse of a bijective `distrib_mul_action_hom` is a `distrib_mul_action_hom`. -/
@[simps] def inverse (f : A →+[M] B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  B →+[M] A :=
{ to_fun := g,
  .. (f : A →+ B).inverse g h₁ h₂,
  .. (f : A →[M] B).inverse g h₁ h₂ }

section semiring

variables {R M'} [add_monoid M'] [distrib_mul_action R M']

@[ext] lemma ext_ring
  {f g : R →+[R] M'} (h : f 1 = g 1) : f = g :=
by { ext x, rw [← mul_one x, ← smul_eq_mul R, f.map_smul, g.map_smul, h], }

lemma ext_ring_iff {f g : R →+[R] M'} : f = g ↔ f 1 = g 1 :=
⟨λ h, h ▸ rfl, ext_ring⟩

end semiring

end distrib_mul_action_hom

/-- Equivariant ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure mul_semiring_action_hom extends R →+[M] S, R →+* S.

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc mul_semiring_action_hom.to_ring_hom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc mul_semiring_action_hom.to_distrib_mul_action_hom

notation R ` →+*[`:25 M:25 `] `:0 S:0 := mul_semiring_action_hom M R S

namespace mul_semiring_action_hom

instance has_coe : has_coe (R →+*[M] S) (R →+* S) :=
⟨to_ring_hom⟩

instance has_coe' : has_coe (R →+*[M] S) (R →+[M] S) :=
⟨to_distrib_mul_action_hom⟩

instance : has_coe_to_fun (R →+*[M] S) :=
⟨_, λ c, c.to_fun⟩

variables {M R S}

@[norm_cast] lemma coe_fn_coe (f : R →+*[M] S) : ((f : R →+* S) : R → S) = f := rfl
@[norm_cast] lemma coe_fn_coe' (f : R →+*[M] S) : ((f : R →+[M] S) : R → S) = f := rfl

@[ext] theorem ext : ∀ {f g : R →+*[M] S}, (∀ x, f x = g x) → f = g
| ⟨f, _, _, _, _, _⟩ ⟨g, _, _, _, _, _⟩ H := by { congr' 1 with x, exact H x }

theorem ext_iff {f g : R →+*[M] S} : f = g ↔ ∀ x, f x = g x :=
⟨λ H x, by rw H, ext⟩

@[simp] lemma map_zero (f : R →+*[M] S) : f 0 = 0 :=
f.map_zero'

@[simp] lemma map_add (f : R →+*[M] S) (x y : R) : f (x + y) = f x + f y :=
f.map_add' x y

@[simp] lemma map_neg (f : R' →+*[M] S') (x : R') : f (-x) = -f x :=
(f : R' →+* S').map_neg x

@[simp] lemma map_sub (f : R' →+*[M] S') (x y : R') : f (x - y) = f x - f y :=
(f : R' →+* S').map_sub x y

@[simp] lemma map_one (f : R →+*[M] S) : f 1 = 1 :=
f.map_one'

@[simp] lemma map_mul (f : R →+*[M] S) (x y : R) : f (x * y) = f x * f y :=
f.map_mul' x y

@[simp] lemma map_smul (f : R →+*[M] S) (m : M) (x : R) : f (m • x) = m • f x :=
f.map_smul' m x

variables (M) {R}

/-- The identity map as an equivariant ring homomorphism. -/
protected def id : R →+*[M] R :=
{ to_fun := id, .. distrib_mul_action_hom.id _, .. ring_hom.id _ }

@[simp] lemma id_apply (x : R) : mul_semiring_action_hom.id M x = x := rfl

variables {M R S T}

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : S →+*[M] T) (f : R →+*[M] S) : R →+*[M] T :=
{ .. distrib_mul_action_hom.comp (g : S →+[M] T) (f : R →+[M] S),
  .. ring_hom.comp (g : S →+* T) (f : R →+* S), }

@[simp] lemma comp_apply (g : S →+*[M] T) (f : R →+*[M] S) (x : R) : g.comp f x = g (f x) := rfl

@[simp] lemma id_comp (f : R →+*[M] S) : (mul_semiring_action_hom.id M).comp f = f :=
ext $ λ x, by rw [comp_apply, id_apply]

@[simp] lemma comp_id (f : R →+*[M] S) : f.comp (mul_semiring_action_hom.id M) = f :=
ext $ λ x, by rw [comp_apply, id_apply]

end mul_semiring_action_hom

section
variables (M) {R'} (U : set R') [is_subring U] [is_invariant_subring M U]
local attribute [instance] subset.ring

/-- The canonical inclusion from an invariant subring. -/
def is_invariant_subring.subtype_hom : U →+*[M] R' :=
{ map_smul' := λ m s, rfl, .. is_subring.subtype U }

@[simp] theorem is_invariant_subring.coe_subtype_hom :
  (is_invariant_subring.subtype_hom M U : U → R') = coe := rfl

@[simp] theorem is_invariant_subring.coe_subtype_hom' :
  (is_invariant_subring.subtype_hom M U : U →+* R') = is_subring.subtype U := rfl

end
