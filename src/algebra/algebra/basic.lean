/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import tactic.nth_rewrite
import data.matrix.basic
import data.equiv.ring_aut
import linear_algebra.tensor_product
import ring_theory.subring
import deprecated.subring
import algebra.opposites
import algebra.iterate_hom

/-!
# Algebra over Commutative Semiring

In this file we define `algebra`s over commutative (semi)rings, algebra homomorphisms `alg_hom`,
algebra equivalences `alg_equiv`. We also define usual operations on `alg_hom`s
(`id`, `comp`).

`subalgebra`s are defined in `algebra.algebra.subalgebra`.

If `S` is an `R`-algebra and `A` is an `S`-algebra then `algebra.comap.algebra R S A` can be used
to provide `A` with a structure of an `R`-algebra. Other than that, `algebra.comap` is now
deprecated and replaced with `is_scalar_tower`.

For the category of `R`-algebras, denoted `Algebra R`, see the file
`algebra/category/Algebra/basic.lean`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/

universes u v w u₁ v₁

open_locale tensor_product big_operators

section prio
-- We set this priority to 0 later in this file
set_option extends_priority 200 /- control priority of
`instance [algebra R A] : has_scalar R A` -/

/--
Given a commutative (semi)ring `R`, an `R`-algebra is a (possibly noncommutative)
(semi)ring `A` endowed with a morphism of rings `R →+* A` which lands in the
center of `A`.

For convenience, this typeclass extends `has_scalar R A` where the scalar action must
agree with left multiplication by the image of the structure morphism.

Given an `algebra R A` instance, the structure morphism `R →+* A` is denoted `algebra_map R A`.
-/
@[nolint has_inhabited_instance]
class algebra (R : Type u) (A : Type v) [comm_semiring R] [semiring A]
  extends has_scalar R A, R →+* A :=
(commutes' : ∀ r x, to_fun r * x = x * to_fun r)
(smul_def' : ∀ r x, r • x = to_fun r * x)
end prio

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebra_map (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : R →+* A :=
algebra.to_ring_hom

/-- Creating an algebra from a morphism to the center of a semiring. -/
def ring_hom.to_algebra' {R S} [comm_semiring R] [semiring S] (i : R →+* S)
  (h : ∀ c x, i c * x = x * i c) :
  algebra R S :=
{ smul := λ c x, i c * x,
  commutes' := h,
  smul_def' := λ c x, rfl,
  to_ring_hom := i}

/-- Creating an algebra from a morphism to a commutative semiring. -/
def ring_hom.to_algebra {R S} [comm_semiring R] [comm_semiring S] (i : R →+* S) :
  algebra R S :=
i.to_algebra' $ λ _, mul_comm _

lemma ring_hom.algebra_map_to_algebra {R S} [comm_semiring R] [comm_semiring S]
  (i : R →+* S) :
  @algebra_map R S _ _ i.to_algebra = i :=
rfl

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w} {B : Type*}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`. -/
def of_module' [comm_semiring R] [semiring A] [module R A]
  (h₁ : ∀ (r : R) (x : A), (r • 1) * x = r • x)
  (h₂ : ∀ (r : R) (x : A), x * (r • 1) = r • x) : algebra R A :=
{ to_fun := λ r, r • 1,
  map_one' := one_smul _ _,
  map_mul' := λ r₁ r₂, by rw [h₁, mul_smul],
  map_zero' := zero_smul _ _,
  map_add' := λ r₁ r₂, add_smul r₁ r₂ 1,
  commutes' := λ r x, by simp only [h₁, h₂],
  smul_def' := λ r x, by simp only [h₁] }

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`. -/
def of_module [comm_semiring R] [semiring A] [module R A]
  (h₁ : ∀ (r : R) (x y : A), (r • x) * y = r • (x * y))
  (h₂ : ∀ (r : R) (x y : A), x * (r • y) = r • (x * y)) : algebra R A :=
of_module' (λ r x, by rw [h₁, one_mul]) (λ r x, by rw [h₂, mul_one])

section semiring

variables [comm_semiring R] [comm_semiring S]
variables [semiring A] [algebra R A] [semiring B] [algebra R B]

lemma smul_def'' (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

/--
To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
-- We'll later use this to show `algebra ℤ M` is a subsingleton.
@[ext]
lemma algebra_ext {R : Type*} [comm_semiring R] {A : Type*} [semiring A] (P Q : algebra R A)
  (w : ∀ (r : R), by { haveI := P, exact algebra_map R A r } =
    by { haveI := Q, exact algebra_map R A r }) :
  P = Q :=
begin
  unfreezingI { rcases P with ⟨⟨P⟩⟩, rcases Q with ⟨⟨Q⟩⟩ },
  congr,
  { funext r a,
    replace w := congr_arg (λ s, s * a) (w r),
    simp only [←algebra.smul_def''] at w,
    apply w, },
  { ext r,
    exact w r, },
  { apply proof_irrel_heq, },
  { apply proof_irrel_heq, },
end

@[priority 200] -- see Note [lower instance priority]
instance to_module : module R A :=
{ one_smul := by simp [smul_def''],
  mul_smul := by simp [smul_def'', mul_assoc],
  smul_add := by simp [smul_def'', mul_add],
  smul_zero := by simp [smul_def''],
  add_smul := by simp [smul_def'', add_mul],
  zero_smul := by simp [smul_def''] }

-- from now on, we don't want to use the following instance anymore
attribute [instance, priority 0] algebra.to_has_scalar

lemma smul_def (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

lemma algebra_map_eq_smul_one (r : R) : algebra_map R A r = r • 1 :=
calc algebra_map R A r = algebra_map R A r * 1 : (mul_one _).symm
                   ... = r • 1                 : (algebra.smul_def r 1).symm

lemma algebra_map_eq_smul_one' : ⇑(algebra_map R A) = λ r, r • (1 : A) :=
funext algebra_map_eq_smul_one

/-- `mul_comm` for `algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : algebra_map R A r * x = x * algebra_map R A r :=
algebra.commutes' r x

/-- `mul_left_comm` for `algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) :
  x * (algebra_map R A r * y) = algebra_map R A r * (x * y) :=
by rw [← mul_assoc, ← commutes, mul_assoc]

/-- `mul_right_comm` for `algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) :
  (x * algebra_map R A r) * y = (x * y) * algebra_map R A r :=
by rw [mul_assoc, commutes, ←mul_assoc]

instance _root_.is_scalar_tower.right : is_scalar_tower R A A :=
⟨λ x y z, by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp] protected lemma mul_smul_comm (s : R) (x y : A) :
  x * (s • y) = s • (x * y) :=
-- TODO: set up `is_scalar_tower.smul_comm_class` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.
by rw [smul_def, smul_def, left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp] protected lemma smul_mul_assoc (r : R) (x y : A) :
  (r • x) * y = r • (x * y) :=
smul_mul_assoc r x y

section
variables {r : R} {a : A}

@[simp] lemma bit0_smul_one : bit0 r • (1 : A) = r • 2 :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit0_smul_bit0 : bit0 r • bit0 a = r • (bit0 (bit0 a)) :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit0_smul_bit1 : bit0 r • bit1 a = r • (bit0 (bit1 a)) :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit1_smul_one : bit1 r • (1 : A) = r • 2 + 1 :=
by simp [bit1, add_smul, smul_add]
@[simp] lemma bit1_smul_bit0 : bit1 r • bit0 a = r • (bit0 (bit0 a)) + bit0 a :=
by simp [bit1, add_smul, smul_add]
@[simp] lemma bit1_smul_bit1 : bit1 r • bit1 a = r • (bit0 (bit1 a)) + bit1 a :=
by { simp only [bit0, bit1, add_smul, smul_add, one_smul], abel }

end

variables (R A)

/--
The canonical ring homomorphism `algebra_map R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linear_map : R →ₗ[R] A :=
{ map_smul' := λ x y, by simp [algebra.smul_def],
  ..algebra_map R A }

@[simp]
lemma linear_map_apply (r : R) : algebra.linear_map R A r = algebra_map R A r := rfl

instance id : algebra R R := (ring_hom.id R).to_algebra

variables {R A}

namespace id

@[simp] lemma map_eq_self (x : R) : algebra_map R R x = x := rfl

@[simp] lemma smul_eq_mul (x y : R) : x • y = x * y := rfl

end id

section prod
variables (R A B)

instance : algebra R (A × B) :=
{ commutes' := by { rintro r ⟨a, b⟩, dsimp, rw [commutes r a, commutes r b] },
  smul_def' := by { rintro r ⟨a, b⟩, dsimp, rw [smul_def r a, smul_def r b] },
  .. prod.module,
  .. ring_hom.prod (algebra_map R A) (algebra_map R B) }

variables {R A B}

@[simp] lemma algebra_map_prod_apply (r : R) :
  algebra_map R (A × B) r = (algebra_map R A r, algebra_map R B r) := rfl

end prod

/-- Algebra over a subsemiring. This builds upon `subsemiring.module`. -/
instance of_subsemiring (S : subsemiring R) : algebra S A :=
{ smul := (•),
  commutes' := λ r x, algebra.commutes r x,
  smul_def' := λ r x, algebra.smul_def r x,
  .. (algebra_map R A).comp S.subtype }

/-- Algebra over a subring. This builds upon `subring.module`. -/
instance of_subring {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  (S : subring R) : algebra S A :=
{ smul := (•),
  .. algebra.of_subsemiring S.to_subsemiring,
  .. (algebra_map R A).comp S.subtype }

lemma algebra_map_of_subring {R : Type*} [comm_ring R] (S : subring R) :
  (algebra_map S R : S →+* R) = subring.subtype S := rfl

lemma coe_algebra_map_of_subring {R : Type*} [comm_ring R] (S : subring R) :
  (algebra_map S R : S → R) = subtype.val := rfl

lemma algebra_map_of_subring_apply {R : Type*} [comm_ring R] (S : subring R) (x : S) :
  algebra_map S R x = x := rfl

section
local attribute [instance] subset.comm_ring

/-- Algebra over a set that is closed under the ring operations. -/
local attribute [instance]
def of_is_subring {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  (S : set R) [hS : fact (is_subring S)] : algebra S A :=
algebra.of_subring (set.to_subring hS.elim)

lemma is_subring_coe_algebra_map_hom {R : Type*} [comm_ring R] (S : set R) [fact (is_subring S)] :
  (algebra_map S R : S →+* R) = is_subring.subtype S := rfl

lemma is_subring_coe_algebra_map {R : Type*} [comm_ring R] (S : set R) [fact (is_subring S)] :
  (algebra_map S R : S → R) = subtype.val := rfl

lemma is_subring_algebra_map_apply {R : Type*} [comm_ring R] (S : set R) [fact (is_subring S)]
  (x : S) : algebra_map S R x = x := rfl

lemma set_range_subset {R : Type*} [comm_ring R] {T₁ T₂ : set R} [fact (is_subring T₁)]
  (hyp : T₁ ⊆ T₂) : set.range (algebra_map T₁ R) ⊆ T₂ :=
begin
  rintros x ⟨⟨t, ht⟩, rfl⟩,
  exact hyp ht,
end

end

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebra_map_submonoid (S : Type*) [semiring S] [algebra R S]
  (M : submonoid R) : (submonoid S) :=
submonoid.map (algebra_map R S : R →* S) M

lemma mem_algebra_map_submonoid_of_mem [algebra R S] {M : submonoid R} (x : M) :
  (algebra_map R S x) ∈ algebra_map_submonoid S M :=
set.mem_image_of_mem (algebra_map R S) x.2

end semiring

section ring
variables [comm_ring R]

variables (R)

/-- A `semiring` that is an `algebra` over a commutative ring carries a natural `ring` structure. -/
def semiring_to_ring [semiring A] [algebra R A] : ring A := {
  ..module.add_comm_monoid_to_add_comm_group R,
  ..(infer_instance : semiring A) }

variables {R}

lemma mul_sub_algebra_map_commutes [ring A] [algebra R A] (x : A) (r : R) :
  x * (x - algebra_map R A r) = (x - algebra_map R A r) * x :=
by rw [mul_sub, ←commutes, sub_mul]

lemma mul_sub_algebra_map_pow_commutes [ring A] [algebra R A] (x : A) (r : R) (n : ℕ) :
  x * (x - algebra_map R A r) ^ n = (x - algebra_map R A r) ^ n * x :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ, ←mul_assoc, mul_sub_algebra_map_commutes,
      mul_assoc, ih, ←mul_assoc], }
end

/-- If `algebra_map R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `injective (algebra_map R A)` typeclass.
-/
lemma no_zero_smul_divisors.of_algebra_map_injective
  [semiring A] [algebra R A] [no_zero_divisors A]
  (h : function.injective (algebra_map R A)) : no_zero_smul_divisors R A :=
⟨λ c x hcx, (mul_eq_zero.mp ((smul_def c x).symm.trans hcx)).imp_left
  ((algebra_map R A).injective_iff.mp h _)⟩

end ring

section field

variables [field R] [semiring A] [algebra R A]

@[priority 100] -- see note [lower instance priority]
instance [nontrivial A] [no_zero_divisors A] : no_zero_smul_divisors R A :=
no_zero_smul_divisors.of_algebra_map_injective (algebra_map R A).injective

end field

end algebra

namespace opposite

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

instance : algebra R Aᵒᵖ :=
{ to_ring_hom := (algebra_map R A).to_opposite $ λ x y, algebra.commutes _ _,
  smul_def' := λ c x, unop_injective $
    by { dsimp, simp only [op_mul, algebra.smul_def, algebra.commutes, op_unop] },
  commutes' := λ r, op_induction $ λ x, by dsimp; simp only [← op_mul, algebra.commutes],
  ..opposite.has_scalar A R }

@[simp] lemma algebra_map_apply (c : R) : algebra_map R Aᵒᵖ c = op (algebra_map R A c) := rfl

end opposite

namespace module
variables (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [module R M]

instance endomorphism_algebra : algebra R (M →ₗ[R] M) :=
{ to_fun    := λ r, r • linear_map.id,
  map_one' := one_smul _ _,
  map_zero' := zero_smul _ _,
  map_add' := λ r₁ r₂, add_smul _ _ _,
  map_mul' := λ r₁ r₂, by { ext x, simp [mul_smul] },
  commutes' := by { intros, ext, simp },
  smul_def' := by { intros, ext, simp } }

lemma algebra_map_End_eq_smul_id (a : R) :
  (algebra_map R (End R M)) a = a • linear_map.id := rfl

@[simp] lemma algebra_map_End_apply (a : R) (m : M) :
  (algebra_map R (End R M)) a m = a • m := rfl

@[simp] lemma ker_algebra_map_End (K : Type u) (V : Type v)
  [field K] [add_comm_group V] [module K V] (a : K) (ha : a ≠ 0) :
  ((algebra_map K (End K V)) a).ker = ⊥ :=
linear_map.ker_smul _ _ ha

end module

instance matrix_algebra (n : Type u) (R : Type v)
  [decidable_eq n] [fintype n] [comm_semiring R] : algebra R (matrix n n R) :=
{ commutes' := by { intros, simp [matrix.scalar], },
  smul_def' := by { intros, simp [matrix.scalar], },
  ..(matrix.scalar n) }

@[simp] lemma matrix.algebra_map_eq_smul (n : Type u) {R : Type v} [decidable_eq n] [fintype n]
  [comm_semiring R] (r : R) : (algebra_map R (matrix n n R)) r = r • 1 := rfl

set_option old_structure_cmd true
/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_inhabited_instance]
structure alg_hom (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] extends ring_hom A B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

run_cmd tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

infixr ` →ₐ `:25 := alg_hom _
notation A ` →ₐ[`:25 R `] ` B := alg_hom R A B

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section semiring

variables [comm_semiring R] [semiring A] [semiring B] [semiring C] [semiring D]
variables [algebra R A] [algebra R B] [algebra R C] [algebra R D]

instance : has_coe_to_fun (A →ₐ[R] B) := ⟨_, λ f, f.to_fun⟩

initialize_simps_projections alg_hom (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : A →ₐ[R] B) : f.to_fun = f := rfl

instance coe_ring_hom : has_coe (A →ₐ[R] B) (A →+* B) := ⟨alg_hom.to_ring_hom⟩

instance coe_monoid_hom : has_coe (A →ₐ[R] B) (A →* B) := ⟨λ f, ↑(f : A →+* B)⟩

instance coe_add_monoid_hom : has_coe (A →ₐ[R] B) (A →+ B) := ⟨λ f, ↑(f : A →+* B)⟩

@[simp, norm_cast] lemma coe_mk {f : A → B} (h₁ h₂ h₃ h₄ h₅) :
  ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f := rfl

-- make the coercion the simp-normal form
@[simp] lemma to_ring_hom_eq_coe (f : A →ₐ[R] B) : f.to_ring_hom = f := rfl

@[simp, norm_cast] lemma coe_to_ring_hom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f := rfl

-- as `simp` can already prove this lemma, it is not tagged with the `simp` attribute.
@[norm_cast] lemma coe_to_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f := rfl

-- as `simp` can already prove this lemma, it is not tagged with the `simp` attribute.
@[norm_cast] lemma coe_to_add_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f := rfl

variables (φ : A →ₐ[R] B)

theorem coe_fn_inj ⦃φ₁ φ₂ : A →ₐ[R] B⦄ (H : ⇑φ₁ = φ₂) : φ₁ = φ₂ :=
by { cases φ₁, cases φ₂, congr, exact H }

theorem coe_ring_hom_injective : function.injective (coe : (A →ₐ[R] B) → (A →+* B)) :=
λ φ₁ φ₂ H, coe_fn_inj $ show ((φ₁ : (A →+* B)) : A → B) = ((φ₂ : (A →+* B)) : A → B),
  from congr_arg _ H

theorem coe_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →* B)) :=
ring_hom.coe_monoid_hom_injective.comp coe_ring_hom_injective

theorem coe_add_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →+ B)) :=
ring_hom.coe_add_monoid_hom_injective.comp coe_ring_hom_injective

protected lemma congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x := H ▸ rfl
protected lemma congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y := h ▸ rfl

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
coe_fn_inj $ funext H

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
⟨alg_hom.congr_fun, ext⟩

@[simp] theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) :
  (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f := ext $ λ _, rfl

@[simp]
theorem commutes (r : R) : φ (algebra_map R A r) = algebra_map R B r := φ.commutes' r

theorem comp_algebra_map : (φ : A →+* B).comp (algebra_map R A) = algebra_map R B :=
ring_hom.ext $ φ.commutes

@[simp] lemma map_add (r s : A) : φ (r + s) = φ r + φ s :=
φ.to_ring_hom.map_add r s

@[simp] lemma map_zero : φ 0 = 0 :=
φ.to_ring_hom.map_zero

@[simp] lemma map_mul (x y) : φ (x * y) = φ x * φ y :=
φ.to_ring_hom.map_mul x y

@[simp] lemma map_one : φ 1 = 1 :=
φ.to_ring_hom.map_one

@[simp] lemma map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
by simp only [algebra.smul_def, map_mul, commutes]

@[simp] lemma map_pow (x : A) (n : ℕ) : φ (x ^ n) = (φ x) ^ n :=
φ.to_ring_hom.map_pow x n

lemma map_sum {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∑ x in s, f x) = ∑ x in s, φ (f x) :=
φ.to_ring_hom.map_sum f s

lemma map_finsupp_sum {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.sum g) = f.sum (λ i a, φ (g i a)) :=
φ.map_sum _ _

@[simp] lemma map_nat_cast (n : ℕ) : φ n = n :=
φ.to_ring_hom.map_nat_cast n

@[simp] lemma map_bit0 (x) : φ (bit0 x) = bit0 (φ x) :=
φ.to_ring_hom.map_bit0 x

@[simp] lemma map_bit1 (x) : φ (bit1 x) = bit1 (φ x) :=
φ.to_ring_hom.map_bit1 x

/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : A →ₐ[R] B :=
{ to_fun := f,
  commutes' := λ c, by simp only [algebra.algebra_map_eq_smul_one, h, f.map_one],
  .. f }

@[simp] lemma coe_mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : ⇑(mk' f h) = f := rfl

section

variables (R A)
/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
{ commutes' := λ _, rfl,
  ..ring_hom.id A  }

@[simp] lemma coe_id : ⇑(alg_hom.id R A) = id := rfl

@[simp] lemma id_to_ring_hom : (alg_hom.id R A : A →+* A) = ring_hom.id _ := rfl

end

lemma id_apply (p : A) : alg_hom.id R A p = p := rfl

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
{ commutes' := λ r : R, by rw [← φ₁.commutes, ← φ₂.commutes]; refl,
  .. φ₁.to_ring_hom.comp ↑φ₂ }

@[simp] lemma coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

lemma comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

lemma comp_to_ring_hom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
  ⇑(φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ := rfl

@[simp] theorem comp_id : φ.comp (alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp : (alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

/-- R-Alg ⥤ R-Mod -/
def to_linear_map : A →ₗ B :=
{ to_fun := φ,
  map_add' := φ.map_add,
  map_smul' := φ.map_smul }

@[simp] lemma to_linear_map_apply (p : A) : φ.to_linear_map p = φ p := rfl

theorem to_linear_map_injective : function.injective (to_linear_map : _ → (A →ₗ[R] B)) :=
λ φ₁ φ₂ h, ext $ linear_map.congr_fun h

@[simp] lemma comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

@[simp] lemma to_linear_map_id : to_linear_map (alg_hom.id R A) = linear_map.id :=
linear_map.ext $ λ _, rfl

/-- Promote a `linear_map` to an `alg_hom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def of_linear_map (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
  A →ₐ[R] B :=
{ to_fun := f,
  map_one' := map_one,
  map_mul' := map_mul,
  commutes' := λ c, by simp only [algebra.algebra_map_eq_smul_one, f.map_smul, map_one],
  .. f.to_add_monoid_hom }

@[simp] lemma of_linear_map_to_linear_map (map_one) (map_mul) :
  of_linear_map φ.to_linear_map map_one map_mul = φ :=
by { ext, refl }

@[simp] lemma to_linear_map_of_linear_map (f : A →ₗ[R] B) (map_one) (map_mul) :
  to_linear_map (of_linear_map f map_one map_mul) = f :=
by { ext, refl }

@[simp] lemma of_linear_map_id (map_one) (map_mul) :
  of_linear_map linear_map.id map_one map_mul = alg_hom.id R A :=
ext $ λ _, rfl

lemma map_list_prod (s : list A) :
  φ s.prod = (s.map φ).prod :=
φ.to_ring_hom.map_list_prod s

section prod

/-- First projection as `alg_hom`. -/
def fst : A × B →ₐ[R] A :=
{ commutes' := λ r, rfl, .. ring_hom.fst A B}

/-- Second projection as `alg_hom`. -/
def snd : A × B →ₐ[R] B :=
{ commutes' := λ r, rfl, .. ring_hom.snd A B}

end prod

end semiring

section comm_semiring

variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra R B] (φ : A →ₐ[R] B)

lemma map_multiset_prod (s : multiset A) :
  φ s.prod = (s.map φ).prod :=
φ.to_ring_hom.map_multiset_prod s

lemma map_prod {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
φ.to_ring_hom.map_prod f s

lemma map_finsupp_prod {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.prod g) = f.prod (λ i a, φ (g i a)) :=
φ.map_prod _ _

end comm_semiring

section ring

variables [comm_semiring R] [ring A] [ring B]
variables [algebra R A] [algebra R B] (φ : A →ₐ[R] B)

@[simp] lemma map_neg (x) : φ (-x) = -φ x :=
φ.to_ring_hom.map_neg x

@[simp] lemma map_sub (x y) : φ (x - y) = φ x - φ y :=
φ.to_ring_hom.map_sub x y

@[simp] lemma map_int_cast (n : ℤ) : φ n = n :=
φ.to_ring_hom.map_int_cast n

end ring

section division_ring

variables [comm_ring R] [division_ring A] [division_ring B]
variables [algebra R A] [algebra R B] (φ : A →ₐ[R] B)

@[simp] lemma map_inv (x) : φ (x⁻¹) = (φ x)⁻¹ :=
φ.to_ring_hom.map_inv x

@[simp] lemma map_div (x y) : φ (x / y) = φ x / φ y :=
φ.to_ring_hom.map_div x y

end division_ring

theorem injective_iff {R A B : Type*} [comm_semiring R] [ring A] [semiring B]
  [algebra R A] [algebra R B] (f : A →ₐ[R] B) :
  function.injective f ↔ (∀ x, f x = 0 → x = 0) :=
ring_hom.injective_iff (f : A →+* B)

end alg_hom

@[simp] lemma rat.smul_one_eq_coe {A : Type*} [division_ring A] [algebra ℚ A] (m : ℚ) :
  m • (1 : A) = ↑m :=
by rw [algebra.smul_def, mul_one, ring_hom.eq_rat_cast]

set_option old_structure_cmd true
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure alg_equiv (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

attribute [nolint doc_blame] alg_equiv.to_ring_equiv
attribute [nolint doc_blame] alg_equiv.to_equiv
attribute [nolint doc_blame] alg_equiv.to_add_equiv
attribute [nolint doc_blame] alg_equiv.to_mul_equiv

notation A ` ≃ₐ[`:50 R `] ` A' := alg_equiv R A A'

namespace alg_equiv

variables {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁}

section semiring

variables [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃]
variables [algebra R A₁] [algebra R A₂] [algebra R A₃]
variables (e : A₁ ≃ₐ[R] A₂)

instance : has_coe_to_fun (A₁ ≃ₐ[R] A₂) := ⟨_, alg_equiv.to_fun⟩

@[ext]
lemma ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
begin
  have h₁ : f.to_equiv = g.to_equiv := equiv.ext h,
  cases f, cases g, congr,
  { exact (funext h) },
  { exact congr_arg equiv.inv_fun h₁ }
end

protected lemma congr_arg {f : A₁ ≃ₐ[R] A₂} : Π {x x' : A₁}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x := h ▸ rfl

lemma ext_iff {f g : A₁ ≃ₐ[R] A₂} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, ext⟩

lemma coe_fun_injective : @function.injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) (λ e, (e : A₁ → A₂)) :=
begin
  intros f g w,
  ext,
  exact congr_fun w a,
end

instance has_coe_to_ring_equiv : has_coe (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) := ⟨alg_equiv.to_ring_equiv⟩

@[simp] lemma coe_mk {to_fun inv_fun left_inv right_inv map_mul map_add commutes} :
  ⇑(⟨to_fun, inv_fun, left_inv, right_inv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = to_fun :=
rfl

@[simp] theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
  (⟨e, e', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e := ext $ λ _, rfl

@[simp] lemma to_fun_eq_coe (e : A₁ ≃ₐ[R] A₂) : e.to_fun = e := rfl

-- TODO: decide on a simp-normal form so that only one of these two lemmas is needed
@[simp, norm_cast] lemma coe_ring_equiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e := rfl
@[simp] lemma coe_ring_equiv' : (e.to_ring_equiv : A₁ → A₂) = e := rfl

lemma coe_ring_equiv_injective : function.injective (coe : (A₁ ≃ₐ[R] A₂) → (A₁ ≃+* A₂)) :=
λ e₁ e₂ h, ext $ ring_equiv.congr_fun h

@[simp] lemma map_add : ∀ x y, e (x + y) = e x + e y := e.to_add_equiv.map_add

@[simp] lemma map_zero : e 0 = 0 := e.to_add_equiv.map_zero

@[simp] lemma map_mul : ∀ x y, e (x * y) = (e x) * (e y) := e.to_mul_equiv.map_mul

@[simp] lemma map_one : e 1 = 1 := e.to_mul_equiv.map_one

@[simp] lemma commutes : ∀ (r : R), e (algebra_map R A₁ r) = algebra_map R A₂ r :=
  e.commutes'

lemma map_sum {ι : Type*} (f : ι → A₁) (s : finset ι) :
  e (∑ x in s, f x) = ∑ x in s, e (f x) :=
e.to_add_equiv.map_sum f s

lemma map_finsupp_sum {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.sum g) = f.sum (λ i b, e (g i b)) :=
e.map_sum _ _

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to_*_hom` projections.
The `simp` normal form is to use the coercion of the `has_coe_to_alg_hom` instance. -/
def to_alg_hom : A₁ →ₐ[R] A₂ :=
{ map_one' := e.map_one, map_zero' := e.map_zero, ..e }

instance has_coe_to_alg_hom : has_coe (A₁ ≃ₐ[R] A₂) (A₁ →ₐ[R] A₂) :=
⟨to_alg_hom⟩

@[simp] lemma to_alg_hom_eq_coe : e.to_alg_hom = e := rfl

@[simp, norm_cast] lemma coe_alg_hom : ((e : A₁ →ₐ[R] A₂) : A₁ → A₂) = e :=
rfl

lemma coe_alg_hom_injective : function.injective (coe : (A₁ ≃ₐ[R] A₂) → (A₁ →ₐ[R] A₂)) :=
λ e₁ e₂ h, ext $ alg_hom.congr_fun h

/-- The two paths coercion can take to a `ring_hom` are equivalent -/
lemma coe_ring_hom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
rfl

@[simp] lemma map_pow : ∀ (x : A₁) (n : ℕ), e (x ^ n) = (e x) ^ n := e.to_alg_hom.map_pow

lemma injective : function.injective e := e.to_equiv.injective

lemma surjective : function.surjective e := e.to_equiv.surjective

lemma bijective : function.bijective e := e.to_equiv.bijective

instance : has_one (A₁ ≃ₐ[R] A₁) := ⟨{commutes' := λ r, rfl, ..(1 : A₁ ≃+* A₁)}⟩

instance : inhabited (A₁ ≃ₐ[R] A₁) := ⟨1⟩

/-- Algebra equivalences are reflexive. -/
@[refl]
def refl : A₁ ≃ₐ[R] A₁ := 1

@[simp] lemma refl_to_alg_hom : ↑(refl : A₁ ≃ₐ[R] A₁) = alg_hom.id R A₁ := rfl

@[simp] lemma coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id := rfl

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
{ commutes' := λ r, by { rw ←e.to_ring_equiv.symm_apply_apply (algebra_map R A₁ r), congr,
                         change _ = e _, rw e.commutes, },
  ..e.to_ring_equiv.symm, }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ := e.symm

initialize_simps_projections alg_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma inv_fun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.inv_fun = e.symm := rfl

@[simp] lemma symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e :=
by { ext, refl, }

lemma symm_bijective : function.bijective (symm : (A₁ ≃ₐ[R] A₂) → (A₂ ≃ₐ[R] A₁)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
  (⟨f, e, h₁, h₂, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
  (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
  { to_fun := f', inv_fun := f,
    ..(⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm } := rfl

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
{ commutes' := λ r, show e₂.to_fun (e₁.to_fun _) = _, by rw [e₁.commutes', e₂.commutes'],
  ..(e₁.to_ring_equiv.trans e₂.to_ring_equiv), }

@[simp] lemma apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.to_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.to_equiv.symm_apply_apply

@[simp] lemma coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

lemma trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma comp_symm (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = alg_hom.id R A₂ :=
by { ext, simp }

@[simp] lemma symm_comp (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = alg_hom.id R A₁ :=
by { ext, simp }

theorem left_inverse_symm (e : A₁ ≃ₐ[R] A₂) : function.left_inverse e.symm e := e.left_inv

theorem right_inverse_symm (e : A₁ ≃ₐ[R] A₂) : function.right_inverse e.symm e := e.right_inv

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
def arrow_congr {A₁' A₂' : Type*} [semiring A₁'] [semiring A₂'] [algebra R A₁'] [algebra R A₂']
  (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') :=
{ to_fun := λ f, (e₂.to_alg_hom.comp f).comp e₁.symm.to_alg_hom,
  inv_fun := λ f, (e₂.symm.to_alg_hom.comp f).comp e₁.to_alg_hom,
  left_inv := λ f, by { simp only [alg_hom.comp_assoc, to_alg_hom_eq_coe, symm_comp],
    simp only [←alg_hom.comp_assoc, symm_comp, alg_hom.id_comp, alg_hom.comp_id] },
  right_inv := λ f, by { simp only [alg_hom.comp_assoc, to_alg_hom_eq_coe, comp_symm],
    simp only [←alg_hom.comp_assoc, comp_symm, alg_hom.id_comp, alg_hom.comp_id] } }

lemma arrow_congr_comp {A₁' A₂' A₃' : Type*} [semiring A₁'] [semiring A₂'] [semiring A₃']
  [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₃) :
  arrow_congr e₁ e₃ (g.comp f) = (arrow_congr e₂ e₃ g).comp (arrow_congr e₁ e₂ f) :=
by { ext, simp only [arrow_congr, equiv.coe_fn_mk, alg_hom.comp_apply],
  congr, exact (e₂.symm_apply_apply _).symm }

@[simp] lemma arrow_congr_refl :
  arrow_congr alg_equiv.refl alg_equiv.refl = equiv.refl (A₁ →ₐ[R] A₂) :=
by { ext, refl }

@[simp] lemma arrow_congr_trans {A₁' A₂' A₃' : Type*} [semiring A₁'] [semiring A₂'] [semiring A₃']
  [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
  (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
  arrow_congr (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr e₁ e₁').trans (arrow_congr e₂ e₂') :=
by { ext, refl }

@[simp] lemma arrow_congr_symm {A₁' A₂' : Type*} [semiring A₁'] [semiring A₂']
  [algebra R A₁'] [algebra R A₂'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
  (arrow_congr e₁ e₂).symm = arrow_congr e₁.symm e₂.symm :=
by { ext, refl }

/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = alg_hom.id R A₂)
  (h₂ : g.comp f = alg_hom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
{ to_fun    := f,
  inv_fun   := g,
  left_inv  := alg_hom.ext_iff.1 h₂,
  right_inv := alg_hom.ext_iff.1 h₁,
  ..f }

lemma coe_alg_hom_of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  ↑(of_alg_hom f g h₁ h₂) = f := alg_hom.ext $ λ _, rfl

@[simp]
lemma of_alg_hom_coe_alg_hom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  of_alg_hom ↑f g h₁ h₂ = f := ext $ λ _, rfl

lemma of_alg_hom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  (of_alg_hom f g h₁ h₂).symm = of_alg_hom g f h₂ h₁ := rfl

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def of_bijective (f : A₁ →ₐ[R] A₂) (hf : function.bijective f) : A₁ ≃ₐ[R] A₂ :=
{ .. ring_equiv.of_bijective (f : A₁ →+* A₂) hf, .. f }

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply] def to_linear_equiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
{ to_fun    := e,
  map_smul' := λ r x, by simp [algebra.smul_def''],
  inv_fun   := e.symm,
  .. e }

@[simp] lemma to_linear_equiv_refl :
  (alg_equiv.refl : A₁ ≃ₐ[R] A₁).to_linear_equiv = linear_equiv.refl R A₁ := rfl

@[simp] lemma to_linear_equiv_symm (e : A₁ ≃ₐ[R] A₂) :
  e.to_linear_equiv.symm = e.symm.to_linear_equiv := rfl

@[simp] lemma to_linear_equiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  (e₁.trans e₂).to_linear_equiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv := rfl

theorem to_linear_equiv_injective : function.injective (to_linear_equiv : _ → (A₁ ≃ₗ[R] A₂)) :=
λ e₁ e₂ h, ext $ linear_equiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def to_linear_map : A₁ →ₗ[R] A₂ :=
e.to_alg_hom.to_linear_map

@[simp] lemma to_alg_hom_to_linear_map :
  (e : A₁ →ₐ[R] A₂).to_linear_map = e.to_linear_map := rfl

@[simp] lemma to_linear_equiv_to_linear_map :
  e.to_linear_equiv.to_linear_map = e.to_linear_map := rfl

@[simp] lemma to_linear_map_apply (x : A₁) : e.to_linear_map x = e x := rfl

theorem to_linear_map_injective : function.injective (to_linear_map : _ → (A₁ →ₗ[R] A₂)) :=
λ e₁ e₂ h, ext $ linear_map.congr_fun h

@[simp] lemma trans_to_linear_map (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
  (f.trans g).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

section of_linear_equiv

variables (l : A₁ ≃ₗ[R] A₂)
  (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)
  (commutes : ∀ r : R, l (algebra_map R A₁ r) = algebra_map R A₂ r)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and action of scalars.
-/
@[simps apply]
def of_linear_equiv : A₁ ≃ₐ[R] A₂ :=
{ to_fun := l,
  inv_fun := l.symm,
  map_mul' := map_mul,
  commutes' := commutes,
  ..l }

@[simp]
lemma of_linear_equiv_symm :
  (of_linear_equiv l map_mul commutes).symm = of_linear_equiv l.symm
    ((of_linear_equiv l map_mul commutes).symm.map_mul)
    ((of_linear_equiv l map_mul commutes).symm.commutes) :=
rfl

@[simp] lemma of_linear_equiv_to_linear_equiv (map_mul) (commutes) :
  of_linear_equiv e.to_linear_equiv map_mul commutes = e :=
by { ext, refl }

@[simp] lemma to_linear_equiv_of_linear_equiv :
  to_linear_equiv (of_linear_equiv l map_mul commutes) = l :=
by { ext, refl }

end of_linear_equiv

instance aut : group (A₁ ≃ₐ[R] A₁) :=
{ mul := λ ϕ ψ, ψ.trans ϕ,
  mul_assoc := λ ϕ ψ χ, rfl,
  one := 1,
  one_mul := λ ϕ, by { ext, refl },
  mul_one := λ ϕ, by { ext, refl },
  inv := symm,
  mul_left_inv := λ ϕ, by { ext, exact symm_apply_apply ϕ a } }

@[simp] lemma mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

/-- An algebra isomorphism induces a group isomorphism between automorphism groups -/
@[simps apply]
def aut_congr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* (A₂ ≃ₐ[R] A₂) :=
{ to_fun := λ ψ, ϕ.symm.trans (ψ.trans ϕ),
  inv_fun := λ ψ, ϕ.trans (ψ.trans ϕ.symm),
  left_inv := λ ψ, by { ext, simp_rw [trans_apply, symm_apply_apply] },
  right_inv := λ ψ, by { ext, simp_rw [trans_apply, apply_symm_apply] },
  map_mul' := λ ψ χ, by { ext, simp only [mul_apply, trans_apply, symm_apply_apply] } }

@[simp] lemma aut_congr_refl : aut_congr (alg_equiv.refl) = mul_equiv.refl (A₁ ≃ₐ[R] A₁) :=
by { ext, refl }

@[simp] lemma aut_congr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (aut_congr ϕ).symm = aut_congr ϕ.symm := rfl

@[simp] lemma aut_congr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
  (aut_congr ϕ).trans (aut_congr ψ) = aut_congr (ϕ.trans ψ) := rfl

end semiring

section comm_semiring

variables [comm_semiring R] [comm_semiring A₁] [comm_semiring A₂]
variables [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

lemma map_prod {ι : Type*} (f : ι → A₁) (s : finset ι) :
  e (∏ x in s, f x) = ∏ x in s, e (f x) :=
e.to_alg_hom.map_prod f s

lemma map_finsupp_prod {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.prod g) = f.prod (λ i a, e (g i a)) :=
e.to_alg_hom.map_finsupp_prod f g

end comm_semiring

section ring

variables [comm_ring R] [ring A₁] [ring A₂]
variables [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

@[simp] lemma map_neg (x) : e (-x) = -e x :=
e.to_alg_hom.map_neg x

@[simp] lemma map_sub (x y) : e (x - y) = e x - e y :=
e.to_alg_hom.map_sub x y

end ring

section division_ring

variables [comm_ring R] [division_ring A₁] [division_ring A₂]
variables [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

@[simp] lemma map_inv (x) : e (x⁻¹) = (e x)⁻¹ :=
e.to_alg_hom.map_inv x

@[simp] lemma map_div (x y) : e (x / y) = e x / e y :=
e.to_alg_hom.map_div x y

end division_ring

end alg_equiv

namespace matrix

/-! ### `matrix` section

Specialize `matrix.one_map` and `matrix.zero_map` to `alg_hom` and `alg_equiv`.
TODO: there should be a way to avoid restating these for each `foo_hom`.
-/

variables {R A₁ A₂ n : Type*} [fintype n]

section semiring

variables [comm_semiring R] [semiring A₁] [algebra R A₁] [semiring A₂] [algebra R A₂]

/-- A version of `matrix.one_map` where `f` is an `alg_hom`. -/
@[simp] lemma alg_hom_map_one [decidable_eq n]
  (f : A₁ →ₐ[R] A₂) : (1 : matrix n n A₁).map f = 1 :=
one_map f.map_zero f.map_one

/-- A version of `matrix.one_map` where `f` is an `alg_equiv`. -/
@[simp] lemma alg_equiv_map_one [decidable_eq n]
  (f : A₁ ≃ₐ[R] A₂) : (1 : matrix n n A₁).map f = 1 :=
one_map f.map_zero f.map_one

/-- A version of `matrix.zero_map` where `f` is an `alg_hom`. -/
@[simp] lemma alg_hom_map_zero
  (f : A₁ →ₐ[R] A₂) : (0 : matrix n n A₁).map f = 0 :=
map_zero f.map_zero

/-- A version of `matrix.zero_map` where `f` is an `alg_equiv`. -/
@[simp] lemma alg_equiv_map_zero
  (f : A₁ ≃ₐ[R] A₂) : (0 : matrix n n A₁).map f = 0 :=
map_zero f.map_zero

end semiring

end matrix

section nat

variables {R : Type*} [semiring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℕ`-algebras. This is only an issue since `algebra.id` and `algebra_nat` are not yet defeq.
-- TODO: fix this by adding an `of_nat` field to semirings.
/-- Semiring ⥤ ℕ-Alg -/
@[priority 99] instance algebra_nat : algebra ℕ R :=
{ commutes' := nat.cast_commute,
  smul_def' := λ _ _, nsmul_eq_mul _ _,
  to_ring_hom := nat.cast_ring_hom R }

instance nat_algebra_subsingleton : subsingleton (algebra ℕ R) :=
⟨λ P Q, by { ext, simp, }⟩

end nat

namespace ring_hom

variables {R S : Type*}

/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def to_nat_alg_hom [semiring R] [semiring S] (f : R →+* S) :
  R →ₐ[ℕ] S :=
{ to_fun := f, commutes' := λ n, by simp, .. f }

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def to_int_alg_hom [ring R] [ring S] [algebra ℤ R] [algebra ℤ S] (f : R →+* S) :
  R →ₐ[ℤ] S :=
{ commutes' := λ n, by simp, .. f }

@[simp] lemma map_rat_algebra_map [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] (f : R →+* S)
  (r : ℚ) :
  f (algebra_map ℚ R r) = algebra_map ℚ S r :=
ring_hom.ext_iff.1 (subsingleton.elim (f.comp (algebra_map ℚ R)) (algebra_map ℚ S)) r

/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. -/
def to_rat_alg_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] (f : R →+* S) :
  R →ₐ[ℚ] S :=
{ commutes' := f.map_rat_algebra_map, .. f }

end ring_hom

namespace rat

instance algebra_rat {α} [division_ring α] [char_zero α] : algebra ℚ α :=
(rat.cast_hom α).to_algebra' $ λ r x, r.cast_commute x

@[simp] theorem algebra_map_rat_rat : algebra_map ℚ ℚ = ring_hom.id ℚ :=
subsingleton.elim _ _

-- TODO[gh-6025]: make this an instance once safe to do so
lemma algebra_rat_subsingleton {α} [semiring α] :
  subsingleton (algebra ℚ α) :=
⟨λ x y, algebra.algebra_ext x y $ ring_hom.congr_fun $ subsingleton.elim _ _⟩

end rat

namespace algebra
open module

variables (R : Type u) (A : Type v)

variables [comm_semiring R] [semiring A] [algebra R A]

/-- `algebra_map` as an `alg_hom`. -/
def of_id : R →ₐ[R] A :=
{ commutes' := λ _, rfl, .. algebra_map R A }
variables {R}

theorem of_id_apply (r) : of_id R A r = algebra_map R A r := rfl

variables (R A)
/-- The multiplication in an algebra is a bilinear map. -/
def lmul : A →ₐ[R] (End R A) :=
{ map_one' := by { ext a, exact one_mul a },
  map_mul' := by { intros a b, ext c, exact mul_assoc a b c },
  map_zero' := by { ext a, exact zero_mul a },
  commutes' := by { intro r, ext a, dsimp, rw [smul_def] },
  .. (show A →ₗ[R] A →ₗ[R] A, from linear_map.mk₂ R (*)
  (λ x y z, add_mul x y z)
  (λ c x y, by rw [smul_def, smul_def, mul_assoc _ x y])
  (λ x y z, mul_add x y z)
  (λ c x y, by rw [smul_def, smul_def, left_comm])) }

variables {A}

/-- The multiplication on the left in an algebra is a linear map. -/
def lmul_left (r : A) : A →ₗ A :=
lmul R A r

/-- The multiplication on the right in an algebra is a linear map. -/
def lmul_right (r : A) : A →ₗ A :=
(lmul R A).to_linear_map.flip r

/-- Simultaneous multiplication on the left and right is a linear map. -/
def lmul_left_right (vw: A × A) : A →ₗ[R] A :=
(lmul_right R vw.2).comp (lmul_left R vw.1)

/-- The multiplication map on an algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def lmul' : A ⊗[R] A →ₗ[R] A :=
tensor_product.lift (lmul R A).to_linear_map

lemma commute_lmul_left_right (a b : A) :
  commute (lmul_left R a) (lmul_right R b) :=
by { ext c, exact (mul_assoc a c b).symm, }

variables {R A}

@[simp] lemma lmul_apply (p q : A) : lmul R A p q = p * q := rfl
@[simp] lemma lmul_left_apply (p q : A) : lmul_left R p q = p * q := rfl
@[simp] lemma lmul_right_apply (p q : A) : lmul_right R p q = q * p := rfl
@[simp] lemma lmul_left_right_apply (vw : A × A) (p : A) :
  lmul_left_right R vw p = vw.1 * p * vw.2 := rfl

@[simp] lemma lmul_left_one : lmul_left R (1:A) = linear_map.id :=
by { ext, simp only [linear_map.id_coe, one_mul, id.def, lmul_left_apply] }

@[simp] lemma lmul_left_mul (a b : A) :
  lmul_left R (a * b) = (lmul_left R a).comp (lmul_left R b) :=
by { ext, simp only [lmul_left_apply, linear_map.comp_apply, mul_assoc] }

@[simp] lemma lmul_right_one : lmul_right R (1:A) = linear_map.id :=
by { ext, simp only [linear_map.id_coe, mul_one, id.def, lmul_right_apply] }

@[simp] lemma lmul_right_mul (a b : A) :
  lmul_right R (a * b) = (lmul_right R b).comp (lmul_right R a) :=
by { ext, simp only [lmul_right_apply, linear_map.comp_apply, mul_assoc] }

@[simp] lemma lmul_left_zero_eq_zero :
  lmul_left R (0 : A) = 0 :=
(lmul R A).map_zero

@[simp] lemma lmul_right_zero_eq_zero :
  lmul_right R (0 : A) = 0 :=
(lmul R A).to_linear_map.flip.map_zero

@[simp] lemma lmul_left_eq_zero_iff (a : A) :
  lmul_left R a = 0 ↔ a = 0 :=
begin
  split; intros h,
  { rw [← mul_one a, ← lmul_left_apply a 1, h, linear_map.zero_apply], },
  { rw h, exact lmul_left_zero_eq_zero, },
end

@[simp] lemma lmul_right_eq_zero_iff (a : A) :
  lmul_right R a = 0 ↔ a = 0 :=
begin
  split; intros h,
  { rw [← one_mul a, ← lmul_right_apply a 1, h, linear_map.zero_apply], },
  { rw h, exact lmul_right_zero_eq_zero, },
end

@[simp] lemma pow_lmul_left (a : A) (n : ℕ) :
  (lmul_left R a) ^ n = lmul_left R (a ^ n) :=
((lmul R A).map_pow a n).symm

@[simp] lemma pow_lmul_right (a : A) (n : ℕ) :
  (lmul_right R a) ^ n = lmul_right R (a ^ n) :=
linear_map.coe_injective $ ((lmul_right R a).coe_pow n).symm ▸ (mul_right_iterate a n)

@[simp] lemma lmul'_apply {x y : A} : lmul' R (x ⊗ₜ y) = x * y :=
by simp only [algebra.lmul', tensor_product.lift.tmul, alg_hom.to_linear_map_apply, lmul_apply]

instance linear_map.module' (R : Type u) [comm_semiring R]
  (M : Type v) [add_comm_monoid M] [module R M]
  (S : Type w) [comm_semiring S] [algebra R S] : module S (M →ₗ[R] S) :=
{ smul := λ s f, linear_map.llcomp _ _ _ _ (algebra.lmul R S s) f,
  one_smul := λ f, linear_map.ext $ λ x, one_mul _,
  mul_smul := λ s₁ s₂ f, linear_map.ext $ λ x, mul_assoc _ _ _,
  smul_add := λ s f g, linear_map.map_add _ _ _,
  smul_zero := λ s, linear_map.map_zero _,
  add_smul := λ s₁ s₂ f, linear_map.ext $ λ x, add_mul _ _ _,
  zero_smul := λ f, linear_map.ext $ λ x, zero_mul _ }

end algebra

section ring

namespace algebra

variables {R A : Type*} [comm_semiring R] [ring A] [algebra R A]

lemma lmul_left_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (lmul_left R x) :=
by { letI : domain A := { exists_pair_ne := ⟨x, 0, hx⟩, ..‹ring A›, ..‹no_zero_divisors A› },
     exact mul_right_injective' hx }

lemma lmul_right_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (lmul_right R x) :=
by { letI : domain A := { exists_pair_ne := ⟨x, 0, hx⟩, ..‹ring A›, ..‹no_zero_divisors A› },
     exact mul_left_injective' hx }

lemma lmul_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (lmul R A x) :=
by { letI : domain A := { exists_pair_ne := ⟨x, 0, hx⟩, ..‹ring A›, ..‹no_zero_divisors A› },
     exact mul_right_injective' hx }

end algebra

end ring

section int

variables (R : Type*) [ring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℤ`-algebras. This is only an issue since `algebra.id ℤ` and `algebra_int ℤ` are not yet defeq.
-- TODO: fix this by adding an `of_int` field to rings.
/-- Ring ⥤ ℤ-Alg -/
@[priority 99] instance algebra_int : algebra ℤ R :=
{ commutes' := int.cast_commute,
  smul_def' := λ _ _, gsmul_eq_mul _ _,
  to_ring_hom := int.cast_ring_hom R }

variables {R}

instance int_algebra_subsingleton : subsingleton (algebra ℤ R) :=
⟨λ P Q, by { ext, simp, }⟩

end int

/-!
The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

We couldn't set this up back in `algebra.pi_instances` because this file imports it.
-/
namespace pi

variable {I : Type u}     -- The indexing type
variable {R : Type*}      -- The scalar type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)
variables (I f)

instance algebra {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] :
  algebra R (Π i : I, f i) :=
{ commutes' := λ a f, begin ext, simp [algebra.commutes], end,
  smul_def' := λ a f, begin ext, simp [algebra.smul_def''], end,
  ..(pi.ring_hom (λ i, algebra_map R (f i)) : R →+* Π i : I, f i) }

@[simp] lemma algebra_map_apply {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] (a : R) (i : I) :
  algebra_map R (Π i, f i) a i = algebra_map R (f i) a := rfl

-- One could also build a `Π i, R i`-algebra structure on `Π i, A i`,
-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.

variables {I} (R) (f)

/-- `function.eval` as an `alg_hom`. The name matches `pi.eval_ring_hom`, `pi.eval_monoid_hom`,
etc. -/
@[simps]
def eval_alg_hom {r : comm_semiring R} [Π i, semiring (f i)] [Π i, algebra R (f i)] (i : I) :
  (Π i, f i) →ₐ[R] f i :=
{ to_fun := λ f, f i, commutes' := λ r, rfl, .. pi.eval_ring_hom f i}

end pi

section is_scalar_tower

variables {R : Type*} [comm_semiring R]
variables (A : Type*) [semiring A] [algebra R A]
variables {M : Type*} [add_comm_monoid M] [module A M] [module R M] [is_scalar_tower R A M]
variables {N : Type*} [add_comm_monoid N] [module A N] [module R N] [is_scalar_tower R A N]

lemma algebra_compatible_smul (r : R) (m : M) : r • m = ((algebra_map R A) r) • m :=
by rw [←(one_smul A m), ←smul_assoc, algebra.smul_def, mul_one, one_smul]

@[simp] lemma algebra_map_smul (r : R) (m : M) : ((algebra_map R A) r) • m = r • m :=
(algebra_compatible_smul A r m).symm

variable {A}

@[priority 100] -- see Note [lower instance priority]
instance is_scalar_tower.to_smul_comm_class : smul_comm_class R A M :=
⟨λ r a m, by rw [algebra_compatible_smul A r (a • m), smul_smul, algebra.commutes, mul_smul,
  ←algebra_compatible_smul]⟩

@[priority 100] -- see Note [lower instance priority]
instance is_scalar_tower.to_smul_comm_class' : smul_comm_class A R M :=
smul_comm_class.symm _ _ _

lemma smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
smul_comm _ _ _

namespace linear_map

instance coe_is_scalar_tower : has_coe (M →ₗ[A] N) (M →ₗ[R] N) :=
⟨restrict_scalars R⟩

variables (R) {A M N}

@[simp, norm_cast squash] lemma coe_restrict_scalars_eq_coe (f : M →ₗ[A] N) :
  (f.restrict_scalars R : M → N) = f := rfl

@[simp, norm_cast squash] lemma coe_coe_is_scalar_tower (f : M →ₗ[A] N) :
  ((f : M →ₗ[R] N) : M → N) = f := rfl

/-- `A`-linearly coerce a `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def lto_fun (R : Type u) (M : Type v) (A : Type w)
  [comm_semiring R] [add_comm_monoid M] [module R M] [comm_ring A] [algebra R A] :
  (M →ₗ[R] A) →ₗ[A] (M → A) :=
{ to_fun := linear_map.to_fun,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

end linear_map

end is_scalar_tower

section restrict_scalars

section type_synonym
variables (R S M A : Type*)

/-- If we put an `R`-algebra structure on a semiring `S`, we get a natural equivalence from the
category of `S`-modules to the category of representations of the algebra `S` (over `R`). The type
synonym `restrict_scalars` is essentially this equivalence.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `S`, given:
```lean
variables (R S M : Type*)
variables [comm_semiring R] [semiring S] [algebra R S] [add_comm_monoid M] [module S M]
```
With the assumptions above we can't directly state our map as we have no `module R M` structure, but
`restrict_scalars` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `restrict_scalars` which is compatible
example : restrict_scalars R S M →ₗ[R] S := sorry
```
However, it is usually better just to add this extra structure as an argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [module R M] [is_scalar_tower R S M] : M →ₗ[R] S := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[module R M] [is_scalar_tower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `restrict_scalars` entirely. If not, we can pass
`restrict_scalars R S M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`is_scalar_tower` rather than `restrict_scalars`.

An example of when one might want to use `restrict_scalars` would be if one has a vector space
over a field of characteristic zero and wishes to make use of the `ℚ`-algebra structure. -/
@[nolint unused_arguments]
def restrict_scalars (R S M : Type*) : Type* := M

instance [I : inhabited M] : inhabited (restrict_scalars R S M) := I

instance [I : add_comm_monoid M] : add_comm_monoid (restrict_scalars R S M) := I

instance [I : add_comm_group M] : add_comm_group (restrict_scalars R S M) := I

instance restrict_scalars.module_orig [semiring S] [add_comm_monoid M] [I : module S M] :
  module S (restrict_scalars R S M) := I

/-- `restrict_scalars.linear_equiv` is an equivalence of modules over the semiring `S`. -/
def restrict_scalars.linear_equiv [semiring S] [add_comm_monoid M] [module S M] :
  restrict_scalars R S M ≃ₗ[S] M :=
linear_equiv.refl S M

section module
variables [semiring S] [add_comm_monoid M] [comm_semiring R] [algebra R S] [module S M]

/--
When `M` is a module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
module structure over `R`.

The preferred way of setting this up is `[module R M] [module S M] [is_scalar_tower R S M]`.
-/
instance : module R (restrict_scalars R S M) :=
module.comp_hom M (algebra_map R S)

lemma restrict_scalars_smul_def (c : R) (x : restrict_scalars R S M) :
  c • x = ((algebra_map R S c) • x : M) := rfl

@[simp] lemma restrict_scalars.linear_equiv_map_smul (t : R) (x : restrict_scalars R S M) :
  restrict_scalars.linear_equiv R S M (t • x)
  = (algebra_map R S t) • restrict_scalars.linear_equiv R S M x :=
rfl

instance : is_scalar_tower R S (restrict_scalars R S M) :=
⟨λ r S M, by { rw [algebra.smul_def, mul_smul], refl }⟩

instance submodule.restricted_module (V : submodule S M) :
  module R V :=
restrict_scalars.module R S V

instance submodule.restricted_module_is_scalar_tower (V : submodule S M) :
  is_scalar_tower R S V :=
restrict_scalars.is_scalar_tower R S V

end module

section algebra

instance [I : semiring A] : semiring (restrict_scalars R S A) := I
instance [I : ring A] : ring (restrict_scalars R S A) := I
instance [I : comm_semiring A] : comm_semiring (restrict_scalars R S A) := I
instance [I : comm_ring A] : comm_ring (restrict_scalars R S A) := I

variables [comm_semiring S] [semiring A]

instance restrict_scalars.algebra_orig [I : algebra S A] : algebra S (restrict_scalars R S A) := I

variables [algebra S A]

/-- Tautological `S`-algebra isomorphism `restrict_scalars R S A ≃ₐ[S] A`. -/
def restrict_scalars.alg_equiv : restrict_scalars R S A ≃ₐ[S] A := alg_equiv.refl

variables [comm_semiring R] [algebra R S]

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
instance : algebra R (restrict_scalars R S A) :=
{ smul := (•),
  commutes' := λ r x, algebra.commutes _ _,
  smul_def' := λ _ _, algebra.smul_def _ _,
  .. (algebra_map S A).comp (algebra_map R S) }

end algebra

end type_synonym

/-! TODO: The following lemmas no longer involve `algebra` at all, and could be moved closer
to `algebra/module/submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `linear_algebra/basic.lean`. -/
section module
open module

variables (R S M N : Type*) [semiring R] [semiring S] [has_scalar R S]
variables [add_comm_monoid M] [module R M] [module S M] [is_scalar_tower R S M]
variables [add_comm_monoid N] [module R N] [module S N] [is_scalar_tower R S N]

variables {S M N}

namespace submodule

/--
`V.restrict_scalars R` is the `R`-submodule of the `R`-module given by restriction of scalars,
corresponding to `V`, an `S`-submodule of the original `S`-module.
-/
@[simps]
def restrict_scalars (V : submodule S M) : submodule R M :=
{ carrier := V.carrier,
  zero_mem' := V.zero_mem,
  smul_mem' := λ c m h, V.smul_of_tower_mem c h,
  add_mem' := λ x y hx hy, V.add_mem hx hy }

@[simp]
lemma restrict_scalars_mem (V : submodule S M) (m : M) :
  m ∈ V.restrict_scalars R ↔ m ∈ V :=
iff.refl _

variables (R S M)

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : submodule S M → submodule R M) :=
λ V₁ V₂ h, ext $ by convert set.ext_iff.1 (set_like.ext'_iff.1 h); refl

@[simp] lemma restrict_scalars_inj {V₁ V₂ : submodule S M} :
  restrict_scalars R V₁ = restrict_scalars R V₂ ↔ V₁ = V₂ :=
(restrict_scalars_injective R _ _).eq_iff

@[simp]
lemma restrict_scalars_bot : restrict_scalars R (⊥ : submodule S M) = ⊥ := rfl

@[simp]
lemma restrict_scalars_top : restrict_scalars R (⊤ : submodule S M) = ⊤ := rfl

/-- If `S` is an `R`-algebra, then the `R`-module generated by a set `X` is included in the
`S`-module generated by `X`. -/
lemma span_le_restrict_scalars (X : set M) : span R (X : set M) ≤ restrict_scalars R (span S X) :=
submodule.span_le.mpr submodule.subset_span

end submodule

@[simp]
lemma linear_map.ker_restrict_scalars (f : M →ₗ[S] N) :
  (f.restrict_scalars R).ker = f.ker.restrict_scalars R :=
rfl

end module

end restrict_scalars

namespace submodule

variables (R A M : Type*)
variables [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M]
variables [module R M] [module A M] [is_scalar_tower R A M]

/-- If `A` is an `R`-algebra such that the induced morhpsim `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
lemma span_eq_restrict_scalars (X : set M) (hsur : function.surjective (algebra_map R A)) :
  span R X = restrict_scalars R (span A X) :=
begin
  apply (span_le_restrict_scalars R A M X).antisymm (λ m hm, _),
  refine span_induction hm subset_span (zero_mem _) (λ _ _, add_mem _) (λ a m hm, _),
  obtain ⟨r, rfl⟩ := hsur a,
  simpa [algebra_map_smul] using smul_mem _ r hm
end

end submodule

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {I : Type*}

variables [comm_semiring R] [semiring A] [semiring B]
variables [algebra R A] [algebra R B]

/-- `R`-algebra homomorphism between the function spaces `I → A` and `I → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps] protected def comp_left (f : A →ₐ[R] B) (I : Type*) : (I → A) →ₐ[R] (I → B) :=
{ to_fun := λ h, f ∘ h,
  commutes' := λ c, by { ext, exact f.commutes' c },
  .. f.to_ring_hom.comp_left I }

end alg_hom
