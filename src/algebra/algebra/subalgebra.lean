/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.operations

/-!
# Subalgebras over Commutative Semiring

In this file we define `subalgebra`s and the usual operations on them (`map`, `comap'`).

More lemmas about `adjoin` can be found in `ring_theory.adjoin`.
-/
universes u v w

open_locale tensor_product big_operators

set_option old_structure_cmd true

/-- A subalgebra is a sub(semi)ring that includes the range of `algebra_map`. -/
structure subalgebra (R : Type u) (A : Type v)
  [comm_semiring R] [semiring A] [algebra R A] extends subsemiring A : Type v :=
(algebra_map_mem' : ∀ r, algebra_map R A r ∈ carrier)
(zero_mem' := (algebra_map R A).map_zero ▸ algebra_map_mem' 0)
(one_mem' := (algebra_map R A).map_one ▸ algebra_map_mem' 1)

/-- Reinterpret a `subalgebra` as a `subsemiring`. -/
add_decl_doc subalgebra.to_subsemiring

namespace subalgebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]
include R

instance : set_like (subalgebra R A) A :=
⟨subalgebra.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp]
lemma mem_carrier {s : subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[ext] theorem ext {S T : subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

@[simp] lemma mem_to_subsemiring {S : subalgebra R A} {x} : x ∈ S.to_subsemiring ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_subsemiring (S : subalgebra R A) : (↑S.to_subsemiring : set A) = S := rfl

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : subalgebra R A) (s : set A) (hs : s = ↑S) : subalgebra R A :=
{ carrier := s,
  add_mem' := hs.symm ▸ S.add_mem',
  mul_mem' := hs.symm ▸ S.mul_mem',
  algebra_map_mem' := hs.symm ▸ S.algebra_map_mem' }

variables (S : subalgebra R A)

theorem algebra_map_mem (r : R) : algebra_map R A r ∈ S :=
S.algebra_map_mem' r

theorem srange_le : (algebra_map R A).srange ≤ S.to_subsemiring :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_subset : set.range (algebra_map R A) ⊆ S :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_le : set.range (algebra_map R A) ≤ S :=
S.range_subset

theorem one_mem : (1 : A) ∈ S :=
S.to_subsemiring.one_mem

theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
S.to_subsemiring.mul_mem hx hy

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
(algebra.smul_def r x).symm ▸ S.mul_mem (S.algebra_map_mem r) hx

theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
S.to_subsemiring.pow_mem hx n

theorem zero_mem : (0 : A) ∈ S :=
S.to_subsemiring.zero_mem

theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
S.to_subsemiring.add_mem hx hy

theorem neg_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
neg_one_smul R x ▸ S.smul_mem hx _

theorem sub_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
by simpa only [sub_eq_add_neg] using S.add_mem hx (S.neg_mem hy)

theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
S.to_subsemiring.nsmul_mem hx n

theorem gsmul_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) : ∀ (n : ℤ), n • x ∈ S
| (n : ℕ) := by { rw [gsmul_coe_nat], exact S.nsmul_mem hx n }
| -[1+ n] := by { rw [gsmul_neg_succ_of_nat], exact S.neg_mem (S.nsmul_mem hx _) }

theorem coe_nat_mem (n : ℕ) : (n : A) ∈ S :=
S.to_subsemiring.coe_nat_mem n

theorem coe_int_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
int.cases_on n (λ i, S.coe_nat_mem i) (λ i, S.neg_mem $ S.coe_nat_mem $ i + 1)

theorem list_prod_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.prod ∈ S :=
S.to_subsemiring.list_prod_mem h

theorem list_sum_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
S.to_subsemiring.list_sum_mem h

theorem multiset_prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.prod ∈ S :=
S.to_subsemiring.multiset_prod_mem m h

theorem multiset_sum_mem {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
S.to_subsemiring.multiset_sum_mem m h

theorem prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∏ x in t, f x ∈ S :=
S.to_subsemiring.prod_mem h

theorem sum_mem {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∑ x in t, f x ∈ S :=
S.to_subsemiring.sum_mem h

lemma is_add_submonoid {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : is_add_submonoid (S : set A) :=
{ zero_mem := S.zero_mem,
  add_mem := λ _ _, S.add_mem }

lemma is_submonoid {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : is_submonoid (S : set A) :=
{ one_mem := S.one_mem,
  mul_mem := λ _ _, S.mul_mem }

/-- A subalgebra over a ring is also a `subring`. -/
def to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
  subring A :=
{ neg_mem' := λ _, S.neg_mem,
  .. S.to_subsemiring }

@[simp] lemma mem_to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  {S : subalgebra R A} {x} : x ∈ S.to_subring ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  (S : subalgebra R A) : (↑S.to_subring : set A) = S := rfl

lemma is_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  (S : subalgebra R A) : is_subring (S : set A) :=
{ neg_mem := λ _, S.neg_mem,
  ..S.is_add_submonoid,
  ..S.is_submonoid }

instance : inhabited S := ⟨(0 : S.to_subsemiring)⟩

section

/-! `subalgebra`s inherit structure from their `subsemiring` / `semiring` coercions. -/

instance to_semiring {R A}
  [comm_semiring R] [semiring A] [algebra R A] (S : subalgebra R A) :
  semiring S := S.to_subsemiring.to_semiring
instance to_comm_semiring {R A}
  [comm_semiring R] [comm_semiring A] [algebra R A] (S : subalgebra R A) :
  comm_semiring S := S.to_subsemiring.to_comm_semiring
instance to_ring {R A}
  [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
  ring S := S.to_subring.to_ring
instance to_comm_ring {R A}
  [comm_ring R] [comm_ring A] [algebra R A] (S : subalgebra R A) :
  comm_ring S := S.to_subring.to_comm_ring

instance to_ordered_semiring {R A}
  [comm_semiring R] [ordered_semiring A] [algebra R A] (S : subalgebra R A) :
  ordered_semiring S := S.to_subsemiring.to_ordered_semiring
instance to_ordered_comm_semiring {R A}
  [comm_semiring R] [ordered_comm_semiring A] [algebra R A] (S : subalgebra R A) :
  ordered_comm_semiring S := S.to_subsemiring.to_ordered_comm_semiring
instance to_ordered_ring {R A}
  [comm_ring R] [ordered_ring A] [algebra R A] (S : subalgebra R A) :
  ordered_ring S := S.to_subring.to_ordered_ring
instance to_ordered_comm_ring {R A}
  [comm_ring R] [ordered_comm_ring A] [algebra R A] (S : subalgebra R A) :
  ordered_comm_ring S := S.to_subring.to_ordered_comm_ring

instance to_linear_ordered_semiring {R A}
  [comm_semiring R] [linear_ordered_semiring A] [algebra R A] (S : subalgebra R A) :
  linear_ordered_semiring S := S.to_subsemiring.to_linear_ordered_semiring
/-! There is no `linear_ordered_comm_semiring`. -/
instance to_linear_ordered_ring {R A}
  [comm_ring R] [linear_ordered_ring A] [algebra R A] (S : subalgebra R A) :
  linear_ordered_ring S := S.to_subring.to_linear_ordered_ring
instance to_linear_ordered_comm_ring {R A}
  [comm_ring R] [linear_ordered_comm_ring A] [algebra R A] (S : subalgebra R A) :
  linear_ordered_comm_ring S := S.to_subring.to_linear_ordered_comm_ring

end

instance algebra : algebra R S :=
{ smul := λ (c:R) x, ⟨c • x.1, S.smul_mem x.2 c⟩,
  commutes' := λ c x, subtype.eq $ algebra.commutes _ _,
  smul_def' := λ c x, subtype.eq $ algebra.smul_def _ _,
  .. (algebra_map R A).cod_srestrict S.to_subsemiring $ λ x, S.range_le ⟨x, rfl⟩ }

instance to_algebra {R A B : Type*} [comm_semiring R] [comm_semiring A] [semiring B]
  [algebra R A] [algebra A B] (A₀ : subalgebra R A) : algebra A₀ B :=
algebra.of_subsemiring A₀.to_subsemiring

instance nontrivial [nontrivial A] : nontrivial S :=
S.to_subsemiring.nontrivial

instance no_zero_smul_divisors_bot [no_zero_smul_divisors R A] : no_zero_smul_divisors R S :=
⟨λ c x h,
  have c = 0 ∨ (x : A) = 0,
  from eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h),
  this.imp_right (@subtype.ext_iff _ _ x 0).mpr⟩

@[simp, norm_cast] lemma coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : S) : A) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : S) : A) = 1 := rfl
@[simp, norm_cast] lemma coe_neg {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  {S : subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl
@[simp, norm_cast] lemma coe_sub {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  {S : subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl
@[simp, norm_cast] lemma coe_smul (r : R) (x : S) : (↑(r • x) : A) = r • ↑x := rfl
@[simp, norm_cast] lemma coe_algebra_map (r : R) : ↑(algebra_map R S r) = algebra_map R A r :=
rfl

@[simp, norm_cast] lemma coe_pow (x : S) (n : ℕ) : (↑(x^n) : A) = (↑x)^n :=
begin
  induction n with n ih,
  { simp, },
  { simp [pow_succ, ih], },
end

@[simp, norm_cast] lemma coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
(subtype.ext_iff.symm : (x : A) = (0 : S) ↔ x = 0)
@[simp, norm_cast] lemma coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
(subtype.ext_iff.symm : (x : A) = (1 : S) ↔ x = 1)

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype

/-- Embedding of a subalgebra into the algebra. -/
def val : S →ₐ[R] A :=
by refine_struct { to_fun := (coe : S → A) }; intros; refl

@[simp] lemma coe_val : (S.val : S → A) = coe := rfl

lemma val_apply (x : S) : S.val x = (x : A) := rfl

/-- Convert a `subalgebra` to `submodule` -/
def to_submodule : submodule R A :=
{ carrier := S,
  zero_mem' := (0:S).2,
  add_mem' := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul_mem' := λ c x hx, (algebra.smul_def c x).symm ▸
    (⟨algebra_map R A c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

lemma to_submodule.is_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  (S : subalgebra R A) : _root_.is_subring (S.to_submodule : set A) := S.is_subring

@[simp] lemma mem_to_submodule {x} : x ∈ S.to_submodule ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_submodule (S : subalgebra R A) : (↑S.to_submodule : set A) = S := rfl

theorem to_submodule_injective :
  function.injective (to_submodule : subalgebra R A → submodule R A) :=
λ S T h, ext $ λ x, by rw [← mem_to_submodule, ← mem_to_submodule, h]

theorem to_submodule_inj {S U : subalgebra R A} : S.to_submodule = U.to_submodule ↔ S = U :=
to_submodule_injective.eq_iff

/-- As submodules, subalgebras are idempotent. -/
@[simp] theorem mul_self : S.to_submodule * S.to_submodule = S.to_submodule :=
begin
  apply le_antisymm,
  { rw submodule.mul_le,
    intros y hy z hz,
    exact mul_mem S hy hz },
  { intros x hx1,
    rw ← mul_one x,
    exact submodule.mul_mem_mul hx1 (one_mem S) }
end

/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def to_submodule_equiv (S : subalgebra R A) : S.to_submodule ≃ₗ[R] S :=
linear_equiv.of_eq _ _ rfl

/-- If `S` is an `R`-subalgebra of `A` and `T` is an `S`-subalgebra of `A`,
then `T` is an `R`-subalgebra of `A`. -/
def under {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  {i : algebra R A} (S : subalgebra R A)
  (T : subalgebra S A) : subalgebra R A :=
{ algebra_map_mem' := λ r, T.algebra_map_mem ⟨algebra_map R A r, S.algebra_map_mem r⟩,
  .. T }

/-- Transport a subalgebra via an algebra homomorphism. -/
def map (S : subalgebra R A) (f : A →ₐ[R] B) : subalgebra R B :=
{ algebra_map_mem' := λ r, f.commutes r ▸ set.mem_image_of_mem _ (S.algebra_map_mem r),
  .. S.to_subsemiring.map (f : A →+* B) }

lemma map_mono {S₁ S₂ : subalgebra R A} {f : A →ₐ[R] B} :
  S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
set.image_subset f

lemma map_injective {S₁ S₂ : subalgebra R A} (f : A →ₐ[R] B)
  (hf : function.injective f) (ih : S₁.map f = S₂.map f) : S₁ = S₂ :=
ext $ set.ext_iff.1 $ set.image_injective.2 hf $ set.ext $ set_like.ext_iff.mp ih

lemma mem_map {S : subalgebra R A} {f : A →ₐ[R] B} {y : B} :
  y ∈ map S f ↔ ∃ x ∈ S, f x = y :=
subsemiring.mem_map

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap' (S : subalgebra R B) (f : A →ₐ[R] B) : subalgebra R A :=
{ algebra_map_mem' := λ r, show f (algebra_map R A r) ∈ S,
    from (f.commutes r).symm ▸ S.algebra_map_mem r,
  .. S.to_subsemiring.comap (f : A →+* B) }

theorem map_le {S : subalgebra R A} {f : A →ₐ[R] B} {U : subalgebra R B} :
  map S f ≤ U ↔ S ≤ comap' U f :=
set.image_subset_iff

@[simp] lemma mem_comap (S : subalgebra R B) (f : A →ₐ[R] B) (x : A) :
  x ∈ S.comap' f ↔ f x ∈ S :=
iff.rfl

@[simp, norm_cast] lemma coe_comap (S : subalgebra R B) (f : A →ₐ[R] B) :
  (S.comap' f : set A) = f ⁻¹' (S : set B) :=
by { ext, simp, }

instance no_zero_divisors {R A : Type*} [comm_ring R] [semiring A] [no_zero_divisors A]
  [algebra R A] (S : subalgebra R A) : no_zero_divisors S :=
S.to_subsemiring.no_zero_divisors

instance no_zero_smul_divisors_top {R A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]
  [no_zero_divisors A] (S : subalgebra R A) : no_zero_smul_divisors S A :=
⟨λ c x h,
  have (c : A) = 0 ∨ x = 0,
  from eq_zero_or_eq_zero_of_mul_eq_zero h,
  this.imp_left (@subtype.ext_iff _ _ c 0).mpr⟩

instance integral_domain {R A : Type*} [comm_ring R] [integral_domain A] [algebra R A]
  (S : subalgebra R A) : integral_domain S :=
@subring.domain A _ S ⟨is_subring S⟩

end subalgebra

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
variables (φ : A →ₐ[R] B)

/-- Range of an `alg_hom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : subalgebra R B :=
{ algebra_map_mem' := λ r, ⟨algebra_map R A r, φ.commutes r⟩,
  .. φ.to_ring_hom.srange }

@[simp] lemma mem_range (φ : A →ₐ[R] B) {y : B} :
  y ∈ φ.range ↔ ∃ x, φ x = y := ring_hom.mem_srange

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range := φ.mem_range.2 ⟨x, rfl⟩

@[simp] lemma coe_range (φ : A →ₐ[R] B) : (φ.range : set B) = set.range φ :=
by { ext, rw [set_like.mem_coe, mem_range], refl }

/-- Restrict the codomain of an algebra homomorphism. -/
def cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
{ commutes' := λ r, subtype.eq $ f.commutes r,
  .. ring_hom.cod_srestrict (f : A →+* B) S.to_subsemiring hf }

@[simp] lemma val_comp_cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) :
  S.val.comp (f.cod_restrict S hf) = f :=
alg_hom.ext $ λ _, rfl

@[simp] lemma coe_cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
  ↑(f.cod_restrict S hf x) = f x := rfl

theorem injective_cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) :
  function.injective (f.cod_restrict S hf) ↔ function.injective f :=
⟨λ H x y hxy, H $ subtype.eq hxy, λ H x y hxy, H (congr_arg subtype.val hxy : _)⟩

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible] def range_restrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
f.cod_restrict f.range f.mem_range_self

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : A →ₐ[R] B) : subalgebra R A :=
{ carrier := {a | ϕ a = ψ a},
  add_mem' := λ x y hx hy, by
  { change ϕ x = ψ x at hx,
    change ϕ y = ψ y at hy,
    change ϕ (x + y) = ψ (x + y),
    rw [alg_hom.map_add, alg_hom.map_add, hx, hy] },
  mul_mem' := λ x y hx hy, by
  { change ϕ x = ψ x at hx,
    change ϕ y = ψ y at hy,
    change ϕ (x * y) = ψ (x * y),
    rw [alg_hom.map_mul, alg_hom.map_mul, hx, hy] },
  algebra_map_mem' := λ x, by
  { change ϕ (algebra_map R A x) = ψ (algebra_map R A x),
    rw [alg_hom.commutes, alg_hom.commutes] } }

@[simp] lemma mem_equalizer (ϕ ψ : A →ₐ[R] B) (x : A) :
  x ∈ ϕ.equalizer ψ ↔ ϕ x = ψ x := iff.rfl

end alg_hom

namespace alg_equiv

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `alg_equiv.of_injective`. -/
def of_left_inverse
  {g : B → A} {f : A →ₐ[R] B} (h : function.left_inverse g f) :
  A ≃ₐ[R] f.range :=
{ to_fun := f.range_restrict,
  inv_fun := g ∘ f.range.val,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := f.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  ..f.range_restrict }

@[simp] lemma of_left_inverse_apply
  {g : B → A} {f : A →ₐ[R] B} (h : function.left_inverse g f) (x : A) :
  ↑(of_left_inverse h x) = f x := rfl

@[simp] lemma of_left_inverse_symm_apply
  {g : B → A} {f : A →ₐ[R] B} (h : function.left_inverse g f) (x : f.range) :
  (of_left_inverse h).symm x = g x := rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def of_injective (f : A →ₐ[R] B) (hf : function.injective f) :
  A ≃ₐ[R] f.range :=
of_left_inverse (classical.some_spec hf.has_left_inverse)

@[simp] lemma of_injective_apply (f : A →ₐ[R] B) (hf : function.injective f) (x : A) :
  ↑(of_injective f hf x) = f x := rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
noncomputable def of_injective_field {E F : Type*} [division_ring E] [semiring F]
  [nontrivial F] [algebra R E] [algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
of_injective f f.to_ring_hom.injective

end alg_equiv

namespace algebra

variables (R : Type u) {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- The minimal subalgebra that includes `s`. -/
def adjoin (s : set A) : subalgebra R A :=
{ algebra_map_mem' := λ r, subsemiring.subset_closure $ or.inl ⟨r, rfl⟩,
  .. subsemiring.closure (set.range (algebra_map R A) ∪ s) }
variables {R}

protected lemma gc : galois_connection (adjoin R : set A → subalgebra R A) coe :=
λ s S, ⟨λ H, le_trans (le_trans (set.subset_union_right _ _) subsemiring.subset_closure) H,
λ H, show subsemiring.closure (set.range (algebra_map R A) ∪ s) ≤ S.to_subsemiring,
     from subsemiring.closure_le.2 $ set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : galois_insertion (adjoin R : set A → subalgebra R A) coe :=
{ choice := λ s hs, (adjoin R s).copy s $ le_antisymm (algebra.gc.le_u_l s) hs,
  gc := algebra.gc,
  le_l_u := λ S, (algebra.gc (S : set A) (adjoin R S)).1 $ le_refl _,
  choice_eq := λ _ _, set_like.coe_injective $ by { generalize_proofs h, exact h } }

instance : complete_lattice (subalgebra R A) :=
galois_insertion.lift_complete_lattice algebra.gi

@[simp]
lemma coe_top : (↑(⊤ : subalgebra R A) : set A) = set.univ := rfl

@[simp] lemma mem_top {x : A} : x ∈ (⊤ : subalgebra R A) :=
set.mem_univ x

@[simp] lemma top_to_submodule : (⊤ : subalgebra R A).to_submodule = ⊤ := rfl

@[simp] lemma top_to_subsemiring : (⊤ : subalgebra R A).to_subsemiring = ⊤ := rfl

@[simp, norm_cast]
lemma coe_inf (S T : subalgebra R A) : (↑(S ⊓ T) : set A) = S ∩ T := rfl

@[simp]
lemma mem_inf {S T : subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

@[simp] lemma inf_to_submodule (S T : subalgebra R A) :
  (S ⊓ T).to_submodule = S.to_submodule ⊓ T.to_submodule := rfl

@[simp] lemma inf_to_subsemiring (S T : subalgebra R A) :
  (S ⊓ T).to_subsemiring = S.to_subsemiring ⊓ T.to_subsemiring := rfl

@[simp, norm_cast]
lemma coe_Inf (S : set (subalgebra R A)) : (↑(Inf S) : set A) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (subalgebra R A)} {x : A} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

@[simp] lemma Inf_to_submodule (S : set (subalgebra R A)) :
  (Inf S).to_submodule = Inf (subalgebra.to_submodule '' S) :=
set_like.coe_injective $ by simp

@[simp] lemma Inf_to_subsemiring (S : set (subalgebra R A)) :
  (Inf S).to_subsemiring = Inf (subalgebra.to_subsemiring '' S) :=
set_like.coe_injective $ by simp

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → subalgebra R A} : (↑(⨅ i, S i) : set A) = ⋂ i, S i :=
set.bInter_range

lemma mem_infi {ι : Sort*} {S : ι → subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp] lemma infi_to_submodule {ι : Sort*} (S : ι → subalgebra R A) :
  (⨅ i, S i).to_submodule = ⨅ i, (S i).to_submodule :=
set_like.coe_injective $ by simp

instance : inhabited (subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra R A) ↔ x ∈ set.range (algebra_map R A) :=
suffices (of_id R A).range = (⊥ : subalgebra R A),
by { rw [← this, ←set_like.mem_coe, alg_hom.coe_range], refl },
le_bot_iff.mp (λ x hx, subalgebra.range_le _ ((of_id R A).coe_range ▸ hx))

theorem to_submodule_bot : (⊥ : subalgebra R A).to_submodule = R ∙ 1 :=
by { ext x, simp [mem_bot, -set.singleton_one, submodule.mem_span_singleton, algebra.smul_def] }

@[simp] theorem coe_bot : ((⊥ : subalgebra R A) : set A) = set.range (algebra_map R A) :=
by simp [set.ext_iff, algebra.mem_bot]

theorem eq_top_iff {S : subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

@[simp] theorem map_top (f : A →ₐ[R] B) : subalgebra.map (⊤ : subalgebra R A) f = f.range :=
subalgebra.ext $ λ x,
  ⟨λ ⟨y, _, hy⟩, ⟨y, hy⟩, λ ⟨y, hy⟩, ⟨y, algebra.mem_top, hy⟩⟩

@[simp] theorem map_bot (f : A →ₐ[R] B) : subalgebra.map (⊥ : subalgebra R A) f = ⊥ :=
eq_bot_iff.2 $ λ x ⟨y, hy, hfy⟩, let ⟨r, hr⟩ := mem_bot.1 hy in subalgebra.range_le _
⟨r, by rwa [← f.commutes, hr]⟩

@[simp] theorem comap_top (f : A →ₐ[R] B) : subalgebra.comap' (⊤ : subalgebra R B) f = ⊤ :=
eq_top_iff.2 $ λ x, mem_top

/-- `alg_hom` to `⊤ : subalgebra R A`. -/
def to_top : A →ₐ[R] (⊤ : subalgebra R A) :=
by refine_struct { to_fun := λ x, (⟨x, mem_top⟩ : (⊤ : subalgebra R A)) }; intros; refl

theorem surjective_algebra_map_iff :
  function.surjective (algebra_map R A) ↔ (⊤ : subalgebra R A) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ λ y _, let ⟨x, hx⟩ := h y in hx ▸ subalgebra.algebra_map_mem _ _,
λ h y, algebra.mem_bot.1 $ eq_bot_iff.1 h (algebra.mem_top : y ∈ _)⟩

theorem bijective_algebra_map_iff {R A : Type*} [field R] [semiring A] [nontrivial A]
  [algebra R A] :
  function.bijective (algebra_map R A) ↔ (⊤ : subalgebra R A) = ⊥ :=
⟨λ h, surjective_algebra_map_iff.1 h.2,
λ h, ⟨(algebra_map R A).injective, surjective_algebra_map_iff.2 h⟩⟩

/-- The bottom subalgebra is isomorphic to the base ring. -/
noncomputable def bot_equiv_of_injective (h : function.injective (algebra_map R A)) :
  (⊥ : subalgebra R A) ≃ₐ[R] R :=
alg_equiv.symm $ alg_equiv.of_bijective (algebra.of_id R _)
⟨λ x y hxy, h (congr_arg subtype.val hxy : _),
 λ ⟨y, hy⟩, let ⟨x, hx⟩ := algebra.mem_bot.1 hy in ⟨x, subtype.eq hx⟩⟩

/-- The bottom subalgebra is isomorphic to the field. -/
noncomputable def bot_equiv (F R : Type*) [field F] [semiring R] [nontrivial R] [algebra F R] :
  (⊥ : subalgebra F R) ≃ₐ[F] F :=
bot_equiv_of_injective (ring_hom.injective _)

/-- The top subalgebra is isomorphic to the field. -/
noncomputable def top_equiv : (⊤ : subalgebra R A) ≃ₐ[R] A :=
(alg_equiv.of_bijective to_top ⟨λ _ _, subtype.mk.inj,
  λ x, ⟨x.val, by { ext, refl }⟩⟩ : A ≃ₐ[R] (⊤ : subalgebra R A)).symm

end algebra

namespace subalgebra
open algebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]
variables (S : subalgebra R A)

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_subsingleton [subsingleton A] : subsingleton (subalgebra R A) :=
⟨λ B C, ext (λ x, by { simp only [subsingleton.elim x 0, zero_mem] })⟩

/--
For performance reasons this is not an instance. If you need this instance, add
```
local attribute [instance] alg_hom.subsingleton subalgebra.subsingleton_of_subsingleton
```
in the section that needs it.
-/
-- TODO[gh-6025]: make this an instance once safe to do so
lemma _root_.alg_hom.subsingleton [subsingleton (subalgebra R A)] : subsingleton (A →ₐ[R] B) :=
⟨λ f g, alg_hom.ext $ λ a,
  have a ∈ (⊥ : subalgebra R A) := subsingleton.elim (⊤ : subalgebra R A) ⊥ ▸ mem_top,
  let ⟨x, hx⟩ := set.mem_range.mp (mem_bot.mp this) in
  hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

-- TODO[gh-6025]: make this an instance once safe to do so
lemma _root_.alg_equiv.subsingleton_left [subsingleton (subalgebra R A)] :
  subsingleton (A ≃ₐ[R] B) :=
begin
  haveI : subsingleton (A →ₐ[R] B) := alg_hom.subsingleton,
  exact ⟨λ f g, alg_equiv.ext
    (λ x, alg_hom.ext_iff.mp (subsingleton.elim f.to_alg_hom g.to_alg_hom) x)⟩,
end

-- TODO[gh-6025]: make this an instance once safe to do so
lemma _root_.alg_equiv.subsingleton_right [subsingleton (subalgebra R B)] :
  subsingleton (A ≃ₐ[R] B) :=
begin
  haveI : subsingleton (B ≃ₐ[R] A) := alg_equiv.subsingleton_left,
  exact ⟨λ f g, eq.trans (alg_equiv.symm_symm _).symm
    (by rw [subsingleton.elim f.symm g.symm, alg_equiv.symm_symm])⟩
end

lemma range_val : S.val.range = S :=
ext $ set.ext_iff.1 $ S.val.coe_range.trans subtype.range_val

instance : unique (subalgebra R R) :=
{ uniq :=
  begin
    intro S,
    refine le_antisymm (λ r hr, _) bot_le,
    simp only [set.mem_range, mem_bot, id.map_eq_self, exists_apply_eq_apply, default],
  end
  .. algebra.subalgebra.inhabited }

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `subalgebra` version of `linear_equiv.of_eq` and `equiv.set.of_eq`. -/
@[simps apply]
def equiv_of_eq (S T : subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
{ to_fun := λ x, ⟨x, h ▸ x.2⟩,
  inv_fun := λ x, ⟨x, h.symm ▸ x.2⟩,
  map_mul' := λ _ _, rfl,
  commutes' := λ _, rfl,
  .. linear_equiv.of_eq _ _ (congr_arg to_submodule h) }

@[simp] lemma equiv_of_eq_symm (S T : subalgebra R A) (h : S = T) :
  (equiv_of_eq S T h).symm = equiv_of_eq T S h.symm :=
rfl

@[simp] lemma equiv_of_eq_rfl (S : subalgebra R A) :
  equiv_of_eq S S rfl = alg_equiv.refl :=
by { ext, refl }

@[simp] lemma equiv_of_eq_trans (S T U : subalgebra R A) (hST : S = T) (hTU : T = U) :
  (equiv_of_eq S T hST).trans (equiv_of_eq T U hTU) = equiv_of_eq S U (trans hST hTU) :=
rfl

section prod

variables (S₁ : subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def prod : subalgebra R (A × B) :=
{ carrier := set.prod S S₁,
  algebra_map_mem' := λ r, ⟨algebra_map_mem _ _, algebra_map_mem _ _⟩,
  .. S.to_subsemiring.prod S₁.to_subsemiring }

@[simp] lemma coe_prod :
  (prod S S₁ : set (A × B)) = set.prod S S₁ := rfl

lemma prod_to_submodule :
  (S.prod S₁).to_submodule = S.to_submodule.prod S₁.to_submodule := rfl

@[simp] lemma mem_prod {S : subalgebra R A} {S₁ : subalgebra R B} {x : A × B} :
  x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := set.mem_prod

@[simp] lemma prod_top : (prod ⊤ ⊤ : subalgebra R (A × B)) = ⊤ :=
by ext; simp

lemma prod_mono {S T : subalgebra R A} {S₁ T₁ : subalgebra R B} :
  S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ := set.prod_mono

@[simp] lemma prod_inf_prod {S T : subalgebra R A} {S₁ T₁ : subalgebra R B} :
  S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
set_like.coe_injective set.prod_inter_prod

end prod

end subalgebra

section nat

variables {R : Type*} [semiring R]

/-- A subsemiring is a `ℕ`-subalgebra. -/
def subalgebra_of_subsemiring (S : subsemiring R) : subalgebra ℕ R :=
{ algebra_map_mem' := λ i, S.coe_nat_mem i,
  .. S }

@[simp] lemma mem_subalgebra_of_subsemiring {x : R} {S : subsemiring R} :
  x ∈ subalgebra_of_subsemiring S ↔ x ∈ S :=
iff.rfl

end nat

section int

variables {R : Type*} [ring R]

/-- A subring is a `ℤ`-subalgebra. -/
def subalgebra_of_subring (S : subring R) : subalgebra ℤ R :=
{ algebra_map_mem' := λ i, int.induction_on i S.zero_mem
  (λ i ih, S.add_mem ih S.one_mem)
  (λ i ih, show ((-i - 1 : ℤ) : R) ∈ S, by { rw [int.cast_sub, int.cast_one],
    exact S.sub_mem ih S.one_mem }),
  .. S }

example {S : set R} (hs : is_subring S) : subring R := set.to_subring hs

/-- A subset closed under the ring operations is a `ℤ`-subalgebra. -/
def subalgebra_of_is_subring {S : set R} (hs : is_subring S) : subalgebra ℤ R :=
subalgebra_of_subring (set.to_subring hs)

variables {S : Type*} [semiring S]

@[simp] lemma mem_subalgebra_of_subring {x : R} {S : subring R} :
  x ∈ subalgebra_of_subring S ↔ x ∈ S :=
iff.rfl

@[simp] lemma mem_subalgebra_of_is_subring {x : R} {S : set R} (hs : is_subring S) :
  x ∈ subalgebra_of_is_subring hs ↔ x ∈ S :=
iff.rfl

end int
