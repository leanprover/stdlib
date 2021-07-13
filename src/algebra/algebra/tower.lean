/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.algebra.subalgebra

/-!
# Towers of algebras

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `to_alg_hom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/

universes u v w u₁ v₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace algebra

variables [comm_semiring R] [semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]

variables {A}

/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `R`-module `M`. -/
def lsmul : A →ₐ[R] module.End R M :=
{ map_one' := by { ext m, exact one_smul A m },
  map_mul' := by { intros a b, ext c, exact smul_assoc a b c },
  map_zero' := by { ext m, exact zero_smul A m },
  commutes' := by { intro r, ext m, exact algebra_map_smul A r m },
  .. (show A →ₗ[R] M →ₗ[R] M, from linear_map.mk₂ R (•)
  (λ x y z, add_smul x y z)
  (λ c x y, smul_assoc c x y)
  (λ x y z, smul_add x y z)
  (λ c x y, smul_algebra_smul_comm c x y)) }

@[simp] lemma lsmul_coe (a : A) : (lsmul R M a : M → M) = (•) a := rfl

@[simp] lemma lmul_algebra_map (x : R) :
  lmul R A (algebra_map R A x) = algebra.lsmul R A x :=
eq.symm $ linear_map.ext $ smul_def'' x

end algebra

namespace is_scalar_tower

section module

variables [comm_semiring R] [semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]

variables {R} (A) {M}
theorem algebra_map_smul (r : R) (x : M) : algebra_map R A r • x = r • x :=
by rw [algebra.algebra_map_eq_smul_one, smul_assoc, one_smul]

end module

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B]

variables {R S A}
theorem of_algebra_map_eq [algebra R A]
  (h : ∀ x, algebra_map R A x = algebra_map S A (algebra_map R S x)) :
  is_scalar_tower R S A :=
⟨λ x y z, by simp_rw [algebra.smul_def, ring_hom.map_mul, mul_assoc, h]⟩

/-- See note [partially-applied ext lemmas]. -/
theorem of_algebra_map_eq' [algebra R A]
  (h : algebra_map R A = (algebra_map S A).comp (algebra_map R S)) :
  is_scalar_tower R S A :=
of_algebra_map_eq $ ring_hom.ext_iff.1 h

variables (R S A)

instance subalgebra (S₀ : subalgebra R S) : is_scalar_tower S₀ S A :=
of_algebra_map_eq $ λ x, rfl

variables [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

theorem algebra_map_eq :
  algebra_map R A = (algebra_map S A).comp (algebra_map R S) :=
ring_hom.ext $ λ x, by simp_rw [ring_hom.comp_apply, algebra.algebra_map_eq_smul_one,
    smul_assoc, one_smul]

theorem algebra_map_apply (x : R) : algebra_map R A x = algebra_map S A (algebra_map R S x) :=
by rw [algebra_map_eq R S A, ring_hom.comp_apply]

instance subalgebra' (S₀ : subalgebra R S) : is_scalar_tower R S₀ A :=
@is_scalar_tower.of_algebra_map_eq R S₀ A _ _ _ _ _ _ $ λ _,
(is_scalar_tower.algebra_map_apply R S A _ : _)

@[ext] lemma algebra.ext {S : Type u} {A : Type v} [comm_semiring S] [semiring A]
  (h1 h2 : algebra S A) (h : ∀ {r : S} {x : A}, (by haveI := h1; exact r • x) = r • x) : h1 = h2 :=
begin
  unfreezingI { cases h1 with f1 g1 h11 h12, cases h2 with f2 g2 h21 h22,
  cases f1, cases f2, congr', { ext r x, exact h },
  ext r, erw [← mul_one (g1 r), ← h12, ← mul_one (g2 r), ← h22, h], refl }
end

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def to_alg_hom : S →ₐ[R] A :=
{ commutes' := λ _, (algebra_map_apply _ _ _ _).symm,
  .. algebra_map S A }

lemma to_alg_hom_apply (y : S) : to_alg_hom R S A y = algebra_map S A y := rfl

@[simp] lemma coe_to_alg_hom : ↑(to_alg_hom R S A) = algebra_map S A :=
ring_hom.ext $ λ _, rfl

@[simp] lemma coe_to_alg_hom' : (to_alg_hom R S A : S → A) = algebra_map S A :=
rfl

variables (R) {S A B}

-- conflicts with is_scalar_tower.subalgebra
@[priority 999] instance subsemiring (U : subsemiring S) : is_scalar_tower U S A :=
of_algebra_map_eq $ λ x, rfl

section
local attribute [instance] algebra.of_is_subring subset.comm_ring
-- conflicts with is_scalar_tower.subalgebra
@[priority 999] instance subring {S A : Type*} [comm_ring S] [ring A] [algebra S A]
  (U : set S) [fact (is_subring U)] : is_scalar_tower U S A :=
of_algebra_map_eq $ λ x, rfl
end

@[nolint instance_priority]
instance of_ring_hom {R A B : Type*} [comm_semiring R] [comm_semiring A] [comm_semiring B]
  [algebra R A] [algebra R B] (f : A →ₐ[R] B) :
  @is_scalar_tower R A B _ (f.to_ring_hom.to_algebra.to_has_scalar) _ :=
by { letI := (f : A →+* B).to_algebra, exact of_algebra_map_eq (λ x, (f.commutes x).symm) }

end semiring

section division_ring
variables [field R] [division_ring S] [algebra R S] [char_zero R] [char_zero S]

instance rat : is_scalar_tower ℚ R S :=
of_algebra_map_eq $ λ x, ((algebra_map R S).map_rat_cast x).symm

end division_ring

end is_scalar_tower

section homs

variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B]
variables [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

variables (R) {A S B}

open is_scalar_tower

/-- Given a scalar tower `R`, `S`, `A` of algebras, reinterpret an `S`-subalgebra of `A` an as an
`R`-subalgebra. -/
def subalgebra.restrict_scalars (iSB : subalgebra S A) :
  subalgebra R A :=
{ one_mem' := iSB.one_mem,
  mul_mem' := λ _ _, iSB.mul_mem,
  algebra_map_mem' := λ r, begin
    rw is_scalar_tower.algebra_map_eq R S,
    exact iSB.algebra_map_mem' _,
  end,
  .. iSB.to_submodule.restrict_scalars R  }

namespace alg_hom

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrict_scalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
{ commutes' := λ r, by { rw [algebra_map_apply R S A, algebra_map_apply R S B],
    exact f.commutes (algebra_map R S r) },
  .. (f : A →+* B) }

lemma restrict_scalars_apply (f : A →ₐ[S] B) (x : A) : f.restrict_scalars R x = f x := rfl

@[simp] lemma coe_restrict_scalars (f : A →ₐ[S] B) : (f.restrict_scalars R : A →+* B) = f := rfl

@[simp] lemma coe_restrict_scalars' (f : A →ₐ[S] B) : (restrict_scalars R f : A → B) = f := rfl

end alg_hom

namespace alg_equiv

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrict_scalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
{ commutes' := λ r, by { rw [algebra_map_apply R S A, algebra_map_apply R S B],
    exact f.commutes (algebra_map R S r) },
  .. (f : A ≃+* B) }

lemma restrict_scalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrict_scalars R x = f x := rfl

@[simp] lemma coe_restrict_scalars (f : A ≃ₐ[S] B) : (f.restrict_scalars R : A ≃+* B) = f := rfl

@[simp] lemma coe_restrict_scalars' (f : A ≃ₐ[S] B) : (restrict_scalars R f : A → B) = f := rfl

end alg_equiv

end homs

namespace subalgebra

open is_scalar_tower

section semiring

variables (R) {S A} [comm_semiring R] [comm_semiring S] [semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

/-- If A/S/R is a tower of algebras then the `res`triction of a S-subalgebra of A is
an R-subalgebra of A. -/
def res (U : subalgebra S A) : subalgebra R A :=
{ algebra_map_mem' := λ x, by { rw algebra_map_apply R S A, exact U.algebra_map_mem _ },
  .. U }

@[simp] lemma res_top : res R (⊤ : subalgebra S A) = ⊤ :=
algebra.eq_top_iff.2 $ λ _, show _ ∈ (⊤ : subalgebra S A), from algebra.mem_top

@[simp] lemma mem_res {U : subalgebra S A} {x : A} : x ∈ res R U ↔ x ∈ U := iff.rfl

lemma res_inj {U V : subalgebra S A} (H : res R U = res R V) : U = V :=
ext $ λ x, by rw [← mem_res R, H, mem_res]

/-- Produces a map from `subalgebra.under`. -/
def of_under {R A B : Type*} [comm_semiring R] [comm_semiring A] [semiring B]
  [algebra R A] [algebra R B] (S : subalgebra R A) (U : subalgebra S A)
  [algebra S B] [is_scalar_tower R S B] (f : U →ₐ[S] B) : S.under U →ₐ[R] B :=
{ commutes' := λ r, (f.commutes (algebra_map R S r)).trans (algebra_map_apply R S B r).symm,
  .. f }

end semiring

end subalgebra

namespace is_scalar_tower

open subalgebra

variables [comm_semiring R] [comm_semiring S] [comm_semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

theorem range_under_adjoin (t : set A) :
  (to_alg_hom R S A).range.under (algebra.adjoin _ t) = res R (algebra.adjoin S t) :=
subalgebra.ext $ λ z,
show z ∈ subsemiring.closure (set.range (algebra_map (to_alg_hom R S A).range A) ∪ t : set A) ↔
  z ∈ subsemiring.closure (set.range (algebra_map S A) ∪ t : set A),
from suffices set.range (algebra_map (to_alg_hom R S A).range A) = set.range (algebra_map S A),
  by rw this,
by { ext z, exact ⟨λ ⟨⟨x, y, h1⟩, h2⟩, ⟨y, h2 ▸ h1⟩, λ ⟨y, hy⟩, ⟨⟨z, y, hy⟩, rfl⟩⟩ }

end is_scalar_tower

section semiring

variables {R S A}
variables [comm_semiring R] [semiring S] [add_comm_monoid A]
variables [algebra R S] [module S A] [module R A] [is_scalar_tower R S A]

namespace submodule

open is_scalar_tower

theorem smul_mem_span_smul_of_mem {s : set S} {t : set A} {k : S} (hks : k ∈ span R s)
  {x : A} (hx : x ∈ t) : k • x ∈ span R (s • t) :=
span_induction hks (λ c hc, subset_span $ set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
  (by { rw zero_smul, exact zero_mem _ })
  (λ c₁ c₂ ih₁ ih₂, by { rw add_smul, exact add_mem _ ih₁ ih₂ })
  (λ b c hc, by { rw is_scalar_tower.smul_assoc, exact smul_mem _ _ hc })

theorem smul_mem_span_smul {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R t) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hx)
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem _ ihx ihy })
  (λ c x hx, smul_comm c k x ▸ smul_mem _ _ hx)

theorem smul_mem_span_smul' {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R (s • t)) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, let ⟨p, q, hp, hq, hpq⟩ := set.mem_smul.1 hx in
    by { rw [← hpq, smul_smul], exact smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hq })
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem _ ihx ihy })
  (λ c x hx, smul_comm c k x ▸ smul_mem _ _ hx)

theorem span_smul {s : set S} (hs : span R s = ⊤) (t : set A) :
  span R (s • t) = (span S t).restrict_scalars R :=
le_antisymm (span_le.2 $ λ x hx, let ⟨p, q, hps, hqt, hpqx⟩ := set.mem_smul.1 hx in
  hpqx ▸ (span S t).smul_mem p (subset_span hqt)) $
λ p hp, span_induction hp (λ x hx, one_smul S x ▸ smul_mem_span_smul hs (subset_span hx))
  (zero_mem _)
  (λ _ _, add_mem _)
  (λ k x hx, smul_mem_span_smul' hs hx)

end submodule

end semiring

section ring

namespace algebra

variables [comm_semiring R] [ring A] [algebra R A]
variables [add_comm_group M] [module A M] [module R M] [is_scalar_tower R A M]

lemma lsmul_injective [no_zero_smul_divisors A M] {x : A} (hx : x ≠ 0) :
  function.injective (lsmul R M x) :=
smul_left_injective _ hx

end algebra

end ring
