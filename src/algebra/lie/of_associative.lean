/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.basic
import algebra.lie.subalgebra
import algebra.algebra.subalgebra

/-!
# Lie algebras of associative algebras

This file defines the Lie algebra structure that arises on an associative algebra via the ring
commutator.

Since the linear endomorphisms of a Lie algebra form an associative algebra, one can define the
adjoint action as a morphism of Lie algebras from a Lie algebra to its linear endomorphisms. We
make such a definition in this file.

## Main definitions

 * `lie_algebra.of_associative_algebra`
 * `lie_algebra.of_associative_algebra_hom`
 * `lie_module.to_endomorphism`
 * `lie_algebra.ad`
 * `linear_equiv.lie_conj`
 * `alg_equiv.to_lie_equiv`

## Tags

lie algebra, ring commutator, adjoint action
-/

universes u v w w₁ w₂

section of_associative

variables {A : Type v} [ring A]

namespace ring

/-- The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
@[priority 100]
instance : has_bracket A A := ⟨λ x y, x*y - y*x⟩

lemma lie_def (x y : A) : ⁅x, y⁆ = x*y - y*x := rfl

end ring

namespace lie_ring

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
@[priority 100]
instance of_associative_ring : lie_ring A :=
{ add_lie      := by simp only [ring.lie_def, right_distrib, left_distrib,
    sub_eq_add_neg, add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_add      := by simp only [ring.lie_def, right_distrib, left_distrib,
    sub_eq_add_neg, add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_self     := by simp only [ring.lie_def, forall_const, sub_self],
  leibniz_lie  := λ x y z, by { repeat { rw ring.lie_def, }, noncomm_ring, } }

lemma of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x*y - y*x := rfl

@[simp] lemma lie_apply {α : Type*} (f g : α → A) (a : α) : ⁅f, g⁆ a = ⁅f a, g a⁆ := rfl

end lie_ring

section lie_algebra

variables {R : Type u} [comm_ring R] [algebra R A]

/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
@[priority 100]
instance lie_algebra.of_associative_algebra : lie_algebra R A :=
{ lie_smul := λ t x y,
    by rw [lie_ring.of_associative_ring_bracket, lie_ring.of_associative_ring_bracket,
           algebra.mul_smul_comm, algebra.smul_mul_assoc, smul_sub], }

namespace alg_hom

variables {B : Type w} {C : Type w₁} [ring B] [ring C] [algebra R B] [algebra R C]
variables (f : A →ₐ[R] B) (g : B →ₐ[R] C)

/-- The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def to_lie_hom : A →ₗ⁅R⁆ B :=
 { map_lie' := λ x y, show f ⁅x,y⁆ = ⁅f x,f y⁆,
     by simp only [lie_ring.of_associative_ring_bracket, alg_hom.map_sub, alg_hom.map_mul],
  ..f.to_linear_map, }

instance : has_coe (A →ₐ[R] B) (A →ₗ⁅R⁆ B) := ⟨to_lie_hom⟩

@[simp] lemma to_lie_hom_coe : f.to_lie_hom = ↑f := rfl

@[simp] lemma coe_to_lie_hom : ((f : A →ₗ⁅R⁆ B) : A → B) = f := rfl

lemma to_lie_hom_apply (x : A) : f.to_lie_hom x = f x := rfl

@[simp] lemma to_lie_hom_id : (alg_hom.id R A : A →ₗ⁅R⁆ A) = lie_hom.id := rfl

@[simp] lemma to_lie_hom_comp : (g.comp f : A →ₗ⁅R⁆ C) = (g : B →ₗ⁅R⁆ C).comp (f : A →ₗ⁅R⁆ B) := rfl

lemma to_lie_hom_injective {f g : A →ₐ[R] B}
  (h : (f : A →ₗ⁅R⁆ B) = (g : A →ₗ⁅R⁆ B)) : f = g :=
by { ext a, exact lie_hom.congr_fun h a, }

end alg_hom

end lie_algebra

end of_associative

section adjoint_action

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module.

See also `lie_module.to_module_hom`. -/
@[simps] def lie_module.to_endomorphism : L →ₗ⁅R⁆ module.End R M :=
{ to_fun    := λ x,
  { to_fun    := λ m, ⁅x, m⁆,
    map_add'  := lie_add x,
    map_smul' := λ t, lie_smul t x, },
  map_add'  := λ x y, by { ext m, apply add_lie, },
  map_smul' := λ t x, by { ext m, apply smul_lie, },
  map_lie'  := λ x y, by { ext m, apply lie_lie, }, }

/-- The adjoint action of a Lie algebra on itself. -/
def lie_algebra.ad : L →ₗ⁅R⁆ module.End R L := lie_module.to_endomorphism R L L

@[simp] lemma lie_algebra.ad_apply (x y : L) : lie_algebra.ad R L x y = ⁅x, y⁆ := rfl

open lie_algebra

lemma lie_algebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [ring A] [algebra R A] :
  (ad R A : A → module.End R A) = algebra.lmul_left R - algebra.lmul_right R :=
by { ext a b, simp [lie_ring.of_associative_ring_bracket], }

variables {R L}

lemma lie_subalgebra.ad_comp_incl_eq (K : lie_subalgebra R L) (x : K) :
  (ad R L ↑x).comp (K.incl : K →ₗ[R] L) = (K.incl : K →ₗ[R] L).comp (ad R K x) :=
begin
  ext y,
  simp only [ad_apply, lie_hom.coe_to_linear_map, lie_subalgebra.coe_incl, linear_map.coe_comp,
    lie_subalgebra.coe_bracket, function.comp_app],
end

end adjoint_action

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lie_subalgebra_of_subalgebra (R : Type u) [comm_ring R] (A : Type v) [ring A] [algebra R A]
  (A' : subalgebra R A) : lie_subalgebra R A :=
{ lie_mem' := λ x y hx hy, by {
    change ⁅x, y⁆ ∈ A', change x ∈ A' at hx, change y ∈ A' at hy,
    rw lie_ring.of_associative_ring_bracket,
    have hxy := A'.mul_mem hx hy,
    have hyx := A'.mul_mem hy hx,
    exact submodule.sub_mem A'.to_submodule hxy hyx, },
  ..A'.to_submodule }

namespace linear_equiv

variables {R : Type u} {M₁ : Type v} {M₂ : Type w}
variables [comm_ring R] [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]
variables (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lie_conj : module.End R M₁ ≃ₗ⁅R⁆ module.End R M₂ :=
{ map_lie' := λ f g, show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆,
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
{ to_fun   := e.to_fun,
  map_lie' := λ x y, by simp [lie_ring.of_associative_ring_bracket],
  ..e.to_linear_equiv }

@[simp] lemma to_lie_equiv_apply (x : A₁) : e.to_lie_equiv x = e x := rfl

@[simp] lemma to_lie_equiv_symm_apply (x : A₂) : e.to_lie_equiv.symm x = e.symm x := rfl

end alg_equiv
