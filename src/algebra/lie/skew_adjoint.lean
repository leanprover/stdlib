/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.basic

/-!
# Lie algebras of skew-adjoint endomorphisms of a bilinear form

## Tags

lie algebra, skew-adjoint, bilinear form
-/

universes u v w w₁

section skew_adjoint_endomorphisms
open bilin_form

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variables (B : bilin_form R M)

lemma bilin_form.is_skew_adjoint_bracket (f g : module.End R M)
  (hf : f ∈ B.skew_adjoint_submodule) (hg : g ∈ B.skew_adjoint_submodule) :
  ⁅f, g⁆ ∈ B.skew_adjoint_submodule :=
begin
  rw mem_skew_adjoint_submodule at *,
  have hfg : is_adjoint_pair B B (f * g) (g * f), { rw ←neg_mul_neg g f, exact hf.mul hg, },
  have hgf : is_adjoint_pair B B (g * f) (f * g), { rw ←neg_mul_neg f g, exact hg.mul hf, },
  change bilin_form.is_adjoint_pair B B (f * g - g * f) (-(f * g - g * f)), rw neg_sub,
  exact hfg.sub hgf,
end

/-- Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomorphisms form a
Lie subalgebra of the Lie algebra of endomorphisms. -/
def skew_adjoint_lie_subalgebra : lie_subalgebra R (module.End R M) :=
{ lie_mem' := B.is_skew_adjoint_bracket, ..B.skew_adjoint_submodule }

variables {N : Type w} [add_comm_group N] [module R N] (e : N ≃ₗ[R] M)

/-- An equivalence of modules with bilinear forms gives equivalence of Lie algebras of skew-adjoint
endomorphisms. -/
def skew_adjoint_lie_subalgebra_equiv :
  skew_adjoint_lie_subalgebra (B.comp (↑e : N →ₗ[R] M) ↑e) ≃ₗ⁅R⁆ skew_adjoint_lie_subalgebra B :=
begin
  apply lie_algebra.equiv.of_subalgebras _ _ e.lie_conj,
  ext f,
  simp only [lie_subalgebra.mem_coe, submodule.mem_map_equiv, lie_subalgebra.mem_map_submodule,
    coe_coe],
  exact (bilin_form.is_pair_self_adjoint_equiv (-B) B e f).symm,
end

@[simp] lemma skew_adjoint_lie_subalgebra_equiv_apply
  (f : skew_adjoint_lie_subalgebra (B.comp ↑e ↑e)) :
  ↑(skew_adjoint_lie_subalgebra_equiv B e f) = e.lie_conj f :=
by simp [skew_adjoint_lie_subalgebra_equiv]

@[simp] lemma skew_adjoint_lie_subalgebra_equiv_symm_apply (f : skew_adjoint_lie_subalgebra B) :
  ↑((skew_adjoint_lie_subalgebra_equiv B e).symm f) = e.symm.lie_conj f :=
by simp [skew_adjoint_lie_subalgebra_equiv]

end skew_adjoint_endomorphisms

section skew_adjoint_matrices
open_locale matrix

variables {R : Type u} {n : Type w} [comm_ring R] [decidable_eq n] [fintype n]
variables (J : matrix n n R)

lemma matrix.lie_transpose (A B : matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ :=
show (A * B - B * A)ᵀ = (Bᵀ * Aᵀ - Aᵀ * Bᵀ), by simp

lemma matrix.is_skew_adjoint_bracket (A B : matrix n n R)
  (hA : A ∈ skew_adjoint_matrices_submodule J) (hB : B ∈ skew_adjoint_matrices_submodule J) :
  ⁅A, B⁆ ∈ skew_adjoint_matrices_submodule J :=
begin
  simp only [mem_skew_adjoint_matrices_submodule] at *,
  change ⁅A, B⁆ᵀ ⬝ J = J ⬝ -⁅A, B⁆, change Aᵀ ⬝ J = J ⬝ -A at hA, change Bᵀ ⬝ J = J ⬝ -B at hB,
  simp only [←matrix.mul_eq_mul] at *,
  rw [matrix.lie_transpose, lie_ring.of_associative_ring_bracket,
    lie_ring.of_associative_ring_bracket, sub_mul, mul_assoc, mul_assoc, hA, hB, ←mul_assoc,
    ←mul_assoc, hA, hB],
  noncomm_ring,
end

/-- The Lie subalgebra of skew-adjoint square matrices corresponding to a square matrix `J`. -/
def skew_adjoint_matrices_lie_subalgebra : lie_subalgebra R (matrix n n R) :=
{ lie_mem' := J.is_skew_adjoint_bracket, ..(skew_adjoint_matrices_submodule J) }

@[simp] lemma mem_skew_adjoint_matrices_lie_subalgebra (A : matrix n n R) :
  A ∈ skew_adjoint_matrices_lie_subalgebra J ↔ A ∈ skew_adjoint_matrices_submodule J :=
iff.rfl

/-- An invertible matrix `P` gives a Lie algebra equivalence between those endomorphisms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP`. -/
noncomputable def skew_adjoint_matrices_lie_subalgebra_equiv (P : matrix n n R) (h : is_unit P) :
  skew_adjoint_matrices_lie_subalgebra J ≃ₗ⁅R⁆ skew_adjoint_matrices_lie_subalgebra (Pᵀ ⬝ J ⬝ P) :=
lie_algebra.equiv.of_subalgebras _ _ (P.lie_conj h).symm
begin
  ext A,
  suffices : P.lie_conj h A ∈ skew_adjoint_matrices_submodule J ↔
    A ∈ skew_adjoint_matrices_submodule (Pᵀ ⬝ J ⬝ P),
  { simp only [lie_subalgebra.mem_coe, submodule.mem_map_equiv, lie_subalgebra.mem_map_submodule,
      coe_coe], exact this, },
  simp [matrix.is_skew_adjoint, J.is_adjoint_pair_equiv _ _ P h],
end

lemma skew_adjoint_matrices_lie_subalgebra_equiv_apply
  (P : matrix n n R) (h : is_unit P) (A : skew_adjoint_matrices_lie_subalgebra J) :
  ↑(skew_adjoint_matrices_lie_subalgebra_equiv J P h A) = P⁻¹ ⬝ ↑A ⬝ P :=
by simp [skew_adjoint_matrices_lie_subalgebra_equiv]

/-- An equivalence of matrix algebras commuting with the transpose endomorphisms restricts to an
equivalence of Lie algebras of skew-adjoint matrices. -/
def skew_adjoint_matrices_lie_subalgebra_equiv_transpose {m : Type w} [decidable_eq m] [fintype m]
  (e : matrix n n R ≃ₐ[R] matrix m m R) (h : ∀ A, (e A)ᵀ = e (Aᵀ)) :
  skew_adjoint_matrices_lie_subalgebra J ≃ₗ⁅R⁆ skew_adjoint_matrices_lie_subalgebra (e J) :=
lie_algebra.equiv.of_subalgebras _ _ e.to_lie_equiv
begin
  ext A,
  suffices : J.is_skew_adjoint (e.symm A) ↔ (e J).is_skew_adjoint A, by simpa [this],
  simp [matrix.is_skew_adjoint, matrix.is_adjoint_pair, ← matrix.mul_eq_mul,
    ← h, ← function.injective.eq_iff e.injective],
end

@[simp] lemma skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply
  {m : Type w} [decidable_eq m] [fintype m]
  (e : matrix n n R ≃ₐ[R] matrix m m R) (h : ∀ A, (e A)ᵀ = e (Aᵀ))
  (A : skew_adjoint_matrices_lie_subalgebra J) :
  (skew_adjoint_matrices_lie_subalgebra_equiv_transpose J e h A : matrix m m R) = e A :=
rfl

lemma mem_skew_adjoint_matrices_lie_subalgebra_unit_smul (u : units R) (J A : matrix n n R) :
  A ∈ skew_adjoint_matrices_lie_subalgebra ((u : R) • J) ↔
  A ∈ skew_adjoint_matrices_lie_subalgebra J :=
begin
  change A ∈ skew_adjoint_matrices_submodule ((u : R) • J) ↔  A ∈ skew_adjoint_matrices_submodule J,
  simp only [mem_skew_adjoint_matrices_submodule, matrix.is_skew_adjoint, matrix.is_adjoint_pair],
  split; intros h,
  { simpa using congr_arg (λ B, (↑u⁻¹ : R) • B) h, },
  { simp [h], },
end

end skew_adjoint_matrices
