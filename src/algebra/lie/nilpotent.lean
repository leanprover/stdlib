/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.solvable
import linear_algebra.eigenspace
import ring_theory.nilpotent

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `lie_module.lower_central_series`
  * `lie_module.is_nilpotent`

## Tags

lie algebra, lower central series, nilpotent
-/

universes u v w w₁ w₂

namespace lie_module

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

/-- The lower central series of Lie submodules of a Lie module. -/
def lower_central_series (k : ℕ) : lie_submodule R L M := (λ I, ⁅(⊤ : lie_ideal R L), I⁆)^[k] ⊤

@[simp] lemma lower_central_series_zero : lower_central_series R L M 0 = ⊤ := rfl

@[simp] lemma lower_central_series_succ (k : ℕ) :
  lower_central_series R L M (k + 1) = ⁅(⊤ : lie_ideal R L), lower_central_series R L M k⁆ :=
function.iterate_succ_apply' (λ I, ⁅(⊤ : lie_ideal R L), I⁆) k ⊤

lemma trivial_iff_lower_central_eq_bot : is_trivial L M ↔ lower_central_series R L M 1 = ⊥ :=
begin
  split; intros h,
  { erw [eq_bot_iff, lie_submodule.lie_span_le], rintros m ⟨x, n, hn⟩, rw [← hn, h.trivial], simp,},
  { rw lie_submodule.eq_bot_iff at h, apply is_trivial.mk, intros x m, apply h,
    apply lie_submodule.subset_lie_span, use [x, m], refl, },
end

lemma iterate_to_endomorphism_mem_lower_central_series (x : L) (m : M) (k : ℕ) :
  (to_endomorphism R L M x)^[k] m ∈ lower_central_series R L M k :=
begin
  induction k with k ih,
  { simp only [function.iterate_zero], },
  { simp only [lower_central_series_succ, function.comp_app, function.iterate_succ',
      to_endomorphism_apply_apply],
    exact lie_submodule.lie_mem_lie _ _ (lie_submodule.mem_top x) ih, },
end

open lie_algebra

lemma derived_series_le_lower_central_series (k : ℕ) :
  derived_series R L k ≤ lower_central_series R L L k :=
begin
  induction k with k h,
  { rw [derived_series_def, derived_series_of_ideal_zero, lower_central_series_zero],
    exact le_refl _, },
  { have h' : derived_series R L k ≤ ⊤, { by simp only [le_top], },
    rw [derived_series_def, derived_series_of_ideal_succ, lower_central_series_succ],
    exact lie_submodule.mono_lie _ _ _ _ h' h, },
end

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
class is_nilpotent : Prop :=
(nilpotent : ∃ k, lower_central_series R L M k = ⊥)

@[priority 100]
instance trivial_is_nilpotent [is_trivial L M] : is_nilpotent R L M :=
⟨by { use 1, change ⁅⊤, ⊤⁆ = ⊥, simp, }⟩

lemma nilpotent_endo_of_nilpotent_module [hM : is_nilpotent R L M] :
  ∃ (k : ℕ), ∀ (x : L), (to_endomorphism R L M x)^k = 0 :=
begin
  unfreezingI { obtain ⟨k, hM⟩ := hM, },
  use k,
  intros x, ext m,
  rw [linear_map.pow_apply, linear_map.zero_apply, ← @lie_submodule.mem_bot R L M, ← hM],
  exact iterate_to_endomorphism_mem_lower_central_series R L M x m k,
end

/-- For a nilpotent Lie module, the weight space of the 0 weight is the whole module.

This result will be used downstream to show that weight spaces are Lie submodules, at which time
it will be possible to state it in the language of weight spaces. -/
lemma infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [is_nilpotent R L M] :
  (⨅ (x : L), (to_endomorphism R L M x).maximal_generalized_eigenspace 0) = ⊤ :=
begin
  ext m,
  simp only [module.End.mem_maximal_generalized_eigenspace, submodule.mem_top, sub_zero, iff_true,
    zero_smul, submodule.mem_infi],
  intros x,
  obtain ⟨k, hk⟩ := nilpotent_endo_of_nilpotent_module R L M,
  use k, rw hk,
  exact linear_map.zero_apply m,
end

end lie_module

@[priority 100]
instance lie_algebra.is_solvable_of_is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [hL : lie_module.is_nilpotent R L L] :
  lie_algebra.is_solvable R L :=
begin
  obtain ⟨k, h⟩ : ∃ k, lie_module.lower_central_series R L L k = ⊥ := hL.nilpotent,
  use k, rw ← le_bot_iff at h ⊢,
  exact le_trans (lie_module.derived_series_le_lower_central_series R L k) h,
end

section nilpotent_algebras

variables (R : Type u) (L : Type v) (L' : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']

/-- We say a Lie algebra is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
abbreviation lie_algebra.is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] : Prop :=
lie_module.is_nilpotent R L L

open lie_algebra

lemma lie_algebra.nilpotent_ad_of_nilpotent_algebra [is_nilpotent R L] :
  ∃ (k : ℕ), ∀ (x : L), (ad R L x)^k = 0 :=
lie_module.nilpotent_endo_of_nilpotent_module R L L

/-- See also `lie_algebra.zero_root_space_eq_top_of_nilpotent`. -/
lemma lie_algebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [is_nilpotent R L] :
  (⨅ (x : L), (ad R L x).maximal_generalized_eigenspace 0) = ⊤ :=
lie_module.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L L

-- TODO Generalise the below to Lie modules if / when we define morphisms, equivs of Lie modules
-- covering a Lie algebra morphism of (possibly different) Lie algebras.

variables {R L L'}

open lie_module (lower_central_series)

lemma lie_ideal.lower_central_series_map_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
  lie_ideal.map f (lower_central_series R L L k) ≤ lower_central_series R L' L' k :=
begin
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero, le_top], },
  { simp only [lie_module.lower_central_series_succ],
    exact le_trans (lie_ideal.map_bracket_le f) (lie_submodule.mono_lie _ _ _ _ le_top ih), },
end

lemma lie_ideal.lower_central_series_map_eq (k : ℕ) {f : L →ₗ⁅R⁆ L'}
  (h : function.surjective f) :
  lie_ideal.map f (lower_central_series R L L k) = lower_central_series R L' L' k :=
begin
  have h' : (⊤ : lie_ideal R L).map f = ⊤,
  { rw ←f.ideal_range_eq_map,
    exact f.ideal_range_eq_top_of_surjective h, },
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero], exact h', },
  { simp only [lie_module.lower_central_series_succ, lie_ideal.map_bracket_eq f h, ih, h'], },
end

lemma function.injective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L'] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.injective f) : is_nilpotent R L :=
{ nilpotent :=
  begin
    tactic.unfreeze_local_instances, obtain ⟨k, hk⟩ := h₁,
    use k,
    apply lie_ideal.bot_of_map_eq_bot h₂, rw [eq_bot_iff, ← hk],
    apply lie_ideal.lower_central_series_map_le,
  end, }

lemma function.surjective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.surjective f) : is_nilpotent R L' :=
{ nilpotent :=
  begin
    tactic.unfreeze_local_instances, obtain ⟨k, hk⟩ := h₁,
    use k,
    rw [← lie_ideal.lower_central_series_map_eq k h₂, hk],
    simp only [lie_ideal.map_eq_bot_iff, bot_le],
  end, }

lemma lie_equiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
  is_nilpotent R L ↔ is_nilpotent R L' :=
begin
  split; introsI h,
  { exact e.symm.injective.lie_algebra_is_nilpotent, },
  { exact e.injective.lie_algebra_is_nilpotent, },
end

instance [h : lie_algebra.is_nilpotent R L] : lie_algebra.is_nilpotent R (⊤ : lie_subalgebra R L) :=
lie_subalgebra.top_equiv_self.nilpotent_iff_equiv_nilpotent.mpr h

end nilpotent_algebras

section of_associative

variables (R : Type u) {A : Type v} [comm_ring R] [ring A] [algebra R A]

lemma lie_algebra.ad_nilpotent_of_nilpotent {a : A} (h : is_nilpotent a) :
  is_nilpotent (lie_algebra.ad R A a) :=
begin
  rw lie_algebra.ad_eq_lmul_left_sub_lmul_right,
  have hl : is_nilpotent (algebra.lmul_left R a), { rwa algebra.is_nilpotent_lmul_left_iff, },
  have hr : is_nilpotent (algebra.lmul_right R a), { rwa algebra.is_nilpotent_lmul_right_iff, },
  exact (algebra.commute_lmul_left_right R a a).is_nilpotent_sub hl hr,
end

variables {R}

lemma lie_subalgebra.is_nilpotent_ad_of_is_nilpotent_ad {L : Type v} [lie_ring L] [lie_algebra R L]
  (K : lie_subalgebra R L) {x : K} (h : is_nilpotent (lie_algebra.ad R L ↑x)) :
  is_nilpotent (lie_algebra.ad R K x) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  exact linear_map.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn,
end

lemma lie_algebra.is_nilpotent_ad_of_is_nilpotent {L : lie_subalgebra R A} {x : L}
  (h : is_nilpotent (x : A)) : is_nilpotent (lie_algebra.ad R L x) :=
L.is_nilpotent_ad_of_is_nilpotent_ad $ lie_algebra.ad_nilpotent_of_nilpotent R h

end of_associative
