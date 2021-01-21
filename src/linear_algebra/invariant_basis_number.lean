/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import linear_algebra.finite_dimensional

/-!
# Invariant basis number property

We say that a ring `R` satisfies the invariant basis number property if there is a well-defined
notion of the rank of a finitely generated free (left) `R`-module. Since a finitely generated free
module with a basis consisting of `n` elements is linearly equivalent to `fin n → R`, it is
sufficient that `(fin n → R) ≃ₗ[R] (fin m → R)` implies `n = m`.

## Main definitions

`invariant_basis_number R` is a type class stating that `R` has the invariant basis number property.

## Main results

We show that every nontrivial commutative ring has the invariant basis number property.

## Future work

So far, there is no API at all for the `invariant_basis_number` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or prividing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `cardinal.mk ι = cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number

## Tags

free module, rank, invariant basis number, IBN

-/

noncomputable theory

open_locale classical big_operators

universes u v w

section
variables (R : Type u) [ring R]

/-- We say that `R` has the invariant basis number property if `(fin n → R) ≃ₗ[R] (fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class invariant_basis_number : Prop :=
(eq_of_fin_equiv : ∀ {n m : ℕ}, ((fin n → R) ≃ₗ[R] (fin m → R)) → n = m)

end

section
variables (R : Type u) [ring R] [invariant_basis_number R]

lemma eq_of_fin_equiv {n m : ℕ} : ((fin n → R) ≃ₗ[R] (fin m → R)) → n = m :=
invariant_basis_number.eq_of_fin_equiv

lemma nontrivial_of_invariant_basis_number : nontrivial R :=
begin
  by_contra h,
  refine zero_ne_one (eq_of_fin_equiv R _),
  haveI := not_nontrivial_iff_subsingleton.1 h,
  haveI : subsingleton (fin 1 → R) := ⟨λ a b, funext $ λ x, subsingleton.elim _ _⟩,
  refine { .. }; { intros, exact 0 } <|> tidy
end

end

section
open finite_dimensional

/-- A field has invariant basis number. This will be superseded below by the fact that any nonzero
    commutative ring has invariant basis number. -/
lemma invariant_basis_number_field {K : Type u} [field K] : invariant_basis_number K :=
⟨λ n m e,
  calc n = fintype.card (fin n) : eq.symm $ fintype.card_fin n
     ... = findim K (fin n → K) : eq.symm $ findim_eq_card_basis (pi.is_basis_fun K (fin n))
     ... = findim K (fin m → K) : linear_equiv.findim_eq e
     ... = fintype.card (fin m) : findim_eq_card_basis (pi.is_basis_fun K (fin m))
     ... = m                    : fintype.card_fin m⟩

end

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `ideal.pi_quot_equiv` and is located in the file `ring_theory/ideals.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/

section
variables {R : Type u} [comm_ring R] (I : ideal R) {ι : Type v} [fintype ι] {ι' : Type w}

/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
private def induced_map (I : ideal R) (e : (ι → R) →ₗ[R] (ι' → R)) :
  (I.pi ι).quotient → (I.pi ι').quotient :=
λ x, quotient.lift_on' x (λ y, ideal.quotient.mk _ (e y))
begin
  refine λ a b hab, ideal.quotient.eq.2 (λ h, _),
  rw ←linear_map.map_sub,
  exact ideal.map_pi _ _ hab e h,
end

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
private def induced_equiv [fintype ι'] (I : ideal R) (e : (ι → R) ≃ₗ[R] (ι' → R)) :
  (I.pi ι).quotient ≃ₗ[I.quotient] (I.pi ι').quotient :=
begin
  refine { to_fun := induced_map I e, inv_fun := induced_map I e.symm, .. },
  all_goals { rintro ⟨a⟩ ⟨b⟩ <|> rintro ⟨a⟩,
    change ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr, simp }
end

end

section
local attribute [instance] invariant_basis_number_field
local attribute [instance, priority 1] ideal.quotient.field

/-- Nontrivial commutative rings have the invariant basis number property. -/
@[priority 100]
instance invariant_basis_number_of_nontrivial_of_comm_ring {R : Type u} [comm_ring R]
  [nontrivial R] : invariant_basis_number R :=
⟨λ n m e, let ⟨I, ⟨hI, hI'⟩⟩ := ideal.exists_le_maximal (⊥ : ideal R) submodule.bot_ne_top in
  by exactI eq_of_fin_equiv I.quotient
    ((ideal.pi_quot_equiv _ _).symm.trans ((induced_equiv _ e).trans (ideal.pi_quot_equiv _ _)))⟩

end
