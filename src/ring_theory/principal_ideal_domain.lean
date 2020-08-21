/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes, Morenikeji Neri
-/
import ring_theory.noetherian
import ring_theory.unique_factorization_domain
/-!
# Principal ideal rings and principal ideal domains

A principal ideal ring (PIR) is a commutative ring in which all ideals are principal. A
principal ideal domain (PID) is an integral domain which is a principal ideal ring.

# Main definitions

Note that for principal ideal domains, one should use
`[integral domain R] [is_principal_ideal_ring R]`. There is no explicit definition of a PID.
Theorems about PID's are in the `principal_ideal_ring` namespace.

- `is_principal_ideal_ring`: a predicate on commutative rings, saying that every
  ideal is principal.
- `generator`: a generator of a principal ideal (or more generally submodule)
- `to_unique_factorization_domain`: a noncomputable definition, putting a UFD structure on a PID.
  Note that the definition of a UFD is currently not a predicate, as it contains data
  of factorizations of non-zero elements.

# Main results

- `to_maximal_ideal`: a non-zero prime ideal in a PID is maximal.
- `euclidean_domain.to_principal_ideal_domain` : a Euclidean domain is a PID.

-/
universes u v
variables {R : Type u} {M : Type v}

open set function
open submodule
open_locale classical

/-- An `R`-submodule of `M` is principal if it is generated by one element. -/
class submodule.is_principal [ring R] [add_comm_group M] [module R M] (S : submodule R M) : Prop :=
(principal [] : ∃ a, S = span R {a})

/-- A commutative ring is a principal ideal ring if all ideals are principal. -/
class is_principal_ideal_ring (R : Type u) [comm_ring R] : Prop :=
(principal : ∀ (S : ideal R), S.is_principal)

attribute [instance] is_principal_ideal_ring.principal

namespace submodule.is_principal

variables [comm_ring R] [add_comm_group M] [module R M]

/-- `generator I`, if `I` is a principal submodule, is the `x ∈ M` such that `span R {x} = I` -/
noncomputable def generator (S : submodule R M) [S.is_principal] : M :=
classical.some (principal S)

lemma span_singleton_generator (S : submodule R M) [S.is_principal] : span R {generator S} = S :=
eq.symm (classical.some_spec (principal S))

@[simp] lemma generator_mem (S : submodule R M) [S.is_principal] : generator S ∈ S :=
by { conv_rhs { rw ← span_singleton_generator S }, exact subset_span (mem_singleton _) }

lemma mem_iff_eq_smul_generator (S : submodule R M) [S.is_principal] {x : M} :
  x ∈ S ↔ ∃ s : R, x = s • generator S :=
by simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]

lemma mem_iff_generator_dvd (S : ideal R) [S.is_principal] {x : R} : x ∈ S ↔ generator S ∣ x :=
(mem_iff_eq_smul_generator S).trans (exists_congr (λ a, by simp only [mul_comm, smul_eq_mul]))

lemma eq_bot_iff_generator_eq_zero (S : submodule R M) [S.is_principal] :
  S = ⊥ ↔ generator S = 0 :=
by rw [← @span_singleton_eq_bot R M, span_singleton_generator]

end submodule.is_principal

namespace is_prime
open submodule.is_principal ideal

-- TODO -- for a non-ID should prove that if p < q then q maximal; 0 isn't prime in a non-ID
lemma to_maximal_ideal [integral_domain R] [is_principal_ideal_ring R] {S : ideal R}
  [hpi : is_prime S] (hS : S ≠ ⊥) : is_maximal S :=
is_maximal_iff.2 ⟨(ne_top_iff_one S).1 hpi.1, begin
  assume T x hST hxS hxT,
  cases (mem_iff_generator_dvd _).1 (hST $ generator_mem S) with z hz,
  cases hpi.2 (show generator T * z ∈ S, from hz ▸ generator_mem S),
  { have hTS : T ≤ S, rwa [← span_singleton_generator T, submodule.span_le, singleton_subset_iff],
    exact (hxS $ hTS hxT).elim },
  cases (mem_iff_generator_dvd _).1 h with y hy,
  have : generator S ≠ 0 := mt (eq_bot_iff_generator_eq_zero _).2 hS,
  rw [← mul_one (generator S), hy, mul_left_comm, mul_right_inj' this] at hz,
  exact hz.symm ▸ ideal.mul_mem_right _ (generator_mem T)
end⟩

end is_prime

section
open euclidean_domain
variable [euclidean_domain R]

lemma mod_mem_iff {S : ideal R} {x y : R} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
⟨λ hxy, div_add_mod x y ▸ ideal.add_mem S (ideal.mul_mem_right S hy) hxy,
  λ hx, (mod_eq_sub_mul_div x y).symm ▸ ideal.sub_mem S hx (ideal.mul_mem_right S hy)⟩

@[priority 100] -- see Note [lower instance priority]
instance euclidean_domain.to_principal_ideal_domain : is_principal_ideal_ring R :=
{ principal := λ S, by exactI
    ⟨if h : {x : R | x ∈ S ∧ x ≠ 0}.nonempty
    then
    have wf : well_founded (euclidean_domain.r : R → R → Prop) := euclidean_domain.r_well_founded,
    have hmin : well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h ∈ S ∧
        well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h ≠ 0,
      from well_founded.min_mem wf {x : R | x ∈ S ∧ x ≠ 0} h,
    ⟨well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h,
      submodule.ext $ λ x,
      ⟨λ hx, div_add_mod x (well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h) ▸
        (ideal.mem_span_singleton.2 $ dvd_add (dvd_mul_right _ _) $
        have (x % (well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h) ∉ {x : R | x ∈ S ∧ x ≠ 0}),
          from λ h₁, well_founded.not_lt_min wf _ h h₁ (mod_lt x hmin.2),
        have x % well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h = 0, by finish [(mod_mem_iff hmin.1).2 hx],
        by simp *),
      λ hx, let ⟨y, hy⟩ := ideal.mem_span_singleton.1 hx in hy.symm ▸ ideal.mul_mem_right _ hmin.1⟩⟩
    else ⟨0, submodule.ext $ λ a, by rw [← @submodule.bot_coe R R _ _ _, span_eq, submodule.mem_bot]; exact
      ⟨λ haS, by_contradiction $ λ ha0, h ⟨a, ⟨haS, ha0⟩⟩,
      λ h₁, h₁.symm ▸ S.zero_mem⟩⟩⟩ }

end

namespace principal_ideal_ring
open is_principal_ideal_ring

variables [integral_domain R] [is_principal_ideal_ring R]

@[priority 100] -- see Note [lower instance priority]
instance is_noetherian_ring : is_noetherian_ring R :=
⟨assume s : ideal R,
begin
  rcases (is_principal_ideal_ring.principal s).principal with ⟨a, rfl⟩,
  rw [← finset.coe_singleton],
  exact ⟨{a}, submodule.coe_injective rfl⟩
end⟩

lemma is_maximal_of_irreducible {p : R} (hp : irreducible p) :
  ideal.is_maximal (span R ({p} : set R)) :=
⟨mt ideal.span_singleton_eq_top.1 hp.1, λ I hI, begin
  rcases principal I with ⟨a, rfl⟩,
  erw ideal.span_singleton_eq_top,
  unfreezingI { rcases ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩ },
  refine (of_irreducible_mul hp).resolve_right (mt (λ hb, _) (not_le_of_lt hI)),
  erw [ideal.span_singleton_le_span_singleton, is_unit.mul_right_dvd hb]
end⟩

lemma irreducible_iff_prime {p : R} : irreducible p ↔ prime p :=
⟨λ hp, (ideal.span_singleton_prime hp.ne_zero).1 $
    (is_maximal_of_irreducible hp).is_prime,
  irreducible_of_prime⟩

lemma associates_irreducible_iff_prime : ∀{p : associates R}, irreducible p ↔ p.prime :=
associates.forall_associated.2 $ assume a,
by rw [associates.irreducible_mk_iff, associates.prime_mk, irreducible_iff_prime]

section
open_locale classical

/-- `factors a` is a multiset of irreducible elements whose product is `a`, up to units -/
noncomputable def factors (a : R) : multiset R :=
if h : a = 0 then ∅ else classical.some
  (is_noetherian_ring.exists_factors a h)

lemma factors_spec (a : R) (h : a ≠ 0) :
  (∀b∈factors a, irreducible b) ∧ associated a (factors a).prod :=
begin
  unfold factors, rw [dif_neg h],
  exact classical.some_spec
    (is_noetherian_ring.exists_factors a h)
end

/-- The unique factorization domain structure given by the principal ideal domain.

This is not added as type class instance, since the `factors` might be computed in a different way.
E.g. factors could return normalized values.
-/
noncomputable def to_unique_factorization_domain : unique_factorization_domain R :=
{ factors := factors,
  factors_prod := assume a ha, associated.symm (factors_spec a ha).2,
  prime_factors := assume a ha, by simpa [irreducible_iff_prime] using (factors_spec a ha).1 }

end

end principal_ideal_ring
