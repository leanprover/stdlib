/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import algebra.module.basic
import linear_algebra.finsupp
import linear_algebra.free_module

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `is_projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `is_projective.lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `is_projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `is_projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

We require that the module sits in at least as high a universe as the ring:
without this, free modules don't even exist,
and it's unclear if projective modules are even a useful notion.

## References

https://en.wikipedia.org/wiki/Projective_module

## TODO

- Direct sum of two projective modules is projective.
- Arbitrary sum of projective modules is projective.
- Any module admits a surjection from a projective module.

All of these should be relatively straightforward.

## Tags

projective module

-/

universes u v

/- The actual implementation we choose: `P` is projective if the natural surjection
   from the free `R`-module on `P` to `P` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
  if maps from the module lift along surjections. There are several other equivalent
  definitions. -/
class module.projective (R : Type u) [semiring R] (P : Type (max u v)) [add_comm_monoid P]
  [module R P] : Prop :=
(out : ∃ s : P →ₗ[R] (P →₀ R), function.left_inverse (finsupp.total P P R id) s)

namespace module

lemma projective_def {R : Type u} [semiring R] {P : Type (max u v)} [add_comm_monoid P]
  [module R P] : projective R P ↔
  (∃ s : P →ₗ[R] (P →₀ R), function.left_inverse (finsupp.total P P R id) s) :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

section semiring

variables {R : Type u} [semiring R] {P : Type (max u v)} [add_comm_monoid P] [module R P]
  {M : Type (max u v)} [add_comm_group M] [module R M] {N : Type*} [add_comm_group N] [module R N]

/-- A projective R-module has the property that maps from it lift along surjections. -/
theorem projective_lifting_property [h : projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N)
  (hf : function.surjective f) : ∃ (h : P →ₗ[R] M), f.comp h = g :=
begin
  /-
  Here's the first step of the proof.
  Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
  on a type `X`. The universal property `finsupp.total` says that to a map
  `X → N` from a type to an `R`-module, we get an associated R-module map
  `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
  `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
  a map `φ : (P →₀ R) →ₗ M`.
  -/
  let φ : (P →₀ R) →ₗ[R] M := finsupp.total _ _ _ (λ p, function.surj_inv hf (g p)),
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  cases h.out with s hs,
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s,
  ext p,
  conv_rhs {rw ← hs p},
  simp [φ, finsupp.total_apply, function.surj_inv_eq hf],
end

/-- A module which satisfies the universal property is projective. Note that the universe variables
in `huniv` are somewhat restricted. -/
theorem projective_of_lifting_property'
  -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
  (huniv : ∀ {M : Type (max v u)} {N : Type (max u v)} [add_comm_monoid M] [add_comm_monoid N],
    by exactI
    ∀ [module R M] [module R N],
    by exactI
    ∀ (f : M →ₗ[R] N) (g : P →ₗ[R] N),
  function.surjective f → ∃ (h : P →ₗ[R] M), f.comp h = g) :
  -- then `P` is projective.
  projective R P :=
begin
  -- let `s` be the universal map `(P →₀ R) →ₗ P` coming from the identity map `P →ₗ P`.
  obtain ⟨s, hs⟩ : ∃ (s : P →ₗ[R] P →₀ R),
    (finsupp.total P P R id).comp s = linear_map.id :=
    huniv (finsupp.total P P R (id : P → P)) (linear_map.id : P →ₗ[R] P) _,
  -- This `s` works.
  { use s,
    rwa linear_map.ext_iff at hs },
  { intro p,
    use finsupp.single p 1,
    simp },
end

end semiring

section ring

variables {R : Type u} [ring R] {P : Type (max u v)} [add_comm_group P] [module R P]

/-- A variant of `of_lifting_property'` when we're working over a `[ring R]`,
which only requires quantifying over modules with an `add_comm_group` instance. -/
theorem projective_of_lifting_property
  -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
  (huniv : ∀ {M : Type (max v u)} {N : Type (max u v)} [add_comm_group M] [add_comm_group N],
    by exactI
    ∀ [module R M] [module R N],
    by exactI
    ∀ (f : M →ₗ[R] N) (g : P →ₗ[R] N),
  function.surjective f → ∃ (h : P →ₗ[R] M), f.comp h = g) :
  -- then `P` is projective.
  projective R P :=
-- We could try and prove this *using* `of_lifting_property`,
-- but this quickly leads to typeclass hell,
-- so we just prove it over again.
begin
  -- let `s` be the universal map `(P →₀ R) →ₗ P` coming from the identity map `P →ₗ P`.
  obtain ⟨s, hs⟩ : ∃ (s : P →ₗ[R] P →₀ R),
    (finsupp.total P P R id).comp s = linear_map.id :=
    huniv (finsupp.total P P R (id : P → P)) (linear_map.id : P →ₗ[R] P) _,
  -- This `s` works.
  { use s,
    rwa linear_map.ext_iff at hs },
  { intro p,
    use finsupp.single p 1,
    simp },
end

/-- Free modules are projective. -/
theorem projective_of_basis {ι : Type*} (b : basis ι R P) : projective R P :=
begin
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ (λ i, finsupp.single (b i) (1 : R)),
  intro m,
  simp only [b.constr_apply, mul_one, id.def, finsupp.smul_single', finsupp.total_single,
    linear_map.map_finsupp_sum],
  exact b.total_repr m,
end

@[priority 100]
instance projective_of_free [module.free R P] : module.projective R P :=
projective_of_basis $ module.free.choose_basis R P

end ring

end module
