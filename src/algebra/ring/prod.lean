/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Chris Hughes, Mario Carneiro, Yury Kudryashov
-/
import algebra.group.prod
import data.equiv.ring

/-!
# Semiring, ring etc structures on `R × S`

In this file we define two-binop (`semiring`, `ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `ring_hom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* R`: projections `prod.fst` and `prod.snd`
  as `ring_hom`s;
* `f.prod g : `R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : `R × S → R' × S'`: `prod.map f g` as a `ring_hom`,
  sends `(x, y)` to `(f x, g y)`.
-/

variables {R : Type*} {R' : Type*} {S : Type*} {S' : Type*} {T : Type*} {T' : Type*}

namespace prod

/-- Product of two semirings is a semiring. -/
instance [semiring R] [semiring S] : semiring (R × S) :=
{ zero_mul := λ a, mk.inj_iff.mpr ⟨zero_mul _, zero_mul _⟩,
  mul_zero := λ a, mk.inj_iff.mpr ⟨mul_zero _, mul_zero _⟩,
  left_distrib := λ a b c, mk.inj_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _⟩,
  right_distrib := λ a b c, mk.inj_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _⟩,
  .. prod.add_comm_monoid, .. prod.monoid }

/-- Product of two commutative semirings is a commutative semiring. -/
instance [comm_semiring R] [comm_semiring S] : comm_semiring (R × S) :=
{ .. prod.semiring, .. prod.comm_monoid }

/-- Product of two rings is a ring. -/
instance [ring R] [ring S] : ring (R × S) :=
{ .. prod.add_comm_group, .. prod.semiring }

/-- Product of two commutative rings is a commutative ring. -/
instance [comm_ring R] [comm_ring S] : comm_ring (R × S) :=
{ .. prod.ring, .. prod.comm_monoid }

end prod

namespace ring_hom

variables (R S) [semiring R] [semiring S]

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`.-/
def fst : R × S →+* R := { to_fun := prod.fst, .. monoid_hom.fst R S, .. add_monoid_hom.fst R S }

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`.-/
def snd : R × S →+* S := { to_fun := prod.snd, .. monoid_hom.snd R S, .. add_monoid_hom.snd R S }

variables {R S}

@[simp] lemma coe_fst : ⇑(fst R S) = prod.fst := rfl
@[simp] lemma coe_snd : ⇑(snd R S) = prod.snd := rfl

section prod

variables [semiring T] (f : R →+* S) (g : R →+* T)

/-- Combine two ring homomorphisms `f : R →+* S`, `g : R →+* T` into `f.prod g : R →+* S × T`
given by `(f.prod g) x = (f x, g x)` -/
protected def prod (f : R →+* S) (g : R →+* T) : R →+* S × T :=
{ to_fun := λ x, (f x, g x),
  .. monoid_hom.prod (f : R →* S) (g : R →* T), .. add_monoid_hom.prod (f : R →+ S) (g : R →+ T) }

@[simp] lemma prod_apply (x) : f.prod g x = (f x, g x) := rfl

@[simp] lemma fst_comp_prod : (fst S T).comp (f.prod g) = f :=
ext $ λ x, rfl

@[simp] lemma snd_comp_prod : (snd S T).comp (f.prod g) = g :=
ext $ λ x, rfl

lemma prod_unique (f : R →+* S × T) :
  ((fst S T).comp f).prod ((snd S T).comp f) = f :=
ext $ λ x, by simp only [prod_apply, coe_fst, coe_snd, comp_apply, prod.mk.eta]

end prod

section prod_map

variables [semiring R'] [semiring S'] [semiring T] (f : R →+* R') (g : S →+* S')

/-- `prod.map` as a `ring_hom`. -/
def prod_map : R × S →* R' × S' := (f.comp (fst R S)).prod (g.comp (snd R S))

lemma prod_map_def : prod_map f g = (f.comp (fst R S)).prod (g.comp (snd R S)) := rfl

@[simp]
lemma coe_prod_map : ⇑(prod_map f g) = prod.map f g := rfl

lemma prod_comp_prod_map (f : T →* R) (g : T →* S) (f' : R →* R') (g' : S →* S') :
  (f'.prod_map g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
rfl

end prod_map

end ring_hom

namespace ring_equiv
variables {R S} [semiring R] [semiring S]

/-- Swapping components as an equivalence of (semi)rings. -/
def prod_comm : R × S ≃+* S × R :=
{ ..add_equiv.prod_comm, ..mul_equiv.prod_comm }

@[simp] lemma coe_prod_comm : ⇑(prod_comm : R × S ≃+* S × R) = prod.swap := rfl
@[simp] lemma coe_prod_comm_symm : ⇑((prod_comm : R × S ≃+* S × R).symm) = prod.swap := rfl

@[simp] lemma fst_comp_coe_prod_comm :
  (ring_hom.fst S R).comp ↑(prod_comm : R × S ≃+* S × R) = ring_hom.snd R S :=
ring_hom.ext $ λ _, rfl

@[simp] lemma snd_comp_coe_prod_comm :
  (ring_hom.snd S R).comp ↑(prod_comm : R × S ≃+* S × R) = ring_hom.fst R S :=
ring_hom.ext $ λ _, rfl

end ring_equiv
