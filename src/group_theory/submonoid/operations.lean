/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/

import group_theory.submonoid.basic
import data.equiv.mul_add
import algebra.group.prod
import algebra.group.inj_surj

/-!
# Operations on `submonoid`s

In this file we define various operations on `submonoid`s and `monoid_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `submonoid.to_add_submonoid`, `submonoid.to_add_submonoid'`, `add_submonoid.to_submonoid`,
  `add_submonoid.to_submonoid'`: convert between multiplicative and additive submonoids of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) monoid structure on a submonoid

* `submonoid.to_monoid`, `submonoid.to_comm_monoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids

* `submonoid.mul_action`, `submonoid.distrib_mul_action`: a submonoid inherits (distributive)
  multiplicative actions.

### Operations on submonoids

* `submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `submonoid.prod`: product of two submonoids `s : submonoid M` and `t : submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `mul_equiv.submonoid_congr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `submonoid.prod_equiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `monoid_hom`s

* `monoid_hom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.mrestrict`: restrict a monoid homomorphism to a submonoid;
* `monoid_hom.cod_mrestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `monoid_hom.mrange_restrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/

variables {M N P : Type*} [mul_one_class M] [mul_one_class N] [mul_one_class P] (S : submonoid M)

/-!
### Conversion to/from `additive`/`multiplicative`
-/

section

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
@[simps]
def submonoid.to_add_submonoid : submonoid M ≃o add_submonoid (additive M) :=
{ to_fun := λ S,
  { carrier := additive.to_mul ⁻¹' S,
    zero_mem' := S.one_mem',
    add_mem' := S.mul_mem' },
  inv_fun := λ S,
  { carrier := additive.of_mul ⁻¹' S,
    one_mem' := S.zero_mem',
    mul_mem' := S.add_mem' },
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl,
  map_rel_iff' := λ a b, iff.rfl, }

/-- Additive submonoids of an additive monoid `additive M` are isomorphic to submonoids of `M`. -/
abbreviation add_submonoid.to_submonoid' : add_submonoid (additive M) ≃o submonoid M :=
submonoid.to_add_submonoid.symm

lemma submonoid.to_add_submonoid_closure (S : set M) :
  (submonoid.closure S).to_add_submonoid = add_submonoid.closure (additive.to_mul ⁻¹' S) :=
le_antisymm
  (submonoid.to_add_submonoid.to_galois_connection.l_le $
    submonoid.closure_le.2 add_submonoid.subset_closure)
  (add_submonoid.closure_le.2 submonoid.subset_closure)

lemma add_submonoid.to_submonoid'_closure (S : set (additive M)) :
  (add_submonoid.closure S).to_submonoid' = submonoid.closure (multiplicative.of_add ⁻¹' S) :=
le_antisymm
  (add_submonoid.to_submonoid'.to_galois_connection.l_le $
    add_submonoid.closure_le.2 submonoid.subset_closure)
  (submonoid.closure_le.2 add_submonoid.subset_closure)

end

section

variables {A : Type*} [add_zero_class A]

/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `multiplicative A`. -/
@[simps]
def add_submonoid.to_submonoid : add_submonoid A ≃o submonoid (multiplicative A) :=
{ to_fun := λ S,
  { carrier := multiplicative.to_add ⁻¹' S,
    one_mem' := S.zero_mem',
    mul_mem' := S.add_mem' },
  inv_fun := λ S,
  { carrier := multiplicative.of_add ⁻¹' S,
    zero_mem' := S.one_mem',
    add_mem' := S.mul_mem' },
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl,
  map_rel_iff' := λ a b, iff.rfl, }

/-- Submonoids of a monoid `multiplicative A` are isomorphic to additive submonoids of `A`. -/
abbreviation submonoid.to_add_submonoid' : submonoid (multiplicative A) ≃o add_submonoid A :=
add_submonoid.to_submonoid.symm

lemma add_submonoid.to_submonoid_closure (S : set A) :
  (add_submonoid.closure S).to_submonoid = submonoid.closure (multiplicative.to_add ⁻¹' S) :=
le_antisymm
  (add_submonoid.to_submonoid.to_galois_connection.l_le $
    add_submonoid.closure_le.2 submonoid.subset_closure)
  (submonoid.closure_le.2 add_submonoid.subset_closure)

lemma submonoid.to_add_submonoid'_closure (S : set (multiplicative A)) :
  (submonoid.closure S).to_add_submonoid' = add_submonoid.closure (additive.of_mul ⁻¹' S) :=
le_antisymm
  (submonoid.to_add_submonoid'.to_galois_connection.l_le $
    submonoid.closure_le.2 add_submonoid.subset_closure)
  (add_submonoid.closure_le.2 submonoid.subset_closure)

end

namespace submonoid

open set

/-!
### `comap` and `map`
-/

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The preimage of an `add_submonoid` along an `add_monoid` homomorphism is an
`add_submonoid`."]
def comap (f : M →* N) (S : submonoid N) : submonoid M :=
{ carrier := (f ⁻¹' S),
  one_mem' := show f 1 ∈ S, by rw f.map_one; exact S.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

@[simp, to_additive]
lemma coe_comap (S : submonoid N) (f : M →* N) : (S.comap f : set M) = f ⁻¹' S := rfl

@[simp, to_additive]
lemma mem_comap {S : submonoid N} {f : M →* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

@[to_additive]
lemma comap_comap (S : submonoid P) (g : N →* P) (f : M →* N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

@[simp, to_additive]
lemma comap_id (S : submonoid P) : S.comap (monoid_hom.id _) = S :=
ext (by simp)

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The image of an `add_submonoid` along an `add_monoid` homomorphism is
an `add_submonoid`."]
def map (f : M →* N) (S : submonoid M) : submonoid N :=
{ carrier := (f '' S),
  one_mem' := ⟨1, S.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

@[simp, to_additive]
lemma coe_map (f : M →* N) (S : submonoid M) :
  (S.map f : set N) = f '' S := rfl

@[simp, to_additive]
lemma mem_map {f : M →* N} {S : submonoid M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

@[to_additive]
lemma mem_map_of_mem (f : M →* N) {S : submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
mem_image_of_mem f hx

@[to_additive]
lemma apply_coe_mem_map (f : M →* N) (S : submonoid M) (x : S) : f x ∈ S.map f :=
mem_map_of_mem f x.prop

@[to_additive]
lemma map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ image_image _ _ _

@[to_additive]
lemma map_le_iff_le_comap {f : M →* N} {S : submonoid M} {T : submonoid N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

@[to_additive]
lemma gc_map_comap (f : M →* N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

@[to_additive]
lemma map_le_of_le_comap {T : submonoid N} {f : M →* N} : S ≤ T.comap f → S.map f ≤ T :=
(gc_map_comap f).l_le

@[to_additive]
lemma le_comap_of_map_le {T : submonoid N} {f : M →* N} : S.map f ≤ T → S ≤ T.comap f :=
(gc_map_comap f).le_u

@[to_additive]
lemma le_comap_map {f : M →* N} : S ≤ (S.map f).comap f :=
(gc_map_comap f).le_u_l _

@[to_additive]
lemma map_comap_le {S : submonoid N} {f : M →* N} : (S.comap f).map f ≤ S :=
(gc_map_comap f).l_u_le _

@[to_additive]
lemma monotone_map {f : M →* N} : monotone (map f) :=
(gc_map_comap f).monotone_l

@[to_additive]
lemma monotone_comap {f : M →* N} : monotone (comap f) :=
(gc_map_comap f).monotone_u

@[simp, to_additive]
lemma map_comap_map {f : M →* N} : ((S.map f).comap f).map f = S.map f :=
congr_fun ((gc_map_comap f).l_u_l_eq_l) _

@[simp, to_additive]
lemma comap_map_comap {S : submonoid N} {f : M →* N} : ((S.comap f).map f).comap f = S.comap f :=
congr_fun ((gc_map_comap f).u_l_u_eq_u) _

@[to_additive]
lemma map_sup (S T : submonoid M) (f : M →* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

@[to_additive]
lemma map_supr {ι : Sort*} (f : M →* N) (s : ι → submonoid M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

@[to_additive]
lemma comap_inf (S T : submonoid N) (f : M →* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

@[to_additive]
lemma comap_infi {ι : Sort*} (f : M →* N) (s : ι → submonoid N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp, to_additive] lemma map_bot (f : M →* N) : (⊥ : submonoid M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp, to_additive] lemma comap_top (f : M →* N) : (⊤ : submonoid N).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp, to_additive] lemma map_id (S : submonoid M) : S.map (monoid_hom.id M) = S :=
ext (λ x, ⟨λ ⟨_, h, rfl⟩, h, λ h, ⟨_, h, rfl⟩⟩)

section galois_coinsertion

variables {ι : Type*} {f : M →* N} (hf : function.injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gci_map_comap : galois_coinsertion (map f) (comap f) :=
(gc_map_comap f).to_galois_coinsertion
  (λ S x, by simp [mem_comap, mem_map, hf.eq_iff])

lemma comap_map_eq_of_injective (S : submonoid M) : (S.map f).comap f = S :=
(gci_map_comap hf).u_l_eq _

lemma comap_surjective_of_injective : function.surjective (comap f) :=
(gci_map_comap hf).u_surjective

lemma map_injective_of_injective : function.injective (map f) :=
(gci_map_comap hf).l_injective

lemma comap_inf_map_of_injective (S T : submonoid M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
(gci_map_comap hf).u_inf_l _ _

lemma comap_infi_map_of_injective (S : ι → submonoid M) : (⨅ i, (S i).map f).comap f = infi S :=
(gci_map_comap hf).u_infi_l _

lemma comap_sup_map_of_injective (S T : submonoid M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
(gci_map_comap hf).u_sup_l _ _

lemma comap_supr_map_of_injective (S : ι → submonoid M) : (⨆ i, (S i).map f).comap f = supr S :=
(gci_map_comap hf).u_supr_l _

lemma map_le_map_iff_of_injective {S T : submonoid M} : S.map f ≤ T.map f ↔ S ≤ T :=
(gci_map_comap hf).l_le_l_iff

lemma map_strict_mono_of_injective : strict_mono (map f) :=
(gci_map_comap hf).strict_mono_l

end galois_coinsertion

section galois_insertion

variables {ι : Type*} {f : M →* N} (hf : function.surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def gi_map_comap : galois_insertion (map f) (comap f) :=
(gc_map_comap f).to_galois_insertion
  (λ S x h, let ⟨y, hy⟩ := hf x in mem_map.2 ⟨y, by simp [hy, h]⟩)

lemma map_comap_eq_of_surjective (S : submonoid N) : (S.comap f).map f = S :=
(gi_map_comap hf).l_u_eq _

lemma map_surjective_of_surjective : function.surjective (map f) :=
(gi_map_comap hf).l_surjective

lemma comap_injective_of_surjective : function.injective (comap f) :=
(gi_map_comap hf).u_injective

lemma map_inf_comap_of_surjective (S T : submonoid N) : (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
(gi_map_comap hf).l_inf_u _ _

lemma map_infi_comap_of_surjective (S : ι → submonoid N) : (⨅ i, (S i).comap f).map f = infi S :=
(gi_map_comap hf).l_infi_u _

lemma map_sup_comap_of_surjective (S T : submonoid N) : (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
(gi_map_comap hf).l_sup_u _ _

lemma map_supr_comap_of_surjective (S : ι → submonoid N) : (⨆ i, (S i).comap f).map f = supr S :=
(gi_map_comap hf).l_supr_u _

lemma comap_le_comap_iff_of_surjective {S T : submonoid N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
(gi_map_comap hf).u_le_u_iff

lemma comap_strict_mono_of_surjective : strict_mono (comap f) :=
(gi_map_comap hf).strict_mono_u

end galois_insertion

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an addition."]
instance has_mul : has_mul S := ⟨λ a b, ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance has_one : has_one S := ⟨⟨_, S.one_mem⟩⟩

@[simp, to_additive] lemma coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl
@[simp, to_additive] lemma coe_one : ((1 : S) : M) = 1 := rfl
attribute [norm_cast] coe_mul coe_one
attribute [norm_cast] add_submonoid.coe_add add_submonoid.coe_zero

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive "An `add_submonoid` of an unital additive magma inherits an unital additive magma
structure."]
instance to_mul_one_class {M : Type*} [mul_one_class M] (S : submonoid M) : mul_one_class S :=
subtype.coe_injective.mul_one_class coe rfl (λ _ _, rfl)

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`
structure."]
instance to_monoid {M : Type*} [monoid M] (S : submonoid M) : monoid S :=
subtype.coe_injective.monoid coe rfl (λ _ _, rfl)

/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `add_comm_monoid` is
an `add_comm_monoid`."]
instance to_comm_monoid {M} [comm_monoid M] (S : submonoid M) : comm_monoid S :=
subtype.coe_injective.comm_monoid coe rfl (λ _ _, rfl)

/-- A submonoid of an `ordered_comm_monoid` is an `ordered_comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `ordered_add_comm_monoid` is
an `ordered_add_comm_monoid`."]
instance to_ordered_comm_monoid {M} [ordered_comm_monoid M] (S : submonoid M) :
  ordered_comm_monoid S :=
subtype.coe_injective.ordered_comm_monoid coe rfl (λ _ _, rfl)

/-- A submonoid of a `linear_ordered_comm_monoid` is a `linear_ordered_comm_monoid`. -/
@[to_additive "An `add_submonoid` of a `linear_ordered_add_comm_monoid` is
a `linear_ordered_add_comm_monoid`."]
instance to_linear_ordered_comm_monoid {M} [linear_ordered_comm_monoid M] (S : submonoid M) :
  linear_ordered_comm_monoid S :=
subtype.coe_injective.linear_ordered_comm_monoid coe rfl (λ _ _, rfl)

/-- A submonoid of an `ordered_cancel_comm_monoid` is an `ordered_cancel_comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `ordered_cancel_add_comm_monoid` is
an `ordered_cancel_add_comm_monoid`."]
instance to_ordered_cancel_comm_monoid {M} [ordered_cancel_comm_monoid M] (S : submonoid M) :
  ordered_cancel_comm_monoid S :=
subtype.coe_injective.ordered_cancel_comm_monoid coe rfl (λ _ _, rfl)

/-- A submonoid of a `linear_ordered_cancel_comm_monoid` is a `linear_ordered_cancel_comm_monoid`.
-/
@[to_additive "An `add_submonoid` of a `linear_ordered_cancel_add_comm_monoid` is
a `linear_ordered_cancel_add_comm_monoid`."]
instance to_linear_ordered_cancel_comm_monoid {M} [linear_ordered_cancel_comm_monoid M]
  (S : submonoid M) : linear_ordered_cancel_comm_monoid S :=
subtype.coe_injective.linear_ordered_cancel_comm_monoid coe rfl (λ _ _, rfl)

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def subtype : S →* M := ⟨coe, rfl, λ _ _, rfl⟩

@[simp, to_additive] theorem coe_subtype : ⇑S.subtype = coe := rfl

/-- An induction principle on elements of the type `submonoid.closure s`.
If `p` holds for `1` and all elements of `s`, and is preserved under multiplication, then `p`
holds for all elements of the closure of `s`.

The difference with `submonoid.closure_induction` is that this acts on the subtype.
-/
@[to_additive "An induction principle on elements of the type `add_submonoid.closure s`.
If `p` holds for `0` and all elements of `s`, and is preserved under addition, then `p`
holds for all elements of the closure of `s`.

The difference with `add_submonoid.closure_induction` is that this acts on the subtype."]
lemma closure_induction' (s : set M) {p : closure s → Prop}
  (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_closure h⟩)
  (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (x : closure s) :
  p x :=
subtype.rec_on x $ λ x hx, begin
  refine exists.elim _ (λ (hx : x ∈ closure s) (hc : p ⟨x, hx⟩), hc),
  exact closure_induction hx
    (λ x hx, ⟨subset_closure hx, Hs x hx⟩)
    ⟨one_mem _, H1⟩
    (λ x y hx hy, exists.elim hx $ λ hx' hx, exists.elim hy $ λ hy' hy,
      ⟨mul_mem _ hx' hy', Hmul _ _ hx hy⟩),
end

attribute [elab_as_eliminator] submonoid.closure_induction' add_submonoid.closure_induction'

/-- Given `submonoid`s `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[to_additive prod "Given `add_submonoid`s `s`, `t` of `add_monoid`s `A`, `B` respectively, `s × t`
as an `add_submonoid` of `A × B`."]
def prod (s : submonoid M) (t : submonoid N) : submonoid (M × N) :=
{ carrier := (s : set M).prod t,
  one_mem' := ⟨s.one_mem, t.one_mem⟩,
  mul_mem' := λ p q hp hq, ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩ }

@[to_additive coe_prod]
lemma coe_prod (s : submonoid M) (t : submonoid N) :
 (s.prod t : set (M × N)) = (s : set M).prod (t : set N) :=
rfl

@[to_additive mem_prod]
lemma mem_prod {s : submonoid M} {t : submonoid N} {p : M × N} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[to_additive prod_mono]
lemma prod_mono {s₁ s₂ : submonoid M} {t₁ t₂ : submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
  s₁.prod t₁ ≤ s₂.prod t₂ :=
set.prod_mono hs ht

@[to_additive prod_top]
lemma prod_top (s : submonoid M) :
  s.prod (⊤ : submonoid N) = s.comap (monoid_hom.fst M N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

@[to_additive top_prod]
lemma top_prod (s : submonoid N) :
  (⊤ : submonoid M).prod s = s.comap (monoid_hom.snd M N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp, to_additive top_prod_top]
lemma top_prod_top : (⊤ : submonoid M).prod (⊤ : submonoid N) = ⊤ :=
(top_prod _).trans $ comap_top _

@[to_additive] lemma bot_prod_bot : (⊥ : submonoid M).prod (⊥ : submonoid N) = ⊥ :=
set_like.coe_injective $ by simp [coe_prod, prod.one_eq_mk]

/-- The product of submonoids is isomorphic to their product as monoids. -/
@[to_additive prod_equiv "The product of additive submonoids is isomorphic to their product
as additive monoids"]
def prod_equiv (s : submonoid M) (t : submonoid N) : s.prod t ≃* s × t :=
{ map_mul' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

open monoid_hom

@[to_additive]
lemma map_inl (s : submonoid M) : s.map (inl M N) = s.prod ⊥ :=
ext $ λ p, ⟨λ ⟨x, hx, hp⟩, hp ▸ ⟨hx, set.mem_singleton 1⟩,
  λ ⟨hps, hp1⟩, ⟨p.1, hps, prod.ext rfl $ (set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]
lemma map_inr (s : submonoid N) : s.map (inr M N) = prod ⊥ s :=
ext $ λ p, ⟨λ ⟨x, hx, hp⟩, hp ▸ ⟨set.mem_singleton 1, hx⟩,
  λ ⟨hp1, hps⟩, ⟨p.2, hps, prod.ext (set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[simp, to_additive prod_bot_sup_bot_prod]
lemma prod_bot_sup_bot_prod (s : submonoid M) (t : submonoid N) :
  (s.prod ⊥) ⊔ (prod ⊥ t) = s.prod t :=
le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t))) $
assume p hp, prod.fst_mul_snd p ▸ mul_mem _
  ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, set.mem_singleton 1⟩)
  ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨set.mem_singleton 1, hp.2⟩)

end submonoid

namespace monoid_hom

open submonoid

/-- For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`set.range f`. In particular this means that the types `↥(set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`set.range` could have been defined as `f '' set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `set.range`, and that it introduces a redudant `x ∈ ⊤`
term which clutters proofs. In such a case one may resort to the `copy`
pattern. A `copy` function converts the definitional problem for the carrier set of a subobject
into a one-off propositional proof obligation which one discharges while writing the definition of
the definitionally convenient range (the parameter `hs` in the example below).

A good example is the case of a morphism of monoids. A convenient definition for
`monoid_hom.mrange` would be `(⊤ : submonoid M).map f`. However since this lacks the required
definitional convenience, we first define `submonoid.copy` as follows:
```lean
protected def copy (S : submonoid M) (s : set M) (hs : s = S) : submonoid M :=
{ carrier  := s,
  one_mem' := hs.symm ▸ S.one_mem',
  mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
def mrange (f : M →* N) : submonoid N :=
((⊤ : submonoid M).map f).copy (set.range f) set.image_univ.symm
```
-/
library_note "range copy pattern"

/-- The range of a monoid homomorphism is a submonoid. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_monoid_hom` is an `add_submonoid`."]
def mrange (f : M →* N) : submonoid N :=
((⊤ : submonoid M).map f).copy (set.range f) set.image_univ.symm

@[simp, to_additive]
lemma coe_mrange (f : M →* N) :
  (f.mrange : set N) = set.range f :=
rfl

@[simp, to_additive] lemma mem_mrange {f : M →* N} {y : N} :
  y ∈ f.mrange ↔ ∃ x, f x = y :=
iff.rfl

@[to_additive] lemma mrange_eq_map (f : M →* N) : f.mrange = (⊤ : submonoid M).map f :=
by ext; simp

@[to_additive]
lemma map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = (g.comp f).mrange :=
by simpa only [mrange_eq_map] using (⊤ : submonoid M).map_map g f

@[to_additive]
lemma mrange_top_iff_surjective {N} [mul_one_class N] {f : M →* N} :
  f.mrange = (⊤ : submonoid N) ↔ function.surjective f :=
set_like.ext'_iff.trans $ iff.trans (by rw [coe_mrange, coe_top]) set.range_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
lemma mrange_top_of_surjective {N} [mul_one_class N] (f : M →* N) (hf : function.surjective f) :
  f.mrange = (⊤ : submonoid N) :=
mrange_top_iff_surjective.2 hf

@[to_additive]
lemma mclosure_preimage_le (f : M →* N) (s : set N) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[to_additive "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals
the `add_submonoid` generated by the image of the set."]
lemma map_mclosure (f : M →* N) (s : set M) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (mclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[to_additive "Restriction of an add_monoid hom to an `add_submonoid` of the domain."]
def mrestrict {N : Type*} [mul_one_class N] (f : M →* N) (S : submonoid M) : S →* N :=
f.comp S.subtype

@[simp, to_additive]
lemma mrestrict_apply {N : Type*} [mul_one_class N] (f : M →* N) (x : S) : f.mrestrict S x = f x :=
rfl

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[to_additive "Restriction of an `add_monoid` hom to an `add_submonoid` of the codomain.", simps]
def cod_mrestrict (f : M →* N) (S : submonoid N) (h : ∀ x, f x ∈ S) : M →* S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_one' := subtype.eq f.map_one,
  map_mul' := λ x y, subtype.eq (f.map_mul x y) }

/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
@[to_additive "Restriction of an `add_monoid` hom to its range interpreted as a submonoid."]
def mrange_restrict {N} [mul_one_class N] (f : M →* N) : M →* f.mrange :=
f.cod_mrestrict f.mrange $ λ x, ⟨x, rfl⟩

@[simp, to_additive]
lemma coe_mrange_restrict {N} [mul_one_class N] (f : M →* N) (x : M) :
  (f.mrange_restrict x : N) = f x :=
rfl

end monoid_hom

namespace submonoid
open monoid_hom

@[to_additive]
lemma mrange_inl : (inl M N).mrange = prod ⊤ ⊥ :=
by simpa only [mrange_eq_map] using map_inl ⊤

@[to_additive]
lemma mrange_inr : (inr M N).mrange = prod ⊥ ⊤ :=
by simpa only [mrange_eq_map] using map_inr ⊤

@[to_additive]
lemma mrange_inl' : (inl M N).mrange = comap (snd M N) ⊥ := mrange_inl.trans (top_prod _)

@[to_additive]
lemma mrange_inr' : (inr M N).mrange = comap (fst M N) ⊥ := mrange_inr.trans (prod_top _)

@[simp, to_additive]
lemma mrange_fst : (fst M N).mrange = ⊤ :=
(fst M N).mrange_top_of_surjective $ @prod.fst_surjective _ _ ⟨1⟩

@[simp, to_additive]
lemma mrange_snd : (snd M N).mrange = ⊤ :=
(snd M N).mrange_top_of_surjective $ @prod.snd_surjective _ _ ⟨1⟩
@[simp, to_additive]

lemma mrange_inl_sup_mrange_inr : (inl M N).mrange ⊔ (inr M N).mrange = ⊤ :=
by simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]

/-- The monoid hom associated to an inclusion of submonoids. -/
@[to_additive "The `add_monoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : submonoid M} (h : S ≤ T) : S →* T :=
S.subtype.cod_mrestrict _ (λ x, h x.2)

@[simp, to_additive]
lemma range_subtype (s : submonoid M) : s.subtype.mrange = s :=
set_like.coe_injective $ (coe_mrange _).trans $ subtype.range_coe

@[to_additive] lemma eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
eq_top_iff.trans ⟨λ h m, h $ mem_top m, λ h m _, h m⟩

@[to_additive] lemma eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) :=
begin
  split,
  { intros h x x_in,
    rwa [h, mem_bot] at x_in },
  { intros h,
    ext x,
    rw mem_bot,
    exact ⟨h x, by { rintros rfl, exact S.one_mem }⟩ },
end

@[to_additive] lemma nontrivial_iff_exists_ne_one (S : submonoid M) :
  nontrivial S ↔ ∃ x ∈ S, x ≠ (1:M) :=
begin
  split,
  { introI h,
    rcases exists_ne (1 : S) with ⟨⟨h, h_in⟩, h_ne⟩,
    use [h, h_in],
    intro hyp,
    apply  h_ne,
    simpa [hyp] },
  { rintros ⟨x, x_in, hx⟩,
    apply nontrivial_of_ne (⟨x, x_in⟩ : S) 1,
    intro hyp,
    apply hx,
    simpa [has_one.one] using hyp },
end

/-- A submonoid is either the trivial submonoid or nontrivial. -/
@[to_additive] lemma bot_or_nontrivial (S : submonoid M) : S = ⊥ ∨ nontrivial S :=
begin
  classical,
  by_cases h : ∀ x ∈ S, x = (1 : M),
  { left,
    exact S.eq_bot_iff_forall.mpr h },
  { right,
    push_neg at h,
    simpa [nontrivial_iff_exists_ne_one] using h },
end

/-- A submonoid is either the trivial submonoid or contains a nonzero element. -/
@[to_additive] lemma bot_or_exists_ne_one (S : submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1:M) :=
begin
  convert S.bot_or_nontrivial,
  rw nontrivial_iff_exists_ne_one
end

end submonoid

namespace mul_equiv

variables {S} {T : submonoid M}

/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
    monoid are equal. -/
@[to_additive "Makes the identity additive isomorphism from a proof two
submonoids of an additive monoid are equal."]
def submonoid_congr (h : S = T) : S ≃* T :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ congr_arg _ h }

-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.

This is a bidirectional version of `monoid_hom.mrange_restrict`. -/
@[to_additive /-"
A additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive
equivalence between `M` and `f.mrange`.

This is a bidirectional version of `add_monoid_hom.mrange_restrict`. "-/, simps {simp_rhs := tt}]
def of_left_inverse' (f : M →* N) {g : N → M} (h : function.left_inverse g f) : M ≃* f.mrange :=
{ to_fun := f.mrange_restrict,
  inv_fun := g ∘ f.mrange.subtype,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := monoid_hom.mem_mrange.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. f.mrange_restrict }

end mul_equiv

/-! ### Actions by `submonoid`s

These instances tranfer the action by an element `m : M` of a monoid `M` written as `m • a` onto the
action by an element `s : S` of a submonoid `S : submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `monoid.to_mul_action`, enabling
`s • m` as an alias for `↑s * m`.
-/
section actions

namespace submonoid

variables {M' : Type*} {α β : Type*} [monoid M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive /-"The additive action by an add_submonoid is the action by the underlying
add_monoid. "-/]
instance [mul_action M' α] (S : submonoid M') : mul_action S α :=
mul_action.comp_hom _ S.subtype

@[to_additive]
lemma smul_def [mul_action M' α] {S : submonoid M'} (g : S) (m : α) : g • m = (g : M') • m := rfl

/-- The action by a submonoid is the action by the underlying monoid. -/
instance [add_monoid α] [distrib_mul_action M' α] (S : submonoid M') : distrib_mul_action S α :=
distrib_mul_action.comp_hom _ S.subtype

@[to_additive]
instance smul_comm_class_left
  [mul_action M' β] [has_scalar α β] [smul_comm_class M' α β] (S : submonoid M') :
  smul_comm_class S α β :=
⟨λ a, (smul_comm (a : M') : _)⟩

@[to_additive]
instance smul_comm_class_right
  [has_scalar α β] [mul_action M' β] [smul_comm_class α M' β] (S : submonoid M') :
  smul_comm_class α S β :=
⟨λ a s, (smul_comm a (s : M') : _)⟩

/-- Note that this provides `is_scalar_tower S M' M'` which is needed by `smul_mul_assoc`. -/
instance
  [has_scalar α β] [mul_action M' α] [mul_action M' β] [is_scalar_tower M' α β] (S : submonoid M') :
  is_scalar_tower S α β :=
⟨λ a, (smul_assoc (a : M') : _)⟩

example {S : submonoid M'} : is_scalar_tower S M' M' := by apply_instance

end submonoid

end actions
