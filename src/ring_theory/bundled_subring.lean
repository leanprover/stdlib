/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Ashvni Narayanan
-/

import group_theory.subgroup
import ring_theory.subsemiring

/-!
# Subrings

Let `R` be a ring. This file defines the "bundled" subring type `subring R`, a type
whose terms correspond to subrings of `R`. This is the preferred way to talk
about subrings in mathlib. Unbundled subrings (`s : set R` and `is_subring s`)
are not in this file, and they will ultimately be deprecated.

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [ring R] (S : Type u) [ring S] (f g : R →+* S)`
`(A : subring R) (B : subring S) (s : set R)`

* `subring R` : the type of subrings of a ring `R`.

* `instance : complete_lattice (subring R)` : the complete lattice structure on the subrings.

* `subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `subring.gi` : `closure : set M → subring M` and coercion `coe : subring M → set M`
  form a `galois_insertion`.

* `closure s` : the minimal subring that includes the set `s`

* `comap f B : subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : subring (R × S)` : the product of subring

* `f.range : subring B` : the range of the ring homomorphism `f`.

* `eq_locus f g : subring R` : given ring homomorphisms `f`, `g`,
     the subring of `R` where `f x = g x`

## Implementation notes

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/

open_locale big_operators
universes u v w

open group
variables {R : Type u} {S : Type v} {T : Type w} [ring R] [ring S] [ring T]

set_option old_structure_cmd true

/-- `subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a multiplicative
submonoid and an additive subgroup. Note in particular that it shares the same 0 and 1 as R -/
structure subring (R : Type u) [ring R] extends submonoid R, add_subgroup R

/-- Reinterpret a `subring` as a `submonoid`. -/
add_decl_doc subring.to_submonoid

/-- Reinterpret a `subring` as an `add_subgroup`. -/
add_decl_doc subring.to_add_subgroup

namespace subring

instance : has_coe (subring R) (set R) := ⟨subring.carrier⟩

instance : has_coe_to_sort (subring R) := ⟨Type*, λ S, S.carrier⟩

instance : has_mem R (subring R) := ⟨λ m S, m ∈ (S:set R)⟩

/-- Construct a `subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : set R) (sm : submonoid R) (hm : ↑sm = s)
  (sa : add_subgroup R) (ha : ↑sa = s) :
  subring R :=
{ carrier := s,
  zero_mem' := ha ▸ sa.zero_mem,
  one_mem' := hm ▸ sm.one_mem,
  add_mem' := λ x y, by simpa only [← ha] using sa.add_mem,
  mul_mem' := λ x y, by simpa only [← hm] using sm.mul_mem,
  neg_mem' := λ x, by simpa only [← ha] using sa.neg_mem, }

@[simp] lemma coe_mk' {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa = s) :
  (subring.mk' s sm hm sa ha : set R) = s := rfl

@[simp] lemma mem_mk' {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa = s) {x : R} :
  x ∈ subring.mk' s sm hm sa ha ↔ x ∈ s :=
iff.rfl

@[simp] lemma mk'_to_submonoid {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa = s) :
  (subring.mk' s sm hm sa ha).to_submonoid = sm :=
submonoid.ext' hm.symm

@[simp] lemma mk'_to_add_subgroup {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa  =s) :
  (subring.mk' s sm hm sa ha).to_add_subgroup = sa :=
add_subgroup.ext' ha.symm

end subring

protected lemma subring.exists {s : subring R} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

protected lemma subring.forall {s : subring R} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

namespace subring

variables (s : subring R)

/-- Two subrings are equal if the underlying subsets are equal. -/
theorem ext' ⦃s t : subring R⦄ (h : (s : set R) = t) : s = t :=
by cases s; cases t; congr'

/-- Two subrings are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {s t : subring R}  : s = t ↔ (s : set R) = t :=
⟨λ h, h ▸ rfl, λ h, ext' h⟩

/-- Two subrings are equal if they have the same elements. -/
@[ext] theorem ext {S T : subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

/-- A subring contains the ring's 1. -/
theorem one_mem : (1 : R) ∈ s := s.one_mem'

/-- A subring contains the ring's 0. -/
theorem zero_mem : (0 : R) ∈ s := s.zero_mem'

/-- A subring is closed under multiplication. -/
theorem mul_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x * y ∈ s := s.mul_mem'

/-- A subring is closed under addition. -/
theorem add_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x + y ∈ s := s.add_mem'

/-- A subring is closed under negation. -/
theorem neg_mem : ∀ {x : R}, x ∈ s → -x ∈ s := s.neg_mem'

/-- Product of a list of elements in a subring is in the subring. -/
lemma list_prod_mem {l : list R} : (∀x ∈ l, x ∈ s) → l.prod ∈ s :=
s.to_submonoid.list_prod_mem

/-- Sum of a list of elements in a subring is in the subring. -/
lemma list_sum_mem {l : list R} : (∀x ∈ l, x ∈ s) → l.sum ∈ s :=
s.to_add_subgroup.list_sum_mem

/-- Product of a multiset of elements in a subring of a `comm_ring` is in the subring. -/
lemma multiset_prod_mem {R} [comm_ring R] (s : subring R) (m : multiset R) :
  (∀a ∈ m, a ∈ s) → m.prod ∈ s :=
s.to_submonoid.multiset_prod_mem m

/-- Sum of a multiset of elements in an `subring` of a `ring` is
in the `subring`. -/
lemma multiset_sum_mem {R} [ring R] (s : subring R) (m : multiset R) :
  (∀a ∈ m, a ∈ s) → m.sum ∈ s :=
s.to_add_subgroup.multiset_sum_mem m

/-- Product of elements of a subring of a `comm_ring` indexed by a `finset` is in the
    subring. -/
lemma prod_mem {R : Type*} [comm_ring R] (s : subring R)
  {ι : Type*} {t : finset ι} {f : ι → R} (h : ∀c ∈ t, f c ∈ s) :
  ∏ i in t, f i ∈ s :=
s.to_submonoid.prod_mem h

/-- Sum of elements in a `subring` of a `ring` indexed by a `finset`
is in the `subring`. -/
lemma sum_mem {R : Type*} [ring R] (s : subring R)
  {ι : Type*} {t : finset ι} {f : ι → R} (h : ∀c ∈ t, f c ∈ s) :
  ∑ i in t, f i ∈ s :=
s.to_add_subgroup.sum_mem h

lemma pow_mem {x : R} (hx : x ∈ s) (n : ℕ) : x^n ∈ s := s.to_submonoid.pow_mem hx n

lemma gsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) :
  n •ℤ x ∈ s := s.to_add_subgroup.gsmul_mem hx n

lemma coe_int_mem (n : ℤ) : (n : R) ∈ s :=
by simp only [← gsmul_one, gsmul_mem, one_mem]

/-- A subring of a ring inherits a ring structure -/
instance to_ring : ring s :=
{ right_distrib := λ x y z, subtype.eq $ right_distrib x y z,
  left_distrib := λ x y z, subtype.eq $ left_distrib x y z,
  .. s.to_submonoid.to_monoid, .. s.to_add_subgroup.to_add_comm_group }

@[simp, norm_cast] lemma coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_neg (x : s) : (↑(-x) : R) = -↑x := rfl
@[simp, norm_cast] lemma coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : s) : R) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : s) : R) = 1 := rfl

/-- A subring of a `comm_ring` is a `comm_ring`. -/
def to_comm_ring {R} [comm_ring R] (s : subring R) : comm_ring s :=
{ mul_comm := λ _ _, subtype.eq $ mul_comm _ _, ..subring.to_ring s}

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : subring R) : s →+* R :=
{ to_fun := coe,
 .. s.to_submonoid.subtype, .. s.to_add_subgroup.subtype
}

@[simp] theorem coe_subtype : ⇑s.subtype = coe := rfl

/-! # Partial order -/

instance : partial_order (subring R) :=
{ le := λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t,
  .. partial_order.lift (coe : subring R → set R) ext' }

lemma le_def {s t : subring R} : s ≤ t ↔ ∀ ⦃x : R⦄, x ∈ s → x ∈ t := iff.rfl

@[simp, norm_cast] lemma coe_subset_coe {s t : subring R} : (s : set R) ⊆ t ↔ s ≤ t := iff.rfl

@[simp, norm_cast] lemma coe_ssubset_coe {s t : subring R} : (s : set R) ⊂ t ↔ s < t := iff.rfl

@[simp, norm_cast]
lemma mem_coe {S : subring R} {m : R} : m ∈ (S : set R) ↔ m ∈ S := iff.rfl

@[simp, norm_cast]
lemma coe_coe (s : subring R) : ↥(s : set R) = s := rfl

@[simp] lemma mem_to_submonoid {s : subring R} {x : R} : x ∈ s.to_submonoid ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_submonoid (s : subring R) : (s.to_submonoid : set R) = s := rfl
@[simp] lemma mem_to_add_subgroup {s : subring R} {x : R} :
  x ∈ s.to_add_subgroup ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_add_subgroup (s : subring R) : (s.to_add_subgroup : set R) = s := rfl

/-! # top -/

/-- The subring `R` of the ring `R`. -/
instance : has_top (subring R) :=
⟨{ .. (⊤ : submonoid R), .. (⊤ : add_subgroup R) }⟩

@[simp] lemma mem_top (x : R) : x ∈ (⊤ : subring R) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : subring R) : set R) = set.univ := rfl

/-! # comap -/

/-- The preimage of a subring along a ring homomorphism is a subring. -/
def comap {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R →+* S) (s : subring S) : subring R :=
{ carrier := f ⁻¹' s.carrier,
 .. s.to_submonoid.comap (f : R →* S),
  .. s.to_add_subgroup.comap (f : R →+ S)
}

@[simp] lemma coe_comap (s : subring S) (f : R →+* S) : (s.comap f : set R) = f ⁻¹' s := rfl

@[simp]
lemma mem_comap {s : subring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s := iff.rfl

lemma comap_comap (s : subring T) (g : S →+* T) (f : R →+* S) :
  (s.comap g).comap f = s.comap (g.comp f) :=
rfl

/-! # map -/

/-- The image of a subring along a ring homomorphism is a subring. -/
def map {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R →+* S) (s : subring R) : subring S :=
  { carrier := f '' s.carrier,
.. s.to_submonoid.map (f : R →* S),
.. s.to_add_subgroup.map (f : R →+ S)
  }

@[simp] lemma coe_map (f : R →+* S) (s : subring R) : (s.map f : set S) = f '' s := rfl

@[simp] lemma mem_map {f : R →+* S} {s : subring R} {y : S} :
  y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
set.mem_image_iff_bex

lemma map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
ext' $ set.image_image _ _ _

lemma map_le_iff_le_comap {f : R →+* S} {s : subring R} {t : subring S} :
  s.map f ≤ t ↔ s ≤ t.comap f :=
set.image_subset_iff

lemma gc_map_comap (f : R →+* S) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

end subring

namespace ring_hom

variables (g : S →+* T) (f : R →+* S)

/-! # range -/

/-- The range of a ring homomorphism, as a subring of the target. -/
def range {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R →+* S) : subring S := (⊤ : subring R).map f

@[simp] lemma coe_range : (f.range : set S) = set.range f := set.image_univ

@[simp] lemma mem_range {f : R →+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
by simp [range]

lemma map_range : f.range.map g = (g.comp f).range :=
(⊤ : subring R).map_map g f

-- TODO -- rename to `cod_restrict` when is_ring_hom is deprecated
/-- Restrict the codomain of a ring homomorphism to a subring that includes the range. -/
def cod_restrict' {R : Type u} {S : Type v} [ring R] [ring S] (f : R →+* S)
  (s : subring S) (h : ∀ x, f x ∈ s) : R →+* s :=
{ to_fun := λ x, ⟨f x, h x⟩,
  map_add' := λ x y, subtype.eq $ f.map_add x y,
  map_zero' := subtype.eq f.map_zero,
  map_mul' := λ x y, subtype.eq $ f.map_mul x y,
  map_one' := subtype.eq f.map_one }

end ring_hom

namespace subring

variables {cR : Type u} [comm_ring cR]

/-- A subring of a commutative ring is a commutative ring. -/
def subset_comm_ring (S : subring cR) : comm_ring S :=
{mul_comm := λ _ _, subtype.eq $ mul_comm _ _, ..subring.to_ring S}

/-- A subring of an integral domain is an integral domain. -/
instance subring.domain {D : Type*} [integral_domain D] (S : subring D) : integral_domain S :=
{ exists_pair_ne := ⟨0, 1, mt subtype.ext_iff_val.1 zero_ne_one⟩,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ ⟨x, hx⟩ ⟨y, hy⟩,
    by { simp only [subtype.ext_iff_val, subtype.coe_mk], exact eq_zero_or_eq_zero_of_mul_eq_zero },
  .. S.subset_comm_ring, }

/-! # bot -/

instance : has_bot (subring R) := ⟨(int.cast_ring_hom R).range⟩

instance : inhabited (subring R) := ⟨⊥⟩

lemma coe_bot : ((⊥ : subring R) : set R) = set.range (coe : ℤ → R) := ring_hom.coe_range (int.cast_ring_hom R)

lemma mem_bot {x : R} : x ∈ (⊥ : subring R) ↔ ∃ (n : ℤ), ↑n = x :=  ring_hom.mem_range

/-! # inf -/

/-- The inf of two subrings is their intersection. -/
instance : has_inf (subring R) :=
⟨λ s t,
  { carrier := s ∩ t,
    .. s.to_submonoid ⊓ t.to_submonoid,
    .. s.to_add_subgroup ⊓ t.to_add_subgroup }⟩

@[simp] lemma coe_inf (p p' : subring R) : ((p ⊓ p' : subring R) : set R) = p ∩ p' := rfl

@[simp] lemma mem_inf {p p' : subring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (subring R) :=
⟨λ s, subring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, subring.to_submonoid t) (by simp)
  (⨅ t ∈ s, subring.to_add_subgroup t) (by simp)⟩

@[simp, norm_cast] lemma coe_Inf (S : set (subring R)) :
  ((Inf S : subring R) : set R) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (subring R)} {x : R} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

@[simp] lemma Inf_to_submonoid (s : set (subring R)) :
  (Inf s).to_submonoid = ⨅ t ∈ s, subring.to_submonoid t := mk'_to_submonoid _ _

@[simp] lemma Inf_to_add_subgroup (s : set (subring R)) :
  (Inf s).to_add_subgroup = ⨅ t ∈ s, subring.to_add_subgroup t := mk'_to_add_subgroup _ _

/-- Subrings of a ring form a complete lattice. -/
instance : complete_lattice (subring R) :=
{ bot := (⊥),
  bot_le := λ s x hx, let ⟨n, hn⟩ := mem_bot.1 hx in hn ▸ s.coe_int_mem n,
  top := (⊤),
  le_top := λ s x hx, trivial,
  inf := (⊓),
  inf_le_left := λ s t x, and.left,
  inf_le_right := λ s t x, and.right,
  le_inf := λ s t₁ t₂ h₁ h₂ x hx, ⟨h₁ hx, h₂ hx⟩,
  .. complete_lattice_of_Inf (subring R)
    (λ s, is_glb.of_image (λ s t, show (s : set R) ≤ t ↔ s ≤ t, from coe_subset_coe) is_glb_binfi)}

/-! # subring closure of a subset -/

/-- The `subring` generated by a set. -/
def closure (s : set R) : subring R := Inf {S | s ⊆ S}

lemma mem_closure {x : R} {s : set R} : x ∈ closure s ↔ ∀ S : subring R, s ⊆ S → x ∈ S :=
mem_Inf

/-- The subring generated by a set includes the set. -/
@[simp] lemma subset_closure {s : set R} : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

/-- A subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
lemma closure_le {s : set R} {t : subring R} : closure s ≤ t ↔ s ⊆ t :=
⟨set.subset.trans subset_closure, λ h, Inf_le h⟩

/-- Subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
lemma closure_mono ⦃s t : set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ set.subset.trans h subset_closure

lemma closure_eq_of_le {s : set R} {t : subring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
  closure s = t :=
le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_eliminator]
lemma closure_induction {s : set R} {p : R → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0) (H1 : p 1)
  (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hneg : ∀ (x : R), p x → p (-x))
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul, H0, Hadd, Hneg⟩).2 Hs h

lemma mem_closure_iff {s : set R} {x} :
  x ∈ closure s ↔ x ∈ add_subgroup.closure (submonoid.closure s : set R) :=
⟨ λ h, closure_induction h (λ x hx, add_subgroup.subset_closure $ submonoid.subset_closure hx )
 (add_subgroup.zero_mem _)
 (add_subgroup.subset_closure ( submonoid.one_mem (submonoid.closure s)) )
 (λ x y hx hy, add_subgroup.add_mem _ hx hy )
 (λ x hx, add_subgroup.neg_mem _ hx )
 ( λ x y hx hy, add_subgroup.closure_induction hy
  (λ q hq, add_subgroup.closure_induction hx
    ( λ p hp, add_subgroup.subset_closure ((submonoid.closure s).mul_mem hp hq) )
    ( begin rw zero_mul q, apply add_subgroup.zero_mem _, end )
    ( λ p₁ p₂ ihp₁ ihp₂, begin rw add_mul p₁ p₂ q, apply add_subgroup.add_mem _ ihp₁ ihp₂, end )
    ( λ x hx, begin have f : -x * q = -(x*q) := by simp, rw f, apply add_subgroup.neg_mem _ hx, end ) )
  ( begin rw mul_zero x, apply add_subgroup.zero_mem _, end )
  ( λ q₁ q₂ ihq₁ ihq₂, begin rw mul_add x q₁ q₂, apply add_subgroup.add_mem _ ihq₁ ihq₂ end )
  ( λ z hz, begin have f : x * -z = -(x*z) := by simp, rw f, apply add_subgroup.neg_mem _ hz, end ) ),
 λ h, add_subgroup.closure_induction h
 ( λ x hx, submonoid.closure_induction hx
  ( λ x hx, subset_closure hx )
  ( one_mem _ )
  ( λ x y hx hy, mul_mem _ hx hy ) )
 ( zero_mem _ )
 (λ x y hx hy, add_mem _ hx hy)
 ( λ x hx, neg_mem _ hx ) ⟩

theorem exists_list_of_mem_closure {s : set R} {x : R} (h : x ∈ closure s) :
  (∃ L : list (list R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = (-1:R)) ∧ (L.map list.prod).sum = x) :=
add_subgroup.closure_induction (mem_closure_iff.1 h)
  (λ x hx, let ⟨l, hl, h⟩ :=submonoid.exists_list_of_mem_closure hx in ⟨[l], by simp [h];
    clear_aux_decl; tauto!⟩)
  ⟨[], by simp⟩
  (λ x y ⟨l, hl1, hl2⟩ ⟨m, hm1, hm2⟩, ⟨l ++ m, λ t ht, (list.mem_append.1 ht).elim (hl1 t) (hm1 t),
    by simp [hl2, hm2]⟩)
  (λ x ⟨L, hL⟩, ⟨L.map (list.cons (-1)), list.forall_mem_map_iff.2 $ λ j hj, list.forall_mem_cons.2
    ⟨or.inr rfl, hL.1 j hj⟩, hL.2 ▸ list.rec_on L (by simp)
      (by simp [list.map_cons, add_comm] {contextual := tt})⟩)

variable (R)
/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure R _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {R}

/-- Closure of a subring `S` equals `S`. -/
lemma closure_eq (s : subring R) : closure (s : set R) = s := (subring.gi R).l_u_eq s

@[simp] lemma closure_empty : closure (∅ : set R) = ⊥ := (subring.gi R).gc.l_bot

@[simp] lemma closure_univ : closure (set.univ : set R) = ⊤ := @coe_top R _ ▸ closure_eq ⊤

lemma closure_union (s t : set R) : closure (s ∪ t) = closure s ⊔ closure t :=
(subring.gi R).gc.l_sup

lemma closure_Union {ι} (s : ι → set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(subring.gi R).gc.l_supr

lemma closure_sUnion (s : set (set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
(subring.gi R).gc.l_Sup

lemma map_sup (s t : subring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
(gc_map_comap f).l_sup

lemma map_supr {ι : Sort*} (f : R →+* S) (s : ι → subring R) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

lemma comap_inf (s t : subring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
(gc_map_comap f).u_inf

lemma comap_infi {ι : Sort*} (f : R →+* S) (s : ι → subring S) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp] lemma map_bot (f : R →+* S) : (⊥ : subring R).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : R →+* S) : (⊤ : subring S).comap f = ⊤ :=
(gc_map_comap f).u_top

/-- Given `subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s × t`
as a subring of `R × S`. -/
def prod (s : subring R) (t : subring S) : subring (R × S) :=
{ carrier := (s : set R).prod t,
  .. s.to_submonoid.prod t.to_submonoid, .. s.to_add_subgroup.prod t.to_add_subgroup}

@[norm_cast]
lemma coe_prod (s : subring R) (t : subring S) :
  (s.prod t : set (R × S)) = (s : set R).prod (t : set S) :=
rfl

lemma mem_prod {s : subring R} {t : subring S} {p : R × S} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[mono] lemma prod_mono ⦃s₁ s₂ : subring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : subring S⦄
  (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
set.prod_mono hs ht

lemma prod_mono_right (s : subring R) : monotone (λ t : subring S, s.prod t) :=
prod_mono (le_refl s)

lemma prod_mono_left (t : subring S) : monotone (λ s : subring R, s.prod t) :=
λ s₁ s₂ hs, prod_mono hs (le_refl t)

lemma prod_top (s : subring R) :
  s.prod (⊤ : subring S) = s.comap (ring_hom.fst R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

lemma top_prod (s : subring S) :
  (⊤ : subring R).prod s = s.comap (ring_hom.snd R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp]
lemma top_prod_top : (⊤ : subring R).prod (⊤ : subring S) = ⊤ :=
(top_prod _).trans $ comap_top _

/-- Product of subrings is isomorphic to their product as rings. -/
def prod_equiv (s : subring R) (t : subring S) : s.prod t ≃+* s × t :=
{ map_mul' := λ x y, rfl, map_add' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

/-- The underlying set of a non-empty directed Sup of subrings is just a union of the subrings.
  Note that this fails without the directedness assumption (the union of two subrings is
  typically not a subring) -/
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subring R} (hS : directed (≤) S)
  {x : R} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (le_def.1 $ le_supr S i) hi⟩,
  let U : subring R := subring.mk' (⋃ i, (S i : set R))
    (⨆ i, (S i).to_submonoid) (submonoid.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id))
    (⨆ i, (S i).to_add_subgroup) (add_subgroup.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id)),
  suffices : (⨆ i, S i) ≤ U, by simpa using @this x,
  exact supr_le (λ i x hx, set.mem_Union.2 ⟨i, hx⟩),
end

lemma coe_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subring R} (hS : directed (≤) S) :
  ((⨆ i, S i : subring R) : set R) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

lemma mem_Sup_of_directed_on {S : set (subring R)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : R} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

lemma coe_Sup_of_directed_on {S : set (subring R)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set R) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

end subring

namespace ring_hom

variables [ring T] {s : subring R}

open subring

/-- Restriction of a ring homomorphism to a subring of the domain. -/
def restrict (f : R →+* S) (s : subring R) : s →+* S := f.comp s.subtype

@[simp] lemma restrict_apply (f : R →+* S) (x : s) : f.restrict s x = f x := rfl

/-- Restriction of a ring homomorphism to its range iterpreted as a subsemiring. -/
def range_restrict (f : R →+* S) : R →+* f.range :=
f.cod_restrict' f.range $ λ x, ⟨x, subring.mem_top x, rfl⟩

@[simp] lemma coe_range_restrict (f : R →+* S) (x : R) : (f.range_restrict x : S) = f x := rfl

lemma range_top_iff_surjective {f : R →+* S} :
  f.range = (⊤ : subring S) ↔ function.surjective f :=
subring.ext'_iff.trans $ iff.trans (by rw [coe_range, coe_top]) set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
lemma range_top_of_surjective (f : R →+* S) (hf : function.surjective f) :
  f.range = (⊤ : subring S) :=
range_top_iff_surjective.2 hf

/-- The subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a subring of R -/
def eq_locus (f g : R →+* S) : subring R :=
{ carrier := {x | f x = g x}, .. (f : R →* S).eq_mlocus g, .. (f : R →+ S).eq_locus g }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subring closure. -/
lemma eq_on_set_closure {f g : R →+* S} {s : set R} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_locus g, from closure_le.2 h

lemma eq_of_eq_on_set_top {f g : R →+* S} (h : set.eq_on f g (⊤ : subring R)) :
  f = g :=
ext $ λ x, h trivial

lemma eq_of_eq_on_set_dense {s : set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_set_top $ hs ▸ eq_on_set_closure h

lemma closure_preimage_le (f : R →+* S) (s : set S) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a ring homomorphism of the subring generated by a set equals
the subring generated by the image of the set. -/
lemma map_closure (f : R →+* S) (s : set R) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (closure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end ring_hom

namespace subring

open ring_hom

/-- The ring homomorphism associated to an inclusion of subrings. -/
def inclusion {S T : subring R} (h : S ≤ T) : S →* T :=
S.subtype.cod_restrict' _ (λ x, h x.2)

@[simp] lemma range_subtype (s : subring R) : s.subtype.range = s :=
ext' $ (coe_srange _).trans subtype.range_coe

@[simp]
lemma range_fst : (fst R S).srange = ⊤ :=
(fst R S).srange_top_of_surjective $ prod.fst_surjective

@[simp]
lemma range_snd : (snd R S).srange = ⊤ :=
(snd R S).srange_top_of_surjective $ prod.snd_surjective

@[simp]
lemma prod_bot_sup_bot_prod (s : subring R) (t : subring S) :
  (s.prod ⊥) ⊔ (prod ⊥ t) = s.prod t :=
le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) $
assume p hp, prod.fst_mul_snd p ▸ mul_mem _
  ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, mem_coe.2 $ one_mem ⊥⟩)
  ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨mem_coe.2 $ one_mem ⊥, hp.2⟩)

end subring

namespace ring_equiv

variables {s t : subring R}

/-- Makes the identity isomorphism from a proof two subrings of a multiplicative
    monoid are equal. -/
def subring_congr (h : s = t) : s ≃+* t :=
{ map_mul' :=  λ _ _, rfl, map_add' := λ _ _, rfl, ..equiv.set_congr $ subring.ext'_iff.1 h }

end ring_equiv

namespace subring

variables {s : set R}
local attribute [reducible] closure

@[elab_as_eliminator]
protected theorem in_closure.rec_on {C : R → Prop} {x : R} (hx : x ∈ closure s)
  (h1 : C 1) (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n))
  (ha : ∀ {x y}, C x → C y → C (x + y)) : C x :=
begin
  have h0 : C 0 := add_neg_self (1:R) ▸ ha h1 hneg1,
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩, clear hx,
  induction L with hd tl ih, { exact h0 },
  rw list.forall_mem_cons at HL,
  suffices : C (list.prod hd),
  { rw [list.map_cons, list.sum_cons],
    exact ha this (ih HL.2) },
  replace HL := HL.1, clear ih tl,
  suffices : ∃ L : list R, (∀ x ∈ L, x ∈ s) ∧ (list.prod hd = list.prod L ∨ list.prod hd = -list.prod L),
  { rcases this with ⟨L, HL', HP | HP⟩,
    { rw HP, clear HP HL hd, induction L with hd tl ih, { exact h1 },
      rw list.forall_mem_cons at HL',
      rw list.prod_cons,
      exact hs _ HL'.1 _ (ih HL'.2) },
    rw HP, clear HP HL hd, induction L with hd tl ih, { exact hneg1 },
    rw [list.prod_cons, neg_mul_eq_mul_neg],
    rw list.forall_mem_cons at HL',
    exact hs _ HL'.1 _ (ih HL'.2) },
  induction hd with hd tl ih,
  { exact ⟨[], list.forall_mem_nil _, or.inl rfl⟩ },
  rw list.forall_mem_cons at HL,
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩; cases HL.1 with hhd hhd,
  { exact ⟨hd :: L, list.forall_mem_cons.2 ⟨hhd, HL'⟩, or.inl $
      by rw [list.prod_cons, list.prod_cons, HP]⟩ },
  { exact ⟨L, HL', or.inr $ by rw [list.prod_cons, hhd, neg_one_mul, HP]⟩ },
  { exact ⟨hd :: L, list.forall_mem_cons.2 ⟨hhd, HL'⟩, or.inr $
      by rw [list.prod_cons, list.prod_cons, HP, neg_mul_eq_mul_neg]⟩ },
  { exact ⟨L, HL', or.inl $ by rw [list.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩ }
end

lemma closure_preimage_le (f : R →+* S) (s : set S) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, mem_coe.2 $ mem_comap.2 $ subset_closure hx

end subring
