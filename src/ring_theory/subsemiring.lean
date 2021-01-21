/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import algebra.ring.prod
import group_theory.submonoid

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `complete_lattice` structure,
`subtype` and `inclusion` ring homomorphisms, subsemiring `map`, `comap` and range (`srange`) of
a `ring_hom` etc.
-/

open_locale big_operators

universes u v w

variables {R : Type u} {S : Type v} {T : Type w} [semiring R] [semiring S] [semiring T]

set_option old_structure_cmd true

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure subsemiring (R : Type u) [semiring R] extends submonoid R, add_submonoid R

/-- Reinterpret a `subsemiring` as a `submonoid`. -/
add_decl_doc subsemiring.to_submonoid

/-- Reinterpret a `subsemiring` as an `add_submonoid`. -/
add_decl_doc subsemiring.to_add_submonoid

namespace subsemiring

instance : has_coe (subsemiring R) (set R) := ⟨subsemiring.carrier⟩

instance : has_mem R (subsemiring R) := ⟨λ m S, m ∈ (S:set R)⟩

instance : has_coe_to_sort (subsemiring R) := ⟨Type*, λ S, {x : R // x ∈ S}⟩

/-- Construct a `subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : set R) (sm : submonoid R) (hm : ↑sm = s)
  (sa : add_submonoid R) (ha : ↑sa = s) :
  subsemiring R :=
{ carrier := s,
  zero_mem' := ha ▸ sa.zero_mem,
  one_mem' := hm ▸ sm.one_mem,
  add_mem' := λ x y, by simpa only [← ha] using sa.add_mem,
  mul_mem' := λ x y, by simpa only [← hm] using sm.mul_mem }

@[simp] lemma coe_mk' {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa = s) :
  (subsemiring.mk' s sm hm sa ha : set R) = s := rfl

@[simp] lemma mem_mk' {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa = s) {x : R} :
  x ∈ subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
iff.rfl

@[simp] lemma mk'_to_submonoid {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa = s) :
  (subsemiring.mk' s sm hm sa ha).to_submonoid = sm :=
submonoid.ext' hm.symm

@[simp] lemma mk'_to_add_submonoid {s : set R} {sm : submonoid R} (hm : ↑sm = s)
  {sa : add_submonoid R} (ha : ↑sa  =s) :
  (subsemiring.mk' s sm hm sa ha).to_add_submonoid = sa :=
add_submonoid.ext' ha.symm

end subsemiring

protected lemma subsemiring.exists {s : subsemiring R} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

protected lemma subsemiring.forall {s : subsemiring R} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

namespace subsemiring

variables (s : subsemiring R)

/-- Two subsemirings are equal if the underlying subsets are equal. -/
theorem ext' ⦃s t : subsemiring R⦄ (h : (s : set R) = t) : s = t :=
by cases s; cases t; congr'

/-- Two subsemirings are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {s t : subsemiring R}  : s = t ↔ (s : set R) = t :=
⟨λ h, h ▸ rfl, λ h, ext' h⟩

/-- Two subsemirings are equal if they have the same elements. -/
@[ext] theorem ext {S T : subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

/-- A subsemiring contains the semiring's 1. -/
theorem one_mem : (1 : R) ∈ s := s.one_mem'

/-- A subsemiring contains the semiring's 0. -/
theorem zero_mem : (0 : R) ∈ s := s.zero_mem'

/-- A subsemiring is closed under multiplication. -/
theorem mul_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x * y ∈ s := s.mul_mem'

/-- A subsemiring is closed under addition. -/
theorem add_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x + y ∈ s := s.add_mem'

/-- Product of a list of elements in a `subsemiring` is in the `subsemiring`. -/
lemma list_prod_mem {l : list R} : (∀x ∈ l, x ∈ s) → l.prod ∈ s :=
s.to_submonoid.list_prod_mem

/-- Sum of a list of elements in a `subsemiring` is in the `subsemiring`. -/
lemma list_sum_mem {l : list R} : (∀x ∈ l, x ∈ s) → l.sum ∈ s :=
s.to_add_submonoid.list_sum_mem

/-- Product of a multiset of elements in a `subsemiring` of a `comm_semiring`
    is in the `subsemiring`. -/
lemma multiset_prod_mem {R} [comm_semiring R] (s : subsemiring R) (m : multiset R) :
  (∀a ∈ m, a ∈ s) → m.prod ∈ s :=
s.to_submonoid.multiset_prod_mem m

/-- Sum of a multiset of elements in a `subsemiring` of a `semiring` is
in the `add_subsemiring`. -/
lemma multiset_sum_mem {R} [semiring R] (s : subsemiring R) (m : multiset R) :
  (∀a ∈ m, a ∈ s) → m.sum ∈ s :=
s.to_add_submonoid.multiset_sum_mem m

/-- Product of elements of a subsemiring of a `comm_semiring` indexed by a `finset` is in the
    subsemiring. -/
lemma prod_mem {R : Type*} [comm_semiring R] (s : subsemiring R)
  {ι : Type*} {t : finset ι} {f : ι → R} (h : ∀c ∈ t, f c ∈ s) :
  ∏ i in t, f i ∈ s :=
s.to_submonoid.prod_mem h

/-- Sum of elements in an `subsemiring` of an `semiring` indexed by a `finset`
is in the `add_subsemiring`. -/
lemma sum_mem {R : Type*} [semiring R] (s : subsemiring R)
  {ι : Type*} {t : finset ι} {f : ι → R} (h : ∀c ∈ t, f c ∈ s) :
  ∑ i in t, f i ∈ s :=
s.to_add_submonoid.sum_mem h

lemma pow_mem {x : R} (hx : x ∈ s) (n : ℕ) : x^n ∈ s := s.to_submonoid.pow_mem hx n

lemma nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) :
  n •ℕ x ∈ s := s.to_add_submonoid.nsmul_mem hx n

lemma coe_nat_mem (n : ℕ) : (n : R) ∈ s :=
by simp only [← nsmul_one, nsmul_mem, one_mem]

/-- A subsemiring of a semiring inherits a semiring structure -/
instance to_semiring : semiring s :=
{ mul_zero := λ x, subtype.eq $ mul_zero x,
  zero_mul := λ x, subtype.eq $ zero_mul x,
  right_distrib := λ x y z, subtype.eq $ right_distrib x y z,
  left_distrib := λ x y z, subtype.eq $ left_distrib x y z,
  .. s.to_submonoid.to_monoid, .. s.to_add_submonoid.to_add_comm_monoid }

instance nontrivial [nontrivial R] : nontrivial s :=
@nontrivial_of_ne s 0 1 (λ H, zero_ne_one (congr_arg subtype.val H : _))

@[simp, norm_cast] lemma coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_one : ((1 : s) : R) = 1 := rfl

/-- A subsemiring of a `comm_semiring` is a `comm_semiring`. -/
instance to_comm_semiring {R} [comm_semiring R] (s : subsemiring R) : comm_semiring s :=
{ mul_comm := λ _ _, subtype.eq $ mul_comm _ _, ..s.to_semiring}

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
{ to_fun := coe, .. s.to_submonoid.subtype, .. s.to_add_submonoid.subtype }

@[simp] theorem coe_subtype : ⇑s.subtype = coe := rfl

instance : partial_order (subsemiring R) :=
{ le := λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t,
  .. partial_order.lift (coe : subsemiring R → set R) ext' }

lemma le_def {s t : subsemiring R} : s ≤ t ↔ ∀ ⦃x : R⦄, x ∈ s → x ∈ t := iff.rfl

@[simp, norm_cast] lemma coe_subset_coe {s t : subsemiring R} : (s : set R) ⊆ t ↔ s ≤ t := iff.rfl

@[simp, norm_cast] lemma coe_ssubset_coe {s t : subsemiring R} : (s : set R) ⊂ t ↔ s < t := iff.rfl

@[simp, norm_cast]
lemma mem_coe {S : subsemiring R} {m : R} : m ∈ (S : set R) ↔ m ∈ S := iff.rfl

@[simp, norm_cast]
lemma coe_coe (s : subsemiring R) : ↥(s : set R) = s := rfl

@[simp] lemma mem_to_submonoid {s : subsemiring R} {x : R} : x ∈ s.to_submonoid ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_submonoid (s : subsemiring R) : (s.to_submonoid : set R) = s := rfl
@[simp] lemma mem_to_add_submonoid {s : subsemiring R} {x : R} :
  x ∈ s.to_add_submonoid ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_add_submonoid (s : subsemiring R) : (s.to_add_submonoid : set R) = s := rfl

/-- The subsemiring `R` of the semiring `R`. -/
instance : has_top (subsemiring R) :=
⟨{ .. (⊤ : submonoid R), .. (⊤ : add_submonoid R) }⟩

@[simp] lemma mem_top (x : R) : x ∈ (⊤ : subsemiring R) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : subsemiring R) : set R) = set.univ := rfl

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
def comap (f : R →+* S) (s : subsemiring S) : subsemiring R :=
{ carrier := f ⁻¹' s,
  .. s.to_submonoid.comap (f : R →* S), .. s.to_add_submonoid.comap (f : R →+ S) }

@[simp] lemma coe_comap (s : subsemiring S) (f : R →+* S) : (s.comap f : set R) = f ⁻¹' s := rfl

@[simp]
lemma mem_comap {s : subsemiring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s := iff.rfl

lemma comap_comap (s : subsemiring T) (g : S →+* T) (f : R →+* S) :
  (s.comap g).comap f = s.comap (g.comp f) :=
rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
def map (f : R →+* S) (s : subsemiring R) : subsemiring S :=
{ carrier := f '' s,
  .. s.to_submonoid.map (f : R →* S), .. s.to_add_submonoid.map (f : R →+ S) }

@[simp] lemma coe_map (f : R →+* S) (s : subsemiring R) : (s.map f : set S) = f '' s := rfl

@[simp] lemma mem_map {f : R →+* S} {s : subsemiring R} {y : S} :
  y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
set.mem_image_iff_bex

lemma map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
ext' $ set.image_image _ _ _

lemma map_le_iff_le_comap {f : R →+* S} {s : subsemiring R} {t : subsemiring S} :
  s.map f ≤ t ↔ s ≤ t.comap f :=
set.image_subset_iff

lemma gc_map_comap (f : R →+* S) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

end subsemiring

namespace ring_hom

variables (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism is a subsemiring. -/
def srange : subsemiring S := (⊤ : subsemiring R).map f

@[simp] lemma coe_srange : (f.srange : set S) = set.range f := set.image_univ

@[simp] lemma mem_srange {f : R →+* S} {y : S} : y ∈ f.srange ↔ ∃ x, f x = y :=
by simp [srange]

lemma map_srange : f.srange.map g = (g.comp f).srange :=
(⊤ : subsemiring R).map_map g f

end ring_hom

namespace subsemiring

instance : has_bot (subsemiring R) := ⟨(nat.cast_ring_hom R).srange⟩

instance : inhabited (subsemiring R) := ⟨⊥⟩

lemma coe_bot : ((⊥ : subsemiring R) : set R) = set.range (coe : ℕ → R) :=
(nat.cast_ring_hom R).coe_srange

lemma mem_bot {x : R} : x ∈ (⊥ : subsemiring R) ↔ ∃ n : ℕ, ↑n=x := ring_hom.mem_srange

/-- The inf of two subsemirings is their intersection. -/
instance : has_inf (subsemiring R) :=
⟨λ s t,
  { carrier := s ∩ t,
    .. s.to_submonoid ⊓ t.to_submonoid,
    .. s.to_add_submonoid ⊓ t.to_add_submonoid }⟩

@[simp] lemma coe_inf (p p' : subsemiring R) : ((p ⊓ p' : subsemiring R) : set R) = p ∩ p' := rfl

@[simp] lemma mem_inf {p p' : subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (subsemiring R) :=
⟨λ s, subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, subsemiring.to_submonoid t) (by simp)
  (⨅ t ∈ s, subsemiring.to_add_submonoid t) (by simp)⟩

@[simp, norm_cast] lemma coe_Inf (S : set (subsemiring R)) :
  ((Inf S : subsemiring R) : set R) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (subsemiring R)} {x : R} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

@[simp] lemma Inf_to_submonoid (s : set (subsemiring R)) :
  (Inf s).to_submonoid = ⨅ t ∈ s, subsemiring.to_submonoid t :=
mk'_to_submonoid _ _

@[simp] lemma Inf_to_add_submonoid (s : set (subsemiring R)) :
  (Inf s).to_add_submonoid = ⨅ t ∈ s, subsemiring.to_add_submonoid t :=
mk'_to_add_submonoid _ _

/-- Subsemirings of a semiring form a complete lattice. -/
instance : complete_lattice (subsemiring R) :=
{ bot := (⊥),
  bot_le := λ s x hx, let ⟨n, hn⟩ := mem_bot.1 hx in hn ▸ s.coe_nat_mem n,
  top := (⊤),
  le_top := λ s x hx, trivial,
  inf := (⊓),
  inf_le_left := λ s t x, and.left,
  inf_le_right := λ s t x, and.right,
  le_inf := λ s t₁ t₂ h₁ h₂ x hx, ⟨h₁ hx, h₂ hx⟩,
  .. complete_lattice_of_Inf (subsemiring R)
    (λ s, is_glb.of_image (λ s t, show (s : set R) ≤ t ↔ s ≤ t, from coe_subset_coe) is_glb_binfi)}

/-- The `subsemiring` generated by a set. -/
def closure (s : set R) : subsemiring R := Inf {S | s ⊆ S}

lemma mem_closure {x : R} {s : set R} : x ∈ closure s ↔ ∀ S : subsemiring R, s ⊆ S → x ∈ S :=
mem_Inf

/-- The subsemiring generated by a set includes the set. -/
@[simp] lemma subset_closure {s : set R} : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
lemma closure_le {s : set R} {t : subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
⟨set.subset.trans subset_closure, λ h, Inf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
lemma closure_mono ⦃s t : set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ set.subset.trans h subset_closure

lemma closure_eq_of_le {s : set R} {t : subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
  closure s = t :=
le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_eliminator]
lemma closure_induction {s : set R} {p : R → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0) (H1 : p 1)
  (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul, H0, Hadd⟩).2 Hs h

lemma mem_closure_iff {s : set R} {x} :
  x ∈ closure s ↔ x ∈ add_submonoid.closure (submonoid.closure s : set R) :=
⟨λ h, closure_induction h (λ x hx, add_submonoid.subset_closure $ submonoid.subset_closure hx)
  (add_submonoid.zero_mem _)
  (add_submonoid.subset_closure $ submonoid.one_mem $ submonoid.closure s)
  (λ _ _, add_submonoid.add_mem _)
  (λ x y ihx ihy, add_submonoid.closure_induction ihy
    (λ q hq, add_submonoid.closure_induction ihx
      (λ p hp, add_submonoid.subset_closure $ (submonoid.closure s).mul_mem hp hq)
      ((zero_mul q).symm ▸ add_submonoid.zero_mem _)
      (λ p₁ p₂ ihp₁ ihp₂, (add_mul p₁ p₂ q).symm ▸ add_submonoid.add_mem _ ihp₁ ihp₂))
    ((mul_zero x).symm ▸ add_submonoid.zero_mem _)
    (λ q₁ q₂ ihq₁ ihq₂, (mul_add x q₁ q₂).symm ▸ add_submonoid.add_mem _ ihq₁ ihq₂)),
λ h, add_submonoid.closure_induction h
  (λ x hx, submonoid.closure_induction hx subset_closure (one_mem _) (λ _ _, mul_mem _))
  (zero_mem _)
  (λ _ _, add_mem _)⟩

lemma mem_closure_iff_exists_list {s : set R} {x} : x ∈ closure s ↔
  ∃ L : list (list R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s) ∧ (L.map list.prod).sum = x :=
⟨λ hx, add_submonoid.closure_induction (mem_closure_iff.1 hx)
  (λ x hx, suffices ∃ t : list R, (∀ y ∈ t, y ∈ s) ∧ t.prod = x,
    from let ⟨t, ht1, ht2⟩ := this in ⟨[t], list.forall_mem_singleton.2 ht1,
      by rw [list.map_singleton, list.sum_singleton, ht2]⟩,
    submonoid.closure_induction hx
      (λ x hx, ⟨[x], list.forall_mem_singleton.2 hx, one_mul x⟩)
      ⟨[], list.forall_mem_nil _, rfl⟩
      (λ x y ⟨t, ht1, ht2⟩ ⟨u, hu1, hu2⟩, ⟨t ++ u, list.forall_mem_append.2 ⟨ht1, hu1⟩,
        by rw [list.prod_append, ht2, hu2]⟩))
  ⟨[], list.forall_mem_nil _, rfl⟩
  (λ x y ⟨L, HL1, HL2⟩ ⟨M, HM1, HM2⟩, ⟨L ++ M, list.forall_mem_append.2 ⟨HL1, HM1⟩,
    by rw [list.map_append, list.sum_append, HL2, HM2]⟩),
λ ⟨L, HL1, HL2⟩, HL2 ▸ list_sum_mem _ (λ r hr, let ⟨t, ht1, ht2⟩ := list.mem_map.1 hr in
  ht2 ▸ list_prod_mem _ (λ y hy, subset_closure $ HL1 t ht1 y hy))⟩

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure R _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {R}

/-- Closure of a subsemiring `S` equals `S`. -/
lemma closure_eq (s : subsemiring R) : closure (s : set R) = s := (subsemiring.gi R).l_u_eq s

@[simp] lemma closure_empty : closure (∅ : set R) = ⊥ := (subsemiring.gi R).gc.l_bot

@[simp] lemma closure_univ : closure (set.univ : set R) = ⊤ := @coe_top R _ ▸ closure_eq ⊤

lemma closure_union (s t : set R) : closure (s ∪ t) = closure s ⊔ closure t :=
(subsemiring.gi R).gc.l_sup

lemma closure_Union {ι} (s : ι → set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(subsemiring.gi R).gc.l_supr

lemma closure_sUnion (s : set (set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
(subsemiring.gi R).gc.l_Sup

lemma map_sup (s t : subsemiring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
(gc_map_comap f).l_sup

lemma map_supr {ι : Sort*} (f : R →+* S) (s : ι → subsemiring R) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

lemma comap_inf (s t : subsemiring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
(gc_map_comap f).u_inf

lemma comap_infi {ι : Sort*} (f : R →+* S) (s : ι → subsemiring S) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp] lemma map_bot (f : R →+* S) : (⊥ : subsemiring R).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : R →+* S) : (⊤ : subsemiring S).comap f = ⊤ :=
(gc_map_comap f).u_top

/-- Given `subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod (s : subsemiring R) (t : subsemiring S) : subsemiring (R × S) :=
{ carrier := (s : set R).prod t,
  .. s.to_submonoid.prod t.to_submonoid, .. s.to_add_submonoid.prod t.to_add_submonoid}

@[norm_cast]
lemma coe_prod (s : subsemiring R) (t : subsemiring S) :
  (s.prod t : set (R × S)) = (s : set R).prod (t : set S) :=
rfl

lemma mem_prod {s : subsemiring R} {t : subsemiring S} {p : R × S} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[mono] lemma prod_mono ⦃s₁ s₂ : subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : subsemiring S⦄
  (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
set.prod_mono hs ht

lemma prod_mono_right (s : subsemiring R) : monotone (λ t : subsemiring S, s.prod t) :=
prod_mono (le_refl s)

lemma prod_mono_left (t : subsemiring S) : monotone (λ s : subsemiring R, s.prod t) :=
λ s₁ s₂ hs, prod_mono hs (le_refl t)

lemma prod_top (s : subsemiring R) :
  s.prod (⊤ : subsemiring S) = s.comap (ring_hom.fst R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

lemma top_prod (s : subsemiring S) :
  (⊤ : subsemiring R).prod s = s.comap (ring_hom.snd R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp]
lemma top_prod_top : (⊤ : subsemiring R).prod (⊤ : subsemiring S) = ⊤ :=
(top_prod _).trans $ comap_top _

/-- Product of subsemirings is isomorphic to their product as monoids. -/
def prod_equiv (s : subsemiring R) (t : subsemiring S) : s.prod t ≃+* s × t :=
{ map_mul' := λ x y, rfl, map_add' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subsemiring R} (hS : directed (≤) S)
  {x : R} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (le_def.1 $ le_supr S i) hi⟩,
  let U : subsemiring R := subsemiring.mk' (⋃ i, (S i : set R))
    (⨆ i, (S i).to_submonoid) (submonoid.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id))
    (⨆ i, (S i).to_add_submonoid) (add_submonoid.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id)),
  suffices : (⨆ i, S i) ≤ U, by simpa using @this x,
  exact supr_le (λ i x hx, set.mem_Union.2 ⟨i, hx⟩),
end

lemma coe_supr_of_directed {ι} [hι : nonempty ι] {S : ι → subsemiring R} (hS : directed (≤) S) :
  ((⨆ i, S i : subsemiring R) : set R) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

lemma mem_Sup_of_directed_on {S : set (subsemiring R)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : R} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

lemma coe_Sup_of_directed_on {S : set (subsemiring R)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set R) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

end subsemiring

namespace ring_hom

variables [semiring T] {s : subsemiring R}

open subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def srestrict (f : R →+* S) (s : subsemiring R) : s →+* S := f.comp s.subtype

@[simp] lemma srestrict_apply (f : R →+* S) (x : s) : f.srestrict s x = f x := rfl

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
def cod_srestrict (f : R →+* S) (s : subsemiring S) (h : ∀ x, f x ∈ s) : R →+* s :=
{ to_fun := λ n, ⟨f n, h n⟩,
  .. (f : R →* S).cod_mrestrict s.to_submonoid h,
  .. (f : R →+ S).cod_mrestrict s.to_add_submonoid h }

/-- Restriction of a ring homomorphism to its range iterpreted as a subsemiring. -/
def srange_restrict (f : R →+* S) : R →+* f.srange :=
f.cod_srestrict f.srange $ λ x, ⟨x, subsemiring.mem_top x, rfl⟩

@[simp] lemma coe_srange_restrict (f : R →+* S) (x : R) :
  (f.srange_restrict x : S) = f x :=
rfl

lemma srange_top_iff_surjective {f : R →+* S} :
  f.srange = (⊤ : subsemiring S) ↔ function.surjective f :=
subsemiring.ext'_iff.trans $ iff.trans (by rw [coe_srange, coe_top]) set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
lemma srange_top_of_surjective (f : R →+* S) (hf : function.surjective f) :
  f.srange = (⊤ : subsemiring S) :=
srange_top_iff_surjective.2 hf

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eq_slocus (f g : R →+* S) : subsemiring R :=
{ carrier := {x | f x = g x}, .. (f : R →* S).eq_mlocus g, .. (f : R →+ S).eq_mlocus g }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
lemma eq_on_sclosure {f g : R →+* S} {s : set R} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_slocus g, from closure_le.2 h

lemma eq_of_eq_on_stop {f g : R →+* S} (h : set.eq_on f g (⊤ : subsemiring R)) :
  f = g :=
ext $ λ x, h trivial

lemma eq_of_eq_on_sdense {s : set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_stop $ hs ▸ eq_on_sclosure h

lemma sclosure_preimage_le (f : R →+* S) (s : set S) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
lemma map_sclosure (f : R →+* S) (s : set R) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (sclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end ring_hom

namespace subsemiring

open ring_hom

/-- The ring homomorphism associated to an inclusion of subsemirings. -/
def inclusion {S T : subsemiring R} (h : S ≤ T) : S →* T :=
S.subtype.cod_srestrict _ (λ x, h x.2)

@[simp] lemma srange_subtype (s : subsemiring R) : s.subtype.srange = s :=
ext' $ (coe_srange _).trans subtype.range_coe

@[simp]
lemma range_fst : (fst R S).srange = ⊤ :=
(fst R S).srange_top_of_surjective $ prod.fst_surjective

@[simp]
lemma range_snd : (snd R S).srange = ⊤ :=
(snd R S).srange_top_of_surjective $ prod.snd_surjective

@[simp]
lemma prod_bot_sup_bot_prod (s : subsemiring R) (t : subsemiring S) :
  (s.prod ⊥) ⊔ (prod ⊥ t) = s.prod t :=
le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) $
assume p hp, prod.fst_mul_snd p ▸ mul_mem _
  ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, mem_coe.2 $ one_mem ⊥⟩)
  ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨mem_coe.2 $ one_mem ⊥, hp.2⟩)

end subsemiring

namespace ring_equiv

variables {s t : subsemiring R}

/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
    monoid are equal. -/
def subsemiring_congr (h : s = t) : s ≃+* t :=
{ map_mul' :=  λ _ _, rfl, map_add' := λ _ _, rfl, ..equiv.set_congr $ subsemiring.ext'_iff.1 h }

end ring_equiv
