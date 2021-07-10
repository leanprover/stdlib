/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen, Patrick Massot
-/

import data.setoid.basic
import data.set.lattice

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : set (set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `is_partition c`
* An indexed partition is a map `s : ι → α` whose image is a partition. This is
  expressed as `indexed_partition s`.

Of course both implementations are related to `quotient` and `setoid`.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/

namespace setoid

variables {α : Type*}

/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
lemma eq_of_mem_eqv_class {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b)
  {x b b'} (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') :
  b = b' :=
(H x).unique2 hc hb hc' hb'

/-- Makes an equivalence relation from a set of sets partitioning α. -/
def mk_classes (c : set (set α)) (H : ∀ a, ∃! b ∈ c, a ∈ b) :
  setoid α :=
⟨λ x y, ∀ s ∈ c, x ∈ s → y ∈ s, ⟨λ _ _ _ hx, hx,
 λ x y h s hs hy, (H x).elim2 $ λ t ht hx _,
   have s = t, from eq_of_mem_eqv_class H hs hy ht (h t ht hx),
   this.symm ▸ hx,
 λ x y z h1 h2 s hs hx, (H y).elim2 $ λ t ht hy _, (H z).elim2 $ λ t' ht' hz _,
   have hst : s = t, from eq_of_mem_eqv_class H hs (h1 _ hs hx) ht hy,
   have htt' : t = t', from eq_of_mem_eqv_class H ht (h2 _ ht hy) ht' hz,
   (hst.trans htt').symm ▸ hz⟩⟩

/-- Makes the equivalence classes of an equivalence relation. -/
def classes (r : setoid α) : set (set α) :=
{s | ∃ y, s = {x | r.rel x y}}

lemma mem_classes (r : setoid α) (y) : {x | r.rel x y} ∈ r.classes := ⟨y, rfl⟩

/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
lemma eq_iff_classes_eq {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ ∀ x, {y | r₁.rel x y} = {y | r₂.rel x y} :=
⟨λ h x, h ▸ rfl, λ h, ext' $ λ x, set.ext_iff.1 $ h x⟩

lemma rel_iff_exists_classes (r : setoid α) {x y} :
  r.rel x y ↔ ∃ c ∈ r.classes, x ∈ c ∧ y ∈ c :=
⟨λ h, ⟨_, r.mem_classes y, h, r.refl' y⟩,
  λ ⟨c, ⟨z, hz⟩, hx, hy⟩, by { subst c, exact r.trans' hx (r.symm' hy) }⟩

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
lemma classes_inj {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ r₁.classes = r₂.classes :=
⟨λ h, h ▸ rfl, λ h, ext' $ λ a b, by simp only [rel_iff_exists_classes, exists_prop, h] ⟩

/-- The empty set is not an equivalence class. -/
lemma empty_not_mem_classes {r : setoid α} : ∅ ∉ r.classes :=
λ ⟨y, hy⟩, set.not_mem_empty y $ hy.symm ▸ r.refl' y

/-- Equivalence classes partition the type. -/
lemma classes_eqv_classes {r : setoid α} (a) : ∃! b ∈ r.classes, a ∈ b :=
exists_unique.intro2 {x | r.rel x a} (r.mem_classes a) (r.refl' _) $
begin
  rintros _ ⟨y, rfl⟩ ha,
  ext x,
  exact ⟨λ hx, r.trans' hx (r.symm' ha), λ hx, r.trans' hx ha⟩
end

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
lemma eq_of_mem_classes {r : setoid α} {x b} (hc : b ∈ r.classes)
  (hb : x ∈ b) {b'} (hc' : b' ∈ r.classes) (hb' : x ∈ b') : b = b' :=
eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/-- The elements of a set of sets partitioning α are the equivalence classes of the
    equivalence relation defined by the set of sets. -/
lemma eq_eqv_class_of_mem {c : set (set α)}
  (H : ∀ a, ∃! b ∈ c, a ∈ b) {s y} (hs : s ∈ c) (hy : y ∈ s) :
  s = {x | (mk_classes c H).rel x y} :=
set.ext $ λ x,
  ⟨λ hs', symm' (mk_classes c H) $ λ b' hb' h', eq_of_mem_eqv_class H hs hy hb' h' ▸ hs',
   λ hx, (H x).elim2 $ λ b' hc' hb' h',
     (eq_of_mem_eqv_class H hs hy hc' $ hx b' hc' hb').symm ▸ hb'⟩

/-- The equivalence classes of the equivalence relation defined by a set of sets
    partitioning α are elements of the set of sets. -/
lemma eqv_class_mem {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {y} :
  {x | (mk_classes c H).rel x y} ∈ c :=
(H y).elim2 $ λ b hc hy hb, eq_eqv_class_of_mem H hc hy ▸ hc

lemma eqv_class_mem' {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x} :
  {y : α | (mk_classes c H).rel x y} ∈ c :=
by { convert setoid.eqv_class_mem H, ext, rw setoid.comm' }

/-- Distinct elements of a set of sets partitioning α are disjoint. -/
lemma eqv_classes_disjoint {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) :
  set.pairwise_disjoint c :=
λ b₁ h₁ b₂ h₂ h, set.disjoint_left.2 $
  λ x hx1 hx2, (H x).elim2 $ λ b hc hx hb, h $ eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

/-- A set of disjoint sets covering α partition α (classical). -/
lemma eqv_classes_of_disjoint_union {c : set (set α)}
  (hu : set.sUnion c = @set.univ α) (H : set.pairwise_disjoint c) (a) :
  ∃! b ∈ c, a ∈ b :=
let ⟨b, hc, ha⟩ := set.mem_sUnion.1 $ show a ∈ _, by rw hu; exact set.mem_univ a in
  exists_unique.intro2 b hc ha $ λ b' hc' ha', H.elim hc' hc a ha' ha

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoid_of_disjoint_union {c : set (set α)} (hu : set.sUnion c = @set.univ α)
  (H : set.pairwise_disjoint c) : setoid α :=
setoid.mk_classes c $ eqv_classes_of_disjoint_union hu H

/-- The equivalence relation made from the equivalence classes of an equivalence
    relation r equals r. -/
theorem mk_classes_classes (r : setoid α) :
  mk_classes r.classes classes_eqv_classes = r :=
ext' $ λ x y, ⟨λ h, r.symm' (h {z | r.rel z x} (r.mem_classes x) $ r.refl' x),
  λ h b hb hx, eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

@[simp] theorem sUnion_classes (r : setoid α) : ⋃₀ r.classes = set.univ :=
set.eq_univ_of_forall $ λ x, set.mem_sUnion.2 ⟨{ y | r.rel y x }, ⟨x, rfl⟩, setoid.refl _⟩

section partition

/-- A collection `c : set (set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def is_partition (c : set (set α)) :=
∅ ∉ c ∧ ∀ a, ∃! b ∈ c, a ∈ b

/-- A partition of `α` does not contain the empty set. -/
lemma nonempty_of_mem_partition {c : set (set α)} (hc : is_partition c) {s} (h : s ∈ c) :
  s.nonempty :=
set.ne_empty_iff_nonempty.1 $ λ hs0, hc.1 $ hs0 ▸ h

lemma is_partition_classes (r : setoid α) : is_partition r.classes :=
⟨empty_not_mem_classes, classes_eqv_classes⟩

lemma is_partition.pairwise_disjoint {c : set (set α)} (hc : is_partition c) :
  c.pairwise_disjoint :=
eqv_classes_disjoint hc.2

lemma is_partition.sUnion_eq_univ {c : set (set α)} (hc : is_partition c) :
  ⋃₀ c = set.univ :=
set.eq_univ_of_forall $ λ x, set.mem_sUnion.2 $
  let ⟨t, ht⟩ := hc.2 x in ⟨t, by clear_aux_decl; finish⟩

/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
lemma exists_of_mem_partition {c : set (set α)} (hc : is_partition c) {s} (hs : s ∈ c) :
  ∃ y, s = {x | (mk_classes c hc.2).rel x y} :=
let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs in
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

/-- The equivalence classes of the equivalence relation defined by a partition of α equal
    the original partition. -/
theorem classes_mk_classes (c : set (set α)) (hc : is_partition c) :
  (mk_classes c hc.2).classes = c :=
set.ext $ λ s,
  ⟨λ ⟨y, hs⟩, (hc.2 y).elim2 $ λ b hm hb hy,
    by rwa (show s = b, from hs.symm ▸ set.ext
      (λ x, ⟨λ hx, symm' (mk_classes c hc.2) hx b hm hb,
             λ hx b' hc' hx', eq_of_mem_eqv_class hc.2 hm hx hc' hx' ▸ hb⟩)),
   exists_of_mem_partition hc⟩

/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
instance partition.le : has_le (subtype (@is_partition α)) :=
⟨λ x y, mk_classes x.1 x.2.2 ≤ mk_classes y.1 y.2.2⟩

/-- Defining a partial order on partitions as the partial order on their induced
    equivalence relations. -/
instance partition.partial_order : partial_order (subtype (@is_partition α)) :=
{ le := (≤),
  lt := λ x y, x ≤ y ∧ ¬y ≤ x,
  le_refl := λ _, @le_refl (setoid α) _ _,
  le_trans := λ _ _ _, @le_trans (setoid α) _ _ _ _,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ x y hx hy, let h := @le_antisymm (setoid α) _ _ _ hx hy in by
    rw [subtype.ext_iff_val, ←classes_mk_classes x.1 x.2, ←classes_mk_classes y.1 y.2, h] }

variables (α)

/-- The order-preserving bijection between equivalence relations and partitions of sets. -/
def partition.rel_iso :
  setoid α ≃o subtype (@is_partition α) :=
{ to_fun := λ r, ⟨r.classes, empty_not_mem_classes, classes_eqv_classes⟩,
  inv_fun := λ x, mk_classes x.1 x.2.2,
  left_inv := mk_classes_classes,
  right_inv := λ x, by rw [subtype.ext_iff_val, ←classes_mk_classes x.1 x.2],
  map_rel_iff' := λ x y,
    by { conv_rhs { rw [←mk_classes_classes x, ←mk_classes_classes y] }, refl } }

variables {α}

/-- A complete lattice instance for partitions; there is more infrastructure for the
    equivalent complete lattice on equivalence relations. -/
instance partition.complete_lattice : complete_lattice (subtype (@is_partition α)) :=
galois_insertion.lift_complete_lattice $ @rel_iso.to_galois_insertion
_ (subtype (@is_partition α)) _ (partial_order.to_preorder _) $ partition.rel_iso α

end partition

end setoid

/-- Constructive information associated with a partition of a type `α` indexed by another type `ι`,
`s : ι → set α`.

`indexed_partition.index` sends an element to its index, while `indexed_partition.some` sends
an index to an element of the corresponding set.

This type is primarily useful for definitional control of `s` - if this is not needed, then
`setoid.ker index` by itself may be sufficient. -/
structure indexed_partition {ι α : Type*} (s : ι → set α) :=
(eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j)
(some : ι → α)
(some_mem : ∀ i, some i ∈ s i)
(index : α → ι)
(mem_index : ∀ x, x ∈ s (index x))

/-- The non-constructive constructor for `indexed_partition`. -/
noncomputable
def indexed_partition.mk' {ι α : Type*} (s : ι → set α) (dis : ∀ i j, i ≠ j → disjoint (s i) (s j))
  (nonempty : ∀ i, (s i).nonempty) (ex : ∀ x, ∃ i, x ∈ s i) : indexed_partition s :=
{ eq_of_mem := λ x i j hxi hxj, classical.by_contradiction $ λ h, dis _ _ h ⟨hxi, hxj⟩,
  some := λ i, (nonempty i).some,
  some_mem := λ i, (nonempty i).some_spec,
  index := λ x, (ex x).some,
  mem_index := λ x, (ex x).some_spec }

namespace indexed_partition

open set

variables {ι α : Type*} {s : ι → set α} (hs : indexed_partition s)

/-- On a unique index set there is the obvious trivial partition -/
instance [unique ι] [inhabited α] :
  inhabited (indexed_partition (λ i : ι, (set.univ : set α))) :=
⟨{ eq_of_mem := λ x i j hi hj, subsingleton.elim _ _,
   some := λ i, default α,
   some_mem := set.mem_univ,
   index := λ a, default ι,
   mem_index := set.mem_univ }⟩

attribute [simp] some_mem mem_index

include hs

lemma exists_mem (x : α) : ∃ i, x ∈ s i := ⟨hs.index x, hs.mem_index x⟩

lemma Union : (⋃ i, s i) = univ :=
by { ext x, simp [hs.exists_mem x] }

lemma disjoint : ∀ {i j}, i ≠ j → disjoint (s i) (s j) :=
λ i j h x ⟨hxi, hxj⟩, h (hs.eq_of_mem hxi hxj)

lemma mem_iff_index_eq {x i} : x ∈ s i ↔ hs.index x = i :=
⟨λ hxi, (hs.eq_of_mem hxi (hs.mem_index x)).symm, λ h, h ▸ hs.mem_index _⟩

lemma eq (i) : s i = {x | hs.index x = i} :=
set.ext $ λ _, hs.mem_iff_index_eq

/-- The equivalence relation associated to an indexed partition. Two
elements are equivalent if they belong to the same set of the partition. -/
protected abbreviation setoid (hs : indexed_partition s) : setoid α :=
setoid.ker hs.index

@[simp] lemma index_some (i : ι) : hs.index (hs.some i) = i :=
(mem_iff_index_eq _).1 $ hs.some_mem i

lemma some_index (x : α) : hs.setoid.rel (hs.some (hs.index x)) x :=
hs.index_some (hs.index x)

/-- The quotient associated to an indexed partition. -/
protected def quotient := quotient hs.setoid

/-- The projection onto the quotient associated to an indexed partition. -/
def proj : α → hs.quotient := quotient.mk'

instance [inhabited α] : inhabited (hs.quotient) := ⟨hs.proj (default α)⟩

lemma proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.index x = hs.index y :=
quotient.eq_rel

@[simp] lemma proj_some_index (x : α) : hs.proj (hs.some (hs.index x)) = hs.proj x :=
quotient.eq'.2 (hs.some_index x)

/-- The obvious equivalence between the quotient associated to an indexed partition and
the indexing type. -/
def equiv_quotient : ι ≃ hs.quotient :=
(setoid.quotient_ker_equiv_of_right_inverse hs.index hs.some $ hs.index_some).symm

@[simp] lemma equiv_quotient_index_apply (x : α) : hs.equiv_quotient (hs.index x) = hs.proj x :=
hs.proj_eq_iff.mpr (some_index hs x)

@[simp] lemma equiv_quotient_symm_proj_apply (x : α) :
  hs.equiv_quotient.symm (hs.proj x) = hs.index x :=
rfl

lemma equiv_quotient_index : hs.equiv_quotient ∘ hs.index = hs.proj :=
funext hs.equiv_quotient_index_apply

/-- A map choosing a representative for each element of the quotient associated to an indexed
partition. This is a computable version of `quotient.out'` using `indexed_partition.some`. -/
def out : hs.quotient ↪ α :=
hs.equiv_quotient.symm.to_embedding.trans ⟨hs.some, function.left_inverse.injective hs.index_some⟩

/-- This lemma is analogous to `quotient.mk_out'`. -/
@[simp]
lemma out_proj (x : α) : hs.out (hs.proj x) = hs.some (hs.index x) :=
rfl

/-- The indices of `quotient.out'` and `indexed_partition.out` are equal. -/
lemma index_out' (x : hs.quotient) : hs.index (x.out') = hs.index (hs.out x) :=
quotient.induction_on' x $ λ x, (setoid.ker_apply_mk_out' x).trans (hs.index_some _).symm

/-- This lemma is analogous to `quotient.out_eq'`. -/
@[simp] lemma proj_out (x : hs.quotient) : hs.proj (hs.out x) = x :=
quotient.induction_on' x $ λ x, quotient.sound' $ hs.some_index x

lemma class_of {x : α} : set_of (hs.setoid.rel x) = s (hs.index x) :=
set.ext $ λ y, eq_comm.trans hs.mem_iff_index_eq.symm

lemma proj_fiber (x : hs.quotient) : hs.proj ⁻¹' {x} = s (hs.equiv_quotient.symm x) :=
quotient.induction_on' x $ λ x, begin
  ext y,
  simp only [set.mem_preimage, set.mem_singleton_iff, hs.mem_iff_index_eq],
  exact quotient.eq',
end

end indexed_partition
