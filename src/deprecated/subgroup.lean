/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison, Johan Commelin, Mario Carneiro,
  Michael Howes
-/
import group_theory.subgroup
import deprecated.submonoid
/-!
# Unbundled subgroups

This file defines unbundled multiplicative and additive subgroups. IMPORTANT : unless you
know what you are doing, you should be using bundled subgroups (`subgroup G`) and
not the `is_subgroup` structure defined in this file.

For the bundled form of submonoids see `group_theory/subgroup`.

We prove some results about centers, normalisers, kernels and so on. These results should
not in general be needed.

## Tags

subgroup, subgroups, is_subgroup
-/
open set function

variables {G : Type*} {H : Type*} {A : Type*} {a a₁ a₂ b c: G}

section group
variables [group G] [add_group A]

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
structure is_add_subgroup (s : set A) extends is_add_submonoid s : Prop :=
(neg_mem {a} : a ∈ s → -a ∈ s)

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
@[to_additive]
structure is_subgroup (s : set G) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)

@[to_additive]
lemma is_subgroup.div_mem {s : set G} (hs : is_subgroup s) {x y : G} (hx : x ∈ s) (hy : y ∈ s) :
  x / y ∈ s :=
by simpa only [div_eq_mul_inv] using hs.mul_mem hx (hs.inv_mem hy)

lemma additive.is_add_subgroup
  {s : set G} (hs : is_subgroup s) : @is_add_subgroup (additive G) _ s :=
@is_add_subgroup.mk (additive G) _ _ (additive.is_add_submonoid hs.to_is_submonoid)
  hs.inv_mem

theorem additive.is_add_subgroup_iff
  {s : set G} : @is_add_subgroup (additive G) _ s ↔ is_subgroup s :=
⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @is_subgroup.mk G _ _ ⟨h₁, @h₂⟩ @h₃,
  λ h, by exactI additive.is_add_subgroup h⟩

lemma multiplicative.is_subgroup
  {s : set A} (hs : is_add_subgroup s) : @is_subgroup (multiplicative A) _ s :=
@is_subgroup.mk (multiplicative A) _ _ (multiplicative.is_submonoid hs.to_is_add_submonoid)
  hs.neg_mem

theorem multiplicative.is_subgroup_iff
  {s : set A} : @is_subgroup (multiplicative A) _ s ↔ is_add_subgroup s :=
⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @is_add_subgroup.mk A _ _ ⟨h₁, @h₂⟩ @h₃,
  λ h, by exactI multiplicative.is_subgroup h⟩

/-- The group structure on a subgroup coerced to a type. -/
@[to_additive "The additive group structure on an additive subgroup coerced to a type."]
def subtype.group {s : set G} [hs : fact (is_subgroup s)] : group s :=
{ inv := λ x, ⟨(x:G)⁻¹, hs.elim.inv_mem x.2⟩,
  mul_left_inv := λ x, subtype.eq $ mul_left_inv x.1,
  div := λ x y, ⟨(x / y : G), hs.elim.div_mem x.2 y.2⟩,
  div_eq_mul_inv := λ x y, subtype.ext $ div_eq_mul_inv x.1 y.1,
  .. @subtype.monoid G _ s ⟨hs.elim.to_is_submonoid⟩}

/-- The commutative group structure on a commutative subgroup coerced to a type. -/
@[to_additive "The additive commutative group structure
 on a additive commutative subgroup coerced to a type."]
def subtype.comm_group {G : Type*} [comm_group G] {s : set G} [fact (is_subgroup s)] :
  comm_group s :=
{ mul_comm := λ x y, subtype.eq $ mul_comm x.1 y.1,
  .. subtype.group,  }

section
local attribute [instance] subtype.group subtype.add_group

@[simp, norm_cast, to_additive]
lemma is_subgroup.coe_inv {s : set G} [fact (is_subgroup s)] (a : s) : ((a⁻¹ : s) : G) = a⁻¹ := rfl
attribute [norm_cast] is_add_subgroup.coe_neg

@[simp, norm_cast] lemma is_subgroup.coe_gpow {s : set G} [hs : fact (is_subgroup s)]
  (a : s) (n : ℤ) : ((a ^ n : s) : G) = a ^ n :=
by induction n; simp [@is_submonoid.coe_pow G _ s ⟨hs.elim.to_is_submonoid⟩ a]

@[simp, norm_cast] lemma is_add_subgroup.gsmul_coe {s : set A} [hs : fact (is_add_subgroup s)]
  (a : s) (n : ℤ) : ((n • a : s) : A) = n • a :=
by induction n; simp [@is_add_submonoid.smul_coe A _ s ⟨hs.elim.to_is_add_submonoid⟩ a]

attribute [to_additive gsmul_coe] is_subgroup.coe_gpow

end

@[to_additive of_add_neg]
theorem is_subgroup.of_div (s : set G)
  (one_mem : (1:G) ∈ s) (div_mem : ∀{a b:G}, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) :
  is_subgroup s :=
have inv_mem : ∀a, a ∈ s → a⁻¹ ∈ s, from
  assume a ha,
  have 1 * a⁻¹ ∈ s, from div_mem one_mem ha,
  by simpa,
{ inv_mem := inv_mem,
  mul_mem := assume a b ha hb,
    have a * b⁻¹⁻¹ ∈ s, from div_mem ha (inv_mem b hb),
    by simpa,
  one_mem := one_mem }

theorem is_add_subgroup.of_sub (s : set A)
  (zero_mem : (0:A) ∈ s) (sub_mem : ∀{a b:A}, a ∈ s → b ∈ s → a - b ∈ s) :
  is_add_subgroup s :=
is_add_subgroup.of_add_neg s zero_mem
  (λ x y hx hy, by simpa only [sub_eq_add_neg] using sub_mem hx hy)

@[to_additive]
lemma is_subgroup.inter {s₁ s₂ : set G} (hs₁ : is_subgroup s₁) (hs₂ : is_subgroup s₂) :
  is_subgroup (s₁ ∩ s₂) :=
{ inv_mem := λ x hx, ⟨hs₁.inv_mem hx.1, hs₂.inv_mem hx.2⟩,
  ..is_submonoid.inter hs₁.to_is_submonoid hs₂.to_is_submonoid}

@[to_additive]
lemma is_subgroup.Inter {ι : Sort*} {s : ι → set G} (hs : ∀ y : ι, is_subgroup (s y)) :
  is_subgroup (set.Inter s) :=
{ inv_mem := λ x h, set.mem_Inter.2 $ λ y, is_subgroup.inv_mem (hs _) (set.mem_Inter.1 h y),
  ..is_submonoid.Inter (λ y, (hs y).to_is_submonoid) }

@[to_additive]
lemma is_subgroup_Union_of_directed {ι : Type*} [hι : nonempty ι]
  {s : ι → set G} (hs : ∀ i, is_subgroup (s i))
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_subgroup (⋃i, s i) :=
{ inv_mem := λ a ha,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    set.mem_Union.2 ⟨i, (hs i).inv_mem hi⟩,
  to_is_submonoid := is_submonoid_Union_of_directed (λ i, (hs i).to_is_submonoid) directed }

/-- `gpowers x` is the subset of `G` correponding to the subgroup generated by `x`. -/
def gpowers (x : G) : set G := set.range ((^) x : ℤ → G)

/-- `gmultiples x` is the subset of `A` correponding to the additive subgroup generated by `x`. -/
def gmultiples (x : A) : set A := set.range (λ i, gsmul i x)
attribute [to_additive gmultiples] gpowers

lemma gpowers.is_subgroup (x : G) : is_subgroup (gpowers x) :=
{ one_mem := ⟨(0:ℤ), by simp⟩,
  mul_mem := assume x₁ x₂ ⟨i₁, h₁⟩ ⟨i₂, h₂⟩, ⟨i₁ + i₂, by simp [gpow_add, *]⟩,
  inv_mem := assume x₀ ⟨i, h⟩, ⟨-i, by simp [h.symm]⟩ }

lemma gmultiples.is_add_subgroup (x : A) : is_add_subgroup (gmultiples x) :=
multiplicative.is_subgroup_iff.1 $ gpowers.is_subgroup _

attribute [to_additive] gpowers.is_subgroup

lemma is_subgroup.gpow_mem {a : G} {s : set G} (hs : is_subgroup s) (h : a ∈ s) : ∀{i:ℤ}, a ^ i ∈ s
| (n : ℕ) := by { rw [gpow_coe_nat], exact hs.to_is_submonoid.pow_mem h }
| -[1+ n] := by { rw [gpow_neg_succ_of_nat], exact hs.inv_mem (hs.to_is_submonoid.pow_mem h) }

lemma is_add_subgroup.gsmul_mem {a : A} {s : set A} (hs : is_add_subgroup s) :
  a ∈ s → ∀{i:ℤ}, gsmul i a ∈ s :=
@is_subgroup.gpow_mem (multiplicative A) _ _ _ (multiplicative.is_subgroup hs)

lemma gpowers_subset {a : G} {s : set G} (hs : is_subgroup s) (h : a ∈ s) : gpowers a ⊆ s :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := hs.gpow_mem h end

lemma gmultiples_subset {a : A} {s : set A} (hs : is_add_subgroup s) (h : a ∈ s) :
  gmultiples a ⊆ s :=
@gpowers_subset (multiplicative A) _ _ _ (multiplicative.is_subgroup hs) h

attribute [to_additive gmultiples_subset] gpowers_subset

lemma mem_gpowers {a : G} : a ∈ gpowers a := ⟨1, by simp⟩
lemma mem_gmultiples {a : A} : a ∈ gmultiples a := ⟨1, by simp⟩
attribute [to_additive mem_gmultiples] mem_gpowers

end group

namespace is_subgroup
open is_submonoid
variables [group G] {s : set G} (hs : is_subgroup s)

include hs

@[to_additive]
lemma inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
⟨λ h, by simpa using hs.inv_mem h, inv_mem hs⟩

@[to_additive]
lemma mul_mem_cancel_right (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
⟨λ hba, by simpa using hs.mul_mem hba (hs.inv_mem h), λ hb, hs.mul_mem hb h⟩

@[to_additive]
lemma mul_mem_cancel_left (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
⟨λ hab, by simpa using hs.mul_mem (hs.inv_mem h) hab, hs.mul_mem h⟩

end is_subgroup

/-- `is_normal_add_subgroup (s : set A)` expresses the fact that `s` is a normal additive subgroup
of the additive group `A`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : add_subgroup A` and `hs : S.normal`, and not via this structure. -/
structure is_normal_add_subgroup [add_group A] (s : set A) extends is_add_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : A, g + n + -g ∈ s)

/-- `is_normal_subgroup (s : set G)` expresses the fact that `s` is a normal subgroup
of the group `G`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : subgroup G` and not via this structure. -/
@[to_additive]
structure is_normal_subgroup [group G] (s : set G) extends is_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : G, g * n * g⁻¹ ∈ s)

@[to_additive]
lemma is_normal_subgroup_of_comm_group [comm_group G] {s : set G} (hs : is_subgroup s) :
  is_normal_subgroup s :=
{ normal := λ n hn g, by rwa [mul_right_comm, mul_right_inv, one_mul],
  ..hs }

lemma additive.is_normal_add_subgroup [group G]
  {s : set G} (hs : is_normal_subgroup s) : @is_normal_add_subgroup (additive G) _ s :=
@is_normal_add_subgroup.mk (additive G) _ _
  (additive.is_add_subgroup hs.to_is_subgroup)
  (is_normal_subgroup.normal hs)

theorem additive.is_normal_add_subgroup_iff [group G]
  {s : set G} : @is_normal_add_subgroup (additive G) _ s ↔ is_normal_subgroup s :=
⟨by rintro ⟨h₁, h₂⟩; exact
    @is_normal_subgroup.mk G _ _ (additive.is_add_subgroup_iff.1 h₁) @h₂,
  λ h, by exactI additive.is_normal_add_subgroup h⟩

lemma multiplicative.is_normal_subgroup [add_group A]
  {s : set A} (hs : is_normal_add_subgroup s) : @is_normal_subgroup (multiplicative A) _ s :=
@is_normal_subgroup.mk (multiplicative A) _ _
  (multiplicative.is_subgroup hs.to_is_add_subgroup)
  (is_normal_add_subgroup.normal hs)

theorem multiplicative.is_normal_subgroup_iff [add_group A]
  {s : set A} : @is_normal_subgroup (multiplicative A) _ s ↔ is_normal_add_subgroup s :=
⟨by rintro ⟨h₁, h₂⟩; exact
    @is_normal_add_subgroup.mk A _ _ (multiplicative.is_subgroup_iff.1 h₁) @h₂,
  λ h, by exactI multiplicative.is_normal_subgroup h⟩

namespace is_subgroup
variable [group G]

-- Normal subgroup properties
@[to_additive]
lemma mem_norm_comm {s : set G} (hs : is_normal_subgroup s) {a b : G} (hab : a * b ∈ s) :
  b * a ∈ s :=
have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ s, from hs.normal (a * b) hab a⁻¹,
by simp at h; exact h

@[to_additive]
lemma mem_norm_comm_iff {s : set G} (hs : is_normal_subgroup s) {a b : G} : a * b ∈ s ↔ b * a ∈ s :=
⟨mem_norm_comm hs, mem_norm_comm hs⟩

/-- The trivial subgroup -/
@[to_additive "the trivial additive subgroup"]
def trivial (G : Type*) [group G] : set G := {1}

@[simp, to_additive]
lemma mem_trivial {g : G} : g ∈ trivial G ↔ g = 1 :=
mem_singleton_iff

@[to_additive]
lemma trivial_normal : is_normal_subgroup (trivial G) :=
by refine {..}; simp [trivial] {contextual := tt}

@[to_additive]
lemma eq_trivial_iff {s : set G} (hs : is_subgroup s) :
  s = trivial G ↔ (∀ x ∈ s, x = (1 : G)) :=
by simp only [set.ext_iff, is_subgroup.mem_trivial];
  exact ⟨λ h x, (h x).1, λ h x, ⟨h x, λ hx, hx.symm ▸ hs.to_is_submonoid.one_mem⟩⟩

@[to_additive]
lemma univ_subgroup : is_normal_subgroup (@univ G) :=
by refine {..}; simp

/-- The underlying set of the center of a group. -/
@[to_additive add_center "The underlying set of the center of an additive group."]
def center (G : Type*) [group G] : set G := {z | ∀ g, g * z = z * g}

@[to_additive mem_add_center]
lemma mem_center {a : G} : a ∈ center G ↔ ∀g, g * a = a * g := iff.rfl

@[to_additive add_center_normal]
lemma center_normal : is_normal_subgroup (center G) :=
{ one_mem := by simp [center],
  mul_mem := assume a b ha hb g,
    by rw [←mul_assoc, mem_center.2 ha g, mul_assoc, mem_center.2 hb g, ←mul_assoc],
  inv_mem := assume a ha g,
    calc
      g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹ : by simp [ha g]
      ...     = a⁻¹ * g             : by rw [←mul_assoc, mul_assoc]; simp,
  normal := assume n ha g h,
    calc
      h * (g * n * g⁻¹) = h * n           : by simp [ha g, mul_assoc]
      ...               = g * g⁻¹ * n * h : by rw ha h; simp
      ...               = g * n * g⁻¹ * h : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc] }

/-- The underlying set of the normalizer of a subset `S : set G` of a group `G`. That is,
  the elements `g : G` such that `g * S * g⁻¹ = S`. -/
@[to_additive add_normalizer "The underlying set of the normalizer of a subset `S : set A` of an
  additive group `A`. That is, the elements `a : A` such that `a + S - a = S`."]
def normalizer (s : set G) : set G :=
{g : G | ∀ n, n ∈ s ↔ g * n * g⁻¹ ∈ s}

@[to_additive]
lemma normalizer_is_subgroup (s : set G) : is_subgroup (normalizer s) :=
{ one_mem := by simp [normalizer],
  mul_mem := λ a b (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s)
    (hb : ∀ n, n ∈ s ↔ b * n * b⁻¹ ∈ s) n,
    by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb],
  inv_mem := λ a (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) n,
    by rw [ha (a⁻¹ * n * a⁻¹⁻¹)];
    simp [mul_assoc] }

@[to_additive subset_add_normalizer]
lemma subset_normalizer {s : set G} (hs : is_subgroup s) : s ⊆ normalizer s :=
λ g hg n, by rw [is_subgroup.mul_mem_cancel_right hs ((is_subgroup.inv_mem_iff hs).2 hg),
  is_subgroup.mul_mem_cancel_left hs hg]

local attribute [instance] subtype.group
/-- Every subgroup is a normal subgroup of its normalizer -/
@[to_additive add_normal_in_add_normalizer]
lemma normal_in_normalizer (s : set G) (hs : is_subgroup s) :
  @is_normal_subgroup (normalizer s) (@subtype.group _ _ _ ⟨normalizer_is_subgroup _⟩)
  (subtype.val ⁻¹' s : set (normalizer s)) :=
{ one_mem := show (1 : G) ∈ s, from hs.to_is_submonoid.one_mem,
  mul_mem := λ a b ha hb, show (a * b : G) ∈ s, from hs.to_is_submonoid.mul_mem ha hb,
  inv_mem := λ a ha, show (a⁻¹ : G) ∈ s, from hs.inv_mem ha,
  normal := λ a ha ⟨m, hm⟩, (hm a).1 ha }

end is_subgroup

-- Homomorphism subgroups
namespace is_group_hom
open is_submonoid is_subgroup
open is_mul_hom (map_mul)

/-- `ker f : set G` is the underlying subset of the kernel of a map `G → H`. -/
@[to_additive "`ker f : set A` is the underlying subset of the kernel of a map `A → B`"]
def ker [group H] (f : G → H) : set G := preimage f (trivial H)

@[to_additive]
lemma mem_ker [group H] (f : G → H) {x : G} : x ∈ ker f ↔ f x = 1 :=
mem_trivial

variables [group G] [group H]

@[to_additive]
lemma one_ker_inv {f : G → H} (hf : is_group_hom f) {a b : G} (h : f (a * b⁻¹) = 1) : f a = f b :=
begin
  rw [hf.map_mul, hf.map_inv] at h,
  rw [←inv_inv (f b), eq_inv_of_mul_eq_one h]
end

@[to_additive]
lemma one_ker_inv' {f : G → H} (hf : is_group_hom f) {a b : G} (h : f (a⁻¹ * b) = 1) : f a = f b :=
begin
  rw [hf.map_mul, hf.map_inv] at h,
  apply inv_injective,
  rw eq_inv_of_mul_eq_one h
end

@[to_additive]
lemma inv_ker_one {f : G → H} (hf : is_group_hom f) {a b : G} (h : f a = f b) : f (a * b⁻¹) = 1 :=
have f a * (f b)⁻¹ = 1, by rw [h, mul_right_inv],
by rwa [←hf.map_inv, ←hf.map_mul] at this

@[to_additive]
lemma inv_ker_one' {f : G → H} (hf : is_group_hom f) {a b : G} (h : f a = f b) : f (a⁻¹ * b) = 1 :=
have (f a)⁻¹ * f b = 1, by rw [h, mul_left_inv],
by rwa [←hf.map_inv, ←hf.map_mul] at this

@[to_additive]
lemma one_iff_ker_inv {f : G → H} (hf : is_group_hom f) (a b : G) : f a = f b ↔ f (a * b⁻¹) = 1 :=
⟨hf.inv_ker_one, hf.one_ker_inv⟩

@[to_additive]
lemma one_iff_ker_inv' {f : G → H} (hf : is_group_hom f) (a b : G) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
⟨hf.inv_ker_one', hf.one_ker_inv'⟩

@[to_additive]
lemma inv_iff_ker {f : G → H} (hf : is_group_hom f) (a b : G) : f a = f b ↔ a * b⁻¹ ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv hf _ _

@[to_additive]
lemma inv_iff_ker' {f : G → H} (hf : is_group_hom f) (a b : G) : f a = f b ↔ a⁻¹ * b ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv' hf _ _

@[to_additive]
lemma image_subgroup {f : G → H} (hf : is_group_hom f) {s : set G} (hs : is_subgroup s) :
  is_subgroup (f '' s) :=
{ mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
             ⟨b₁ * b₂, hs.mul_mem hb₁ hb₂, by simp [eq₁, eq₂, hf.map_mul]⟩,
  one_mem := ⟨1, hs.to_is_submonoid.one_mem, hf.map_one⟩,
  inv_mem := assume a ⟨b, hb, eq⟩, ⟨b⁻¹, hs.inv_mem hb, by { rw hf.map_inv, simp * }⟩ }

@[to_additive]
lemma range_subgroup {f : G → H} (hf : is_group_hom f) : is_subgroup (set.range f) :=
@set.image_univ _ _ f ▸ hf.image_subgroup univ_subgroup.to_is_subgroup

local attribute [simp] one_mem inv_mem mul_mem is_normal_subgroup.normal

@[to_additive]
lemma preimage {f : G → H} (hf : is_group_hom f) {s : set H} (hs : is_subgroup s) :
  is_subgroup (f ⁻¹' s) :=
by { refine {..};
     simp [hs.one_mem, hs.mul_mem, hs.inv_mem, hf.map_mul, hf.map_one, hf.map_inv, @inv_mem H _ s]
     {contextual := tt} }

@[to_additive]
lemma preimage_normal {f : G → H} (hf : is_group_hom f) {s : set H} (hs : is_normal_subgroup s) :
  is_normal_subgroup (f ⁻¹' s) :=
{ one_mem := by simp [hf.map_one, hs.to_is_subgroup.one_mem],
  mul_mem := by simp [hf.map_mul, hs.to_is_subgroup.mul_mem] {contextual := tt},
  inv_mem := by simp [hf.map_inv, hs.to_is_subgroup.inv_mem] {contextual := tt},
  normal := by simp [hs.normal, hf.map_mul, hf.map_inv] {contextual := tt}}

@[to_additive]
lemma is_normal_subgroup_ker {f : G → H} (hf : is_group_hom f) : is_normal_subgroup (ker f) :=
hf.preimage_normal (trivial_normal)

@[to_additive]
lemma injective_of_trivial_ker {f : G → H} (hf : is_group_hom f) (h : ker f = trivial G) :
  function.injective f :=
begin
  intros a₁ a₂ hfa,
  simp [ext_iff, ker, is_subgroup.trivial] at h,
  have ha : a₁ * a₂⁻¹ = 1, by rw ←h; exact hf.inv_ker_one hfa,
  rw [eq_inv_of_mul_eq_one ha, inv_inv a₂]
end

@[to_additive]
lemma trivial_ker_of_injective {f : G → H} (hf : is_group_hom f) (h : function.injective f) :
  ker f = trivial G :=
set.ext $ assume x, iff.intro
  (assume hx,
    suffices f x = f 1, by simpa using h this,
    by simp [hf.map_one]; rwa [mem_ker] at hx)
  (by simp [mem_ker, hf.map_one] {contextual := tt})

@[to_additive]
lemma injective_iff_trivial_ker {f : G → H} (hf : is_group_hom f) :
  function.injective f ↔ ker f = trivial G :=
⟨hf.trivial_ker_of_injective, hf.injective_of_trivial_ker⟩

@[to_additive]
lemma trivial_ker_iff_eq_one {f : G → H} (hf : is_group_hom f) :
  ker f = trivial G ↔ ∀ x, f x = 1 → x = 1 :=
by rw set.ext_iff; simp [ker]; exact
⟨λ h x hx, (h x).1 hx, λ h x, ⟨h x, λ hx, by rw [hx, hf.map_one]⟩⟩

end is_group_hom

section
local attribute [instance] subtype.group

@[to_additive]
lemma subtype_val.is_group_hom [group G] {s : set G} [hs : fact (is_subgroup s)] :
  is_group_hom (subtype.val : s → G) :=
{ ..@subtype_val.is_monoid_hom _ _ _ ⟨hs.elim.to_is_submonoid⟩}

@[to_additive]
lemma coe.is_group_hom [group G] {s : set G} [fact (is_subgroup s)] :
  is_group_hom (coe : s → G) := subtype_val.is_group_hom

@[to_additive]
lemma subtype_mk.is_group_hom [group G] [group H] {s : set G}
  [hs : fact (is_subgroup s)] {f : H → G} (hf : is_group_hom f) (h : ∀ x, f x ∈ s) :
  is_group_hom (λ x, (⟨f x, h x⟩ : s)) :=
{ ..@subtype_mk.is_monoid_hom _ _ _ _ _ ⟨hs.elim.to_is_submonoid⟩ _ hf.to_is_monoid_hom h }

@[to_additive]
lemma set_inclusion.is_group_hom [group G] {s t : set G}
  [fact (is_subgroup s)] [fact (is_subgroup t)]
  (h : s ⊆ t) : is_group_hom (set.inclusion h) :=
subtype_mk.is_group_hom coe.is_group_hom _

end

section
local attribute [instance] subtype.monoid

/-- `subtype.val : set.range f → H` as a monoid homomorphism, when `f` is a monoid homomorphism. -/
@[to_additive "`subtype.val : set.range f → H` as an additive monoid homomorphism, when `f` is
an additive monoid homomorphism."]
def monoid_hom.range_subtype_val [monoid G] [monoid H] (f : G →* H) :
  @monoid_hom (set.range f) H
  (@monoid.to_mul_one_class (set.range f)
    (@subtype.monoid _ _ _ ⟨range.is_submonoid f.is_monoid_hom_coe⟩)) _ :=
@monoid_hom.of _ _
  (@monoid.to_mul_one_class (set.range f)
    (@subtype.monoid _ _ _ ⟨range.is_submonoid f.is_monoid_hom_coe⟩)) _ _
  (@coe.is_monoid_hom _ _ _ ⟨range.is_submonoid f.is_monoid_hom_coe⟩)

/-- `set.range_factorization f : G → set.range f` as a monoid homomorphism, when `f` is a monoid
homomorphism. -/
@[to_additive "`set.range_factorization f : G → set.range f` as an additive monoid homomorphism,
when `f` is an additive monoid homomorphism."]
def monoid_hom.range_factorization [monoid G] [monoid H] (f : G →* H) :
  @monoid_hom G (set.range f) _ (@monoid.to_mul_one_class (set.range f)
    (@subtype.monoid _ _ _ ⟨range.is_submonoid f.is_monoid_hom_coe⟩)) :=
{ to_fun := set.range_factorization f,
  map_one' := by { dsimp [set.range_factorization], simp, refl, },
  map_mul' := by { intros, dsimp [set.range_factorization], simp, refl, } }

end

namespace add_group

variables [add_group A]

/-- If `A` is an additive group and `s : set A`, then `in_closure s : set A` is the underlying
subset of the subgroup generated by `s`. -/
inductive in_closure (s : set A) : A → Prop
| basic {a : A} : a ∈ s → in_closure a
| zero : in_closure 0
| neg {a : A} : in_closure a → in_closure (-a)
| add {a b : A} : in_closure a → in_closure b → in_closure (a + b)

end add_group

namespace group
open is_submonoid is_subgroup

variables [group G] {s : set G}

/-- If `G` is a group and `s : set G`, then `in_closure s : set G` is the underlying
subset of the subgroup generated by `s`. -/
@[to_additive]
inductive in_closure (s : set G) : G → Prop
| basic {a : G} : a ∈ s → in_closure a
| one : in_closure 1
| inv {a : G} : in_closure a → in_closure a⁻¹
| mul {a b : G} : in_closure a → in_closure b → in_closure (a * b)

/-- `group.closure s` is the subgroup generated by `s`, i.e. the smallest subgroup containg `s`. -/
@[to_additive "`add_group.closure s` is the additive subgroup generated by `s`, i.e., the
  smallest additive subgroup containing `s`."]
def closure (s : set G) : set G := {a | in_closure s a }

@[to_additive]
lemma mem_closure {a : G} : a ∈ s → a ∈ closure s := in_closure.basic

@[to_additive]
lemma closure.is_subgroup (s : set G) : is_subgroup (closure s) :=
{ one_mem := in_closure.one,
  mul_mem := assume a b, in_closure.mul,
  inv_mem := assume a, in_closure.inv }

@[to_additive]
theorem subset_closure {s : set G} : s ⊆ closure s := λ a, mem_closure

@[to_additive]
theorem closure_subset {s t : set G} (ht : is_subgroup t) (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, ht.one_mem, ht.mul_mem, inv_mem_iff]

@[to_additive]
lemma closure_subset_iff {s t : set G} (ht : is_subgroup t) : closure s ⊆ t ↔ s ⊆ t :=
⟨assume h b ha, h (mem_closure ha), assume h b ha, closure_subset ht h ha⟩

@[to_additive]
theorem closure_mono {s t : set G} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset (closure.is_subgroup _) $ set.subset.trans h subset_closure

@[simp, to_additive]
lemma closure_subgroup {s : set G} (hs : is_subgroup s) : closure s = s :=
set.subset.antisymm (closure_subset hs $ set.subset.refl s) subset_closure

@[to_additive]
theorem exists_list_of_mem_closure {s : set G} {a : G} (h : a ∈ closure s) :
  (∃l:list G, (∀x∈l, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.prod = a) :=
in_closure.rec_on h
  (λ x hxs, ⟨[x], list.forall_mem_singleton.2 $ or.inl hxs, one_mul _⟩)
  ⟨[], list.forall_mem_nil _, rfl⟩
  (λ x _ ⟨L, HL1, HL2⟩, ⟨L.reverse.map has_inv.inv,
    λ x hx, let ⟨y, hy1, hy2⟩ := list.exists_of_mem_map hx in
      hy2 ▸ or.imp id (by rw [inv_inv]; exact id) (HL1 _ $ list.mem_reverse.1 hy1).symm,
      HL2 ▸ list.rec_on L one_inv.symm (λ hd tl ih,
        by rw [list.reverse_cons, list.map_append, list.prod_append, ih, list.map_singleton,
            list.prod_cons, list.prod_nil, mul_one, list.prod_cons, mul_inv_rev])⟩)
  (λ x y hx hy ⟨L1, HL1, HL2⟩ ⟨L2, HL3, HL4⟩, ⟨L1 ++ L2, list.forall_mem_append.2 ⟨HL1, HL3⟩,
    by rw [list.prod_append, HL2, HL4]⟩)

@[to_additive]
lemma image_closure [group H] {f : G → H} (hf : is_group_hom f) (s : set G) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [hf.to_is_monoid_hom.map_one],
      apply is_submonoid.one_mem (closure.is_subgroup _).to_is_submonoid, },
    { rw [hf.map_inv],
      apply is_subgroup.inv_mem (closure.is_subgroup _), assumption },
    { rw [hf.to_is_monoid_hom.map_mul],
      solve_by_elim [is_submonoid.mul_mem (closure.is_subgroup _).to_is_submonoid] }
  end
  (closure_subset (hf.image_subgroup $ closure.is_subgroup _) $ set.image_subset _ subset_closure)

@[to_additive]
theorem mclosure_subset {s : set G} : monoid.closure s ⊆ closure s :=
monoid.closure_subset (closure.is_subgroup _).to_is_submonoid $ subset_closure

@[to_additive]
theorem mclosure_inv_subset {s : set G} : monoid.closure (has_inv.inv ⁻¹' s) ⊆ closure s :=
monoid.closure_subset (closure.is_subgroup _).to_is_submonoid $ λ x hx,
  inv_inv x ▸ ((closure.is_subgroup _).inv_mem $ subset_closure hx)

@[to_additive]
theorem closure_eq_mclosure {s : set G} : closure s = monoid.closure (s ∪ has_inv.inv ⁻¹' s) :=
set.subset.antisymm
  (@closure_subset _ _ _ (monoid.closure (s ∪ has_inv.inv ⁻¹' s))
    { one_mem := (monoid.closure.is_submonoid _).one_mem,
      mul_mem := (monoid.closure.is_submonoid _).mul_mem,
      inv_mem := λ x hx, monoid.in_closure.rec_on hx
      (λ x hx, or.cases_on hx (λ hx, monoid.subset_closure $ or.inr $
        show x⁻¹⁻¹ ∈ s, from (inv_inv x).symm ▸ hx)
        (λ hx, monoid.subset_closure $ or.inl hx))
      ((@one_inv G _).symm ▸ is_submonoid.one_mem (monoid.closure.is_submonoid _))
      (λ x y hx hy ihx ihy,
        (mul_inv_rev x y).symm ▸ is_submonoid.mul_mem (monoid.closure.is_submonoid _) ihy ihx) }
    (set.subset.trans (set.subset_union_left _ _) monoid.subset_closure))
  (monoid.closure_subset (closure.is_subgroup _).to_is_submonoid $ set.union_subset subset_closure $
    λ x hx, inv_inv x ▸ (is_subgroup.inv_mem (closure.is_subgroup _) $ subset_closure hx))

@[to_additive]
theorem mem_closure_union_iff {G : Type*} [comm_group G] {s t : set G} {x : G} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
begin
  simp only [closure_eq_mclosure, monoid.mem_closure_union_iff, exists_prop, preimage_union], split,
  { rintro ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, rfl⟩,
    refine ⟨_, ⟨_, hys, _, hzs, rfl⟩, _, ⟨_, hyt, _, hzt, rfl⟩, _⟩,
    rw [mul_assoc, mul_assoc, mul_left_comm zs] },
  { rintro ⟨_, ⟨ys, hys, zs, hzs, rfl⟩, _, ⟨yt, hyt, zt, hzt, rfl⟩, rfl⟩,
    refine ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, _⟩,
    rw [mul_assoc, mul_assoc, mul_left_comm yt] }
end

@[to_additive gmultiples_eq_closure]
theorem gpowers_eq_closure {a : G} : gpowers a = closure {a} :=
subset.antisymm
  (gpowers_subset (closure.is_subgroup _) $ mem_closure $ by simp)
  (closure_subset (gpowers.is_subgroup _) $ by simp [mem_gpowers])

end group

namespace is_subgroup
variable [group G]

@[to_additive]
lemma trivial_eq_closure : trivial G = group.closure ∅ :=
subset.antisymm
  (by simp [set.subset_def, (group.closure.is_subgroup _).one_mem])
  (group.closure_subset (trivial_normal).to_is_subgroup $ by simp)

end is_subgroup

/-The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/

namespace group
variables {s : set G} [group G]

lemma conjugates_of_subset {t : set G} (ht : is_normal_subgroup t) {a : G} (h : a ∈ t) :
  conjugates_of a ⊆ t :=
λ x hc,
begin
  obtain ⟨c, w⟩ := is_conj_iff.1 hc,
  have H := is_normal_subgroup.normal ht a h c,
  rwa ←w,
end

theorem conjugates_of_set_subset' {s t : set G} (ht : is_normal_subgroup t) (h : s ⊆ t) :
  conjugates_of_set s ⊆ t :=
set.bUnion_subset (λ x H, conjugates_of_subset ht (h H))

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def normal_closure (s : set G) : set G := closure (conjugates_of_set s)

theorem conjugates_of_set_subset_normal_closure : conjugates_of_set s ⊆ normal_closure s :=
subset_closure

theorem subset_normal_closure : s ⊆ normal_closure s :=
set.subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure

/-- The normal closure of a set is a subgroup. -/
lemma normal_closure.is_subgroup (s : set G) : is_subgroup (normal_closure s) :=
closure.is_subgroup (conjugates_of_set s)

/-- The normal closure of s is a normal subgroup. -/
lemma normal_closure.is_normal : is_normal_subgroup (normal_closure s) :=
{ normal := λ n h g,
begin
  induction h with x hx x hx ihx x y hx hy ihx ihy,
  {exact (conjugates_of_set_subset_normal_closure (conj_mem_conjugates_of_set hx))},
  {simpa using (normal_closure.is_subgroup s).one_mem},
  {rw ←conj_inv,
   exact ((normal_closure.is_subgroup _).inv_mem ihx)},
  {rw ←conj_mul,
   exact ((normal_closure.is_subgroup _).to_is_submonoid.mul_mem ihx ihy)},
end,
..normal_closure.is_subgroup _ }

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normal_closure_subset {s t : set G} (ht : is_normal_subgroup t) (h : s ⊆ t) :
  normal_closure s ⊆ t :=
λ a w,
begin
  induction w with x hx x hx ihx x y hx hy ihx ihy,
  {exact (conjugates_of_set_subset' ht h $ hx)},
  {exact ht.to_is_subgroup.to_is_submonoid.one_mem},
  {exact ht.to_is_subgroup.inv_mem ihx},
  {exact ht.to_is_subgroup.to_is_submonoid.mul_mem ihx ihy}
end

lemma normal_closure_subset_iff {s t : set G} (ht : is_normal_subgroup t) :
  s ⊆ t ↔ normal_closure s ⊆ t :=
⟨normal_closure_subset ht, set.subset.trans (subset_normal_closure)⟩

theorem normal_closure_mono {s t : set G} : s ⊆ t → normal_closure s ⊆ normal_closure t :=
λ h, normal_closure_subset normal_closure.is_normal (set.subset.trans h (subset_normal_closure))

end group

/-- Create a bundled subgroup from a set `s` and `[is_subgroup s]`. -/
@[to_additive "Create a bundled additive subgroup from a set `s` and `[is_add_subgroup s]`."]
def subgroup.of [group G] {s : set G} (h : is_subgroup s) : subgroup G :=
{ carrier := s,
  one_mem' := h.1.1,
  mul_mem' := h.1.2,
  inv_mem' := h.2 }

@[to_additive]
lemma subgroup.is_subgroup [group G] (K : subgroup G) : is_subgroup (K : set G) :=
{ one_mem := K.one_mem',
  mul_mem := K.mul_mem',
  inv_mem := K.inv_mem' }

-- this will never fire if it's an instance
@[to_additive]
lemma subgroup.of_normal [group G] (s : set G) (h : is_subgroup s) (n : is_normal_subgroup s) :
  subgroup.normal (subgroup.of h) :=
{ conj_mem := n.normal, }
