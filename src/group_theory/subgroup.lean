/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison, Johan Commelin, Mario Carneiro,
  Michael Howes
-/
import group_theory.submonoid
open set function

variables {G : Type*} {H : Type*} {A : Type*} {a a₁ a₂ b c: G}

section group
variables [group G] [add_group A]

@[to_additive]
lemma injective_mul {a : G} : injective ((*) a) :=
assume a₁ a₂ h,
have a⁻¹ * a * a₁ = a⁻¹ * a * a₂, by rw [mul_assoc, mul_assoc, h],
by rwa [inv_mul_self, one_mul, one_mul] at this

section prio
set_option default_priority 100 -- see Note [default priority]
/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
class is_add_subgroup (s : set A) extends is_add_submonoid s : Prop :=
(neg_mem {a} : a ∈ s → -a ∈ s)

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
@[to_additive is_add_subgroup]
class is_subgroup (s : set G) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)
end prio

lemma additive.is_add_subgroup
  (s : set G) [is_subgroup s] : @is_add_subgroup (additive G) _ s :=
@is_add_subgroup.mk (additive G) _ _ (additive.is_add_submonoid _)
  (@is_subgroup.inv_mem _ _ _ _)

theorem additive.is_add_subgroup_iff
  {s : set G} : @is_add_subgroup (additive G) _ s ↔ is_subgroup s :=
⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @is_subgroup.mk G _ _ ⟨h₁, @h₂⟩ @h₃,
  λ h, by exactI additive.is_add_subgroup _⟩

lemma multiplicative.is_subgroup
  (s : set A) [is_add_subgroup s] : @is_subgroup (multiplicative A) _ s :=
@is_subgroup.mk (multiplicative A) _ _ (multiplicative.is_submonoid _)
  (@is_add_subgroup.neg_mem _ _ _ _)

theorem multiplicative.is_subgroup_iff
  {s : set A} : @is_subgroup (multiplicative A) _ s ↔ is_add_subgroup s :=
⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @is_add_subgroup.mk A _ _ ⟨h₁, @h₂⟩ @h₃,
  λ h, by exactI multiplicative.is_subgroup _⟩

@[to_additive add_group]
instance subtype.group {s : set G} [is_subgroup s] : group s :=
{ inv := λ x, ⟨(x:G)⁻¹, is_subgroup.inv_mem x.2⟩,
  mul_left_inv := λ x, subtype.eq $ mul_left_inv x.1,
  .. subtype.monoid }

@[to_additive add_comm_group]
instance subtype.comm_group {G : Type*} [comm_group G] {s : set G} [is_subgroup s] : comm_group s :=
{ .. subtype.group, .. subtype.comm_monoid }

@[simp, norm_cast, to_additive]
lemma is_subgroup.coe_inv {s : set G} [is_subgroup s] (a : s) : ((a⁻¹ : s) : G) = a⁻¹ := rfl
attribute [norm_cast] is_add_subgroup.coe_neg

@[simp, norm_cast] lemma is_subgroup.coe_gpow {s : set G} [is_subgroup s] (a : s) (n : ℤ) : ((a ^ n : s) : G) = a ^ n :=
by induction n; simp [is_submonoid.coe_pow a]

@[simp, norm_cast] lemma is_add_subgroup.gsmul_coe {s : set A} [is_add_subgroup s] (a : s) (n : ℤ) :
  ((gsmul n a : s) : A) = gsmul n a :=
by induction n; simp [is_add_submonoid.smul_coe a]
attribute [to_additive gsmul_coe] is_subgroup.coe_gpow

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
is_add_subgroup.of_add_neg s zero_mem (λ x y hx hy, sub_mem hx hy)

@[to_additive]
instance is_subgroup.inter (s₁ s₂ : set G) [is_subgroup s₁] [is_subgroup s₂] :
  is_subgroup (s₁ ∩ s₂) :=
{ inv_mem := λ x hx, ⟨is_subgroup.inv_mem hx.1, is_subgroup.inv_mem hx.2⟩ }

@[to_additive]
instance is_subgroup.Inter {ι : Sort*} (s : ι → set G) [h : ∀ y : ι, is_subgroup (s y)] :
  is_subgroup (set.Inter s) :=
{ inv_mem := λ x h, set.mem_Inter.2 $ λ y, is_subgroup.inv_mem (set.mem_Inter.1 h y) }

@[to_additive is_add_subgroup_Union_of_directed]
lemma is_subgroup_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set G) [∀ i, is_subgroup (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_subgroup (⋃i, s i) :=
{ inv_mem := λ a ha,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    set.mem_Union.2 ⟨i, is_subgroup.inv_mem hi⟩,
  to_is_submonoid := is_submonoid_Union_of_directed s directed }

def gpowers (x : G) : set G := set.range ((^) x : ℤ → G)
def gmultiples (x : A) : set A := set.range (λ i, gsmul i x)
attribute [to_additive gmultiples] gpowers

instance gpowers.is_subgroup (x : G) : is_subgroup (gpowers x) :=
{ one_mem := ⟨(0:ℤ), by simp⟩,
  mul_mem := assume x₁ x₂ ⟨i₁, h₁⟩ ⟨i₂, h₂⟩, ⟨i₁ + i₂, by simp [gpow_add, *]⟩,
  inv_mem := assume x₀ ⟨i, h⟩, ⟨-i, by simp [h.symm]⟩ }

instance gmultiples.is_add_subgroup (x : A) : is_add_subgroup (gmultiples x) :=
multiplicative.is_subgroup_iff.1 $ gpowers.is_subgroup _
attribute [to_additive is_add_subgroup] gpowers.is_subgroup

lemma is_subgroup.gpow_mem {a : G} {s : set G} [is_subgroup s] (h : a ∈ s) : ∀{i:ℤ}, a ^ i ∈ s
| (n : ℕ) := is_submonoid.pow_mem h
| -[1+ n] := is_subgroup.inv_mem (is_submonoid.pow_mem h)

lemma is_add_subgroup.gsmul_mem {a : A} {s : set A} [is_add_subgroup s] : a ∈ s → ∀{i:ℤ}, gsmul i a ∈ s :=
@is_subgroup.gpow_mem (multiplicative A) _ _ _ (multiplicative.is_subgroup _)

lemma gpowers_subset {a : G} {s : set G} [is_subgroup s] (h : a ∈ s) : gpowers a ⊆ s :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := is_subgroup.gpow_mem h end

lemma gmultiples_subset {a : A} {s : set A} [is_add_subgroup s] (h : a ∈ s) : gmultiples a ⊆ s :=
@gpowers_subset (multiplicative A) _ _ _ (multiplicative.is_subgroup _) h

attribute [to_additive gmultiples_subset] gpowers_subset

lemma mem_gpowers {a : G} : a ∈ gpowers a := ⟨1, by simp⟩
lemma mem_gmultiples {a : A} : a ∈ gmultiples a := ⟨1, by simp⟩
attribute [to_additive mem_gmultiples] mem_gpowers

end group

namespace is_subgroup
open is_submonoid
variables [group G] (s : set G) [is_subgroup s]

@[to_additive]
lemma inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
⟨λ h, by simpa using inv_mem h, inv_mem⟩

@[to_additive]
lemma mul_mem_cancel_left (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
⟨λ hba, by simpa using mul_mem hba (inv_mem h), λ hb, mul_mem hb h⟩

@[to_additive]
lemma mul_mem_cancel_right (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
⟨λ hab, by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

end is_subgroup

theorem is_add_subgroup.sub_mem {A} [add_group A] (s : set A) [is_add_subgroup s] (a b : A)
  (ha : a ∈ s) (hb : b ∈ s) : a - b ∈ s :=
is_add_submonoid.add_mem ha (is_add_subgroup.neg_mem hb)

section prio
set_option default_priority 100 -- see Note [default priority]
class normal_add_subgroup [add_group A] (s : set A) extends is_add_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : A, g + n - g ∈ s)

@[to_additive normal_add_subgroup]
class normal_subgroup [group G] (s : set G) extends is_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : G, g * n * g⁻¹ ∈ s)
end prio

@[to_additive normal_add_subgroup_of_add_comm_group]
lemma normal_subgroup_of_comm_group [comm_group G] (s : set G) [hs : is_subgroup s] :
  normal_subgroup s :=
{ normal := λ n hn g, by rwa [mul_right_comm, mul_right_inv, one_mul],
  ..hs }

lemma additive.normal_add_subgroup [group G]
  (s : set G) [normal_subgroup s] : @normal_add_subgroup (additive G) _ s :=
@normal_add_subgroup.mk (additive G) _ _
  (@additive.is_add_subgroup G _ _ _)
  (@normal_subgroup.normal _ _ _ _)

theorem additive.normal_add_subgroup_iff [group G]
  {s : set G} : @normal_add_subgroup (additive G) _ s ↔ normal_subgroup s :=
⟨by rintro ⟨h₁, h₂⟩; exact
    @normal_subgroup.mk G _ _ (additive.is_add_subgroup_iff.1 h₁) @h₂,
  λ h, by exactI additive.normal_add_subgroup _⟩

lemma multiplicative.normal_subgroup [add_group A]
  (s : set A) [normal_add_subgroup s] : @normal_subgroup (multiplicative A) _ s :=
@normal_subgroup.mk (multiplicative A) _ _
  (@multiplicative.is_subgroup A _ _ _)
  (@normal_add_subgroup.normal _ _ _ _)

theorem multiplicative.normal_subgroup_iff [add_group A]
  {s : set A} : @normal_subgroup (multiplicative A) _ s ↔ normal_add_subgroup s :=
⟨by rintro ⟨h₁, h₂⟩; exact
    @normal_add_subgroup.mk A _ _ (multiplicative.is_subgroup_iff.1 h₁) @h₂,
  λ h, by exactI multiplicative.normal_subgroup _⟩

namespace is_subgroup
variable [group G]

-- Normal subgroup properties
@[to_additive]
lemma mem_norm_comm {s : set G} [normal_subgroup s] {a b : G} (hab : a * b ∈ s) : b * a ∈ s :=
have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ s, from normal_subgroup.normal (a * b) hab a⁻¹,
by simp at h; exact h

@[to_additive]
lemma mem_norm_comm_iff {s : set G} [normal_subgroup s] {a b : G} : a * b ∈ s ↔ b * a ∈ s :=
⟨mem_norm_comm, mem_norm_comm⟩

/-- The trivial subgroup -/
@[to_additive]
def trivial (G : Type*) [group G] : set G := {1}

@[simp, to_additive]
lemma mem_trivial {g : G} : g ∈ trivial G ↔ g = 1 :=
mem_singleton_iff

@[to_additive]
instance trivial_normal : normal_subgroup (trivial G) :=
by refine {..}; simp [trivial] {contextual := tt}

@[to_additive]
lemma eq_trivial_iff {s : set G} [is_subgroup s] :
  s = trivial G ↔ (∀ x ∈ s, x = (1 : G)) :=
by simp only [set.ext_iff, is_subgroup.mem_trivial];
  exact ⟨λ h x, (h x).1, λ h x, ⟨h x, λ hx, hx.symm ▸ is_submonoid.one_mem⟩⟩

@[to_additive]
instance univ_subgroup : normal_subgroup (@univ G) :=
by refine {..}; simp

@[to_additive add_center]
def center (G : Type*) [group G] : set G := {z | ∀ g, g * z = z * g}

@[to_additive mem_add_center]
lemma mem_center {a : G} : a ∈ center G ↔ ∀g, g * a = a * g := iff.rfl

@[to_additive add_center_normal]
instance center_normal : normal_subgroup (center G) :=
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

@[to_additive add_normalizer]
def normalizer (s : set G) : set G :=
{g : G | ∀ n, n ∈ s ↔ g * n * g⁻¹ ∈ s}

@[to_additive normalizer_is_add_subgroup]
instance normalizer_is_subgroup (s : set G) : is_subgroup (normalizer s) :=
{ one_mem := by simp [normalizer],
  mul_mem := λ a b (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s)
    (hb : ∀ n, n ∈ s ↔ b * n * b⁻¹ ∈ s) n,
    by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb],
  inv_mem := λ a (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) n,
    by rw [ha (a⁻¹ * n * a⁻¹⁻¹)];
    simp [mul_assoc] }

@[to_additive subset_add_normalizer]
lemma subset_normalizer (s : set G) [is_subgroup s] : s ⊆ normalizer s :=
λ g hg n, by rw [is_subgroup.mul_mem_cancel_left _ ((is_subgroup.inv_mem_iff _).2 hg),
  is_subgroup.mul_mem_cancel_right _ hg]

/-- Every subgroup is a normal subgroup of its normalizer -/
@[to_additive add_normal_in_add_normalizer]
instance normal_in_normalizer (s : set G) [is_subgroup s] :
  normal_subgroup (subtype.val ⁻¹' s : set (normalizer s)) :=
{ one_mem := show (1 : G) ∈ s, from is_submonoid.one_mem,
  mul_mem := λ a b ha hb, show (a * b : G) ∈ s, from is_submonoid.mul_mem ha hb,
  inv_mem := λ a ha, show (a⁻¹ : G) ∈ s, from is_subgroup.inv_mem ha,
  normal := λ a ha ⟨m, hm⟩, (hm a).1 ha }

end is_subgroup

-- Homomorphism subgroups
namespace is_group_hom
open is_submonoid is_subgroup
open is_mul_hom (map_mul)

@[to_additive]
def ker [group H] (f : G → H) : set G := preimage f (trivial H)

@[to_additive]
lemma mem_ker [group H] (f : G → H) {x : G} : x ∈ ker f ↔ f x = 1 :=
mem_trivial

variables [group G] [group H]

@[to_additive]
lemma one_ker_inv (f : G → H) [is_group_hom f] {a b : G} (h : f (a * b⁻¹) = 1) : f a = f b :=
begin
  rw [map_mul f, map_inv f] at h,
  rw [←inv_inv (f b), eq_inv_of_mul_eq_one h]
end

@[to_additive]
lemma one_ker_inv' (f : G → H) [is_group_hom f] {a b : G} (h : f (a⁻¹ * b) = 1) : f a = f b :=
begin
  rw [map_mul f, map_inv f] at h,
  apply eq_of_inv_eq_inv,
  rw eq_inv_of_mul_eq_one h
end

@[to_additive]
lemma inv_ker_one (f : G → H) [is_group_hom f] {a b : G} (h : f a = f b) : f (a * b⁻¹) = 1 :=
have f a * (f b)⁻¹ = 1, by rw [h, mul_right_inv],
by rwa [←map_inv f, ←map_mul f] at this

@[to_additive]
lemma inv_ker_one' (f : G → H) [is_group_hom f] {a b : G} (h : f a = f b) : f (a⁻¹ * b) = 1 :=
have (f a)⁻¹ * f b = 1, by rw [h, mul_left_inv],
by rwa [←map_inv f, ←map_mul f] at this

@[to_additive]
lemma one_iff_ker_inv (f : G → H) [is_group_hom f] (a b : G) : f a = f b ↔ f (a * b⁻¹) = 1 :=
⟨inv_ker_one f, one_ker_inv f⟩

@[to_additive]
lemma one_iff_ker_inv' (f : G → H) [is_group_hom f] (a b : G) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
⟨inv_ker_one' f, one_ker_inv' f⟩

@[to_additive]
lemma inv_iff_ker (f : G → H) [w : is_group_hom f] (a b : G) : f a = f b ↔ a * b⁻¹ ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv _ _ _

@[to_additive]
lemma inv_iff_ker' (f : G → H) [w : is_group_hom f] (a b : G) : f a = f b ↔ a⁻¹ * b ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv' _ _ _

@[to_additive image_add_subgroup]
instance image_subgroup (f : G → H) [is_group_hom f] (s : set G) [is_subgroup s] :
  is_subgroup (f '' s) :=
{ mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
             ⟨b₁ * b₂, mul_mem hb₁ hb₂, by simp [eq₁, eq₂, map_mul f]⟩,
  one_mem := ⟨1, one_mem, map_one f⟩,
  inv_mem := assume a ⟨b, hb, eq⟩, ⟨b⁻¹, inv_mem hb, by rw map_inv f; simp *⟩ }

@[to_additive range_add_subgroup]
instance range_subgroup (f : G → H) [is_group_hom f] : is_subgroup (set.range f) :=
@set.image_univ _ _ f ▸ is_group_hom.image_subgroup f set.univ

local attribute [simp] one_mem inv_mem mul_mem normal_subgroup.normal

@[to_additive]
instance preimage (f : G → H) [is_group_hom f] (s : set H) [is_subgroup s] :
  is_subgroup (f ⁻¹' s) :=
by refine {..}; simp [map_mul f, map_one f, map_inv f, @inv_mem H _ s] {contextual:=tt}

@[to_additive]
instance preimage_normal (f : G → H) [is_group_hom f] (s : set H) [normal_subgroup s] :
  normal_subgroup (f ⁻¹' s) :=
⟨by simp [map_mul f, map_inv f] {contextual:=tt}⟩

@[to_additive]
instance normal_subgroup_ker (f : G → H) [is_group_hom f] : normal_subgroup (ker f) :=
is_group_hom.preimage_normal f (trivial H)

@[to_additive]
lemma inj_of_trivial_ker (f : G → H) [is_group_hom f] (h : ker f = trivial G) :
  function.injective f :=
begin
  intros a₁ a₂ hfa,
  simp [ext_iff, ker, is_subgroup.trivial] at h,
  have ha : a₁ * a₂⁻¹ = 1, by rw ←h; exact inv_ker_one f hfa,
  rw [eq_inv_of_mul_eq_one ha, inv_inv a₂]
end

@[to_additive]
lemma trivial_ker_of_inj (f : G → H) [is_group_hom f] (h : function.injective f) :
  ker f = trivial G :=
set.ext $ assume x, iff.intro
  (assume hx,
    suffices f x = f 1, by simpa using h this,
    by simp [map_one f]; rwa [mem_ker] at hx)
  (by simp [mem_ker, is_group_hom.map_one f] {contextual := tt})

@[to_additive]
lemma inj_iff_trivial_ker (f : G → H) [is_group_hom f] :
  function.injective f ↔ ker f = trivial G :=
⟨trivial_ker_of_inj f, inj_of_trivial_ker f⟩

@[to_additive]
lemma trivial_ker_iff_eq_one (f : G → H) [is_group_hom f] :
  ker f = trivial G ↔ ∀ x, f x = 1 → x = 1 :=
by rw set.ext_iff; simp [ker]; exact
⟨λ h x hx, (h x).1 hx, λ h x, ⟨h x, λ hx, by rw [hx, map_one f]⟩⟩

end is_group_hom

@[to_additive is_add_group_hom]
instance subtype_val.is_group_hom [group G] {s : set G} [is_subgroup s] :
  is_group_hom (subtype.val : s → G) := { ..subtype_val.is_monoid_hom }

@[to_additive is_add_group_hom]
instance coe.is_group_hom [group G] {s : set G} [is_subgroup s] :
  is_group_hom (coe : s → G) := { ..subtype_val.is_monoid_hom }

@[to_additive is_add_group_hom]
instance subtype_mk.is_group_hom [group G] [group H] {s : set G}
  [is_subgroup s] (f : H → G) [is_group_hom f] (h : ∀ x, f x ∈ s) :
  is_group_hom (λ x, (⟨f x, h x⟩ : s)) := { ..subtype_mk.is_monoid_hom f h }

@[to_additive is_add_group_hom]
instance set_inclusion.is_group_hom [group G] {s t : set G}
  [is_subgroup s] [is_subgroup t] (h : s ⊆ t) : is_group_hom (set.inclusion h) :=
subtype_mk.is_group_hom _ _

/-- `subtype.val : set.range f → H` as a monoid homomorphism, when `f` is a monoid homomorphism. -/
@[to_additive "`subtype.val : set.range f → H` as an additive monoid homomorphism, when `f` is an additive monoid homomorphism."]
def monoid_hom.range_subtype_val [monoid G] [monoid H] (f : G →* H) : (set.range f) →* H :=
monoid_hom.of subtype.val

/-- `set.range_factorization f : G → set.range f` as a monoid homomorphism, when `f` is a monoid homomorphism. -/
@[to_additive "`set.range_factorization f : G → set.range f` as an additive monoid homomorphism, when `f` is an additive monoid homomorphism."]
def monoid_hom.range_factorization [monoid G] [monoid H] (f : G →* H) : G →* (set.range f) :=
{ to_fun := set.range_factorization f,
  map_one' := by { dsimp [set.range_factorization], simp, refl, },
  map_mul' := by { intros, dsimp [set.range_factorization], simp, refl, } }

namespace add_group

variables [add_group A]

inductive in_closure (s : set A) : A → Prop
| basic {a : A} : a ∈ s → in_closure a
| zero : in_closure 0
| neg {a : A} : in_closure a → in_closure (-a)
| add {a b : A} : in_closure a → in_closure b → in_closure (a + b)

end add_group

namespace group
open is_submonoid is_subgroup

variables [group G] {s : set G}

@[to_additive]
inductive in_closure (s : set G) : G → Prop
| basic {a : G} : a ∈ s → in_closure a
| one : in_closure 1
| inv {a : G} : in_closure a → in_closure a⁻¹
| mul {a b : G} : in_closure a → in_closure b → in_closure (a * b)

/-- `group.closure s` is the subgroup closed over `s`, i.e. the smallest subgroup containg s. -/
@[to_additive]
def closure (s : set G) : set G := {a | in_closure s a }

@[to_additive]
lemma mem_closure {a : G} : a ∈ s → a ∈ closure s := in_closure.basic

@[to_additive is_add_subgroup]
instance closure.is_subgroup (s : set G) : is_subgroup (closure s) :=
{ one_mem := in_closure.one, mul_mem := assume a b, in_closure.mul, inv_mem := assume a, in_closure.inv }

@[to_additive]
theorem subset_closure {s : set G} : s ⊆ closure s := λ a, mem_closure

@[to_additive]
theorem closure_subset {s t : set G} [is_subgroup t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, one_mem, mul_mem, inv_mem_iff]

@[to_additive]
lemma closure_subset_iff (s t : set G) [is_subgroup t] : closure s ⊆ t ↔ s ⊆ t :=
⟨assume h b ha, h (mem_closure ha), assume h b ha, closure_subset h ha⟩

@[to_additive]
theorem closure_mono {s t : set G} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure

@[simp, to_additive closure_add_subgroup]
lemma closure_subgroup (s : set G) [is_subgroup s] : closure s = s :=
set.subset.antisymm (closure_subset $ set.subset.refl s) subset_closure

@[to_additive]
theorem exists_list_of_mem_closure {s : set G} {a : G} (h : a ∈ closure s) :
  (∃l:list G, (∀x∈l, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.prod = a) :=
in_closure.rec_on h
  (λ x hxs, ⟨[x], list.forall_mem_singleton.2 $ or.inl hxs, by exact _root_.one_mul x⟩)
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
lemma image_closure [group H] (f : G → H) [is_group_hom f] (s : set G) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [is_monoid_hom.map_one f], apply is_submonoid.one_mem },
    { rw [is_group_hom.map_inv f], apply is_subgroup.inv_mem, assumption },
    { rw [is_monoid_hom.map_mul f], solve_by_elim [is_submonoid.mul_mem] }
  end
  (closure_subset $ set.image_subset _ subset_closure)

@[to_additive]
theorem mclosure_subset {s : set G} : monoid.closure s ⊆ closure s :=
monoid.closure_subset $ subset_closure

@[to_additive]
theorem mclosure_inv_subset {s : set G} : monoid.closure (has_inv.inv ⁻¹' s) ⊆ closure s :=
monoid.closure_subset $ λ x hx, inv_inv x ▸ (is_subgroup.inv_mem $ subset_closure hx)

@[to_additive]
theorem closure_eq_mclosure {s : set G} : closure s = monoid.closure (s ∪ has_inv.inv ⁻¹' s) :=
set.subset.antisymm
  (@closure_subset _ _ _ (monoid.closure (s ∪ has_inv.inv ⁻¹' s))
    { inv_mem := λ x hx, monoid.in_closure.rec_on hx
      (λ x hx, or.cases_on hx (λ hx, monoid.subset_closure $ or.inr $ show x⁻¹⁻¹ ∈ s, from (inv_inv x).symm ▸ hx)
        (λ hx, monoid.subset_closure $ or.inl hx))
      ((@one_inv G _).symm ▸ is_submonoid.one_mem)
      (λ x y hx hy ihx ihy, (mul_inv_rev x y).symm ▸ is_submonoid.mul_mem ihy ihx) }
    (set.subset.trans (set.subset_union_left _ _) monoid.subset_closure))
  (monoid.closure_subset $ set.union_subset subset_closure $ λ x hx, inv_inv x ▸ (is_subgroup.inv_mem $ subset_closure hx))

@[to_additive]
theorem mem_closure_union_iff {G : Type*} [comm_group G] {s t : set G} {x : G} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
begin
  simp only [closure_eq_mclosure, monoid.mem_closure_union_iff, exists_prop, preimage_union], split,
  { rintro ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, rfl⟩,
    refine ⟨_, ⟨_, hys, _, hzs, rfl⟩, _, ⟨_, hyt, _, hzt, rfl⟩, _⟩,
    rw [_root_.mul_assoc, _root_.mul_assoc, mul_left_comm zs], },
  { rintro ⟨_, ⟨ys, hys, zs, hzs, rfl⟩, _, ⟨yt, hyt, zt, hzt, rfl⟩, rfl⟩,
    refine ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, _⟩,
    rw [_root_.mul_assoc, _root_.mul_assoc, mul_left_comm yt] }
end

@[to_additive gmultiples_eq_closure]
theorem gpowers_eq_closure {a : G} : gpowers a = closure {a} :=
subset.antisymm
  (gpowers_subset $ mem_closure $ by simp)
  (closure_subset $ by simp [mem_gpowers])

end group

namespace is_subgroup
variable [group G]

@[to_additive]
lemma trivial_eq_closure : trivial G = group.closure ∅ :=
subset.antisymm
  (by simp [set.subset_def, is_submonoid.one_mem])
  (group.closure_subset $ by simp)

end is_subgroup

/-The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/

namespace group
variables {s : set G} [group G]

/-- Given an element a, conjugates a is the set of conjugates. -/
def conjugates (a : G) : set G := {b | is_conj a b}

lemma mem_conjugates_self {a : G} : a ∈ conjugates a := is_conj_refl _

/-- Given a set s, conjugates_of_set s is the set of all conjugates of
the elements of s. -/
def conjugates_of_set (s : set G) : set G := ⋃ a ∈ s, conjugates a

lemma mem_conjugates_of_set_iff {x : G} : x ∈ conjugates_of_set s ↔ ∃ a ∈ s, is_conj a x :=
set.mem_bUnion_iff

theorem subset_conjugates_of_set : s ⊆ conjugates_of_set s :=
λ (x : G) (h : x ∈ s), mem_conjugates_of_set_iff.2 ⟨x, h, is_conj_refl _⟩

theorem conjugates_of_set_mono {s t : set G} (h : s ⊆ t) :
  conjugates_of_set s ⊆ conjugates_of_set t :=
set.bUnion_subset_bUnion_left h

lemma conjugates_subset {t : set G} [normal_subgroup t] {a : G} (h : a ∈ t) : conjugates a ⊆ t :=
λ x ⟨c,w⟩,
begin
  have H := normal_subgroup.normal a h c,
  rwa ←w,
end

theorem conjugates_of_set_subset {s t : set G} [normal_subgroup t] (h : s ⊆ t) :
  conjugates_of_set s ⊆ t :=
set.bUnion_subset (λ x H, conjugates_subset (h H))

/-- The set of conjugates of s is closed under conjugation. -/
lemma conj_mem_conjugates_of_set {x c : G} :
  x ∈ conjugates_of_set s → (c * x * c⁻¹ ∈ conjugates_of_set s) :=
λ H,
begin
  rcases (mem_conjugates_of_set_iff.1 H) with ⟨a,h₁,h₂⟩,
  exact mem_conjugates_of_set_iff.2 ⟨a, h₁, is_conj_trans h₂ ⟨c,rfl⟩⟩,
end

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def normal_closure (s : set G) : set G := closure (conjugates_of_set s)

theorem conjugates_of_set_subset_normal_closure : conjugates_of_set s ⊆ normal_closure s :=
subset_closure

theorem subset_normal_closure : s ⊆ normal_closure s :=
set.subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure

/-- The normal closure of a set is a subgroup. -/
instance normal_closure.is_subgroup (s : set G) : is_subgroup (normal_closure s) :=
closure.is_subgroup (conjugates_of_set s)

/-- The normal closure of s is a normal subgroup. -/
instance normal_closure.is_normal : normal_subgroup (normal_closure s) :=
⟨ λ n h g,
begin
  induction h with x hx x hx ihx x y hx hy ihx ihy,
  {exact (conjugates_of_set_subset_normal_closure (conj_mem_conjugates_of_set hx))},
  {simpa using (normal_closure.is_subgroup s).one_mem},
  {rw ←conj_inv,
   exact (is_subgroup.inv_mem ihx)},
  {rw ←conj_mul,
   exact (is_submonoid.mul_mem ihx ihy)},
end ⟩

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normal_closure_subset {s t : set G} [normal_subgroup t] (h : s ⊆ t) :
  normal_closure s ⊆ t :=
λ a w,
begin
  induction w with x hx x hx ihx x y hx hy ihx ihy,
  {exact (conjugates_of_set_subset h $ hx)},
  {exact is_submonoid.one_mem},
  {exact is_subgroup.inv_mem ihx},
  {exact is_submonoid.mul_mem ihx ihy}
end

lemma normal_closure_subset_iff {s t : set G} [normal_subgroup t] : s ⊆ t ↔ normal_closure s ⊆ t :=
⟨normal_closure_subset, set.subset.trans (subset_normal_closure)⟩

theorem normal_closure_mono {s t : set G} : s ⊆ t → normal_closure s ⊆ normal_closure t :=
λ h, normal_closure_subset (set.subset.trans h (subset_normal_closure))

end group

section simple_group

class simple_group (G : Type*) [group G] : Prop :=
(simple : ∀ (N : set G) [normal_subgroup N], N = is_subgroup.trivial G ∨ N = set.univ)

class simple_add_group (A : Type*) [add_group A] : Prop :=
(simple : ∀ (N : set A) [normal_add_subgroup N], N = is_add_subgroup.trivial A ∨ N = set.univ)

attribute [to_additive simple_add_group] simple_group

theorem additive.simple_add_group_iff [group G] :
  simple_add_group (additive G) ↔ simple_group G :=
⟨λ hs, ⟨λ N h, @simple_add_group.simple _ _ hs _ (by exactI additive.normal_add_subgroup_iff.2 h)⟩,
  λ hs, ⟨λ N h, @simple_group.simple _ _ hs _ (by exactI additive.normal_add_subgroup_iff.1 h)⟩⟩

instance additive.simple_add_group [group G] [simple_group G] :
  simple_add_group (additive G) := additive.simple_add_group_iff.2 (by apply_instance)

theorem multiplicative.simple_group_iff [add_group A] :
  simple_group (multiplicative A) ↔ simple_add_group A :=
⟨λ hs, ⟨λ N h, @simple_group.simple _ _ hs _ (by exactI multiplicative.normal_subgroup_iff.2 h)⟩,
  λ hs, ⟨λ N h, @simple_add_group.simple _ _ hs _ (by exactI multiplicative.normal_subgroup_iff.1 h)⟩⟩

instance multiplicative.simple_group [add_group A] [simple_add_group A] :
simple_group (multiplicative A) := multiplicative.simple_group_iff.2 (by apply_instance)

@[to_additive simple_add_group_of_surjective]
lemma simple_group_of_surjective [group G] [group H] [simple_group G] (f : G → H)
  [is_group_hom f] (hf : function.surjective f) : simple_group H :=
⟨λ H iH, have normal_subgroup (f ⁻¹' H), by resetI; apply_instance,
  begin
    resetI,
    cases simple_group.simple (f ⁻¹' H) with h h,
    { refine or.inl (is_subgroup.eq_trivial_iff.2 (λ x hx, _)),
      cases hf x with y hy,
      rw ← hy at hx,
      rw [← hy, is_subgroup.eq_trivial_iff.1 h y hx, is_group_hom.map_one f] },
    { refine or.inr (set.eq_univ_of_forall (λ x, _)),
      cases hf x with y hy,
      rw set.eq_univ_iff_forall at h,
      rw ← hy,
      exact h y }
  end⟩

end simple_group
