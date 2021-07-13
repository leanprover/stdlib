/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import deprecated.group

/-!
# Unbundled semiring and ring homomorphisms (deprecated)

This file defines structures for unbundled semiring and ring homomorphisms. Though bundled
morphisms are now preferred, the unbundled structures are still occasionally used in mathlib,
and probably will not go away before Lean 4 because Lean 3 often fails to coerce a bundled
homomorphism to a function.

## Main Definitions

`is_semiring_hom` (deprecated), `is_ring_hom` (deprecated)

## Tags

is_semiring_hom, is_ring_hom

-/

universes u v w

variable {α : Type u}

/-- Predicate for semiring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
structure is_semiring_hom {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) : Prop :=
(map_zero [] : f 0 = 0)
(map_one [] : f 1 = 1)
(map_add [] : ∀ {x y}, f (x + y) = f x + f y)
(map_mul [] : ∀ {x y}, f (x * y) = f x * f y)

namespace is_semiring_hom

variables {β : Type v} [semiring α] [semiring β]
variables {f : α → β} (hf : is_semiring_hom f) {x y : α}

/-- The identity map is a semiring homomorphism. -/
lemma id : is_semiring_hom (@id α) := by refine {..}; intros; refl

/-- The composition of two semiring homomorphisms is a semiring homomorphism. -/
lemma comp (hf : is_semiring_hom f) {γ} [semiring γ] {g : β → γ} (hg : is_semiring_hom g) :
  is_semiring_hom (g ∘ f) :=
{ map_zero := by simpa [map_zero hf] using map_zero hg,
  map_one := by simpa [map_one hf] using map_one hg,
  map_add := λ x y, by simp [map_add hf, map_add hg],
  map_mul := λ x y, by simp [map_mul hf, map_mul hg] }

/-- A semiring homomorphism is an additive monoid homomorphism. -/
lemma to_is_add_monoid_hom (hf : is_semiring_hom f) : is_add_monoid_hom f :=
{ ..‹is_semiring_hom f› }

/-- A semiring homomorphism is a monoid homomorphism. -/
lemma to_is_monoid_hom (hf : is_semiring_hom f) : is_monoid_hom f :=
{ ..‹is_semiring_hom f› }

end is_semiring_hom

/-- Predicate for ring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
class is_ring_hom {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) : Prop :=
(map_one [] : f 1 = 1)
(map_mul [] : ∀ {x y}, f (x * y) = f x * f y)
(map_add [] : ∀ {x y}, f (x + y) = f x + f y)

namespace is_ring_hom

variables {β : Type v} [ring α] [ring β]

/-- A map of rings that is a semiring homomorphism is also a ring homomorphism. -/
lemma of_semiring {f : α → β} (H : is_semiring_hom f) : is_ring_hom f := {..H}

variables {f : α → β} (hf : is_ring_hom f) {x y : α}

/-- Ring homomorphisms map zero to zero. -/
lemma map_zero (hf : is_ring_hom f) : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [hf.map_add]; simp
     ... = 0 : by simp

/-- Ring homomorphisms preserve additive inverses. -/
lemma map_neg (hf : is_ring_hom f) : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [hf.map_add]; simp
        ... = -f x : by simp [hf.map_zero]

/-- Ring homomorphisms preserve subtraction. -/
lemma map_sub (hf : is_ring_hom f) : f (x - y) = f x - f y :=
by simp [sub_eq_add_neg, hf.map_add, hf.map_neg]

/-- The identity map is a ring homomorphism. -/
instance id : is_ring_hom (@id α) := by refine {..}; intros; refl

/-- The composition of two ring homomorphisms is a ring homomorphism. -/
-- see Note [no instance on morphisms]
lemma comp (hf : is_ring_hom f) {γ} [ring γ] {g : β → γ} (hg : is_ring_hom g) :
  is_ring_hom (g ∘ f) :=
{ map_add := λ x y, by simp [map_add f]; rw map_add g; refl,
  map_mul := λ x y, by simp [map_mul f]; rw map_mul g; refl,
  map_one := by simp [map_one f]; exact map_one g }

/-- A ring homomorphism is also a semiring homomorphism. -/
lemma to_is_semiring_hom (hf : is_ring_hom f) : is_semiring_hom f :=
{ map_zero := map_zero hf, ..‹is_ring_hom f› }

lemma to_is_add_group_hom (hf : is_ring_hom f) : is_add_group_hom f := { map_add := hf.map_add }

end is_ring_hom

variables {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β]

namespace ring_hom

section
include rα rβ

/-- Interpret `f : α → β` with `is_semiring_hom f` as a ring homomorphism. -/
def of {f : α → β} (hf : is_semiring_hom f) : α →+* β :=
{ to_fun := f,
  .. monoid_hom.of hf.to_is_monoid_hom,
  .. add_monoid_hom.of hf.to_is_add_monoid_hom }

@[simp] lemma coe_of {f : α → β} (hf : is_semiring_hom f) : ⇑(of hf) = f := rfl

lemma to_is_semiring_hom (f : α →+* β) : is_semiring_hom f :=
{ map_zero := f.map_zero,
  map_one := f.map_one,
  map_add := f.map_add,
  map_mul := f.map_mul }

end

lemma to_is_ring_hom {α γ} [ring α] [ring γ] (g : α →+* γ) : is_ring_hom g :=
is_ring_hom.of_semiring g.to_is_semiring_hom

end ring_hom
