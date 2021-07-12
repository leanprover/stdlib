/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import topology.continuous_function.basic
import data.bundle

/-!
# Continuous sections

In this file we define bundled continuous sections of a map.

-/

section

set_option old_structure_cmd true

variables {α: Type*} {β: Type*} {f : α → β}
variables [topological_space α] [topological_space β]

/-- A continuous section of a map `f` is a continuous map that is a right inverse of `f`.
Note that the `nolint has_inhabited_instance` here has a true matematical meaning: the universal
cover of a circle is a map that does not admit continuous sections. -/
@[nolint has_inhabited_instance]
structure continuous_section (f : α → β) extends right_inv f, C(β, α)

instance : has_coe_to_fun (continuous_section f) := ⟨λ f, β → α, continuous_section.to_fun⟩

instance : has_coe (continuous_section f) (right_inv f) :=
⟨continuous_section.to_right_inv⟩

namespace continuous_section

-- The linter does not recognize that these are structure projections, disable it.
attribute [nolint doc_blame] to_right_inv to_continuous_map

variables {s t : continuous_section f}

lemma coe_injective (H : ⇑s = t) : s = t :=
by { cases s, cases t, congr' }

@[ext] theorem ext (H : ∀ a, s a = t a) : s = t :=
coe_injective $ funext H

lemma ext_right_inv (g h : continuous_section f) (H : (g : right_inv f) = h) :
  g = h := by { cases g, cases h, injection H, dsimp only at h_1, induction h_1, refl }

@[simp] lemma to_fun_eq_coe (g : continuous_section f) : g.to_fun = ⇑g := rfl
@[simp] lemma coe_fn_coe (g : continuous_section f) :
  ⇑(g : right_inv f) = g := rfl

end continuous_section

end

section bundle

open bundle

variables {B : Type*} [topological_space B] {E : B → Type*} [topological_space (total_space E)]

@[nolint unused_arguments]
instance bundle_section_to_right_inv : has_coe (bundle_section E) (right_inv (proj E)) :=
⟨bundle_section_right_inv⟩

/-- A continuous section of a bundle `E` is an element of `Π x, E x` that is continuous when
coerced to the total space.
Note that the `nolint has_inhabited_instance` here has a true matematical meaning: the universal
cover of a circle is a map that does not admit continuous sections. -/
@[nolint has_inhabited_instance]
structure continuous_bundle_section (E : B → Type*) [topological_space (total_space E)] :=
(to_fun : bundle_section E)
(continuous_to_fun : continuous to_fun)

namespace continuous_bundle_section

variables (s t : continuous_bundle_section E)

instance : has_coe_to_fun (continuous_bundle_section E) := ⟨λ s, Π x, E x, to_fun⟩

/-- Natural identification as a `continuous_section`. -/
def to_continuous_section (s : continuous_bundle_section E) : continuous_section (proj E) :=
{ ..bundle_section_right_inv s, ..s }

instance : has_coe (continuous_bundle_section E) (continuous_section (proj E)) :=
⟨to_continuous_section⟩

lemma coe_injective : @function.injective (continuous_bundle_section E) (Π x, E x) coe_fn :=
λ X Y h, by { cases X, cases Y, congr' }

@[ext] theorem ext (h : ∀ x, s x = t x) : s = t := coe_injective $ funext h

@[simp] lemma to_fun_eq_coe : s.to_fun = s := rfl

@[continuity] lemma continuous : continuous (s : B → total_space E) := s.continuous_to_fun

end continuous_bundle_section

end bundle
