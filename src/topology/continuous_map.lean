/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import topology.subset_properties

/-!
# Continuous bundled map

In this file we define the type `continuous_map` of continuous bundled maps.
-/

/-- Bundled continuous maps. -/
@[protect_proj]
structure continuous_map (α : Type*) (β : Type*)
[topological_space α] [topological_space β] :=
(to_fun             : α → β)
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')

notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

attribute [continuity] continuous_map.continuous_to_fun

variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

instance : has_coe_to_fun (C(α, β)) := ⟨_, continuous_map.to_fun⟩

variables {α β} {f g : continuous_map α β}

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun

@[continuity] lemma coe_continuous : continuous (f : α → β) := f.continuous_to_fun

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance [inhabited β] : inhabited C(α, β) :=
⟨{ to_fun := λ _, default _, }⟩

lemma coe_inj ⦃f g : C(α, β)⦄ (h : (f : α → β) = g) : f = g :=
by cases f; cases g; cases h; refl

/-- The identity as a continuous map. -/
def id : C(α, α) := ⟨id⟩

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) := ⟨f ∘ g⟩

/-- Constant map as a continuous map -/
def const (b : β) : C(α, β) := ⟨λ x, b⟩

end continuous_map
