import measure_theory.tactic
import measure_theory.borel_space

variables {α β : Type*} [measurable_space α] [measurable_space β]
  {f g : α → β} {s₁ s₂ : set α} {t₁ t₂ : set β} {μ ν : measure_theory.measure α}

-- Test the use of assumption

example (hf : measurable f) : measurable f := by measurability

-- Test that intro does not unfold `measurable`

example : measurable f → measurable f := by measurability

-- Tests on sets

example (hf : measurable f) (hs₁ : measurable_set s₁) (ht₂ : measurable_set t₂) :
  measurable_set ((f ⁻¹' t₂) ∩ s₁) :=
by measurability

-- Tests on functions

example [has_add β] [has_measurable_add₂ β] (hf : measurable f) (hg : measurable g) :
  measurable (λ x, f x + g x) :=
by measurability

example [has_add β] [has_measurable_add₂ β] (hf : measurable f) (hg : ae_measurable g μ) :
  ae_measurable (λ x, f x + g x) μ :=
by measurability

example [has_div β] [has_measurable_div₂ β] (hf : measurable f) (hg : measurable g)
  (ht : measurable_set t₂):
  measurable_set ((λ x, f x / g x) ⁻¹' t₂) :=
by measurability

example [topological_space α] [topological_space β] [opens_measurable_space α] [borel_space β]
  (hf : continuous f) :
  measurable f :=
by measurability
