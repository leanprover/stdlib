/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.equiv.basic

/-!
# Monad

## Attributes

 * ext
 * functor_norm
 * monad_norm

## Implementation Details

Set of rewrite rules and automation for monads in general and
`reader_t`, `state_t`, `except_t` and `option_t` in particular.

The rewrite rules for monads are carefully chosen so that `simp with
functor_norm` will not introduce monadic vocabulary in a context where
applicatives would do just fine but will handle monadic notation
already present in an expression.

In a context where monadic reasoning is desired `simp with monad_norm`
will translate functor and applicative notation into monad notation
and use regular `functor_norm` rules as well.

## Tags

functor, applicative, monad, simp

-/

mk_simp_attribute monad_norm none with functor_norm

attribute [ext] reader_t.ext state_t.ext except_t.ext option_t.ext
attribute [functor_norm]   bind_assoc pure_bind bind_pure
attribute [monad_norm] seq_eq_bind_map
universes u v

@[monad_norm]
lemma map_eq_bind_pure_comp (m : Type u → Type v) [monad m] [is_lawful_monad m] {α β : Type u} (f : α → β) (x : m α) :
  f <$> x = x >>= pure ∘ f := by rw bind_pure_comp_eq_map

/-- run a `state_t` program and discard the final state -/
def state_t.eval {m : Type u → Type v} [functor m] {σ α} (cmd : state_t σ m α) (s : σ) : m α :=
prod.fst <$> cmd.run s

universes u₀ u₁ v₀ v₁

/-- reduce the equivalence between two state monads to the equivalence between
their respective function spaces -/
def state_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
  {α₁ σ₁ : Type u₀} {α₂ σ₂ : Type u₁} (F : (σ₁ → m₁ (α₁ × σ₁)) ≃ (σ₂ → m₂ (α₂ × σ₂))) :
  state_t σ₁ m₁ α₁ ≃ state_t σ₂ m₂ α₂ :=
{ to_fun := λ ⟨f⟩, ⟨F f⟩,
  inv_fun := λ ⟨f⟩, ⟨F.symm f⟩,
  left_inv := λ ⟨f⟩, congr_arg state_t.mk $ F.left_inv _,
  right_inv := λ ⟨f⟩, congr_arg state_t.mk $ F.right_inv _ }

/-- reduce the equivalence between two reader monads to the equivalence between
their respective function spaces -/
def reader_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
  {α₁ ρ₁ : Type u₀} {α₂ ρ₂ : Type u₁} (F : (ρ₁ → m₁ α₁) ≃ (ρ₂ → m₂ α₂)) :
  reader_t ρ₁ m₁ α₁ ≃ reader_t ρ₂ m₂ α₂ :=
{ to_fun := λ ⟨f⟩, ⟨F f⟩,
  inv_fun := λ ⟨f⟩, ⟨F.symm f⟩,
  left_inv := λ ⟨f⟩, congr_arg reader_t.mk $ F.left_inv _,
  right_inv := λ ⟨f⟩, congr_arg reader_t.mk $ F.right_inv _ }
