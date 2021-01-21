/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import computability.DFA

/-!
# Nondeterministic Finite Automata
This file contains the definition of a Nondeterministic Finite Automaton (NFA), a state machine
which determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular
set by evaluating the string over every possible path.
We show that DFA's are equivalent to NFA's however the construction from NFA to DFA uses an
exponential number of states.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true NFA's.
-/

universes u v

/-- An NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states. These are the states that it
  may be sent to. -/
structure NFA (α : Type u) (σ : Type v) :=
(step : σ → α → set σ)
(start : set σ)
(accept : set σ)

variables {α : Type u} {σ σ' : Type v} (M : NFA α σ)

namespace NFA

instance : inhabited (NFA α σ) := ⟨ NFA.mk (λ _ _, ∅) ∅ ∅ ⟩

/-- `M.step_set S a` is the union of `M.step s a` for all `s ∈ S`. -/
def step_set : set σ → α → set σ :=
λ Ss a, Ss >>= (λ S, (M.step S a))

lemma mem_step_set (s : σ) (S : set σ) (a : α) :
  s ∈ M.step_set S a ↔ ∃ t ∈ S, s ∈ M.step t a :=
by simp only [step_set, set.mem_Union, set.bind_def]

/-- `M.eval_from S x` computes all possible paths though `M` with input `x` starting at an element
  of `S`. -/
def eval_from (start : set σ) : list α → set σ :=
list.foldl M.step_set start

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval := M.eval_from M.start

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : language α :=
λ x, ∃ S ∈ M.accept, S ∈ M.eval x

/-- `M.to_DFA` is an `DFA` constructed from a `NFA` `M` using the subset construction. The
  states is the type of `set`s of `M.state` and the step function is `M.step_set`. -/
def to_DFA : DFA α (set σ) :=
{ step := M.step_set,
  start := M.start,
  accept := {S | ∃ s ∈ S, s ∈ M.accept} }

@[simp] lemma to_DFA_correct :
  M.to_DFA.accepts = M.accepts :=
begin
  ext x,
  rw [accepts, DFA.accepts, eval, DFA.eval],
  change list.foldl _ _ _ ∈ {S | _} ↔ _,
  finish
end

end NFA

namespace DFA

/-- `M.to_NFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
def to_NFA (M : DFA α σ') : NFA α σ' :=
{ step := λ s a, {M.step s a},
  start := {M.start},
  accept := M.accept }

@[simp] lemma to_NFA_eval_from_match (M : DFA α σ) (start : σ) (s : list α) :
  M.to_NFA.eval_from {start} s = {M.eval_from start s} :=
begin
  change list.foldl M.to_NFA.step_set {start} s = {list.foldl M.step start s},
  induction s with a s ih generalizing start,
  { tauto },
  { rw [list.foldl, list.foldl],
    have h : M.to_NFA.step_set {start} a = {M.step start a},
    { rw NFA.step_set,
      finish },
    rw h,
    tauto }
end

@[simp] lemma to_NFA_correct (M : DFA α σ) :
  M.to_NFA.accepts = M.accepts :=
begin
  ext x,
  change (∃ S H, S ∈ M.to_NFA.eval_from {M.start} x) ↔ _,
  rw to_NFA_eval_from_match,
  split,
  { rintro ⟨ S, hS₁, hS₂ ⟩,
    rw set.mem_singleton_iff at hS₂,
    rw hS₂ at hS₁,
    assumption },
  { intro h,
    use M.eval x,
    finish }
end

end DFA
