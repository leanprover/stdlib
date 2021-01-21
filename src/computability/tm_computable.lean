/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/

import computability.encoding
import computability.turing_machine
import data.polynomial.eval

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in turing_machine.lean), a definition of when a TM gives a certain
output (in a certain time), and the definition of computability (in polytime or any time function)
of a function between two types that have an encoding (as in encoding.lean).

## Main theorems

- `id_computable_in_poly_time` : a TM + a proof it computes the identity on a type in polytime.
- `id_computable`              : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type stmt); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, so on). However, as functions
only contain a finite number of executions and each one is executed at most once, this execution
time is up to multiplication by a constant the amount of fundamental steps.
-/

open computability

namespace turing
/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `turing.TM2` in `turing_machine.lean`), with an input and output stack,
 a main function, an initial state and some finiteness guarantees. -/
structure fin_tm2 :=
 {K : Type} [K_decidable_eq : decidable_eq K] [K_fin : fintype K] -- index type of stacks
 (k₀ k₁ : K) -- input and output stack
 (Γ : K → Type) -- type of stack elements
 (Λ : Type) (main : Λ) [Λ_fin : fintype Λ] -- type of function labels
 (σ : Type) (initial_state : σ) -- type of states of the machine
 [σ_fin : fintype σ]
 [Γk₀_fin : fintype (Γ k₀)]
 (M : Λ → turing.TM2.stmt Γ Λ σ) -- the program itself, i.e. one function for every function label

namespace fin_tm2
section
variable (tm : fin_tm2)

instance : decidable_eq tm.K := tm.K_decidable_eq
instance : inhabited tm.σ := ⟨tm.initial_state⟩

/-- The type of statements (functions) corresponding to this TM. -/
@[derive inhabited]
def stmt : Type := turing.TM2.stmt tm.Γ tm.Λ tm.σ

/-- The type of configurations (functions) corresponding to this TM. -/
def cfg : Type := turing.TM2.cfg tm.Γ tm.Λ tm.σ

instance inhabited_cfg : inhabited (cfg tm) :=
turing.TM2.cfg.inhabited _ _ _

/-- The step function corresponding to this TM. -/
@[simp] def step : tm.cfg → option tm.cfg :=
turing.TM2.step tm.M
end
end fin_tm2

/-- The initial configuration corresponding to a list in the input alphabet. -/
def init_list (tm : fin_tm2) (s : list (tm.Γ tm.k₀)) : tm.cfg :=
{ l := option.some tm.main,
  var := tm.initial_state,
  stk := λ k, @dite (k = tm.k₀) (tm.K_decidable_eq k tm.k₀) (list (tm.Γ k))
                (λ h, begin rw h, exact s, end)
                (λ _,[]) }

/-- The final configuration corresponding to a list in the output alphabet. -/
def halt_list (tm : fin_tm2) (s : list (tm.Γ tm.k₁)) : tm.cfg :=
{ l := option.none,
  var := tm.initial_state,
  stk := λ k, @dite (k = tm.k₁) (tm.K_decidable_eq k tm.k₁) (list (tm.Γ k))
                (λ h, begin rw h, exact s, end)
                (λ _,[]) }

/-- A "proof" of the fact that f eventually reaches b when repeatedly evaluated on a,
remembering the number of steps it takes. -/
structure evals_to {σ : Type*} (f : σ → option σ) (a : σ) (b : option σ) :=
(steps : ℕ)
(evals_in_steps : ((flip bind f)^[steps] a) = b)

/-- A "proof" of the fact that f eventually reaches b in at most m steps when repeatedly evaluated on a,
remembering the number of steps it takes. -/
structure evals_to_in_time {σ : Type*} (f : σ → option σ) (a : σ) (b : option σ) (m : ℕ) extends evals_to f a b :=
(steps_le_m : steps ≤ m)

/-- Reflexivity of `evals_to` in 0 steps. -/
@[refl] def evals_to.refl {σ : Type*} (f : σ → option σ) (a : σ) : evals_to f a a := ⟨0,rfl⟩

/-- Transitivity of `evals_to` in the sum of the numbers of steps. -/
@[trans] def evals_to.trans {σ : Type*} (f : σ → option σ) (a : σ) (b : σ) (c : option σ)
  (h₁ : evals_to f a b) (h₂ : evals_to f b c) : evals_to f a c :=
⟨h₂.steps + h₁.steps,
 by rw [function.iterate_add_apply,h₁.evals_in_steps,h₂.evals_in_steps]⟩

/-- Reflexivity of `evals_to_in_time` in 0 steps. -/
@[refl] def evals_to_in_time.refl {σ : Type*} (f : σ → option σ) (a : σ) : evals_to_in_time f a a 0 :=
⟨evals_to.refl f a, le_refl 0⟩

/-- Transitivity of `evals_to_in_time` in the sum of the numbers of steps. -/
@[trans] def evals_to_in_time.trans {σ : Type*} (f : σ → option σ) (a : σ) (b : σ) (c : option σ)
  (m₁ : ℕ) (m₂ : ℕ) (h₁ : evals_to_in_time f a b m₁) (h₂ : evals_to_in_time f b c m₂) :
  evals_to_in_time f a c (m₂ + m₁) :=
⟨evals_to.trans f a b c h₁.to_evals_to h₂.to_evals_to, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

/-- A proof of tm outputting l' when given l. -/
def tm2_outputs (tm : fin_tm2) (l : list (tm.Γ tm.k₀)) (l' : option (list (tm.Γ tm.k₁))) :=
evals_to tm.step (init_list tm l) ((option.map (halt_list tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def tm2_outputs_in_time (tm : fin_tm2) (l : list (tm.Γ tm.k₀)) (l' : option (list (tm.Γ tm.k₁))) (m : ℕ) :=
evals_to_in_time tm.step (init_list tm l) ((option.map (halt_list tm)) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def tm2_outputs_in_time.to_tm2_outputs {tm : fin_tm2} {l : list (tm.Γ tm.k₀)}
{l' : option (list (tm.Γ tm.k₁))} {m : ℕ} (h : tm2_outputs_in_time tm l l' m) : tm2_outputs tm l l' :=
h.to_evals_to

/-- A Turing machine with input alphabet equivalent to Γ₀ and output alphabet equivalent to Γ₁. -/
structure tm2_computable_aux (Γ₀ Γ₁ : Type) :=
( tm : fin_tm2 )
( input_alphabet : tm.Γ tm.k₀ ≃ Γ₀ )
( output_alphabet : tm.Γ tm.k₁ ≃ Γ₁ )

/-- A Turing machine + a proof it outputs f. -/
structure tm2_computable {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β)
  extends tm2_computable_aux ea.Γ eb.Γ :=
(outputs_fun : ∀ a, tm2_outputs tm (list.map input_alphabet.inv_fun (ea.encode a))
  (option.some ((list.map output_alphabet.inv_fun) (eb.encode (f a)))) )

/-- A Turing machine + a time function + a proof it outputs f in at most time(len(input)) steps. -/
structure tm2_computable_in_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β)
  extends tm2_computable_aux ea.Γ eb.Γ :=
( time: ℕ → ℕ )
( outputs_fun : ∀ a, tm2_outputs_in_time tm (list.map input_alphabet.inv_fun (ea.encode a))
  (option.some ((list.map output_alphabet.inv_fun) (eb.encode (f a))))
  (time (ea.encode a).length) )

/-- A Turing machine + a polynomial time function + a proof it outputs f in at most time(len(input)) steps. -/
structure tm2_computable_in_poly_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β)
  extends tm2_computable_aux ea.Γ eb.Γ :=
( time: polynomial ℕ )
( outputs_fun : ∀ a, tm2_outputs_in_time tm (list.map input_alphabet.inv_fun (ea.encode a))
  (option.some ((list.map output_alphabet.inv_fun) (eb.encode (f a))))
  (time.eval (ea.encode a).length) )

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def tm2_computable_in_time.to_tm2_computable {α β : Type} {ea : fin_encoding α} {eb : fin_encoding β}
{f : α → β} (h : tm2_computable_in_time ea eb f) : tm2_computable ea eb f :=
⟨h.to_tm2_computable_aux, λ a, tm2_outputs_in_time.to_tm2_outputs (h.outputs_fun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
def tm2_computable_in_poly_time.to_tm2_computable_in_time {α β : Type} {ea : fin_encoding α}
{eb : fin_encoding β} {f : α → β} (h : tm2_computable_in_poly_time ea eb f) : tm2_computable_in_time ea eb f :=
⟨h.to_tm2_computable_aux, λ n, h.time.eval n, h.outputs_fun⟩

open turing.TM2.stmt

/-- A Turing machine computing the identity on α. -/
def id_computer {α : Type} (ea : fin_encoding α) : fin_tm2 :=
{ K := unit,
  k₀ := ⟨⟩,
  k₁ := ⟨⟩,
  Γ := λ _, ea.Γ,
  Λ := unit,
  main := ⟨⟩,
  σ := unit,
  initial_state := ⟨⟩,
  Γk₀_fin := ea.Γ_fin,
  M := λ _, halt }

instance inhabited_fin_tm2 : inhabited fin_tm2 :=
⟨id_computer computability.inhabited_fin_encoding.default⟩

noncomputable theory

/-- A proof that the identity map on α is computable in polytime. -/
def id_computable_in_poly_time {α : Type} (ea : fin_encoding α) : @tm2_computable_in_poly_time α α ea ea id :=
{ tm := id_computer ea,
  input_alphabet := equiv.cast rfl,
  output_alphabet := equiv.cast rfl,
  time := 1,
  outputs_fun := λ _, { steps := 1,
    evals_in_steps := rfl,
    steps_le_m := by simp only [polynomial.eval_one] } }

instance inhabited_tm2_computable_in_poly_time : inhabited (tm2_computable_in_poly_time
(default (fin_encoding bool)) (default (fin_encoding bool)) id) :=
⟨id_computable_in_poly_time computability.inhabited_fin_encoding.default⟩

instance inhabited_tm2_outputs_in_time : inhabited (tm2_outputs_in_time (id_computer fin_encoding_bool_bool)
(list.map (equiv.cast rfl).inv_fun [ff]) (some (list.map (equiv.cast rfl).inv_fun [ff])) _)
 :=
⟨(id_computable_in_poly_time fin_encoding_bool_bool).outputs_fun ff⟩

instance inhabited_tm2_outputs : inhabited (tm2_outputs (id_computer fin_encoding_bool_bool)
(list.map (equiv.cast rfl).inv_fun [ff]) (some (list.map (equiv.cast rfl).inv_fun [ff]))) :=
⟨tm2_outputs_in_time.to_tm2_outputs turing.inhabited_tm2_outputs_in_time.default⟩

instance inhabited_evals_to_in_time : inhabited (evals_to_in_time (λ _ : unit, some ⟨⟩) ⟨⟩ (some ⟨⟩) 0)
:= ⟨evals_to_in_time.refl _ _⟩

instance inhabited_tm2_evals_to : inhabited (evals_to (λ _ : unit, some ⟨⟩) ⟨⟩ (some ⟨⟩))
:= ⟨evals_to.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
def id_computable_in_time {α : Type} (ea : fin_encoding α) : @tm2_computable_in_time α α ea ea id :=
tm2_computable_in_poly_time.to_tm2_computable_in_time $ id_computable_in_poly_time ea

instance inhabited_tm2_computable_in_time : inhabited (tm2_computable_in_time fin_encoding_bool_bool fin_encoding_bool_bool id) :=
⟨id_computable_in_time computability.inhabited_fin_encoding.default⟩

/-- A proof that the identity map on α is computable. -/
def id_computable {α : Type} (ea : fin_encoding α) : @tm2_computable α α ea ea id :=
tm2_computable_in_time.to_tm2_computable $ id_computable_in_time ea

instance inhabited_tm2_computable : inhabited (tm2_computable fin_encoding_bool_bool fin_encoding_bool_bool id) :=
⟨id_computable computability.inhabited_fin_encoding.default⟩

instance inhabited_tm2_computable_aux : inhabited (tm2_computable_aux bool bool) :=
⟨(default (tm2_computable fin_encoding_bool_bool fin_encoding_bool_bool id)).to_tm2_computable_aux⟩

end turing
