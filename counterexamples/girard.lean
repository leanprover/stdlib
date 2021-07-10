/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import logic.basic

/-!
# Girard's paradox

Girard's paradox is a proof that `Type : Type` entails a contradiction. We can't say this directly
in Lean because `Type : Type 1` and it's not possible to give `Type` a different type via an axiom,
so instead we axiomatize the behavior of the Pi type and application if the typing rule for Pi was
`(Type → Type) → Type` instead of `(Type → Type) → Type 1`.

Furthermore, we don't actually want false axioms in mathlib, so rather than introducing the axioms
using `axiom` or `constant` declarations, we take them as assumptions to the `girard` theorem.

Based on Watkins' LF implementation of Hurkens' simplification of Girard's paradox:
<http://www.cs.cmu.edu/~kw/research/hurkens95tlca.elf>.

## Main statements

* `girard`: there are no Girard universes.
-/

/-- **Girard's paradox**: there are no universes `u` such that `Type u : Type u`.
Since we can't actually change the type of Lean's `Π` operator, we assume the existence of
`pi`, `lam`, `app` and the `beta` rule equivalent to the `Π` and `app` constructors of type theory.
-/
theorem {u} girard
  (pi : (Type u → Type u) → Type u)
  (lam : ∀ {A : Type u → Type u}, (∀ x, A x) → pi A)
  (app : ∀ {A}, pi A → ∀ x, A x)
  (beta : ∀ {A : Type u → Type u} (f : ∀ x, A x) (x), app (lam f) x = f x) : false :=
let F (X) := (set (set X) → X) → set (set X), U := pi F in
let G (T : set (set U)) (X) : F X := λ f, {p | {x : U | f (app x X f) ∈ p} ∈ T} in
let τ (T : set (set U)) : U := lam (G T) in
let σ (S : U) : set (set U) := app S U τ in
have στ : ∀ {s S}, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := λ s S,
  iff_of_eq (congr_arg (λ f : F U, s ∈ f τ) (beta (G S) U) : _),
let ω : set (set U) := {p | ∀ x, p ∈ σ x → x ∈ p} in
let δ (S : set (set U)) := ∀ p, p ∈ S → τ S ∈ p in
have δ ω := λ p d, d (τ ω) $ στ.2 $ λ x h, d (τ (σ x)) (στ.2 h),
this {y | ¬ δ (σ y)} (λ x e f, f _ e (λ p h, f _ (στ.1 h))) (λ p h, this _ (στ.1 h))
