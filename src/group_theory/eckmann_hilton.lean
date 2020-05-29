/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis
-/
import tactic.basic
import algebra.group.basic

universe u

namespace eckmann_hilton
variables {X : Type u}

local notation a `<`m`>` b := m a b

class is_unital (m : X → X → X) (e : X) : Prop :=
(one_mul : ∀ x : X, (e <m> x) = x)
(mul_one : ∀ x : X, (x <m> e) = x)

lemma monoid.is_unital [G : monoid X] : is_unital (*) (1 : X) := { ..G }

variables {m₁ m₂ : X → X → X} {e₁ e₂ : X}
variables (h₁ : is_unital m₁ e₁) (h₂ : is_unital m₂ e₂)
variables (distrib : ∀ a b c d, ((a <m₂> b) <m₁> (c <m₂> d)) = ((a <m₁> c) <m₂> (b <m₁> d)))
include h₁ h₂ distrib

lemma one : e₁ = e₂ :=
by simpa only [h₁.one_mul, h₁.mul_one, h₂.one_mul, h₂.mul_one] using distrib e₂ e₁ e₁ e₂

lemma mul : (m₁ = m₂) :=
begin
  funext a b,
  calc m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) :
    by simp only [one h₁ h₂ distrib, h₁.one_mul, h₁.mul_one, h₂.one_mul, h₂.mul_one]
          ... = m₂ a b :
    by simp only [distrib, h₁.one_mul, h₁.mul_one, h₂.one_mul, h₂.mul_one]
end

lemma mul_comm : is_commutative _ m₂ :=
⟨λ a b, by simpa [mul h₁ h₂ distrib, h₂.one_mul, h₂.mul_one] using distrib e₂ a b e₂⟩

lemma mul_assoc : is_associative _ m₂ :=
⟨λ a b c, by simpa [mul h₁ h₂ distrib, h₂.one_mul, h₂.mul_one] using distrib a b e₂ c⟩

def comm_monoid : comm_monoid X :=
{ mul := m₂,
  one := e₂,
  mul_comm := (mul_comm h₁ h₂ distrib).comm,
  mul_assoc := (mul_assoc h₁ h₂ distrib).assoc,
  ..h₂ }

def comm_group [G : group X] (distrib : ∀ a b c d, ((a * b) <m₁> (c * d)) = ((a <m₁> c) * (b <m₁> d))) : comm_group X :=
{ mul_comm := (eckmann_hilton.comm_monoid h₁ monoid.is_unital distrib).mul_comm,
  ..G }

end eckmann_hilton
