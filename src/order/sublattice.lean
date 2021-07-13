/-
Copyright (c) 2020 Matúš Behun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matúš Behun
-/
import order.lattice
import data.set_like

/-!
    Definition of sublattice based on typeclass of lattice
-/

variables { L : Type* } [ lattice L ] { s : set L }

structure sublattice ( L : Type* ) [ lattice L ] :=
  ( carrier : set L)
  ( inf_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier )
  ( sup_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier )

namespace sublattice

instance : set_like (sublattice L) L :=
  ⟨sublattice.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp]
lemma mem_carrier {SL : sublattice L} {x : L} : x ∈ SL.carrier ↔ x ∈ SL := iff.rfl

@[ext]
theorem ext {A B : sublattice L}
  (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := set_like.ext h

def copy (SL : sublattice L) (S : set L) (hs : S = SL) : sublattice L :=
{ carrier := S,
  inf_mem' := hs.symm ▸ SL.inf_mem',
  sup_mem' := hs.symm ▸ SL.sup_mem' }

variables { SL : sublattice L }

lemma coe_copy {B : sublattice L} {A : set L} (hs : A = SL) :
  (SL.copy A hs : set L) = A := rfl

lemma copy_eq {s : set L} (hs : s = SL) : SL.copy s hs = SL :=
  set_like.coe_injective hs

theorem inf_mem {a b : L} : a ∈ SL → b ∈ SL → a ⊓ b ∈ SL :=
  sublattice.inf_mem' SL

theorem sup_mem {a b : L} : a ∈ SL → b ∈ SL → a ⊔ b ∈ SL :=
  sublattice.sup_mem' SL

open function

variables { SL₁ : Type* } { SL₂ : Type* }

/-- Trying to make definition of sublattice based on injective map
preserving structure to lattice -/
protected def function.injective.sublattice [ lattice SL₂ ] [ has_inf SL₁ ] [ has_sup SL₁ ]
  (f : SL₁ → SL₂ )
  (hf: injective f)
  (inf : ∀ a b, f(a ⊓ b) = f(a) ⊓ f(b) )
  (sup : ∀ a b, f(a ⊔ b) = f(a) ⊔ f(b) ) :
  sublattice SL₁ :=
{ sup_mem' := λ a b, ,
  inf_mem' := λ a b, ,
  carrier :=
}

end sublattice
