/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.concrete_category
import order.basic

/-!
# Category instances for ordered structures

We introduce
* Preorder     : the category of preorders and monotone functions.
* PartialOrder : the category of partial orders and monotone functions.
* LinOrder     : the category of linear orders and monotone functions.
* DecLinOrder  : the category of decidable linear orders and monotone functions.

and the appropriate forgetful functors between them.
-/


universes u v

open category_theory

/-- The category of preorders and monotone maps. -/
@[reducible]
def Preorder : Type (u+1) := bundled preorder

namespace Preorder

def of (X : Type u) [preorder X] : Preorder := bundled.of X

instance : unbundled_hom @monotone :=
⟨@monotone_id, (λ _ _ _ _ _ _ _ _ m₁ m₂, by exactI monotone_comp m₂ m₁)⟩

instance (X : Preorder) : preorder X := X.str

example : concrete_category Preorder.{u} := infer_instance

end Preorder

/-- The category of partial orders and monotone maps. -/
@[reducible]
def PartialOrder : Type (u+1) := induced_category Preorder (bundled.map partial_order.to_preorder.{u})

namespace PartialOrder

instance (X : PartialOrder) : partial_order X := X.str

def of (X : Type u) [partial_order X] : PartialOrder := bundled.of X

example : concrete_category PartialOrder.{u} := infer_instance
example : has_forget₂ PartialOrder.{u} Preorder.{u} := infer_instance

end PartialOrder

/-- The category of linear orders and monotone maps. -/
@[reducible]
def LinOrder : Type (u+1) := induced_category PartialOrder (bundled.map linear_order.to_partial_order.{u})

namespace LinOrder

instance (X : LinOrder) : linear_order X := X.str

def of (X : Type u) [linear_order X] : LinOrder := bundled.of X

example : concrete_category LinOrder.{u} := infer_instance
example : has_forget₂ LinOrder.{u} PartialOrder.{u} := infer_instance

end LinOrder

/-- The category of decidable linear orders and monotone maps. -/
@[reducible]
def DecLinOrder : Type (u+1) := induced_category LinOrder (bundled.map decidable_linear_order.to_linear_order.{u})

namespace DecLinOrder

instance (X : DecLinOrder) : decidable_linear_order X := X.str

def of (X : Type u) [decidable_linear_order X] : DecLinOrder := bundled.of X

example : concrete_category DecLinOrder.{u} := infer_instance
example : has_forget₂ DecLinOrder.{u} LinOrder.{u} := infer_instance

end DecLinOrder
