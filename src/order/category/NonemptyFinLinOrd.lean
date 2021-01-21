/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.fintype.sort
import order.category.LinearOrder

/-! # Nonempty finite linear orders

Nonempty finite linear orders form the index category for simplicial objects.
-/

universe variables u v

open category_theory

set_option old_structure_cmd true

/-- A typeclass for nonempty finite linear orders. -/
class nonempty_fin_lin_ord (α : Type*) extends fintype α, linear_order α, order_bot α, order_top α.

instance punit.nonempty_fin_lin_ord : nonempty_fin_lin_ord punit :=
begin
  refine_struct
  { .. punit.linear_ordered_cancel_add_comm_monoid,
    .. punit.fintype };
  { intros, exact punit.star <|> exact dec_trivial }
end

section
open_locale classical

instance fin.nonempty_fin_lin_ord (n : ℕ) :
  nonempty_fin_lin_ord (fin (n+1)) :=
{ top := fin.last n,
  le_top := fin.le_last,
  bot := 0,
  bot_le := fin.zero_le,
  .. fin.fintype _,
  .. fin.linear_order }

end

instance ulift.nonempty_fin_lin_ord (α : Type u) [nonempty_fin_lin_ord α] :
  nonempty_fin_lin_ord (ulift.{v} α) :=
{ top := ulift.up ⊤,
  bot := ulift.up ⊥,
  le_top := λ ⟨a⟩, show a ≤ ⊤, from le_top,
  bot_le := λ ⟨a⟩, show ⊥ ≤ a, from bot_le,
  .. linear_order.lift equiv.ulift (equiv.injective _),
  .. ulift.fintype _ }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrd := bundled nonempty_fin_lin_ord

namespace NonemptyFinLinOrd

instance : bundled_hom.parent_projection @nonempty_fin_lin_ord.to_linear_order := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] NonemptyFinLinOrd

/-- Construct a bundled NonemptyFinLinOrd from the underlying type and typeclass. -/
def of (α : Type*) [nonempty_fin_lin_ord α] : NonemptyFinLinOrd := bundled.of α

instance : inhabited NonemptyFinLinOrd := ⟨of punit⟩

instance (α : NonemptyFinLinOrd) : nonempty_fin_lin_ord α := α.str

end NonemptyFinLinOrd
