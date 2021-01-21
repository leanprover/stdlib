/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Patrick Massot
-/
import tactic.ring

/-!
# `group`

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`gpow` which takes a group element and an
integer), then simplify the exponents using the `ring` tactic. The process needs to be repeated
since `ring` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

## Tags

group_theory
-/

-- The next four lemmas are not general purpose lemmas, they are intended for use only by
-- the `group` tactic.

lemma tactic.group.gpow_trick {G : Type*} [group G] (a b : G) (n m : ℤ) : a*b^n*b^m = a*b^(n+m) :=
by rw [mul_assoc, ← gpow_add]

lemma tactic.group.gpow_trick_one {G : Type*} [group G] (a b : G) (m : ℤ) : a*b*b^m = a*b^(m+1) :=
by rw [mul_assoc, mul_self_gpow]

lemma tactic.group.gpow_trick_one' {G : Type*} [group G] (a b : G) (n : ℤ) : a*b^n*b = a*b^(n+1) :=
by rw [mul_assoc, mul_gpow_self]

lemma tactic.group.gpow_trick_sub {G : Type*} [group G] (a b : G) (n m : ℤ) : a*b^n*b^(-m) = a*b^(n-m) :=
by rw [mul_assoc, ← gpow_add] ; refl

namespace tactic
open tactic.simp_arg_type tactic.interactive interactive tactic.group.
/-- Auxilliary tactic for the `group` tactic. Calls the simplifier only. -/
meta def aux_group₁ (locat : loc) : tactic unit :=
  simp_core {} skip tt [
  expr ``(mul_one),
  expr ``(one_mul),
  expr ``(one_pow),
  expr ``(one_gpow),
  expr ``(sub_self),
  expr ``(add_neg_self),
  expr ``(neg_add_self),
  expr ``(neg_neg),
  expr ``(nat.sub_self),
  expr ``(int.coe_nat_add),
  expr ``(int.coe_nat_mul),
  expr ``(int.coe_nat_zero),
  expr ``(int.coe_nat_one),
  expr ``(int.coe_nat_bit0),
  expr ``(int.coe_nat_bit1),
  expr ``(int.mul_neg_eq_neg_mul_symm),
  expr ``(int.neg_mul_eq_neg_mul_symm),
  symm_expr ``(gpow_coe_nat),
  symm_expr ``(gpow_neg_one),
  symm_expr ``(gpow_mul),
  symm_expr ``(gpow_add_one),
  symm_expr ``(gpow_one_add),
  symm_expr ``(gpow_add),
  expr ``(mul_gpow_neg_one),
  expr ``(gpow_zero),
  expr ``(mul_gpow),
  symm_expr ``(mul_assoc),
  expr ``(gpow_trick),
  expr ``(gpow_trick_one),
  expr ``(gpow_trick_one'),
  expr ``(gpow_trick_sub),
  expr ``(tactic.ring.horner)]
  [] locat

/-- Auxilliary tactic for the `group` tactic. Calls `ring` to normalize exponents. -/
meta def aux_group₂ (locat : loc) : tactic unit :=
ring none tactic.ring.normalize_mode.raw locat
end tactic

namespace tactic.interactive
setup_tactic_parser
open tactic

/--
Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h, -- normalizes `h` which becomes `h : c = d`
  rw h,       -- the goal is now `a*d*d⁻¹ = a`
  group,      -- which then normalized and closed
end
```
-/
meta def group (locat : parse location) : tactic unit :=
do when locat.include_goal `[rw ← mul_inv_eq_one],
   try (aux_group₁ locat),
   repeat (aux_group₂ locat ; aux_group₁ locat)

end tactic.interactive

add_tactic_doc
{ name := "group",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.group],
  tags := ["decision procedure", "simplification"] }
