/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import tactic.norm_num

/-!
# `field_simp` tactic

Tactic to clear denominators in algebraic expressions, based on `simp` with a specific simpset.
-/

namespace tactic

/-- Try to prove a goal of the form `x ≠ 0` by calling `assumption`, or `norm_num1` if `x` is
a numeral. -/
meta def field_simp.ne_zero : tactic unit := do
  goal ← tactic.target,
  match goal with
  | `(%%e ≠ 0) := assumption <|> do n ← e.to_rat, `[norm_num1]
  | _ := tactic.fail "goal should be of the form `x ≠ 0`"
  end

namespace interactive
open interactive interactive.types

/--
The goal of `field_simp` is to reduce an expression in a field to an expression of the form `n / d`
where neither `n` nor `d` contains any division symbol, just using the simplifier (with a carefully
crafted simpset named `field_simps`) to reduce the number of division symbols whenever possible by
iterating the following steps:

- write an inverse as a division
- in any product, move the division to the right
- if there are several divisions in a product, group them together at the end and write them as a
  single division
- reduce a sum to a common denominator

If the goal is an equality, this simpset will also clear the denominators, so that the proof
can normally be concluded by an application of `ring` or `ring_exp`.

`field_simp [hx, hy]` is a short form for
`simp [-one_div, -mul_eq_zero, hx, hy] with field_simps {discharger := [field_simp.ne_zero]}`

Note that this naive algorithm will not try to detect common factors in denominators to reduce the
complexity of the resulting expression. Instead, it relies on the ability of `ring` to handle
complicated expressions in the next step.

As always with the simplifier, reduction steps will only be applied if the preconditions of the
lemmas can be checked. This means that proofs that denominators are nonzero should be included. The
fact that a product is nonzero when all factors are, and that a power of a nonzero number is
nonzero, are included in the simpset, but more complicated assertions (especially dealing with sums)
should be given explicitly. If your expression is not completely reduced by the simplifier
invocation, check the denominators of the resulting expression and provide proofs that they are
nonzero to enable further progress.

To check that denominators are nonzero, `field_simp` will look for facts in the context, and
will try to apply `norm_num` to close numerical goals.

The invocation of `field_simp` removes the lemma `one_div` from the simpset, as this lemma
works against the algorithm explained above. It also removes
`mul_eq_zero : x * y = 0 ↔ x = 0 ∨ y = 0`, as `norm_num` can not work on disjunctions to
close goals of the form `24 ≠ 0`, and replaces it with `mul_ne_zero : x ≠ 0 → y ≠ 0 → x * y ≠ 0`
creating two goals instead of a disjunction.

For example,
```lean
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
  a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) :=
begin
  field_simp,
  ring
end
```

See also the `cancel_denoms` tactic, which tries to do a similar simplification for expressions
that have numerals in denominators.
The tactics are not related: `cancel_denoms` will only handle numeric denominators, and will try to
entirely remove (numeric) division from the expression by multiplying by a factor.
-/
meta def field_simp (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list)
  (locat : parse location)
  (cfg : simp_config_ext := {discharger := field_simp.ne_zero}) : tactic unit :=
let attr_names := `field_simps :: attr_names,
    hs := simp_arg_type.except `one_div :: simp_arg_type.except `mul_eq_zero :: hs in
propagate_tags (simp_core cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat)

add_tactic_doc
{ name       := "field_simp",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.field_simp],
  tags       := ["simplification", "arithmetic"] }

end interactive
end tactic
