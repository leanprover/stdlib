/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import data.int.cast

/-!
# A tactic to shift `ℕ` goals to `ℤ`

It is often easier to work in `ℤ`, where subtraction is well behaved, than in `ℕ` where it isn't.
`zify` is a tactic that casts goals and hypotheses about natural numbers to ones about integers.
It makes use of `push_cast`, part of the `norm_cast` family, to simplify these goals.

## Implementation notes

`zify` is extensible, using the attribute `@[zify]` to label lemmas used for moving propositions
from `ℕ` to `ℤ`.
`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.

`zify` is very nearly just `simp only with zify push_cast`. There are a few minor differences:
* `zify` lemmas are used in the opposite order of the standard simp form.
  E.g. we will rewrite with `int.coe_nat_le_coe_nat_iff` from right to left.
* `zify` should fail if no `zify` lemma applies (i.e. it was unable to shift any proposition to ℤ).
  However, once this succeeds, it does not necessarily need to rewrite with any `push_cast` rules.
-/

open tactic

namespace zify

/--
The `zify` attribute is used by the `zify` tactic. It applies to lemmas that shift propositions
between `nat` and `int`.

`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.
-/
@[user_attribute]
meta def zify_attr : user_attribute simp_lemmas unit :=
{ name := `zify,
  descr := "Used to tag lemmas for use in the `zify` tactic",
  cache_cfg :=
    { mk_cache :=
        λ ns, mmap (λ n, do c ← mk_const n, return (c, tt)) ns >>= simp_lemmas.mk.append_with_symm,
      dependencies := [] } }

/--
Given an expression `e`, `lift_to_z e` looks for subterms of `e` that are propositions "about"
natural numbers and change them to propositions about integers.

Returns an expression `e'` and a proof that `e = e'`.

Includes `ge_iff_le` and `gt_iff_lt` in the simp set. These can't be tagged with `zify` as we
want to use them in the "forward", not "backward", direction.
-/
meta def lift_to_z (e : expr) : tactic (expr × expr) :=
do sl ← zify_attr.get_cache,
   sl ← sl.add_simp `ge_iff_le, sl ← sl.add_simp `gt_iff_lt,
   simplify sl [] e

attribute [zify] int.coe_nat_le_coe_nat_iff int.coe_nat_lt_coe_nat_iff int.coe_nat_eq_coe_nat_iff

end zify

@[zify] lemma int.coe_nat_ne_coe_nat_iff (a b : ℕ) : (a : ℤ) ≠ b ↔ a ≠ b :=
by simp

/--
`zify extra_lems e` is used to shift propositions in `e` from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

The list of extra lemmas is used in the `push_cast` step.

Returns an expression `e'` and a proof that `e = e'`.-/
meta def tactic.zify (extra_lems : list simp_arg_type) : expr → tactic (expr × expr) := λ z,
do (z1, p1) ← zify.lift_to_z z <|> fail "failed to find an applicable zify lemma",
   (z2, p2) ← norm_cast.derive_push_cast extra_lems z1,
   prod.mk z2 <$> mk_eq_trans p1 p2

/--
A variant of `tactic.zify` that takes `h`, a proof of a proposition about natural numbers,
and returns a proof of the zified version of that propositon.
-/
meta def tactic.zify_proof (extra_lems : list simp_arg_type) (h : expr) : tactic expr :=
do (_, pf) ← infer_type h >>= tactic.zify extra_lems,
   mk_eq_mp pf h

section

setup_tactic_parser

/--
The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

```lean
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b :=
begin
  zify,
  zify at h,
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
end
```

`zify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : false :=
begin
  zify [hab] at h,
  /- h : ↑a - ↑b < ↑c -/
end
```

`zify` makes use of the `@[zify]` attribute to move propositions,
and the `push_cast` tactic to simplify the `ℤ`-valued expressions.

`zify` is in some sense dual to the `lift` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
meta def tactic.interactive.zify (sl : parse simp_arg_list) (l : parse location) : tactic unit :=
do locs ← l.get_locals,
replace_at (tactic.zify sl) locs l.include_goal >>= guardb

end

add_tactic_doc
{ name := "zify",
  category := doc_category.attr,
  decl_names := [`zify.zify_attr],
  tags := ["coercions", "transport"] }

add_tactic_doc
{ name := "zify",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.zify],
  tags := ["coercions", "transport"] }
