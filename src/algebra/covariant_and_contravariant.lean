/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import algebra.group.defs

/-!

# Covariants and contravariants

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `ordered_[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `covariant_class` and
`contravariant_class`:

* `covariant_class` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `contravariant_class` models the implication `a * b < a * c → b < c`.

Since `co(ntra)variant_class` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`ordered_[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[ordered_cancel_monoid M]`, into three typeclasses, e.g.
`[left_cancel_semigroup M] [partial_order M] [covariant_class M M (function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several co(ntra)variant_class assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[covariant_class M M (*) (≤)] [contravariant_class M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `covariant_class` uses the `(≤)`-relation, while
`contravariant_class` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[semigroup α] [partial_order α] [contravariant_class α α (*) (≤)] => left_cancel_semigroup α
```
holds -- note the `co*ntra*` assumption on the `(≤)`-relation.

# Formalization notes

We stick to the convention of using `function.swap (*)` (or `function.swap (+)`), for the
typeclass assumptions, since `function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use. -/

-- TODO: convert `has_exists_mul_of_le`, `has_exists_add_of_le`?
-- TODO: relationship with `con/add_con`
-- TODO: include equivalence of `left_cancel_semigroup` with
-- `semigroup partial_order contravariant_class α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion?  See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.

section variants
variables {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variables (M N)
/-- `covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `covariant_class` doc-string for its meaning. -/
def covariant     : Prop := ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/-- `contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `contravariant_class` doc-string for its meaning. -/
def contravariant : Prop := ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

/--  Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`covariant_class` says that "the action `μ` preserves the relation `r`.

More precisely, the `covariant_class` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by "acting upon it by `m`".

If `m : M` and `h : r n₁ n₂`, then `covariant_class.elim m h : r (μ m n₁) (μ m n₂)`.
-/
@[protect_proj] class covariant_class : Prop :=
(elim :  covariant M N μ r)

/--  Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`contravariant_class` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`.

More precisely, the `contravariant_class` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by "acting upon it by `m`"", then, the relation `r`
also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `contravariant_class.elim m h : r n₁ n₂`.
-/
@[protect_proj] class contravariant_class : Prop :=
(elim : contravariant M N μ r)

lemma rel_iff_cov [covariant_class M N μ r] [contravariant_class M N μ r] (m : M) {a b : N} :
  r (μ m a) (μ m b) ↔ r a b :=
⟨contravariant_class.elim _, covariant_class.elim _⟩

section covariant
variables {M N μ r} [covariant_class M N μ r]

lemma act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) :
  r (μ m a) (μ m b) :=
covariant_class.elim _ ab

lemma group.covariant_iff_contravariant [group N] :
  covariant N N (*) r ↔ contravariant N N (*) r :=
begin
  refine ⟨λ h a b c bc, _, λ h a b c bc, _⟩,
  { rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c],
    exact h a⁻¹ bc },
  { rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc,
    exact h a⁻¹ bc }
end

lemma covconv [group N] [cov : covariant_class N N (*) r] : contravariant_class N N (*) r :=
{ elim := λ a b c bc, group.covariant_iff_contravariant.mp cov.elim _ bc }


section is_trans
variables [is_trans N r] (m n : M) {a b c d : N}

/-  Lemmas with 3 elements. -/
lemma act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) :
  r (μ m a) c :=
trans (act_rel_act_of_rel m ab) rl

lemma rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) :
  r c (μ m b) :=
trans rr (act_rel_act_of_rel _ ab)

end is_trans

end covariant

/-  Lemma with 4 elements. -/
section M_eq_N
variables {M N μ r} {mu : N → N → N} [is_trans N r]
  [covariant_class N N mu r] [covariant_class N N (function.swap mu) r] {a b c d : N}

lemma act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) :
  r (mu a c) (mu b d) :=
trans (act_rel_act_of_rel c ab : _) (act_rel_act_of_rel b cd)

end M_eq_N

section contravariant
variables {M N μ r} [contravariant_class M N μ r]

lemma rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) :
  r a b :=
contravariant_class.elim _ ab

section is_trans
variables [is_trans N r] (m n : M) {a b c d : N}

/-  Lemmas with 3 elements. -/
lemma act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
  r (μ m a) c :=
trans ab (rel_of_act_rel_act m rl)

lemma rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
  r a (μ m c) :=
trans (rel_of_act_rel_act m ab) rr

end is_trans

end contravariant

lemma covariant_le_of_covariant_lt [partial_order N] :
  covariant M N μ (<) → covariant M N μ (≤) :=
begin
  refine λ h a b c bc, _,
  rcases le_iff_eq_or_lt.mp bc with rfl | bc,
  { exact rfl.le },
  { exact (h _ bc).le }
end

lemma contravariant_lt_of_contravariant_le [partial_order N] :
  contravariant M N μ (≤) → contravariant M N μ (<) :=
begin
  refine λ h a b c bc, lt_iff_le_and_ne.mpr ⟨h a bc.le, _⟩,
  rintro rfl,
  exact lt_irrefl _ bc,
end

lemma covariant_le_iff_contravariant_lt [linear_order N] :
  covariant M N μ (≤) ↔ contravariant M N μ (<) :=
⟨ λ h a b c bc, not_le.mp (λ k, not_le.mpr bc (h _ k)),
  λ h a b c bc, not_lt.mp (λ k, not_lt.mpr bc (h _ k))⟩

lemma covariant_lt_iff_contravariant_le [linear_order N] :
  covariant M N μ (<) ↔ contravariant M N μ (≤) :=
⟨ λ h a b c bc, not_lt.mp (λ k, not_lt.mpr bc (h _ k)),
  λ h a b c bc, not_le.mp (λ k, not_le.mpr bc (h _ k))⟩

@[to_additive]
lemma covariant_flip_mul_iff [comm_semigroup N] :
  covariant N N (flip (*)) (r) ↔ covariant N N (*) (r) :=
by rw is_symm_op.flip_eq

@[to_additive]
lemma contravariant_flip_mul_iff [comm_semigroup N] :
  contravariant N N (flip (*)) (r) ↔ contravariant N N (*) (r) :=
by rw is_symm_op.flip_eq

@[to_additive]
instance contravariant_mul_lt_of_covariant_mul_le [has_mul N] [linear_order N]
  [covariant_class N N (*) (≤)] : contravariant_class N N (*) (<) :=
{ elim := (covariant_le_iff_contravariant_lt N N (*)).mp covariant_class.elim }

@[to_additive]
instance covariant_swap_mul_le_of_covariant_mul_le [comm_semigroup N] [has_le N]
  [covariant_class N N (*) (≤)] : covariant_class N N (function.swap (*)) (≤) :=
{ elim := (covariant_flip_mul_iff N (≤)).mpr covariant_class.elim }

@[to_additive]
instance contravariant_swap_mul_le_of_contravariant_mul_le [comm_semigroup N] [has_le N]
  [contravariant_class N N (*) (≤)] : contravariant_class N N (function.swap (*)) (≤) :=
{ elim := (contravariant_flip_mul_iff N (≤)).mpr contravariant_class.elim }

@[to_additive]
instance contravariant_swap_mul_lt_of_contravariant_mul_lt [comm_semigroup N] [has_lt N]
  [contravariant_class N N (*) (<)] : contravariant_class N N (function.swap (*)) (<) :=
{ elim := (contravariant_flip_mul_iff N (<)).mpr contravariant_class.elim }

@[to_additive]
instance covariant_swap_mul_lt_of_covariant_mul_lt [comm_semigroup N] [has_lt N]
  [covariant_class N N (*) (<)] : covariant_class N N (function.swap (*)) (<) :=
{ elim := (covariant_flip_mul_iff N (<)).mpr covariant_class.elim }

@[to_additive]
instance left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le
  [left_cancel_semigroup N] [partial_order N] [covariant_class N N (*) (≤)] :
  covariant_class N N (*) (<) :=
{ elim := λ a b c bc, by { cases lt_iff_le_and_ne.mp bc with bc cb,
    exact lt_iff_le_and_ne.mpr ⟨covariant_class.elim a bc, (mul_ne_mul_right a).mpr cb⟩ } }

@[to_additive]
instance right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le
  [right_cancel_semigroup N] [partial_order N] [covariant_class N N (function.swap (*)) (≤)] :
  covariant_class N N (function.swap (*)) (<) :=
{ elim := λ a b c bc, by { cases lt_iff_le_and_ne.mp bc with bc cb,
    exact lt_iff_le_and_ne.mpr ⟨covariant_class.elim a bc, (mul_ne_mul_left a).mpr cb⟩ } }

@[to_additive]
instance left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt
  [left_cancel_semigroup N] [partial_order N] [contravariant_class N N (*) (<)] :
  contravariant_class N N (*) (≤) :=
{ elim := λ a b c bc, by { cases le_iff_eq_or_lt.mp bc with h h,
    { exact ((mul_right_inj a).mp h).le },
    { exact (contravariant_class.elim _ h).le } } }

@[to_additive]
instance right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt
  [right_cancel_semigroup N] [partial_order N] [contravariant_class N N (function.swap (*)) (<)] :
  contravariant_class N N (function.swap (*)) (≤) :=
{ elim := λ a b c bc, by { cases le_iff_eq_or_lt.mp bc with h h,
    { exact ((mul_left_inj a).mp h).le },
    { exact (contravariant_class.elim _ h).le } } }

end variants
