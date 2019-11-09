# Mathlib tactics #

In addition to [core tactics](https://leanprover.github.io/reference/tactics.html),
mathlib provides a number of specific interactive tactics and commands.
Here we document the mostly commonly used ones.

### tfae

The `tfae` tactic suite is a set of tactics that help with proving that certain
propositions are equivalent.
In `data/list/basic.lean` there is a section devoted to propositions of the
form
```lean
tfae [p1, p2, ..., pn]
```
where `p1`, `p2`, through, `pn` are terms of type `Prop`.
This proposition asserts that all the `pi` are pairwise equivalent.
There are results that allow to extract the equivalence
of two propositions `pi` and `pj`.

To prove a goal of the form `tfae [p1, p2, ..., pn]`, there are two
tactics.  The first tactic is `tfae_have`.  As an argument it takes an
expression of the form `i arrow j`, where `i` and `j` are two positive
natural numbers, and `arrow` is an arrow such as `→`, `->`, `←`, `<-`,
`↔`, or `<->`.  The tactic `tfae_have : i arrow j` sets up a subgoal in
which the user has to prove the equivalence (or implication) of `pi` and `pj`.

The remaining tactic, `tfae_finish`, is a finishing tactic. It
collects all implications and equivalences from the local context and
computes their transitive closure to close the
main goal.

`tfae_have` and `tfae_finish` can be used together in a proof as
follows:

```lean
example (a b c d : Prop) : tfae [a,b,c,d] :=
begin
  tfae_have : 3 → 1,
  { /- prove c → a -/ },
  tfae_have : 2 → 3,
  { /- prove b → c -/ },
  tfae_have : 2 ← 1,
  { /- prove a → b -/ },
  tfae_have : 4 ↔ 2,
  { /- prove d ↔ b -/ },
    -- a b c d : Prop,
    -- tfae_3_to_1 : c → a,
    -- tfae_2_to_3 : b → c,
    -- tfae_1_to_2 : a → b,
    -- tfae_4_iff_2 : d ↔ b
    -- ⊢ tfae [a, b, c, d]
  tfae_finish,
end
```

### rcases

The `rcases` tactic is the same as `cases`, but with more flexibility in the
`with` pattern syntax to allow for recursive case splitting. The pattern syntax
uses the following recursive grammar:

```lean
patt ::= (patt_list "|")* patt_list
patt_list ::= id | "_" | "⟨" (patt ",")* patt "⟩"
```

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive
datatype, naming the first three parameters of the first constructor as
`a,b,c` and the first two of the second constructor `d,e`. If the list
is not as long as the number of arguments to the constructor or the
number of constructors, the remaining variables will be automatically
named. If there are nested brackets such as `⟨⟨a⟩, b | c⟩ | d` then
these will cause more case splits as necessary. If there are too many
arguments, such as `⟨a, b, c⟩` for splitting on `∃ x, ∃ y, p x`, then it
will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last parameter as
necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an assumption
`h : e = PAT` will be added to the context.

`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.

### rintro

The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintros (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.

### obtain

The `obtain` tactic is a combination of `have` and `rcases`.
```lean
obtain ⟨patt⟩ : type,
{ ... }
```
is equivalent to
```lean
have h : type,
{ ... },
rcases h with ⟨patt⟩
```

 The syntax `obtain ⟨patt⟩ : type := proof` is also supported.

 If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

 If `type` is omitted, `:= proof` is required.


### simpa

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ...] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ...]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic.

### replace

Acts like `have`, but removes a hypothesis with the same name as
this one. For example if the state is `h : p ⊢ goal` and `f : p → q`,
then after `replace h := f h` the goal will be `h : q ⊢ goal`,
where `have h := f h` would result in the state `h : p, h : q ⊢ goal`.
This can be used to simulate the `specialize` and `apply at` tactics
of Coq.

### elide/unelide

The `elide n (at ...)` tactic hides all subterms of the target goal or hypotheses
beyond depth `n` by replacing them with `hidden`, which is a variant
on the identity function. (Tactics should still mostly be able to see
through the abbreviation, but if you want to unhide the term you can use
`unelide`.)

The `unelide (at ...)` tactic removes all `hidden` subterms in the target
types (usually added by `elide`).

### finish/clarify/safe

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

* finish:  solves the goal or fails
* clarify: makes as much progress as possible while not leaving more than one goal
* safe:    splits freely, finishes off whatever subgoals it can, and leaves the rest

All accept an optional list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.) All also accept an optional list of `ematch` lemmas, which must be preceded by `using`.

### abel

Evaluate expressions in the language of *additive*, commutative monoids and groups.
It attempts to prove the goal outright if there is no `at`
specifier and the target is an equality, but if this
fails, it falls back to rewriting all monoid expressions into a normal form.
If there is an `at` specifier, it rewrites the given target into a normal form.
```lean
example {α : Type*} {a b : α} [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example {α : Type*} {a b : α} [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example {α : Type*} {a b : α} [add_comm_group α] (hyp : a + a - a = b - b) : a = 0 :=
by { abel at hyp, exact hyp }
```

### ring

Evaluate expressions in the language of *commutative* (semi)rings.
Based on [Proving Equalities in a Commutative Ring Done Right in Coq](http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf) by Benjamin Grégoire and Assia Mahboubi.

### congr'

Same as the `congr` tactic, but takes an optional argument which gives
the depth of recursive applications. This is useful when `congr`
is too aggressive in breaking down the goal. For example, given
`⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`.
If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.

### convert

The `exact e` and `refine e` tactics require a term `e` whose type is
definitionally equal to the goal. `convert e` is similar to `refine
e`, but the type of `e` is not required to exactly match the
goal. Instead, new goals are created for differences between the type
of `e` and the goal. For example, in the proof state

```lean
n : ℕ,
e : prime (2 * n + 1)
⊢ prime (n + n + 1)
```

the tactic `convert e` will change the goal to

```lean
⊢ n + n = 2 * n
```

In this example, the new goal can be solved using `ring`.

The syntax `convert ← e` will reverse the direction of the new goals
(producing `⊢ 2 * n = n + n` in this example).

Internally, `convert e` works by creating a new goal asserting that
the goal equals the type of `e`, then simplifying it using
`congr'`. The syntax `convert e using n` can be used to control the
depth of matching (like `congr' n`). In the example, `convert e using
1` would produce a new goal `⊢ n + n + 1 = 2 * n + 1`.

### unfold_coes

Unfold coercion-related definitions

### Instance cache tactics

For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics described below
helps forcing such updates. For a simple (but very artificial) example,
consider the function `default` from the core library. It has type
`Π (α : Sort u) [inhabited α], α`, so one can use `default α` only if Lean
can find a registered instance of `inhabited α`. Because the database of
such instance is not automatically updated during a proof, the following
attempt won't work (Lean will not pick up the instance from the local
context):
```lean
def my_id (α : Type) : α → α :=
begin
  intro x,
  have : inhabited α := ⟨x⟩,
  exact default α, -- Won't work!
end
```
However, it will work, producing the identity function, if one replaces have by its variant `haveI` described below.

* `resetI`: Reset the instance cache. This allows any instances
  currently in the context to be used in typeclass inference.

* `unfreezeI`: Unfreeze local instances, which allows us to revert
  instances in the context

* `introI`/`introsI`: `intro`/`intros` followed by `resetI`. Like
  `intro`/`intros`, but uses the introduced variable in typeclass inference.

* `haveI`/`letI`: `have`/`let` followed by `resetI`. Used to add typeclasses
  to the context so that they can be used in typeclass inference. The syntax
  `haveI := <proof>` and `haveI : t := <proof>` is supported, but
  `haveI : t, from _` and `haveI : t, { <proof> }` are not; in these cases
  use `have : t, { <proof> }, resetI` directly).

* `exactI`: `resetI` followed by `exact`. Like `exact`, but uses all
  variables in the context for typeclass inference.

### suggest

`suggest` lists possible usages of the `refine` tactic and leaves the tactic state unchanged.
It is intended as a complement of the search function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num` (or less, if all possibilities are exhausted) possibilities ordered by length of lemma names. The default for `num` is `50`.

For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that `suggest` might miss some results if `num` is not large enough. However, because `suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.

An example of `suggest` in action,

```lean
example (n : nat) : n < n + 1 :=
begin suggest, sorry end
```

prints the list,

```lean
exact nat.lt.base n
exact nat.lt_succ_self n
refine not_le.mp _
refine gt_iff_lt.mp _
refine nat.lt.step _
refine lt_of_not_ge _
...
```

### library_search

`library_search` is a tactic to identify existing lemmas in the library. It tries to close the
current goal by applying a lemma from the library, then discharging any new goals using
`solve_by_elim`.

Typical usage is:
```
example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- exact nat.mul_sub_left_distrib n m k
```

`library_search` prints a trace message showing the proof it found, shown above as a comment.
Typically you will then copy and paste this proof, replacing the call to `library_search`.

### find

The `find` command from `tactic.find` allows to find lemmas using
pattern matching. For instance:

```lean
import tactic.find

#find _ + _ = _ + _
#find (_ : ℕ) + _ = _ + _
```

### solve_by_elim

The tactic `solve_by_elim` repeatedly applies assumptions to the current goal, and succeeds if this eventually discharges the main goal.
```lean
solve_by_elim { discharger := `[cc] }
```
also attempts to discharge the goal using congruence closure before each round of applying assumptions.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

By default `solve_by_elim` also applies `congr_fun` and `congr_arg` against the goal.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas (or all lemmas tagged with the named
attributes).
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context, `congr_fun`, or `congr_arg`
unless they are explicitly included.
* `solve_by_elim [-id_1, ... -id_n]` uses the default assumptions, removing the specified ones.

### ext1 / ext

 * `ext1 id` selects and apply one extensionality lemma (with
    attribute `ext`), using `id`, if provided, to name a
    local constant introduced by the lemma. If `id` is omitted, the
    local constant is named automatically, as per `intro`.

 * `ext` applies as many extensionality lemmas as possible;
 * `ext ids`, with `ids` a list of identifiers, finds extentionality
    and applies them until it runs out of identifiers in `ids` to name
    the local constants.

When trying to prove:

  ```lean
  α β : Type,
  f g : α → set β
  ⊢ f = g
  ```

applying `ext x y` yields:

  ```lean
  α β : Type,
  f g : α → set β,
  x : α,
  y : β
  ⊢ y ∈ f x ↔ y ∈ g x
  ```

by applying functional extensionality and set extensionality.

A maximum depth can be provided with `ext x y z : 3`.

### The `ext` attribute

 Tag lemmas of the form:

 ```lean
 @[ext]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 The attribute indexes extensionality lemma using the type of the
 objects (i.e. `my_collection`) which it gets from the statement of
 the lemma.  In some cases, the same lemma can be used to state the
 extensionality of multiple types that are definitionally equivalent.

 ```lean
 attribute [ext [(→),thunk,stream]] funext
 ```

 Those parameters are cumulative. The following are equivalent:

 ```lean
 attribute [ext [(→),thunk]] funext
 attribute [ext [stream]] funext
 ```

 and

 ```lean
 attribute [ext [(→),thunk,stream]] funext
 ```

 One removes type names from the list for one lemma with:

 ```lean
 attribute [ext [-stream,-thunk]] funext
 ```

 Also, the following:

 ```lean
 @[ext]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 is equivalent to

 ```lean
 @[ext *]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 The `*` parameter indicates to simply infer the
 type from the lemma's statement.

 This allows us specify type synonyms along with the type
 that referred to in the lemma statement.

 ```lean
 @[ext [*,my_type_synonym]]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 Attribute `ext` can be applied to a structure to generate its extensionality lemma:

 ```
 @[ext]
 structure foo (α : Type*) :=
 (x y : ℕ)
 (z : {z // z < x})
 (k : α)
 (h : x < y)
 ```

 will generate:

 ```
 @[ext] lemma foo.ext : ∀ {α : Type u_1} (x y : foo α), x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
 ```
 
### refine_struct

`refine_struct { .. }` acts like `refine` but works only with structure instance
literals. It creates a goal for each missing field and tags it with the name of the
field so that `have_field` can be used to generically refer to the field currently
being refined.

As an example, we can use `refine_struct` to automate the construction semigroup
instances:

```lean
refine_struct ( { .. } : semigroup α ),
-- case semigroup, mul
-- α : Type u,
-- ⊢ α → α → α

-- case semigroup, mul_assoc
-- α : Type u,
-- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)
```

`have_field`, used after `refine_struct _` poses `field` as a local constant
with the type of the field of the current goal:

```lean
refine_struct ({ .. } : semigroup α),
{ have_field, ... },
{ have_field, ... },
```
behaves like
```lean
refine_struct ({ .. } : semigroup α),
{ have field := @semigroup.mul, ... },
{ have field := @semigroup.mul_assoc, ... },
```

### apply_rules

`apply_rules hs n` applies the list of lemmas `hs` and `assumption` on the
first goal and the resulting subgoals, iteratively, at most `n` times.
`n` is optional, equal to 50 by default.
`hs` can contain user attributes: in this case all theorems with this
attribute are added to the list of rules.

For instance:

```lean
@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }

attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

lemma my_test {a b c d e : real} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
-- any of the following lines solve the goal:
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3
by apply_rules [add_le_add, mul_le_mul_of_nonneg_right]
by apply_rules [mono_rules]
by apply_rules mono_rules
```

### h_generalize

`h_generalize Hx : e == x` matches on `cast _ e` in the goal and replaces it with
`x`. It also adds `Hx : e == x` as an assumption. If `cast _ e` appears multiple
times (not necessarily with the same proof), they are all replaced by `x`. `cast`
`eq.mp`, `eq.mpr`, `eq.subst`, `eq.substr`, `eq.rec` and `eq.rec_on` are all treated
as casts.

 - `h_generalize Hx : e == x with h` adds hypothesis `α = β` with `e : α, x : β`;
 - `h_generalize Hx : e == x with _` chooses automatically chooses the name of
    assumption `α = β`;
  - `h_generalize! Hx : e == x` reverts `Hx`;
  - when `Hx` is omitted, assumption `Hx : e == x` is not added.

### pi_instance

`pi_instance` constructs an instance of `my_class (Π i : I, f i)`
where we know `Π i, my_class (f i)`. If an order relation is required,
it defaults to `pi.partial_order`. Any field of the instance that
`pi_instance` cannot construct is left untouched and generated as a
new goal.

### assoc_rewrite

`assoc_rewrite [h₀, ← h₁] at ⊢ h₂` behaves like
`rewrite [h₀, ← h₁] at ⊢ h₂` with the exception that associativity is
used implicitly to make rewriting possible.

### restate_axiom

`restate_axiom` makes a new copy of a structure field, first definitionally simplifying the type.
This is useful to remove `auto_param` or `opt_param` from the statement.

As an example, we have:
```lean
structure A :=
(x : ℕ)
(a' : x = 1 . skip)

example (z : A) : z.x = 1 := by rw A.a' -- rewrite tactic failed, lemma is not an equality nor a iff

restate_axiom A.a'
example (z : A) : z.x = 1 := by rw A.a
```

By default, `restate_axiom` names the new lemma by removing a trailing `'`, or otherwise appending
`_lemma` if there is no trailing `'`. You can also give `restate_axiom` a second argument to
specify the new name, as in
```lean
restate_axiom A.a f
example (z : A) : z.x = 1 := by rw A.f
```

### def_replacer

`def_replacer foo` sets up a stub definition `foo : tactic unit`, which can
effectively be defined and re-defined later, by tagging definitions with `@[foo]`.

- `@[foo] meta def foo_1 : tactic unit := ...` replaces the current definition of `foo`.
- `@[foo] meta def foo_2 (old : tactic unit) : tactic unit := ...` replaces the current
  definition of `foo`, and provides access to the previous definition via `old`.
  (The argument can also be an `option (tactic unit)`, which is provided as `none` if
  this is the first definition tagged with `@[foo]` since `def_replacer` was invoked.)

`def_replacer foo : α → β → tactic γ` allows the specification of a replacer with
custom input and output types. In this case all subsequent redefinitions must have the
same type, or the type `α → β → tactic γ → tactic γ` or
`α → β → option (tactic γ) → tactic γ` analogously to the previous cases.

### tidy

`tidy` attempts to use a variety of conservative tactics to solve the goals.
In particular, `tidy` uses the `chain` tactic to repeatedly apply a list of tactics to
the goal and recursively on new goals, until no tactic makes further progress.

`tidy` can report the tactic script it found using `tidy?`. As an example
```lean
example : ∀ x : unit, x = unit.star :=
begin
  tidy? -- Prints the trace message: "intros x, exact dec_trivial"
end
```

The default list of tactics can be found by looking up the definition of
[`default_tidy_tactics`](https://github.com/leanprover/mathlib/blob/master/tactic/tidy.lean).

This list can be overriden using `tidy { tactics :=  ... }`. (The list must be a list of
`tactic string`, so that `tidy?` can report a usable tactic script.)

### linarith

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `false`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over the rationals. While there is some special handling for non-dense orders like `nat` and `int`, this tactic is not complete for these theories and will not prove every true goal.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
h1, h2, h3, and proofs t1, t2, t3. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith {discharger := tac, restrict_type := tp, exfalso := ff}` takes a config object with three optional
arguments.
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
proof stage. The default is `ring`. Other options currently include `ring SOP` or `simp` for basic
problems.
* `restrict_type` will only use hypotheses that are inequalities over `tp`. This is useful
if you have e.g. both integer and rational valued inequalities in the local context, which can
sometimes confuse the tactic.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`. (True by default.)

### choose

`choose a b h using hyp` takes an hypothesis `hyp` of the form
`∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b` for some `P : X → Y → A → B → Prop` and outputs
into context a function `a : X → Y → A`, `b : X → Y → B` and a proposition `h` stating
`∀ (x : X) (y : Y), P x y (a x y) (b x y)`. It presumably also works with dependent versions.

Example:

```lean
example (h : ∀n m : ℕ, ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i := ℕ → ℕ → ℕ,
  guard_hyp j := ℕ → ℕ → ℕ,
  guard_hyp h := ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n,
  trivial
end
```

### squeeze_simp / squeeze_simpa

`squeeze_simp` and `squeeze_simpa` perform the same task with
the difference that `squeeze_simp` relates to `simp` while
`squeeze_simpa` relates to `simpa`. The following applies to both
`squeeze_simp` and `squeeze_simpa`.

`squeeze_simp` behaves like `simp` (including all its arguments)
and prints a `simp only` invokation to skip the search through the
`simp` lemma list.

For instance, the following is easily solved with `simp`:

```lean
example : 0 + 1 = 1 + 0 := by simp
```

To guide the proof search and speed it up, we may replace `simp`
with `squeeze_simp`:

```lean
example : 0 + 1 = 1 + 0 := by squeeze_simp
-- prints: simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp` suggests a replacement which we can use instead of
`squeeze_simp`.

```lean
example : 0 + 1 = 1 + 0 := by simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp only` prints nothing as it already skips the `simp` list.

This tactic is useful for speeding up the compilation of a complete file.
Steps:

   1. search and replace ` simp` with ` squeeze_simp` (the space helps avoid the
      replacement of `simp` in `@[simp]`) throughout the file.
   2. Starting at the beginning of the file, go to each printout in turn, copy
      the suggestion in place of `squeeze_simp`.
   3. after all the suggestions were applied, search and replace `squeeze_simp` with
      `simp` to remove the occurrences of `squeeze_simp` that did not produce a suggestion.

Known limitation(s):
  * in cases where `squeeze_simp` is used after a `;` (e.g. `cases x; squeeze_simp`),
    `squeeze_simp` will produce as many suggestions as the number of goals it is applied to.
    It is likely that none of the suggestion is a good replacement but they can all be
    combined by concatenating their list of lemmas.

### fin_cases
`fin_cases h` performs case analysis on a hypothesis of the form
1) `h : A`, where `[fintype A]` is available, or
2) `h ∈ A`, where `A : finset X`, `A : multiset X` or `A : list X`.

`fin_cases *` performs case analysis on all suitable hypotheses.

As an example, in
```
example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases p; simp,
  all_goals { assumption }
end
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.

### conv
The `conv` tactic is built-in to lean. Inside `conv` blocks mathlib currently
additionally provides
   * `erw`,
   * `ring` and `ring2`,
   * `norm_num`, and
   * `conv` (within another `conv`).
Using `conv` inside a `conv` block allows the user to return to the previous
state of the outer `conv` block after it is finished. Thus you can continue
editing an expression without having to start a new `conv` block and re-scoping
everything. For example:
```lean
example (a b c d : ℕ) (h₁ : b = c) (h₂ : a + c = a + d) : a + b = a + d :=
by conv {
  to_lhs,
  conv {
    congr, skip,
    rw h₁,
  },
  rw h₂,
}
```
Without `conv` the above example would need to be proved using two successive
`conv` blocks each beginning with `to_lhs`.

Also, as a shorthand `conv_lhs` and `conv_rhs` are provided, so that
```lean
example : 0 + 0 = 0 :=
begin
  conv_lhs { simp }
end
```
just means
```lean
example : 0 + 0 = 0 :=
begin
  conv { to_lhs, simp }
end
```
and likewise for `to_rhs`.

### mono

- `mono` applies a monotonicity rule.
- `mono*` applies monotonicity rules repetitively.
- `mono with x ≤ y` or `mono with [0 ≤ x,0 ≤ y]` creates an assertion for the listed
  propositions. Those help to select the right monotonicity rule.
- `mono left` or `mono right` is useful when proving strict orderings:
   for `x + y < w + z` could be broken down into either
    - left:  `x ≤ w` and `y < z` or
    - right: `x < w` and `y ≤ z`

To use it, first import `tactic.monotonicity`.

Here is an example of mono:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
  mono, -- unfold `(-)`, apply add_le_add
  { -- ⊢ k + 3 + x ≤ k + 4 + x
    mono, -- apply add_le_add, refl
    -- ⊢ k + 3 ≤ k + 4
    mono },
  { -- ⊢ -y ≤ -z
    mono /- apply neg_le_neg -/ }
end
```

More succinctly, we can prove the same goal as:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
by mono*
```

### ac_mono

`ac_mono` reduces the `f x ⊑ f y`, for some relation `⊑` and a
monotonic function `f` to `x ≺ y`.

`ac_mono*` unwraps monotonic functions until it can't.

`ac_mono^k`, for some literal number `k` applies monotonicity `k`
times.

`ac_mono h`, with `h` a hypothesis, unwraps monotonic functions and
uses `h` to solve the remaining goal. Can be combined with `*` or `^k`:
`ac_mono* h`

`ac_mono : p` asserts `p` and uses it to discharge the goal result
unwrapping a series of monotonic functions. Can be combined with * or
^k: `ac_mono* : p`

In the case where `f` is an associative or commutative operator,
`ac_mono` will consider any possible permutation of its arguments and
use the one the minimizes the difference between the left-hand side
and the right-hand side.

To use it, first import `tactic.monotonicity`.

`ac_mono` can be used as follows:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  -- ⊢ (m + x + n) * z ≤ z * (y + n + m)
  ac_mono,
  -- ⊢ m + x + n ≤ y + n + m
  ac_mono,
end
```

As with `mono*`, `ac_mono*` solves the goal in one go and so does
`ac_mono* h₁`. The latter syntax becomes especially interesting in the
following example:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by ac_mono* h₁.
```

By giving `ac_mono` the assumption `h₁`, we are asking `ac_refl` to
stop earlier than it would normally would.

### use
Similar to `existsi`. `use x` will instantiate the first term of an `∃` or `Σ` goal with `x`.
Unlike `existsi`, `x` is elaborated with respect to the expected type.
Equivalent to `refine ⟨x, _⟩`.

`use` will alternatively take a list of terms `[x0, ..., xn]`.

Examples:

```lean
example (α : Type) : ∃ S : set α, S = S :=
by use ∅

example : ∃ x : ℤ, x = x :=
by use 42

example : ∃ a b c : ℤ, a + b + c = 6 :=
by use [1, 2, 3]

example : ∃ p : ℤ × ℤ, p.1 = 1 :=
by use ⟨1, 42⟩
```

### clear_aux_decl

`clear_aux_decl` clears every `aux_decl` in the local context for the current goal.
This includes the induction hypothesis when using the equation compiler and
`_let_match` and `_fun_match`.

It is useful when using a tactic such as `finish`, `simp *` or `subst` that may use these
auxiliary declarations, and produce an error saying the recursion is not well founded.

```lean
example (n m : ℕ) (h₁ : n = m) (h₂ : ∃ a : ℕ, a = n ∧ a = m) : 2 * m = 2 * n :=
let ⟨a, ha⟩ := h₂ in
begin
  clear_aux_decl, -- subst will fail without this line
  subst h₁
end

example (x y : ℕ) (h₁ : ∃ n : ℕ, n * 1 = 2) (h₂ : 1 + 1 = 2 → x * 1 = y) : x = y :=
let ⟨n, hn⟩ := h₁ in
begin
  clear_aux_decl, -- finish produces an error without this line
  finish
end
```
### set

`set a := t with h` is a variant of `let a := t`. It adds the hypothesis `h : a = t` to the local context and replaces `t` with `a` everywhere it can.

`set a := t with ←h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.

```lean
example (x : ℕ) (h : x = 3)  : x + x + x = 9 :=
begin
  set y := x with ←h_xy,
/-
x : ℕ,
y : ℕ := x,
h_xy : x = y,
h : y = 3
⊢ y + y + y = 9
-/
end
```

### omega

`omega` attempts to discharge goals in the quantifier-free fragment of linear integer and natural number arithmetic using the Omega test. In other words, the core procedure of `omega` works with goals of the form
```lean
∀ x₁, ... ∀ xₖ, P
```
where `x₁, ... xₖ` are integer (resp. natural number) variables, and `P` is a quantifier-free formula of linear integer (resp. natural number) arithmetic. For instance:
```lean
example : ∀ (x y : int), (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by omega
```
By default, `omega` tries to guess the correct domain by looking at the goal and hypotheses, and then reverts all relevant hypotheses and variables (e.g., all variables of type `nat` and `Prop`s in linear natural number arithmetic, if the domain was determined to be `nat`) to universally close the goal before calling the main procedure. Therefore, `omega` will often work even if the goal is not in the above form:
```lean
example (x y : nat) (h : 2 * x + 1 = 2 * y) : false := by omega
```
But this behaviour is not always optimal, since it may revert irrelevant hypotheses or incorrectly guess the domain. Use `omega manual` to disable automatic reverts, and `omega int` or `omega nat` to specify the domain.
```lean
example (x y z w : int) (h1 : 3 * y ≥ x) (h2 : z > 19 * w) : 3 * x ≤ 9 * y :=
by {revert h1 x y, omega manual}

example (i : int) (n : nat) (h1 : i = 0) (h2 : n < n) : false := by omega nat

example (n : nat) (h1 : n < 34) (i : int) (h2 : i * 9 = -72) : i = -8 :=
by {revert h2 i, omega manual int}
```
`omega` handles `nat` subtraction by repeatedly rewriting goals of the form `P[t-s]` into `P[x] ∧ (t = s + x ∨ (t ≤ s ∧ x = 0))`, where `x` is fresh. This means that each (distinct) occurrence of subtraction will cause the goal size to double during DNF transformation.

`omega` implements the real shadow step of the Omega test, but not the dark and gray shadows. Therefore, it should (in principle) succeed whenever the negation of the goal has no real solution, but it may fail if a real solution exists, even if there is no integer/natural number solution.

### push_neg

This tactic pushes negations inside expressions. For instance, given an assumption
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(the pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every assumption and the goal using `push_neg at *` or at selected assumptions and the goal
using say `push_neg at h h' ⊢` as usual.

### contrapose

Transforms the goal into its contrapositive.

`contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`

`contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
                 using `push_neg`

`contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`

`contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`

`contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

### norm_cast

This tactic normalizes casts inside expressions.
It is basically a simp tactic with a specific set of lemmas to move casts
upwards in the expression.
Therefore it can be used more safely as a non-terminating tactic.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```

writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

You can also use `exact_mod_cast`, `apply_mod_cast`, `rw_mod_cast`
or `assumption_mod_cast`.
Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize the goal and h before using `exact h` or `apply h`.
Writing `assumption_mod_cast` will normalize the goal and for every
expression `h` in the context it will try to normalize `h` and use
`exact h`.
`rw_mod_cast` acts like the `rw` tactic but it applies `norm_cast` between steps.

These tactics work with three attributes,
`elim_cast`, `move_cast` and `squash_cast`.

`elim_cast` is for elimination lemmas of the shape
`Π ..., P ↑a1 ... ↑an = P a1 ... an`, for instance:

```lean
int.coe_nat_inj' : ∀ {m n : ℕ}, ↑m = ↑n ↔ m = n

rat.coe_int_denom : ∀ (n : ℤ), ↑n.denom = 1
```

`move_cast` is for compositional lemmas of the shape
`Π ..., ↑(P a1 ... an) = P ↑a1 ... ↑an`, for instance:
```lean
int.coe_nat_add : ∀ (m n : ℕ), ↑(m + n) = ↑m + ↑n`

nat.cast_sub : ∀ {α : Type*} [add_group α] [has_one α] {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
```

`squash_cast` is for lemmas of the shape
`Π ..., ↑↑a = ↑a`, for instance:
```lean
int.cast_coe_nat : ∀ (n : ℕ), ↑↑n = ↑n

int.cats_id : int.cast_id : ∀ (n : ℤ), ↑n = n
```

### vampire

`vampire` uses proof output from the Vampire theorem prover (https://vprover.github.io/) to discharge FOL goals. The tactic can either work in online mode which calls Vampire to obtain a proof, or in offline mode which uses the user-supplied proof. When invoked without a string argument, `vampire` defaults to the former to discharge the goal and displays the proof it used:
```
variables [inhabited α] (p q : α → Prop) (a : α)
example : (∀ x, p x → q x) → (∀ x, p x) → q a := by vampire
/-
  Trace output :
  n10hen0n10ymsn0hen10n0mn1n0msen10n0msn1hen10n1mn0n1msen10n0m
  n1n0msren1n0mn0n0msen0n10ymsr
-/
```
(Note the `inhabited` instance, which is required per the assumption of non-empty domain for FOL.)
The online mode of `vampire` requires a local installation of Vampire (consult the readme in `tactic/vampire` for details). To invoke `vampire` in offline mode, copy and paste the trace output as a string argument:
```
variables [inhabited α] (p q : α → Prop) (a : α)
example : (∀ x, p x → q x) → (∀ x, p x) → q a :=
by vampire
"
n10hen0n10ymsn0hen10n0mn1n0msen10n0msn1hen10n1mn0n1msen10n0m
n1n0msren1n0mn0n0msen0n10ymsr
"
```
`vampire` only proves valid formulas of FOL, which means that all the necessary hypotheses should be included in the goal as antecedents.
```
example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
by vampire -- fails
```
You can include the names of relevant hypotheses in order to revert them and call `vampire` in one step.
```
example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
by vampire h1 h2
```
Use the `all` keyword to revert all hypotheses of type `Prop`. Hypothesis reversion can be used in offline mode as well.
```
example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
by vampire all "n10hn1tn1hrn0hr"
```
### convert_to

`convert_to g using n` attempts to change the current goal to `g`, but unlike `change`,
it will generate equality proof obligations using `congr' n` to resolve discrepancies.
`convert_to g` defaults to using `congr' 1`.

`ac_change` is `convert_to` followed by `ac_refl`. It is useful for rearranging/reassociating
e.g. sums:
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N :=
begin
  ac_change a + d + e + f + c + g + b ≤ _,
-- ⊢ a + d + e + f + c + g + b ≤ N
end
```

### apply_fun

Apply a function to some local assumptions which are either equalities
or inequalities. For instance, if the context contains `h : a = b` and
some function `f` then `apply_fun f at h` turns `h` into
`h : f a = f b`. When the assumption is an inequality `h : a ≤ b`, a side
goal `monotone f` is created, unless this condition is provided using
`apply_fun f at h using P` where `P : monotone f`, or the `mono` tactic
can prove it.

Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end
```

### Localized Notation

This consists of two user-commands which allow you to declare notation and commands localized to a namespace.

* Declare notation which is localized to a namespace using:
```
localized "infix ` ⊹ `:60 := my_add" in my.add
```
* After this command it will be available in the same section/namespace/file, just as if you wrote `local infix ` ⊹ `:60 := my_add`
* You can open it in other places. The following command will declare the notation again as local notation in that section/namespace/files:
```
open_locale my.add
```
* More generally, the following will declare all localized notation in the specified namespaces.
```
open_locale namespace1 namespace2 ...
```
* You can also declare other localized commands, like local attributes
```
localized "attribute [simp] le_refl" in le
```
* Warning 1: as a limitation on user commands, you cannot put `open_locale` directly after your imports. You have to write another command first (e.g. `open`, `namespace`, `universe variables`, `noncomputable theory`, `run_cmd tactic.skip`, ...).
* Warning 2: You have to fully specify the names used in localized notation, so that the localized notation also works when the appropriate namespaces are not opened.

### swap

`swap n` will move the `n`th goal to the front. `swap` defaults to `swap 2`, and so interchanges the first and second goals.

### rotate

`rotate` moves the first goal to the back. `rotate n` will do this `n` times.

### The `reassoc` attribute

The `reassoc` attribute can be applied to a lemma

```lean
@[reassoc]
lemma some_lemma : foo ≫ bar = baz := ...
```

and produce

```lean
lemma some_lemma_assoc {Y : C} (f : X ⟶ Y) : foo ≫ bar ≫ f = baz ≫ f := ...
```

The name of the produced lemma can be specified with `@[reassoc other_lemma_name]`. If
`simp` is added first, the generated lemma will also have the `simp` attribute.

### The `reassoc_axiom` command

When declaring a class of categories, the axioms can be reformulated to be more amenable
to manipulation in right associated expressions:

```lean
class some_class (C : Type) [category C] :=
(foo : Π X : C, X ⟶ X)
(bar : ∀ {X Y : C} (f : X ⟶ Y), foo X ≫ f = f ≫ foo Y)

reassoc_axiom some_class.bar
```

The above will produce:

```lean
lemma some_class.bar_assoc {Z : C} (g : Y ⟶ Z) :
  foo X ≫ f ≫ g = f ≫ foo Y ≫ g := ...
```

Here too, the `reassoc` attribute can be used instead. It works well when combined with
`simp`:

```lean
attribute [simp, reassoc] some_class.bar
```

### The reassoc_of function

`reassoc_of h` takes local assumption `h` and add a ` ≫ f` term on the right of both sides of the equality.
Instead of creating a new assumption from the result, `reassoc_of h` stands for the proof of that reassociated
statement. This prevents poluting the local context with complicated assumptions used only once or twice.

In the following, assumption `h` is needed in a reassociated form. Instead of proving it as a new goal and adding it as
an assumption, we use `reassoc_of h` as a rewrite rule which works just as well.

```lean
example (X Y Z W : C) (x : X ⟶ Y) (y : Y ⟶ Z) (z z' : Z ⟶ W) (w : X ⟶ Z)
  (h : x ≫ y = w)
  (h' : y ≫ z = y ≫ z') :
  x ≫ y ≫ z = w ≫ z' :=
begin
  -- reassoc_of h : ∀ {X' : C} (f : W ⟶ X'), x ≫ y ≫ f = w ≫ f
  rw [h',reassoc_of h],
end
```

Although `reassoc_of` is not a tactic or a meta program, its type is generated
through meta-programming to make it usable inside normal expressions.

### lint
User commands to spot common mistakes in the code

* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

The following linters are run by default:
1. `unused_arguments` checks for unused arguments in declarations.
2. `def_lemma` checks whether a declaration is incorrectly marked as a def/lemma.
3. `dup_namespce` checks whether a namespace is duplicated in the name of a declaration.
4. `illegal_constant` checks whether ≥/> is used in the declaration.
5. `instance_priority` checks that instances that always apply have priority below default.
6. `doc_blame` checks for missing doc strings on definitions and constants.

Another linter, `doc_blame_thm`, checks for missing doc strings on lemmas and theorems.
This is not run by default.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output of passing checks.
A silent lint will fail if any test fails.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint]` to a declaration omits it from all linter checks.

### lift

Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℕ, h : P ↑n ⊢ ↑n = 3` and `n : ℤ, h : P n ⊢ n ≥ 0`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `can_lift α β`. In this case the proof obligation is specified by `can_lift.cond`.

### import_private

`import_private foo from bar` finds a private declaration `foo` in the same file as `bar` and creates a
local notation to refer to it.

`import_private foo`, looks for `foo` in all (imported) files.

When possible, make `foo` non-private rather than using this feature.

### default_dec_tac'

`default_dec_tac'` is a replacement for the core tactic `default_dec_tac`, fixing a bug. This
bug is often indicated by a message `nested exception message: tactic failed, there are no goals to be solved`,and solved by appending `using_well_founded wf_tacs` to the recursive definition.
See also additional documentation of `using_well_founded` in
[docs/extras/well_founded_recursion.md](extras/well_founded_recursion.md).

### simps

* The `@[simps]` attribute automatically derives lemmas specifying the projections of the declaration.
* Example: (note that the forward and reverse functions are specified differently!)
  ```lean
  @[simps] def refl (α) : α ≃ α := ⟨id, λ x, x, λ x, rfl, λ x, rfl⟩
  ```
  derives two simp-lemmas:
  ```lean
  @[simp] lemma refl_to_fun (α) (x : α) : (refl α).to_fun x = id x
  @[simp] lemma refl_inv_fun (α) (x : α) : (refl α).inv_fun x = x
  ```
* It does not derive simp-lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but not unfold any definitions.
* If one of the fields itself is a structure, this command will recursively create
  simp-lemmas for all fields in that structure.
* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections. For example:
  ```lean
  attribute [simps to_fun] refl
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.
* You can use `@[simps lemmas_only]` to derive the lemmas, but not mark them
  as simp-lemmas.
* You can use `@[simps short_name]` to only use the name of the last projection for the name of the
  generated lemmas.
* The precise syntax is `('simps' 'lemmas_only'? 'short_name'? ident*)`.
* If one of the projections is marked as a coercion, the generated lemmas do *not* use this
  coercion.
* `@[simps]` reduces let-expressions where necessary.
* If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens).
