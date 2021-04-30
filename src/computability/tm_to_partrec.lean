/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import computability.halting
import computability.turing_machine
import data.num.lemmas
import tactic.derive_fintype

/-!
# Modelling partial recursive functions using Turing machines

This file defines a simplified basis for partial recursive functions, and a `turing.TM2` model
Turing machine for evaluating these functions. This amounts to a constructive proof that every
`partrec` function can be evaluated by a Turing machine.

## Main definitions

* `to_partrec.code`: a simplified basis for partial recursive functions, valued in
  `list ℕ →. list ℕ`.
  * `to_partrec.code.eval`: semantics for a `to_partrec.code` program
* `partrec_to_TM2.tr`: A TM2 turing machine which can evaluate `code` programs
-/

open function (update)
open relation

namespace turing

/-!
## A simplified basis for partrec

This section constructs the type `code`, which is a data type of programs with `list ℕ` input and
output, with enough expressivity to write any partial recursive function. The primitives are:

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `nat.cases_on`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)

This basis is convenient because it is closer to the Turing machine model - the key operations are
splitting and merging of lists of unknown length, while the messy `n`-ary composition operation
from the traditional basis for partial recursive functions is absent - but it retains a
compositional semantics. The first step in transitioning to Turing machines is to make a sequential
evaluator for this basis, which we take up in the next section.
-/

namespace to_partrec

/-- The type of codes for primitive recursive functions. Unlike `nat.partrec.code`, this uses a set
of operations on `list ℕ`. See `code.eval` for a description of the behavior of the primitives. -/
@[derive [decidable_eq, inhabited]]
inductive code
| zero'
| succ
| tail
| cons : code → code → code
| comp : code → code → code
| case : code → code → code
| fix : code → code

/-- The semantics of the `code` primitives, as partial functions `list ℕ →. list ℕ`. By convention
we functions that return a single result return a singleton `[n]`, or in some cases `n :: v` where
`v` will be ignored by a subsequent function.

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `nat.cases_on`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)
-/
@[simp] def code.eval : code → list ℕ →. list ℕ
| code.zero' := λ v, pure (0 :: v)
| code.succ := λ v, pure [v.head.succ]
| code.tail := λ v, pure v.tail
| (code.cons f fs) := λ v, do n ← code.eval f v, ns ← code.eval fs v, pure (n.head :: ns)
| (code.comp f g) := λ v, g.eval v >>= f.eval
| (code.case f g) := λ v, v.head.elim (f.eval v.tail) (λ y _, g.eval (y :: v.tail))
| (code.fix f) := pfun.fix $ λ v, (f.eval v).map $ λ v,
  if v.head = 0 then sum.inl v.tail else sum.inr v.tail

namespace code

/-- `nil` is the constant nil function: `nil v = []`. -/
def nil : code := tail.comp succ
@[simp] theorem nil_eval (v) : nil.eval v = pure [] := by simp [nil]

/-- `id` is the identity function: `id v = v`. -/
def id : code := tail.comp zero'
@[simp] theorem id_eval (v) : id.eval v = pure v := by simp [id]

/-- `head` gets the head of the input list: `head [] = [0]`, `head (n :: v) = [n]`. -/
def head : code := cons id nil
@[simp] theorem head_eval (v) : head.eval v = pure [v.head] := by simp [head]

/-- `zero` is the constant zero function: `zero v = [0]`. -/
def zero : code := cons zero' nil
@[simp] theorem zero_eval (v) : zero.eval v = pure [0] := by simp [zero]

/-- `pred` returns the predecessor of the head of the input:
`pred [] = [0]`, `pred (0 :: v) = [0]`, `pred (n+1 :: v) = [n]`. -/
def pred : code := case zero head

@[simp] theorem pred_eval (v) : pred.eval v = pure [v.head.pred] :=
by simp [pred]; cases v.head; simp

/-- `rfind f` performs the function of the `rfind` primitive of partial recursive functions.
`rfind f v` returns the smallest `n` such that `(f (n :: v)).head = 0`.

It is implemented as:

    rfind f v = pred (fix (λ (n::v), f (n::v) :: n+1 :: v) (0 :: v))

The idea is that the initial state is `0 :: v`, and the `fix` keeps `n :: v` as its internal state;
it calls `f (n :: v)` as the exit test and `n+1 :: v` as the next state. At the end we get
`n+1 :: v` where `n` is the desired output, and `pred (n+1 :: v) = [n]` returns the result.
 -/
def rfind (f : code) : code := comp pred $ comp (fix $ cons f $ cons succ tail) zero'

/-- `prec f g` implements the `prec` (primitive recursion) operation of partial recursive
functions. `prec f g` evaluates as:

* `prec f g [] = [f []]`
* `prec f g (0 :: v) = [f v]`
* `prec f g (n+1 :: v) = [g (n :: prec f g (n :: v) :: v)]`

It is implemented as:

    G (a :: b :: IH :: v) = (b :: a+1 :: b-1 :: g (a :: IH :: v) :: v)
    F (0 :: f_v :: v) = (f_v :: v)
    F (n+1 :: f_v :: v) = (fix G (0 :: n :: f_v :: v)).tail.tail
    prec f g (a :: v) = [(F (a :: f v :: v)).head]

Because `fix` always evaluates its body at least once, we must special case the `0` case to avoid
calling `g` more times than necessary (which could be bad if `g` diverges). If the input is
`0 :: v`, then `F (0 :: f v :: v) = (f v :: v)` so we return `[f v]`. If the input is `n+1 :: v`,
we evaluate the function from the bottom up, with initial state `0 :: n :: f v :: v`. The first
number counts up, providing arguments for the applications to `g`, while the second number counts
down, providing the exit condition (this is the initial `b` in the return value of `G`, which is
stripped by `fix`). After the `fix` is complete, the final state is `n :: 0 :: res :: v` where
`res` is the desired result, and the rest reduces this to `[res]`. -/
def prec (f g : code) : code :=
let G := cons tail $ cons succ $ cons (comp pred tail) $
  cons (comp g $ cons id $ comp tail tail) $ comp tail $ comp tail tail in
let F := case id $ comp (comp (comp tail tail) (fix G)) zero' in
cons (comp F (cons head $ cons (comp f tail) tail)) nil

local attribute [-simp] roption.bind_eq_bind roption.map_eq_map roption.pure_eq_some

theorem exists_code.comp {m n} {f : vector ℕ n →. ℕ} {g : fin n → vector ℕ m →. ℕ}
  (hf : ∃ c : code, ∀ v : vector ℕ n, c.eval v.1 = pure <$> f v)
  (hg : ∀ i, ∃ c : code, ∀ v : vector ℕ m, c.eval v.1 = pure <$> g i v) :
  ∃ c : code, ∀ v : vector ℕ m, c.eval v.1 = pure <$> (vector.m_of_fn (λ i, g i v) >>= f) :=
begin
  suffices : ∃ c : code, ∀ v : vector ℕ m,
    c.eval v.1 = subtype.val <$> vector.m_of_fn (λ i, g i v),
  { obtain ⟨cf, hf⟩ := hf, obtain ⟨cg, hg⟩ := this,
    exact ⟨cf.comp cg, λ v,
      by { simp [hg, hf, map_bind, seq_bind_eq, (∘), -subtype.val_eq_coe], refl }⟩ },
  clear hf f, induction n with n IH,
  { exact ⟨nil, λ v, by simp [vector.m_of_fn]; refl⟩ },
  { obtain ⟨cg, hg₁⟩ := hg 0, obtain ⟨cl, hl⟩ := IH (λ i, hg i.succ),
    exact ⟨cons cg cl, λ v, by { simp [vector.m_of_fn, hg₁, map_bind,
      seq_bind_eq, bind_assoc, (∘), hl, -subtype.val_eq_coe], refl }⟩ },
end

theorem exists_code {n} {f : vector ℕ n →. ℕ} (hf : nat.partrec' f) :
  ∃ c : code, ∀ v : vector ℕ n, c.eval v.1 = pure <$> f v :=
begin
  induction hf with n f hf,
  induction hf,
  case prim zero { exact ⟨zero', λ ⟨[], _⟩, rfl⟩ },
  case prim succ { exact ⟨succ, λ ⟨[v], _⟩, rfl⟩ },
  case prim nth : n i {
    refine fin.succ_rec (λ n, _) (λ n i IH, _) i,
    { exact ⟨head, λ ⟨list.cons a as, _⟩, by simp; refl⟩ },
    { obtain ⟨c, h⟩ := IH,
      exact ⟨c.comp tail, λ v, by simpa [← vector.nth_tail] using h v.tail⟩ } },
  case prim comp : m n f g hf hg IHf IHg {
    simpa [roption.bind_eq_bind] using exists_code.comp IHf IHg },
  case prim prec : n f g hf hg IHf IHg {
    obtain ⟨cf, hf⟩ := IHf, obtain ⟨cg, hg⟩ := IHg,
    simp only [roption.map_eq_map, roption.map_some, pfun.coe_val] at hf hg,
    refine ⟨prec cf cg, λ v, _⟩, rw ← v.cons_head_tail,
    specialize hf v.tail, replace hg := λ a b, hg (a ::ᵥ b ::ᵥ v.tail),
    simp only [vector.cons_val, vector.tail_val] at hf hg,
    simp only [roption.map_eq_map, roption.map_some, vector.cons_val,
      vector.cons_tail, vector.cons_head, pfun.coe_val, vector.tail_val],
    simp only [← roption.pure_eq_some] at hf hg ⊢,
    induction v.head with n IH; simp [prec, hf, bind_assoc, ← roption.map_eq_map,
      ← bind_pure_comp_eq_map, show ∀ x, pure x = [x], from λ _, rfl, -subtype.val_eq_coe],
    suffices : ∀ a b, a + b = n →
      (n.succ :: 0 :: g
        (n ::ᵥ (nat.elim (f v.tail) (λ y IH, g (y ::ᵥ IH ::ᵥ v.tail)) n) ::ᵥ v.tail)
        :: v.val.tail : list ℕ) ∈
      pfun.fix (λ v : list ℕ, do
        x ← cg.eval (v.head :: v.tail.tail),
        pure $ if v.tail.head = 0
          then sum.inl (v.head.succ :: v.tail.head.pred :: x.head :: v.tail.tail.tail : list ℕ)
          else sum.inr (v.head.succ :: v.tail.head.pred :: x.head :: v.tail.tail.tail))
        (a :: b :: nat.elim (f v.tail)
          (λ y IH, g (y ::ᵥ IH ::ᵥ v.tail)) a :: v.val.tail),
    { rw (_ : pfun.fix _ _ = pure _), swap, exact roption.eq_some_iff.2 (this 0 n (zero_add n)),
      simp only [list.head, pure_bind, list.tail_cons] },
    intros a b e, induction b with b IH generalizing a e,
    { refine pfun.mem_fix_iff.2 (or.inl $ roption.eq_some_iff.1 _),
      simp only [hg, ← e, pure_bind, list.tail_cons], refl },
    { refine pfun.mem_fix_iff.2 (or.inr ⟨_, _, IH (a+1) (by rwa add_right_comm)⟩),
      simp only [hg, eval, pure_bind, nat.elim_succ, list.tail],
      exact roption.mem_some_iff.2 rfl } },
  case comp : m n f g hf hg IHf IHg { exact exists_code.comp IHf IHg },
  case rfind : n f hf IHf {
    obtain ⟨cf, hf⟩ := IHf, refine ⟨rfind cf, λ v, _⟩,
    replace hf := λ a, hf (a ::ᵥ v),
    simp only [roption.map_eq_map, roption.map_some, vector.cons_val, pfun.coe_val,
      show ∀ x, pure x = [x], from λ _, rfl] at hf ⊢,
    refine roption.ext (λ x, _),
    simp only [rfind, roption.bind_eq_bind, roption.pure_eq_some, roption.map_eq_map,
      roption.bind_some, exists_prop, eval, list.head, pred_eval, roption.map_some,
      bool.ff_eq_to_bool_iff, roption.mem_bind_iff, list.length,
      roption.mem_map_iff, nat.mem_rfind, list.tail, bool.tt_eq_to_bool_iff,
      roption.mem_some_iff, roption.map_bind],
    split,
    { rintro ⟨v', h1, rfl⟩,
      suffices : ∀ (v₁ : list ℕ), v' ∈ pfun.fix
        (λ v, (cf.eval v).bind $ λ y, roption.some $ if y.head = 0 then
          sum.inl (v.head.succ :: v.tail) else sum.inr (v.head.succ :: v.tail)) v₁ →
        ∀ n, v₁ = n :: v.val → (∀ m < n, ¬f (m ::ᵥ v) = 0) →
        (∃ (a : ℕ), (f (a ::ᵥ v) = 0 ∧ ∀ {m : ℕ}, m < a → ¬f (m ::ᵥ v) = 0) ∧
          [a] = [v'.head.pred]),
      { exact this _ h1 0 rfl (by rintro _ ⟨⟩) },
      clear h1, intros v₀ h1,
      refine pfun.fix_induction h1 (λ v₁ h2 IH, _), clear h1,
      rintro n rfl hm,
      have := pfun.mem_fix_iff.1 h2,
      simp only [hf, roption.bind_some] at this,
      split_ifs at this,
      { simp only [list.head, exists_false, or_false, roption.mem_some_iff,
          list.tail_cons, false_and] at this,
        subst this, exact ⟨_, ⟨h, hm⟩, rfl⟩ },
      { simp only [list.head, exists_eq_left, roption.mem_some_iff,
          list.tail_cons, false_or] at this,
        refine IH _ this (by simp [hf, h, -subtype.val_eq_coe]) _ rfl (λ m h', _),
        obtain h|rfl := nat.lt_succ_iff_lt_or_eq.1 h', exacts [hm _ h, h] } },
    { rintro ⟨n, ⟨hn, hm⟩, rfl⟩, refine ⟨n.succ :: v.1, _, rfl⟩,
      have : (n.succ :: v.1 : list ℕ) ∈ pfun.fix
        (λ v, (cf.eval v).bind $ λ y, roption.some $ if y.head = 0 then
          sum.inl (v.head.succ :: v.tail) else sum.inr (v.head.succ :: v.tail)) (n :: v.val) :=
        pfun.mem_fix_iff.2 (or.inl (by simp [hf, hn, -subtype.val_eq_coe])),
      generalize_hyp : (n.succ :: v.1 : list ℕ) = w at this ⊢, clear hn,
      induction n with n IH, {exact this},
      refine IH (λ m h', hm (nat.lt_succ_of_lt h')) (pfun.mem_fix_iff.2 (or.inr ⟨_, _, this⟩)),
      simp only [hf, hm n.lt_succ_self, roption.bind_some, list.head, eq_self_iff_true,
        if_false, roption.mem_some_iff, and_self, list.tail_cons] } }
end

end code

/-!
## From compositional semantics to sequential semantics

Our initial sequential model is designed to be as similar as possible to the compositional
semantics in terms of its primitives, but it is a sequential semantics, meaning that rather than
defining an `eval c : list ℕ →. list ℕ` function for each program, defined by recursion on
programs, we have a type `cfg` with a step function `step : cfg → option cfg` that provides a
deterministic evaluation order. In order to do this, we introduce the notion of a *continuation*,
which can be viewed as a `code` with a hole in it where evaluation is currently taking place.
Continuations can be assigned a `list ℕ →. list ℕ` semantics as well, with the interpretation
being that given a `list ℕ` result returned from the code in the hole, the remainder of the
program will evaluate to a `list ℕ` final value.

The continuations are:

* `halt`: the empty continuation: the hole is the whole program, whatever is returned is the
  final result. In our notation this is just `_`.
* `cons₁ fs v k`: evaluating the first part of a `cons`, that is `k (_ :: fs v)`, where `k` is the
  outer continuation.
* `cons₂ ns k`: evaluating the second part of a `cons`: `k (ns.head :: _)`. (Technically we don't
  need to hold on to all of `ns` here since we are already committed to taking the head, but this
  is more regular.)
* `comp f k`: evaluating the first part of a composition: `k (f _)`.
* `fix f k`: waiting for the result of `f` in a `fix f` expression:
  `k (if _.head = 0 then _.tail else fix f (_.tail))`

The type `cfg` of evaluation states is:

* `ret k v`: we have received a result, and are now evaluating the continuation `k` with result
  `v`; that is, `k v` where `k` is ready to evaluate.
* `halt v`: we are done and the result is `v`.

The main theorem of this section is that for each code `c`, the state `step_normal c halt v` steps
to `v'` in finitely many steps if and only if `code.eval c v = some v'`.
-/

/-- The type of continuations, built up during evaluation of a `code` expression. -/
@[derive inhabited]
inductive cont
| halt
| cons₁ : code → list ℕ → cont → cont
| cons₂ : list ℕ → cont → cont
| comp : code → cont → cont
| fix : code → cont → cont

/-- The semantics of a continuation. -/
def cont.eval : cont → list ℕ →. list ℕ
| cont.halt := pure
| (cont.cons₁ fs as k) := λ v, do ns ← code.eval fs as, cont.eval k (v.head :: ns)
| (cont.cons₂ ns k) := λ v, cont.eval k (ns.head :: v)
| (cont.comp f k) := λ v, code.eval f v >>= cont.eval k
| (cont.fix f k) := λ v, if v.head = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval

/-- The set of configurations of the machine:

* `halt v`: The machine is about to stop and `v : list ℕ` is the result.
* `ret k v`: The machine is about to pass `v : list ℕ` to continuation `k : cont`.

We don't have a state corresponding to normal evaluation because these are evaluated immediately
to a `ret` "in zero steps" using the `step_normal` function. -/
@[derive inhabited]
inductive cfg
| halt : list ℕ → cfg
| ret : cont → list ℕ → cfg

/-- Evaluating `c : code` in a continuation `k : cont` and input `v : list ℕ`. This goes by
recursion on `c`, building an augmented continuation and a value to pass to it.

* `zero' v = 0 :: v` evaluates immediately, so we return it to the parent continuation
* `succ v = [v.head.succ]` evaluates immediately, so we return it to the parent continuation
* `tail v = v.tail` evaluates immediately, so we return it to the parent continuation
* `cons f fs v = (f v).head :: fs v` requires two sub-evaluations, so we evaluate
  `f v` in the continuation `k (_.head :: fs v)` (called `cont.cons₁ fs v k`)
* `comp f g v = f (g v)` requires two sub-evaluations, so we evaluate
  `g v` in the continuation `k (f _)` (called `cont.comp f k`)
* `case f g v = v.head.cases_on (f v.tail) (λ n, g (n :: v.tail))` has the information needed to
  evaluate the case statement, so we do that and transition to either `f v` or `g (n :: v.tail)`.
* `fix f v = let v' := f v in if v'.head = 0 then k v'.tail else fix f v'.tail`
  needs to first evaluate `f v`, so we do that and leave the rest for the continuation (called
  `cont.fix f k`)
-/
def step_normal : code → cont → list ℕ → cfg
| code.zero' k v := cfg.ret k (0 :: v)
| code.succ k v := cfg.ret k [v.head.succ]
| code.tail k v := cfg.ret k v.tail
| (code.cons f fs) k v := step_normal f (cont.cons₁ fs v k) v
| (code.comp f g) k v := step_normal g (cont.comp f k) v
| (code.case f g) k v :=
  v.head.elim (step_normal f k v.tail) (λ y _, step_normal g k (y :: v.tail))
| (code.fix f) k v := step_normal f (cont.fix f k) v

/-- Evaluating a continuation `k : cont` on input `v : list ℕ`. This is the second part of
evaluation, when we receive results from continuations built by `step_normal`.

* `cont.halt v = v`, so we are done and transition to the `cfg.halt v` state
* `cont.cons₁ fs as k v = k (v.head :: fs as)`, so we evaluate `fs as` now with the continuation
  `k (v.head :: _)` (called `cons₂ v k`).
* `cont.cons₂ ns k v = k (ns.head :: v)`, where we now have everything we need to evaluate
  `ns.head :: v`, so we return it to `k`.
* `cont.comp f k v = k (f v)`, so we call `f v` with `k` as the continuation.
* `cont.fix f k v = k (if v.head = 0 then k v.tail else fix f v.tail)`, where `v` is a value,
  so we evaluate the if statement and either call `k` with `v.tail`, or call `fix f v` with `k` as
  the continuation (which immediately calls `f` with `cont.fix f k` as the continuation).
-/
def step_ret : cont → list ℕ → cfg
| cont.halt v := cfg.halt v
| (cont.cons₁ fs as k) v := step_normal fs (cont.cons₂ v k) as
| (cont.cons₂ ns k) v := step_ret k (ns.head :: v)
| (cont.comp f k) v := step_normal f k v
| (cont.fix f k) v := if v.head = 0 then step_ret k v.tail else
  step_normal f (cont.fix f k) v.tail

/-- If we are not done (in `cfg.halt` state), then we must be still stuck on a continuation, so
this main loop calls `step_ret` with the new continuation. The overall `step` function transitions
from one `cfg` to another, only halting at the `cfg.halt` state. -/
def step : cfg → option cfg
| (cfg.halt _) := none
| (cfg.ret k v) := some (step_ret k v)

/-- In order to extract a compositional semantics from the sequential execution behavior of
configurations, we observe that continuations have a monoid structure, with `cont.halt` as the unit
and `cont.then` as the multiplication. `cont.then k₁ k₂` runs `k₁` until it halts, and then takes
the result of `k₁` and passes it to `k₂`.

We will not prove it is associative (although it is), but we are instead interested in the
associativity law `k₂ (eval c k₁) = eval c (k₁.then k₂)`. This holds at both the sequential and
compositional levels, and allows us to express running a machine without the ambient continuation
and relate it to the original machine's evaluation steps. In the literature this is usually
where one uses Turing machines embedded inside other Turing machines, but this approach allows us
to avoid changing the ambient type `cfg` in the middle of the recursion.
-/
def cont.then : cont → cont → cont
| cont.halt k' := k'
| (cont.cons₁ fs as k) k' := cont.cons₁ fs as (k.then k')
| (cont.cons₂ ns k) k' := cont.cons₂ ns (k.then k')
| (cont.comp f k) k' := cont.comp f (k.then k')
| (cont.fix f k) k' := cont.fix f (k.then k')

theorem cont.then_eval {k k' : cont} {v} : (k.then k').eval v = k.eval v >>= k'.eval :=
begin
  induction k generalizing v; simp only [cont.eval, cont.then, bind_assoc, pure_bind, *],
  { simp only [← k_ih] },
  { split_ifs; [refl, simp only [← k_ih, bind_assoc]] }
end

/-- The `then k` function is a "configuration homomorphism". Its operation on states is to append
`k` to the continuation of a `cfg.ret` state, and to run `k` on `v` if we are in the `cfg.halt v`
state. -/
def cfg.then : cfg → cont → cfg
| (cfg.halt v) k' := step_ret k' v
| (cfg.ret k v) k' := cfg.ret (k.then k') v

/-- The `step_normal` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
theorem step_normal_then (c) (k k' : cont) (v) :
  step_normal c (k.then k') v = (step_normal c k v).then k' :=
begin
  induction c with generalizing k v;
    simp only [cont.then, step_normal, cfg.then, *] {constructor_eq := ff},
  case turing.to_partrec.code.cons : c c' ih ih'
  { rw [← ih, cont.then] },
  case turing.to_partrec.code.comp : c c' ih ih'
  { rw [← ih', cont.then] },
  { cases v.head; simp only [nat.elim] },
  case turing.to_partrec.code.fix : c ih
  { rw [← ih, cont.then] },
end

/-- The `step_ret` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
theorem step_ret_then {k k' : cont} {v} :
  step_ret (k.then k') v = (step_ret k v).then k' :=
begin
  induction k generalizing v;
    simp only [cont.then, step_ret, cfg.then, *],
  { rw ← step_normal_then, refl },
  { rw ← step_normal_then },
  { split_ifs, {rw ← k_ih}, {rw ← step_normal_then, refl} },
end

/-- This is a temporary definition, because we will prove in `code_is_ok` that it always holds.
It asserts that `c` is semantically correct; that is, for any `k` and `v`,
`eval (step_normal c k v) = eval (cfg.ret k (code.eval c v))`, as an equality of partial values
(so one diverges iff the other does).

In particular, we can let `k = cont.halt`, and then this asserts that `step_normal c cont.halt v`
evaluates to `cfg.halt (code.eval c v)`. -/
def code.ok (c : code) :=
∀ k v, eval step (step_normal c k v) = code.eval c v >>= λ v, eval step (cfg.ret k v)

theorem code.ok.zero {c} (h : code.ok c) {v} :
  eval step (step_normal c cont.halt v) = cfg.halt <$> code.eval c v :=
begin
  rw [h, ← bind_pure_comp_eq_map], congr, funext v,
  exact roption.eq_some_iff.2 (mem_eval.2 ⟨refl_trans_gen.single rfl, rfl⟩),
end

theorem step_normal.is_ret (c k v) : ∃ k' v', step_normal c k v = cfg.ret k' v' :=
begin
  induction c generalizing k v,
  iterate 3 { exact ⟨_, _, rfl⟩ },
  case cons : f fs IHf IHfs { apply IHf },
  case comp : f g IHf IHg { apply IHg },
  case case : f g IHf IHg {
    rw step_normal, cases v.head; simp only [nat.elim]; [apply IHf, apply IHg] },
  case fix : f IHf { apply IHf },
end

theorem cont_eval_fix {f k v} (fok : code.ok f) :
  eval step (step_normal f (cont.fix f k) v) = f.fix.eval v >>= λ v, eval step (cfg.ret k v) :=
begin
  refine roption.ext (λ x, _),
  simp only [roption.bind_eq_bind, roption.mem_bind_iff],
  split,
  { suffices :
      ∀ c, x ∈ eval step c →
      ∀ v c', c = cfg.then c' (cont.fix f k) → reaches step (step_normal f cont.halt v) c' →
      ∃ v₁ ∈ f.eval v,
      ∃ v₂ ∈ (if list.head v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail),
      x ∈ eval step (cfg.ret k v₂),
    { intro h,
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (step_normal_then _ cont.halt _ _) refl_trans_gen.refl,
      refine ⟨v₂, pfun.mem_fix_iff.2 _, h₃⟩,
      simp only [roption.eq_some_iff.2 hv₁, roption.map_some],
      split_ifs at hv₂ ⊢,
      { rw roption.mem_some_iff.1 hv₂, exact or.inl (roption.mem_some _) },
      { exact or.inr ⟨_, roption.mem_some _, hv₂⟩ } },
    refine λ c he, eval_induction he (λ y h IH, _),
    rintro v (⟨v'⟩ | ⟨k',v'⟩) rfl hr; rw cfg.then at h IH,
    { have := mem_eval.2 ⟨hr, rfl⟩,
      rw [fok, roption.bind_eq_bind, roption.mem_bind_iff] at this,
      obtain ⟨v'', h₁, h₂⟩ := this,
      rw reaches_eval at h₂, swap, exact refl_trans_gen.single rfl,
      cases roption.mem_unique h₂ (mem_eval.2 ⟨refl_trans_gen.refl, rfl⟩),
      refine ⟨v', h₁, _⟩, rw [step_ret] at h,
      revert h, by_cases he : v'.head = 0; simp only [exists_prop, if_pos, if_false, he]; intro h,
      { refine ⟨_, roption.mem_some _, _⟩,
        rw reaches_eval, exact h, exact refl_trans_gen.single rfl },
      { obtain ⟨k₀, v₀, e₀⟩ := step_normal.is_ret f cont.halt v'.tail,
        have e₁ := step_normal_then f cont.halt (cont.fix f k) v'.tail,
        rw [e₀, cont.then, cfg.then] at e₁,
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (step_ret (k₀.then (cont.fix f k)) v₀) _ _ v'.tail _ step_ret_then _,
        { refine ⟨_, pfun.mem_fix_iff.2 _, h₃⟩,
          simp only [roption.eq_some_iff.2 hv₁, roption.map_some, roption.mem_some_iff],
          split_ifs at hv₂ ⊢; [exact or.inl (roption.mem_some_iff.1 hv₂),
            exact or.inr ⟨_, rfl, hv₂⟩] },
        { rwa [← @reaches_eval _ _ (cfg.ret (k₀.then (cont.fix f k)) v₀), ← e₁],
          exact refl_trans_gen.single rfl },
        { rw [step_ret, if_neg he, e₁], refl },
        { apply refl_trans_gen.single, rw e₀, exact rfl } } },
    { rw reaches_eval at h, swap, exact refl_trans_gen.single rfl,
      exact IH _ h rfl _ _ step_ret_then (refl_trans_gen.tail hr rfl) } },
  { rintro ⟨v', he, hr⟩,
    rw reaches_eval at hr, swap, exact refl_trans_gen.single rfl,
    refine pfun.fix_induction he (λ v (he : v' ∈ f.fix.eval v) IH, _),
    rw [fok, roption.bind_eq_bind, roption.mem_bind_iff],
    obtain he | ⟨v'', he₁', he₂'⟩ := pfun.mem_fix_iff.1 he,
    { obtain ⟨v', he₁, he₂⟩ := (roption.mem_map_iff _).1 he, split_ifs at he₂; cases he₂,
      refine ⟨_, he₁, _⟩,
      rw reaches_eval, swap, exact refl_trans_gen.single rfl,
      rwa [step_ret, if_pos h] },
    { obtain ⟨v₁, he₁, he₂⟩ := (roption.mem_map_iff _).1 he₁', split_ifs at he₂; cases he₂,
      clear he₂ he₁', change _ ∈ f.fix.eval _ at he₂',
      refine ⟨_, he₁, _⟩,
      rw reaches_eval, swap, exact refl_trans_gen.single rfl,
      rwa [step_ret, if_neg h],
      exact IH v₁.tail he₂' ((roption.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩) } }
end

theorem code_is_ok (c) : code.ok c :=
begin
  induction c; intros k v; rw step_normal,
  iterate 3 { simp only [code.eval, pure_bind] },
  case cons : f fs IHf IHfs {
    rw [code.eval, IHf],
    simp only [bind_assoc, cont.eval, pure_bind], congr, funext v,
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [step_ret, IHfs], congr, funext v',
    refine eq.trans _ (eq.symm _);
    try {exact reaches_eval (refl_trans_gen.single rfl)} },
  case comp : f g IHf IHg {
    rw [code.eval, IHg],
    simp only [bind_assoc, cont.eval, pure_bind], congr, funext v,
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [step_ret, IHf] },
  case case : f g IHf IHg {
    simp only [code.eval], cases v.head; simp only [nat.elim, code.eval];
    [apply IHf, apply IHg] },
  case fix : f IHf { rw cont_eval_fix IHf },
end

theorem step_normal_eval (c v) : eval step (step_normal c cont.halt v) = cfg.halt <$> c.eval v :=
(code_is_ok c).zero

theorem step_ret_eval {k v} : eval step (step_ret k v) = cfg.halt <$> k.eval v :=
begin
  induction k generalizing v,
  case halt : {
    simp only [mem_eval, cont.eval, map_pure],
    exact roption.eq_some_iff.2 (mem_eval.2 ⟨refl_trans_gen.refl, rfl⟩) },
  case cons₁ : fs as k IH {
    rw [cont.eval, step_ret, code_is_ok],
    simp only [← bind_pure_comp_eq_map, bind_assoc], congr, funext v',
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [step_ret, IH, bind_pure_comp_eq_map] },
  case cons₂ : ns k IH { rw [cont.eval, step_ret], exact IH },
  case comp : f k IH {
    rw [cont.eval, step_ret, code_is_ok],
    simp only [← bind_pure_comp_eq_map, bind_assoc], congr, funext v',
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [IH, bind_pure_comp_eq_map] },
  case fix : f k IH {
    rw [cont.eval, step_ret], simp only [bind_pure_comp_eq_map],
    split_ifs, { exact IH },
    simp only [← bind_pure_comp_eq_map, bind_assoc, cont_eval_fix (code_is_ok _)],
    congr, funext, rw [bind_pure_comp_eq_map, ← IH],
    exact reaches_eval (refl_trans_gen.single rfl) },
end

end to_partrec

/-!
## Simulating sequentialized partial recursive functions in TM2

At this point we have a sequential model of partial recursive functions: the `cfg` type and
`step : cfg → option cfg` function from the previous section. The key feature of this model is that
it does a finite amount of computation (in fact, an amount which is statically bounded by the size
of the program) between each step, and no individual step can diverge (unlike the compositional
semantics, where every sub-part of the computation is potentially divergent). So we can utilize the
same techniques as in the other TM simulations in `computability.turing_machine` to prove that
each step corresponds to a finite number of steps in a lower level model. (We don't prove it here,
but in anticipation of the complexity class P, the simulation is actually polynomial-time as well.)

The target model is `turing.TM2`, which has a fixed finite set of stacks, a bit of local storage,
with programs selected from a potentially infinite (but finitely accessible) set of program
positions, or labels `Λ`, each of which executes a finite sequence of basic stack commands.

For this program we will need four stacks, each on an alphabet `Γ'` like so:

    inductive Γ'  | Cons | cons | bit0 | bit1

We represent a number as a bit sequence, lists of numbers by putting `cons` after each element, and
lists of lists of natural numbers by putting `Cons` after each list. For example:

    0 ~> []
    1 ~> [bit1]
    6 ~> [bit0, bit1, bit1]
    [1, 2] ~> [bit1, cons, bit0, bit1, cons]
    [[], [1, 2]] ~> [Cons, bit1, cons, bit0, bit1, cons, Cons]

The four stacks are `main`, `rev`, `aux`, `stack`. In normal mode, `main` contains the input to the
current program (a `list ℕ`) and `stack` contains data (a `list (list ℕ)`) associated to the
current continuation, and in `ret` mode `main` contains the value that is being passed to the
continuation and `stack` contains the data for the continuation. The `rev` and `aux` stacks are
usually empty; `rev` is used to store reversed data when e.g. moving a value from one stack to
another, while `aux` is used as a temporary for a `main`/`stack` swap that happens during `cons₁`
evaluation.

The only local store we need is `option Γ'`, which stores the result of the last pop
operation. (Most of our working data are natural numbers, which are too large to fit in the local
store.)

The continuations from the previous section are data-carrying, containing all the values that have
been computed and are awaiting other arguments. In order to have only a finite number of
continuations appear in the program so that they can be used in machine states, we separate the
data part (anything with type `list ℕ`) from the `cont` type, producing a `cont'` type that lacks
this information. The data is kept on the `stack` stack.

Because we want to have subroutines for e.g. moving an entire stack to another place, we use an
infinite inductive type `Λ'` so that we can execute a program and then return to do something else
without having to define too many different kinds of intermediate states. (We must nevertheless
prove that only finitely many labels are accessible.) The labels are:

* `move p k₁ k₂ q`: move elements from stack `k₁` to `k₂` while `p` holds of the value being moved.
  The last element, that fails `p`, is placed in neither stack but left in the local store.
  At the end of the operation, `k₂` will have the elements of `k₁` in reverse order. Then do `q`.
* `clear p k q`: delete elements from stack `k` until `p` is true. Like `move`, the last element is
  left in the local storage. Then do `q`.
* `copy q`: Move all elements from `rev` to both `main` and `stack` (in reverse order),
  then do `q`. That is, it takes `(a, b, c, d)` to `(b.reverse ++ a, [], c, b.reverse ++ d)`.
* `push k f q`: push `f s`, where `s` is the local store, to stack `k`, then do `q`. This is a
  duplicate of the `push` instruction that is part of the TM2 model, but by having a subroutine
  just for this purpose we can build up programs to execute inside a `goto` statement, where we
  have the flexibility to be general recursive.
* `read (f : option Γ' → Λ')`: go to state `f s` where `s` is the local store. Again this is only
  here for convenience.
* `succ q`: perform a successor operation. Assuming `[n]` is encoded on `main` before,
  `[n+1]` will be on main after. This implements successor for binary natural numbers.
* `pred q₁ q₂`: perform a predecessor operation or `case` statement. If `[]` is encoded on
  `main` before, then we transition to `q₁` with `[]` on main; if `(0 :: v)` is on `main` before
  then `v` will be on `main` after and we transition to `q₁`; and if `(n+1 :: v)` is on `main`
  before then `n :: v` will be on `main` after and we transition to `q₂`.
* `ret k`: call continuation `k`. Each continuation has its own interpretation of the data in
  `stack` and sets up the data for the next continuation.
  * `ret (cons₁ fs k)`: `v :: k_data` on `stack` and `ns` on `main`, and the next step expects
    `v` on `main` and `ns :: k_data` on `stack`. So we have to do a little dance here with six
    reverse-moves using the `aux` stack to perform a three-point swap, each of which involves two
    reversals.
  * `ret (cons₂ k)`: `ns :: k_data` is on `stack` and `v` is on `main`, and we have to put
    `ns.head :: v` on `main` and `k_data` on `stack`. This is done using the `head` subroutine.
  * `ret (fix f k)`: This stores no data, so we just check if `main` starts with `0` and
    if so, remove it and call `k`, otherwise `clear` the first value and call `f`.
  * `ret halt`: the stack is empty, and `main` has the output. Do nothing and halt.

In addition to these basic states, we define some additional subroutines that are used in the
above:
* `push'`, `peek'`, `pop'` are special versions of the builtins that use the local store to supply
  inputs and outputs.
* `unrev`: special case `move ff rev main` to move everything from `rev` back to `main`. Used as a
  cleanup operation in several functions.
* `move_excl p k₁ k₂ q`: same as `move` but pushes the last value read back onto the source stack.
* `move₂ p k₁ k₂ q`: double `move`, so that the result comes out in the right order at the target
  stack. Implemented as `move_excl p k rev; move ff rev k₂`. Assumes that neither `k₁` nor `k₂` is
  `rev` and `rev` is initially empty.
* `head k q`: get the first natural number from stack `k` and reverse-move it to `rev`, then clear
  the rest of the list at `k` and then `unrev` to reverse-move the head value to `main`. This is
  used with `k = main` to implement regular `head`, i.e. if `v` is on `main` before then `[v.head]`
  will be on `main` after; and also with `k = stack` for the `cons` operation, which has `v` on
  `main` and `ns :: k_data` on `stack`, and results in `k_data` on `stack` and `ns.head :: v` on
  `main`.
* `tr_normal` is the main entry point, defining states that perform a given `code` computation.
  It mostly just dispatches to functions written above.

The main theorem of this section is `tr_eval`, which asserts that for each that for each code `c`,
the state `init c v` steps to `halt v'` in finitely many steps if and only if
`code.eval c v = some v'`.
-/

namespace partrec_to_TM2

section
open to_partrec

/-- The alphabet for the stacks in the program. `bit0` and `bit1` are used to represent `ℕ` values
as lists of binary digits, `cons` is used to separate `list ℕ` values, and `Cons` is used to
separate `list (list ℕ)` values. See the section documentation. -/
@[derive [decidable_eq, inhabited, fintype]]
inductive Γ' | Cons | cons | bit0 | bit1

/-- The four stacks used by the program. `main` is used to store the input value in `tr_normal`
mode and the output value in `Λ'.ret` mode, while `stack` is used to keep all the data for the
continuations. `rev` is used to store reversed lists when transferring values between stacks, and
`aux` is only used once in `cons₁`. See the section documentation. -/
@[derive [decidable_eq, inhabited]]
inductive K' | main | rev | aux | stack
open K'

/-- Continuations as in `to_partrec.cont` but with the data removed. This is done because we want
the set of all continuations in the program to be finite (so that it can ultimately be encoded into
the finite state machine of a Turing machine), but a continuation can handle a potentially infinite
number of data values during execution. -/
@[derive [decidable_eq, inhabited]]
inductive cont'
| halt
| cons₁ : code → cont' → cont'
| cons₂ : cont' → cont'
| comp : code → cont' → cont'
| fix : code → cont' → cont'

/-- The set of program positions. We make extensive use of inductive types here to let us describe
"subroutines"; for example `clear p k q` is a program that clears stack `k`, then does `q` where
`q` is another label. In order to prevent this from resulting in an infinite number of distinct
accessible states, we are careful to be non-recursive (although loops are okay). See the section
documentation for a description of all the programs. -/
inductive Λ'
| move (p : Γ' → bool) (k₁ k₂ : K') (q : Λ')
| clear (p : Γ' → bool) (k : K') (q : Λ')
| copy (q : Λ')
| push (k : K') (s : option Γ' → option Γ') (q : Λ')
| read (f : option Γ' → Λ')
| succ (q : Λ')
| pred (q₁ q₂ : Λ')
| ret (k : cont')

instance : inhabited Λ' := ⟨Λ'.ret cont'.halt⟩

instance : decidable_eq Λ' :=
λ a b, begin
  induction a generalizing b; cases b; try { apply decidable.is_false, rintro ⟨⟨⟩⟩, done },
  all_goals { exactI decidable_of_iff' _ (by simp [function.funext_iff]) },
end

/-- The type of TM2 statements used by this machine. -/
@[derive inhabited]
def stmt' := TM2.stmt (λ _:K', Γ') Λ' (option Γ')
/-- The type of TM2 configurations used by this machine. -/
@[derive inhabited]
def cfg' := TM2.cfg (λ _:K', Γ') Λ' (option Γ')

open TM2.stmt

/-- A predicate that detects the end of a natural number, either `Γ'.cons` or `Γ'.Cons` (or
implicitly the end of the list), for use in predicate-taking functions like `move` and `clear`. -/
def nat_end : Γ' → bool
| Γ'.Cons := tt
| Γ'.cons := tt
| _ := ff

/-- Pop a value from the stack and place the result in local store. -/
@[simp] def pop' (k : K') : stmt' → stmt' := pop k (λ x v, v)
/-- Peek a value from the stack and place the result in local store. -/
@[simp] def peek' (k : K') : stmt' → stmt' := peek k (λ x v, v)
/-- Push the value in the local store to the given stack. -/
@[simp] def push' (k : K') : stmt' → stmt' := push k (λ x, x.iget)

/-- Move everything from the `rev` stack to the `main` stack (reversed). -/
def unrev := Λ'.move (λ _, ff) rev main

/-- Move elements from `k₁` to `k₂` while `p` holds, with the last element being left on `k₁`. -/
def move_excl (p k₁ k₂ q) :=
Λ'.move p k₁ k₂ $ Λ'.push k₁ id q

/-- Move elements from `k₁` to `k₂` without reversion, by performing a double move via the `rev`
stack. -/
def move₂ (p k₁ k₂ q) := move_excl p k₁ rev $ Λ'.move (λ _, ff) rev k₂ q

/-- Assuming `tr_list v` is on the front of stack `k`, remove it, and push `v.head` onto `main`.
See the section documentation. -/
def head (k : K') (q : Λ') : Λ' :=
Λ'.move nat_end k rev $
Λ'.push rev (λ _, some Γ'.cons) $
Λ'.read $ λ s,
(if s = some Γ'.Cons then id else Λ'.clear (λ x, x = Γ'.Cons) k) $
unrev q

/-- The program that evaluates code `c` with continuation `k`. This expects an initial state where
`tr_list v` is on `main`, `tr_cont_stack k` is on `stack`, and `aux` and `rev` are empty.
See the section documentation for details. -/
@[simp] def tr_normal : code → cont' → Λ'
| code.zero' k := Λ'.push main (λ _, some Γ'.cons) $ Λ'.ret k
| code.succ k := head main $ Λ'.succ $ Λ'.ret k
| code.tail k := Λ'.clear nat_end main $ Λ'.ret k
| (code.cons f fs) k :=
  Λ'.push stack (λ _, some Γ'.Cons) $
  Λ'.move (λ _, ff) main rev $ Λ'.copy $
  tr_normal f (cont'.cons₁ fs k)
| (code.comp f g) k := tr_normal g (cont'.comp f k)
| (code.case f g) k := Λ'.pred (tr_normal f k) (tr_normal g k)
| (code.fix f) k := tr_normal f (cont'.fix f k)

/-- The main program. See the section documentation for details. -/
@[simp] def tr : Λ' → stmt'
| (Λ'.move p k₁ k₂ q) :=
  pop' k₁ $ branch (λ s, s.elim tt p)
  ( goto $ λ _, q )
  ( push' k₂ $ goto $ λ _, Λ'.move p k₁ k₂ q )
| (Λ'.push k f q) :=
  branch (λ s, (f s).is_some)
  ( push k (λ s, (f s).iget) $ goto $ λ _, q )
  ( goto $ λ _, q )
| (Λ'.read q) := goto q
| (Λ'.clear p k q) :=
  pop' k $ branch (λ s, s.elim tt p)
  ( goto $ λ _, q )
  ( goto $ λ _, Λ'.clear p k q )
| (Λ'.copy q) :=
  pop' rev $ branch option.is_some
  ( push' main $ push' stack $ goto $ λ _, Λ'.copy q )
  ( goto $ λ _, q )
| (Λ'.succ q) :=
  pop' main $ branch (λ s, s = some Γ'.bit1)
  ( push rev (λ _, Γ'.bit0) $
    goto $ λ _, Λ'.succ q ) $
  branch (λ s, s = some Γ'.cons)
  ( push main (λ _, Γ'.cons) $
    push main (λ _, Γ'.bit1) $
    goto $ λ _, unrev q )
  ( push main (λ _, Γ'.bit1) $
    goto $ λ _, unrev q )
| (Λ'.pred q₁ q₂) :=
  pop' main $ branch (λ s, s = some Γ'.bit0)
  ( push rev (λ _, Γ'.bit1) $
    goto $ λ _, Λ'.pred q₁ q₂ ) $
  branch (λ s, nat_end s.iget)
  ( goto $ λ _, q₁ )
  ( peek' main $ branch (λ s, nat_end s.iget)
    ( goto $ λ _, unrev q₂ )
    ( push rev (λ _, Γ'.bit0) $
      goto $ λ _, unrev q₂ ) )
| (Λ'.ret (cont'.cons₁ fs k)) := goto $ λ _,
  move₂ (λ _, ff) main aux $
  move₂ (λ s, s = Γ'.Cons) stack main $
  move₂ (λ _, ff) aux stack $
  tr_normal fs (cont'.cons₂ k)
| (Λ'.ret (cont'.cons₂ k)) := goto $ λ _, head stack $ Λ'.ret k
| (Λ'.ret (cont'.comp f k)) := goto $ λ _, tr_normal f k
| (Λ'.ret (cont'.fix f k)) :=
  pop' main $ goto $ λ s,
  cond (nat_end s.iget) (Λ'.ret k) $
  Λ'.clear nat_end main $ tr_normal f (cont'.fix f k)
| (Λ'.ret cont'.halt) := load (λ _, none) $ halt

/-- Translating a `cont` continuation to a `cont'` continuation simply entails dropping all the
data. This data is instead encoded in `tr_cont_stack` in the configuration. -/
def tr_cont : cont → cont'
| cont.halt := cont'.halt
| (cont.cons₁ c _ k) := cont'.cons₁ c (tr_cont k)
| (cont.cons₂ _ k) := cont'.cons₂ (tr_cont k)
| (cont.comp c k) := cont'.comp c (tr_cont k)
| (cont.fix c k) := cont'.fix c (tr_cont k)

/-- We use `pos_num` to define the translation of binary natural numbers. A natural number is
represented as a little-endian list of `bit0` and `bit1` elements:

    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]

In particular, this representation guarantees no trailing `bit0`'s at the end of the list. -/
def tr_pos_num : pos_num → list Γ'
| pos_num.one := [Γ'.bit1]
| (pos_num.bit0 n) := Γ'.bit0 :: tr_pos_num n
| (pos_num.bit1 n) := Γ'.bit1 :: tr_pos_num n

/-- We use `num` to define the translation of binary natural numbers. Positive numbers are
translated using `tr_pos_num`, and `tr_num 0 = []`. So there are never any trailing `bit0`'s in
a translated `num`.

    0 = []
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
-/
def tr_num : num → list Γ'
| num.zero := []
| (num.pos n) := tr_pos_num n

/-- Because we use binary encoding, we define `tr_nat` in terms of `tr_num`, using `num`, which are
binary natural numbers. (We could also use `nat.binary_rec_on`, but `num` and `pos_num` make for
easy inductions.) -/
def tr_nat (n : ℕ) : list Γ' := tr_num n

@[simp] theorem tr_nat_zero : tr_nat 0 = [] := rfl

/-- Lists are translated with a `cons` after each encoded number.
For example:

    [] = []
    [0] = [cons]
    [1] = [bit1, cons]
    [6, 0] = [bit0, bit1, bit1, cons, cons]
-/
@[simp] def tr_list : list ℕ → list Γ'
| [] := []
| (n :: ns) := tr_nat n ++ Γ'.cons :: tr_list ns

/-- Lists of lists are translated with a `Cons` after each encoded list.
For example:

    [] = []
    [[]] = [Cons]
    [[], []] = [Cons, Cons]
    [[0]] = [cons, Cons]
    [[1, 2], [0]] = [bit1, cons, bit0, bit1, cons, Cons, cons, Cons]
-/
@[simp] def tr_llist : list (list ℕ) → list Γ'
| [] := []
| (l :: ls) := tr_list l ++ Γ'.Cons :: tr_llist ls

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `tr_llist`. -/
@[simp] def cont_stack : cont → list (list ℕ)
| cont.halt := []
| (cont.cons₁ _ ns k) := ns :: cont_stack k
| (cont.cons₂ ns k) := ns :: cont_stack k
| (cont.comp _ k) := cont_stack k
| (cont.fix _ k) := cont_stack k

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `tr_llist`. -/
def tr_cont_stack (k : cont) := tr_llist (cont_stack k)

/-- This is the nondependent eliminator for `K'`, but we use it specifically here in order to
represent the stack data as four lists rather than as a function `K' → list Γ'`, because this makes
rewrites easier. The theorems `K'.elim_update_main` et. al. show how such a function is updated
after an `update` to one of the components. -/
@[simp] def K'.elim (a b c d : list Γ') : K' → list Γ'
| K'.main := a
| K'.rev := b
| K'.aux := c
| K'.stack := d

@[simp] theorem K'.elim_update_main {a b c d a'} :
  update (K'.elim a b c d) main a' = K'.elim a' b c d := by funext x; cases x; refl
@[simp] theorem K'.elim_update_rev {a b c d b'} :
  update (K'.elim a b c d) rev b' = K'.elim a b' c d := by funext x; cases x; refl
@[simp] theorem K'.elim_update_aux {a b c d c'} :
  update (K'.elim a b c d) aux c' = K'.elim a b c' d := by funext x; cases x; refl
@[simp] theorem K'.elim_update_stack {a b c d d'} :
  update (K'.elim a b c d) stack d' = K'.elim a b c d' := by funext x; cases x; refl

/-- The halting state corresponding to a `list ℕ` output value. -/
def halt (v : list ℕ) : cfg' := ⟨none, none, K'.elim (tr_list v) [] [] []⟩

/-- The `cfg` states map to `cfg'` states almost one to one, except that in normal operation the
local store contains an arbitrary garbage value. To make the final theorem cleaner we explicitly
clear it in the halt state so that there is exactly one configuration corresponding to output `v`.
-/
def tr_cfg : cfg → cfg' → Prop
| (cfg.ret k v) c' := ∃ s, c' =
  ⟨some (Λ'.ret (tr_cont k)), s, K'.elim (tr_list v) [] [] (tr_cont_stack k)⟩
| (cfg.halt v) c' := c' = halt v

/-- This could be a general list definition, but it is also somewhat specialized to this
application. `split_at_pred p L` will search `L` for the first element satisfying `p`.
If it is found, say `L = l₁ ++ a :: l₂` where `a` satisfies `p` but `l₁` does not, then it returns
`(l₁, some a, l₂)`. Otherwise, if there is no such element, it returns `(L, none, [])`. -/
def split_at_pred {α} (p : α → bool) : list α → list α × option α × list α
| [] := ([], none, [])
| (a :: as) := cond (p a) ([], some a, as) $
  let ⟨l₁, o, l₂⟩ := split_at_pred as in ⟨a :: l₁, o, l₂⟩

theorem split_at_pred_eq {α} (p : α → bool) : ∀ L l₁ o l₂,
  (∀ x ∈ l₁, p x = ff) →
  option.elim o (L = l₁ ∧ l₂ = []) (λ a, p a = tt ∧ L = l₁ ++ a :: l₂) →
  split_at_pred p L = (l₁, o, l₂)
| [] _ none _ _ ⟨rfl, rfl⟩ := rfl
| [] l₁ (some o) l₂ h₁ ⟨h₂, h₃⟩ := by simp at h₃; contradiction
| (a :: L) l₁ o l₂ h₁ h₂ := begin
    rw [split_at_pred],
    have IH := split_at_pred_eq L,
    cases o,
    { cases l₁ with a' l₁; rcases h₂ with ⟨⟨⟩, rfl⟩,
      rw [h₁ a (or.inl rfl), cond, IH L none [] _ ⟨rfl, rfl⟩], refl,
      exact λ x h, h₁ x (or.inr h) },
    { cases l₁ with a' l₁; rcases h₂ with ⟨h₂, ⟨⟩⟩, {rw [h₂, cond]},
      rw [h₁ a (or.inl rfl), cond, IH l₁ (some o) l₂ _ ⟨h₂, _⟩]; try {refl},
      exact λ x h, h₁ x (or.inr h) },
  end

theorem split_at_pred_ff {α} (L : list α) : split_at_pred (λ _, ff) L = (L, none, []) :=
split_at_pred_eq _ _ _ _ _ (λ _ _, rfl) ⟨rfl, rfl⟩

theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → list Γ'}
  (h₁ : k₁ ≠ k₂) (e : split_at_pred p (S k₁) = (L₁, o, L₂)) :
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.move p k₁ k₂ q), s, S⟩
    ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverse_core (S k₂))⟩ :=
begin
  induction L₁ with a L₁ IH generalizing S s,
  { rw [(_ : [].reverse_core _ = _), function.update_eq_self],
    swap, { rw function.update_noteq h₁.symm, refl },
    refine trans_gen.head' rfl _,
    simp, cases S k₁ with a Sk, {cases e, refl},
    simp [split_at_pred] at e ⊢,
    cases p a; simp at e ⊢,
    { revert e, rcases split_at_pred p Sk with ⟨_, _, _⟩, rintro ⟨⟩ },
    { simp only [e] } },
  { refine trans_gen.head rfl _, simp,
    cases e₁ : S k₁ with a' Sk; rw [e₁, split_at_pred] at e, {cases e},
    cases e₂ : p a'; simp only [e₂, cond] at e, swap, {cases e},
    rcases e₃ : split_at_pred p Sk with ⟨_, _, _⟩, rw [e₃, split_at_pred] at e, cases e,
    simp [e₂],
    convert @IH (update (update S k₁ Sk) k₂ (a :: S k₂)) _ _ using 2;
      simp [function.update_noteq, h₁, h₁.symm, e₃, list.reverse_core],
    simp [function.update_comm h₁.symm] }
end

theorem unrev_ok {q s} {S : K' → list Γ'} :
  reaches₁ (TM2.step tr) ⟨some (unrev q), s, S⟩
    ⟨some q, none, update (update S rev []) main (list.reverse_core (S rev) (S main))⟩ :=
move_ok dec_trivial $ split_at_pred_ff _

theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → list Γ'}
  (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂) (h₂ : S rev = [])
  (e : split_at_pred p (S k₁) = (L₁, o, L₂)) :
  reaches₁ (TM2.step tr)
    ⟨some (move₂ p k₁ k₂ q), s, S⟩
    ⟨some q, none, update (update S k₁ (o.elim id list.cons L₂)) k₂ (L₁ ++ S k₂)⟩ :=
begin
  refine (move_ok h₁.1 e).trans (trans_gen.head rfl _),
  cases o; simp only [option.elim, tr, id.def],
  { convert move_ok h₁.2.1.symm (split_at_pred_ff _) using 2,
    simp only [function.update_comm h₁.1, function.update_idem],
    rw show update S rev [] = S, by rw [← h₂, function.update_eq_self],
    simp only [function.update_noteq h₁.2.2.symm, function.update_noteq h₁.2.1,
      function.update_noteq h₁.1.symm, list.reverse_core_eq, h₂,
      function.update_same, list.append_nil, list.reverse_reverse] },
  { convert move_ok h₁.2.1.symm (split_at_pred_ff _) using 2,
    simp only [h₂, function.update_comm h₁.1,
      list.reverse_core_eq, function.update_same, list.append_nil, function.update_idem],
    rw show update S rev [] = S, by rw [← h₂, function.update_eq_self],
    simp only [function.update_noteq h₁.1.symm,
      function.update_noteq h₁.2.2.symm, function.update_noteq h₁.2.1,
      function.update_same, list.reverse_reverse] },
end

theorem clear_ok {p k q s L₁ o L₂} {S : K' → list Γ'}
  (e : split_at_pred p (S k) = (L₁, o, L₂)) :
  reaches₁ (TM2.step tr) ⟨some (Λ'.clear p k q), s, S⟩ ⟨some q, o, update S k L₂⟩ :=
begin
  induction L₁ with a L₁ IH generalizing S s,
  { refine trans_gen.head' rfl _,
    simp, cases S k with a Sk, {cases e, refl},
    simp [split_at_pred] at e ⊢,
    cases p a; simp at e ⊢,
    { revert e, rcases split_at_pred p Sk with ⟨_, _, _⟩, rintro ⟨⟩ },
    { simp only [e] } },
  { refine trans_gen.head rfl _, simp,
    cases e₁ : S k with a' Sk; rw [e₁, split_at_pred] at e, {cases e},
    cases e₂ : p a'; simp only [e₂, cond] at e, swap, {cases e},
    rcases e₃ : split_at_pred p Sk with ⟨_, _, _⟩, rw [e₃, split_at_pred] at e, cases e,
    simp [e₂],
    convert @IH (update S k Sk) _ _ using 2; simp [e₃] }
end

theorem copy_ok (q s a b c d) :
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
    ⟨some q, none, K'.elim (list.reverse_core b a) [] c (list.reverse_core b d)⟩ :=
begin
  induction b with x b IH generalizing a d s,
  { refine trans_gen.single _, simp, refl },
  refine trans_gen.head rfl _, simp, exact IH _ _ _,
end

theorem tr_pos_num_nat_end : ∀ n (x ∈ tr_pos_num n), nat_end x = ff
| pos_num.one _ (or.inl rfl) := rfl
| (pos_num.bit0 n) _ (or.inl rfl) := rfl
| (pos_num.bit0 n) _ (or.inr h) := tr_pos_num_nat_end n _ h
| (pos_num.bit1 n) _ (or.inl rfl) := rfl
| (pos_num.bit1 n) _ (or.inr h) := tr_pos_num_nat_end n _ h

theorem tr_num_nat_end : ∀ n (x ∈ tr_num n), nat_end x = ff
| (num.pos n) x h := tr_pos_num_nat_end n x h

theorem tr_nat_nat_end (n) : ∀ x ∈ tr_nat n, nat_end x = ff := tr_num_nat_end _

theorem tr_list_ne_Cons : ∀ l (x ∈ tr_list l), x ≠ Γ'.Cons
| (a :: l) x h := begin
  simp [tr_list] at h,
  obtain h | rfl | h := h,
  { rintro rfl, cases tr_nat_nat_end _ _ h },
  { rintro ⟨⟩ },
  { exact tr_list_ne_Cons l _ h }
end

theorem head_main_ok {q s L} {c d : list Γ'} :
  reaches₁ (TM2.step tr)
    ⟨some (head main q), s, K'.elim (tr_list L) [] c d⟩
    ⟨some q, none, K'.elim (tr_list [L.head]) [] c d⟩ :=
begin
  let o : option Γ' := list.cases_on L none (λ _ _, some Γ'.cons),
  refine (move_ok dec_trivial
    (split_at_pred_eq _ _ (tr_nat L.head) o (tr_list L.tail) (tr_nat_nat_end _) _)).trans
    (trans_gen.head rfl (trans_gen.head rfl _)),
  { cases L; exact ⟨rfl, rfl⟩ },
  simp [show o ≠ some Γ'.Cons, by cases L; rintro ⟨⟩],
  refine (clear_ok (split_at_pred_eq _ _ _ none [] _ ⟨rfl, rfl⟩)).trans _,
  { exact λ x h, (to_bool_ff (tr_list_ne_Cons _ _ h)) },
  convert unrev_ok, simp [list.reverse_core_eq],
end

theorem head_stack_ok {q s L₁ L₂ L₃} :
  reaches₁ (TM2.step tr)
    ⟨some (head stack q), s, K'.elim (tr_list L₁) [] [] (tr_list L₂ ++ Γ'.Cons :: L₃)⟩
    ⟨some q, none, K'.elim (tr_list (L₂.head :: L₁)) [] [] L₃⟩ :=
begin
  cases L₂ with a L₂,
  { refine trans_gen.trans (move_ok dec_trivial
      (split_at_pred_eq _ _ [] (some Γ'.Cons) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
      (trans_gen.head rfl (trans_gen.head rfl _)),
    convert unrev_ok, simp, refl },
  { refine trans_gen.trans (move_ok dec_trivial
      (split_at_pred_eq _ _ (tr_nat a) (some Γ'.cons)
        (tr_list L₂ ++ Γ'.Cons :: L₃) (tr_nat_nat_end _) ⟨rfl, by simp⟩))
      (trans_gen.head rfl (trans_gen.head rfl _)),
    simp,
    refine trans_gen.trans (clear_ok
      (split_at_pred_eq _ _ (tr_list L₂) (some Γ'.Cons) L₃
        (λ x h, (to_bool_ff (tr_list_ne_Cons _ _ h))) ⟨rfl, by simp⟩)) _,
    convert unrev_ok, simp [list.reverse_core_eq] },
end

theorem succ_ok {q s n} {c d : list Γ'} :
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.succ q), s, K'.elim (tr_list [n]) [] c d⟩
    ⟨some q, none, K'.elim (tr_list [n.succ]) [] c d⟩ :=
begin
  simp [tr_nat, num.add_one],
  cases (n:num) with a,
  { refine trans_gen.head rfl _, simp,
    rw if_neg, swap, rintro ⟨⟩, rw if_pos, swap, refl,
    convert unrev_ok, simp, refl },
  simp [num.succ, tr_num, num.succ'],
  suffices : ∀ l₁,
    ∃ l₁' l₂' s', list.reverse_core l₁ (tr_pos_num a.succ) = list.reverse_core l₁' l₂' ∧
    reaches₁ (TM2.step tr)
      ⟨some q.succ, s, K'.elim (tr_pos_num a ++ [Γ'.cons]) l₁ c d⟩
      ⟨some (unrev q), s', K'.elim (l₂' ++ [Γ'.cons]) l₁' c d⟩,
  { obtain ⟨l₁', l₂', s', e, h⟩ := this [], simp [list.reverse_core] at e,
    refine h.trans _, convert unrev_ok using 2, simp [e, list.reverse_core_eq] },
  induction a with m IH m IH generalizing s; intro l₁,
  { refine ⟨Γ'.bit0 :: l₁, [Γ'.bit1], some Γ'.cons, rfl, trans_gen.head rfl (trans_gen.single _)⟩,
    simp [tr_pos_num] },
  { obtain ⟨l₁', l₂', s', e, h⟩ := IH (Γ'.bit0 :: l₁),
    refine ⟨l₁', l₂', s', e, trans_gen.head _ h⟩, swap,
    simp [pos_num.succ, tr_pos_num] },
  { refine ⟨l₁, _, some Γ'.bit0, rfl, trans_gen.single _⟩, simp, refl },
end

theorem pred_ok (q₁ q₂ s v) (c d : list Γ') :
  ∃ s', reaches₁ (TM2.step tr)
    ⟨some (Λ'.pred q₁ q₂), s, K'.elim (tr_list v) [] c d⟩
    (v.head.elim
      ⟨some q₁, s', K'.elim (tr_list v.tail) [] c d⟩
      (λ n _, ⟨some q₂, s', K'.elim (tr_list (n :: v.tail)) [] c d⟩)) :=
begin
  rcases v with _|⟨_|n, v⟩,
  { refine ⟨none, trans_gen.single _⟩, simp, refl },
  { refine ⟨some Γ'.cons, trans_gen.single _⟩, simp, refl },
  refine ⟨none, _⟩, simp [tr_nat, num.add_one, num.succ, tr_num],
  cases (n:num) with a,
  { simp [tr_pos_num, tr_num, show num.zero.succ' = pos_num.one, from rfl],
    refine trans_gen.head rfl _, convert unrev_ok, simp, refl },
  simp [tr_num, num.succ'],
  suffices : ∀ l₁,
    ∃ l₁' l₂' s', list.reverse_core l₁ (tr_pos_num a) = list.reverse_core l₁' l₂' ∧
    reaches₁ (TM2.step tr)
      ⟨some (q₁.pred q₂), s, K'.elim (tr_pos_num a.succ ++ Γ'.cons :: tr_list v) l₁ c d⟩
      ⟨some (unrev q₂), s', K'.elim (l₂' ++ Γ'.cons :: tr_list v) l₁' c d⟩,
  { obtain ⟨l₁', l₂', s', e, h⟩ := this [], simp [list.reverse_core] at e,
    refine h.trans _, convert unrev_ok using 2, simp [e, list.reverse_core_eq] },
  induction a with m IH m IH generalizing s; intro l₁,
  { refine ⟨Γ'.bit1 :: l₁, [], some Γ'.cons, rfl, trans_gen.head rfl (trans_gen.single _)⟩,
    simp [tr_pos_num, show pos_num.one.succ = pos_num.one.bit0, from rfl], refl },
  { obtain ⟨l₁', l₂', s', e, h⟩ := IH (some Γ'.bit0) (Γ'.bit1 :: l₁),
    refine ⟨l₁', l₂', s', e, trans_gen.head _ h⟩, simp, refl },
  { obtain ⟨a, l, e, h⟩ : ∃ a l, tr_pos_num m = a :: l ∧ nat_end a = ff,
    { cases m; refine ⟨_, _, rfl, rfl⟩ },
    refine ⟨Γ'.bit0 :: l₁, _, some a, rfl, trans_gen.single _⟩,
    simp [tr_pos_num, pos_num.succ, e, h, nat_end,
      show some Γ'.bit1 ≠ some Γ'.bit0, from dec_trivial] },
end

theorem tr_normal_respects (c k v s) : ∃ b₂, tr_cfg (step_normal c k v) b₂ ∧
  reaches₁ (TM2.step tr)
    ⟨some (tr_normal c (tr_cont k)), s, K'.elim (tr_list v) [] [] (tr_cont_stack k)⟩ b₂ :=
begin
  induction c generalizing k v s,
  case zero' : { refine ⟨_, ⟨s, rfl⟩, trans_gen.single _⟩, simp },
  case succ : { refine ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩ },
  case tail : {
    let o : option Γ' := list.cases_on v none (λ _ _, some Γ'.cons),
    refine ⟨_, ⟨o, rfl⟩, _⟩, convert clear_ok _, simp, swap,
    refine split_at_pred_eq _ _ (tr_nat v.head) _ _ (tr_nat_nat_end _) _,
    cases v; exact ⟨rfl, rfl⟩ },
  case cons : f fs IHf IHfs {
    obtain ⟨c, h₁, h₂⟩ := IHf (cont.cons₁ fs v k) v none,
    refine ⟨c, h₁, trans_gen.head rfl $ (move_ok dec_trivial (split_at_pred_ff _)).trans _⟩,
    simp [step_normal],
    refine (copy_ok _ none [] (tr_list v).reverse _ _).trans _,
    convert h₂ using 2,
    simp [list.reverse_core_eq, tr_cont_stack] },
  case comp : f g IHf IHg { exact IHg (cont.comp f k) v s },
  case case : f g IHf IHg {
    rw step_normal,
    obtain ⟨s', h⟩ := pred_ok _ _ s v _ _,
    cases v.head with n,
    { obtain ⟨c, h₁, h₂⟩ := IHf k _ s', exact ⟨_, h₁, h.trans h₂⟩ },
    { obtain ⟨c, h₁, h₂⟩ := IHg k _ s', exact ⟨_, h₁, h.trans h₂⟩ } },
  case fix : f IH { apply IH }
end

theorem tr_ret_respects (k v s) : ∃ b₂, tr_cfg (step_ret k v) b₂ ∧
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.ret (tr_cont k)), s, K'.elim (tr_list v) [] [] (tr_cont_stack k)⟩ b₂ :=
begin
  induction k generalizing v s,
  case halt { exact ⟨_, rfl, trans_gen.single rfl⟩ },
  case cons₁ : fs as k IH {
    obtain ⟨s', h₁, h₂⟩ := tr_normal_respects fs (cont.cons₂ v k) as none,
    refine ⟨s', h₁, trans_gen.head rfl _⟩, simp,
    refine (move₂_ok dec_trivial _ (split_at_pred_ff _)).trans _, {refl}, simp,
    refine (move₂_ok dec_trivial _ _).trans _, swap 4, {refl},
    swap 4, {exact (split_at_pred_eq _ _ _ (some Γ'.Cons) _
      (λ x h, to_bool_ff (tr_list_ne_Cons _ _ h)) ⟨rfl, rfl⟩)},
    refine (move₂_ok dec_trivial _ (split_at_pred_ff _)).trans _, {refl}, simp,
    exact h₂ },
  case cons₂ : ns k IH {
    obtain ⟨c, h₁, h₂⟩ := IH (ns.head :: v) none,
    exact ⟨c, h₁, trans_gen.head rfl $ head_stack_ok.trans h₂⟩ },
  case comp : f k IH {
    obtain ⟨s', h₁, h₂⟩ := tr_normal_respects f k v s,
    exact ⟨_, h₁, trans_gen.head rfl h₂⟩ },
  case fix : f k IH {
    rw [step_ret],
    have : if v.head = 0
      then nat_end (tr_list v).head'.iget = tt ∧ (tr_list v).tail = tr_list v.tail
      else nat_end (tr_list v).head'.iget = ff ∧
        (tr_list v).tail = (tr_nat v.head).tail ++ Γ'.cons :: tr_list v.tail,
    { cases v with n, {exact ⟨rfl, rfl⟩}, cases n, {exact ⟨rfl, rfl⟩},
      rw [tr_list, list.head, tr_nat, nat.cast_succ, num.add_one, num.succ, list.tail],
      cases (n:num).succ'; exact ⟨rfl, rfl⟩ },
    by_cases v.head = 0; simp [h] at this ⊢,
    { obtain ⟨c, h₁, h₂⟩ := IH v.tail (tr_list v).head',
      refine ⟨c, h₁, trans_gen.head rfl _⟩,
      simp [tr_cont, tr_cont_stack, this], exact h₂ },
    { obtain ⟨s', h₁, h₂⟩ := tr_normal_respects f (cont.fix f k) v.tail (some Γ'.cons),
      refine ⟨_, h₁, trans_gen.head rfl $ trans_gen.trans _ h₂⟩,
      swap 3, simp [tr_cont, this.1],
      convert clear_ok (split_at_pred_eq _ _ (tr_nat v.head).tail (some Γ'.cons) _ _ _) using 2,
      { simp },
      { exact λ x h, tr_nat_nat_end _ _ (list.tail_subset _ h) },
      { exact ⟨rfl, this.2⟩ } } },
end

theorem tr_respects : respects step (TM2.step tr) tr_cfg
| (cfg.ret k v) _ ⟨s, rfl⟩ := tr_ret_respects _ _ _
| (cfg.halt v)  _ rfl := rfl

/-- The initial state, evaluating function `c` on input `v`. -/
def init (c : code) (v : list ℕ) : cfg' :=
⟨some (tr_normal c cont'.halt), none, K'.elim (tr_list v) [] [] []⟩

theorem tr_init (c v) : ∃ b, tr_cfg (step_normal c cont.halt v) b ∧
  reaches₁ (TM2.step tr) (init c v) b := tr_normal_respects _ _ _ _

theorem tr_eval (c v) : eval (TM2.step tr) (init c v) = halt <$> code.eval c v :=
begin
  obtain ⟨i, h₁, h₂⟩ := tr_init c v,
  refine roption.ext (λ x, _),
  rw [reaches_eval h₂.to_refl], simp,
  refine ⟨λ h, _, _⟩,
  { obtain ⟨c, hc₁, hc₂⟩ := tr_eval_rev tr_respects h₁ h,
    simp [step_normal_eval] at hc₂,
    obtain ⟨v', hv, rfl⟩ := hc₂,
    exact ⟨_, hv, hc₁.symm⟩ },
  { rintro ⟨v', hv, rfl⟩,
    have := tr_eval tr_respects h₁,
    simp [step_normal_eval] at this,
    obtain ⟨_, ⟨⟩, h⟩ := this _ hv rfl,
    exact h }
end

/-- The set of machine states reachable via downward label jumps, discounting jumps via `ret`. -/
def tr_stmts₁ : Λ' → finset Λ'
| Q@(Λ'.move p k₁ k₂ q) := insert Q $ tr_stmts₁ q
| Q@(Λ'.push k f q)     := insert Q $ tr_stmts₁ q
| Q@(Λ'.read q)         := insert Q $ finset.univ.bUnion $ λ s, tr_stmts₁ (q s)
| Q@(Λ'.clear p k q)    := insert Q $ tr_stmts₁ q
| Q@(Λ'.copy q)         := insert Q $ tr_stmts₁ q
| Q@(Λ'.succ q)         := insert Q $ insert (unrev q) $ tr_stmts₁ q
| Q@(Λ'.pred q₁ q₂)     := insert Q $ tr_stmts₁ q₁ ∪ insert (unrev q₂) (tr_stmts₁ q₂)
| Q@(Λ'.ret k)          := {Q}

theorem tr_stmts₁_trans {q q'} : q' ∈ tr_stmts₁ q → tr_stmts₁ q' ⊆ tr_stmts₁ q :=
begin
  induction q;
    simp only [tr_stmts₁, finset.mem_insert, finset.mem_union, or_imp_distrib,
      finset.mem_singleton, finset.subset.refl, imp_true_iff, true_and] {contextual := tt},
  iterate 4 { exact λ h, finset.subset.trans (q_ih h) (finset.subset_insert _ _) },
  { simp, intros s h x h', simp, exact or.inr ⟨_, q_ih s h h'⟩ },
  { split,
    { rintro rfl, apply finset.subset_insert },
    { intros h x h', simp, exact or.inr (or.inr $ q_ih h h') } },
  { refine ⟨λ h x h', _, λ h x h', _, λ h x h', _⟩; simp,
    { exact or.inr (or.inr $ or.inl $ q_ih_q₁ h h') },
    { cases finset.mem_insert.1 h' with h' h'; simp [h', unrev] },
    { exact or.inr (or.inr $ or.inr $ q_ih_q₂ h h') } },
end

theorem tr_stmts₁_self (q) : q ∈ tr_stmts₁ q :=
by induction q; { apply finset.mem_singleton_self <|> apply finset.mem_insert_self }

/-- The (finite!) set of machine states visited during the course of evaluation of `c`,
including the state `ret k` but not any states after that (that is, the states visited while
evaluating `k`). -/
def code_supp' : code → cont' → finset Λ'
| c@code.zero' k := tr_stmts₁ (tr_normal c k)
| c@code.succ k := tr_stmts₁ (tr_normal c k)
| c@code.tail k := tr_stmts₁ (tr_normal c k)
| c@(code.cons f fs) k :=
  tr_stmts₁ (tr_normal c k) ∪ (code_supp' f (cont'.cons₁ fs k) ∪
  (tr_stmts₁ (
    move₂ (λ _, ff) main aux $
    move₂ (λ s, s = Γ'.Cons) stack main $
    move₂ (λ _, ff) aux stack $
    tr_normal fs (cont'.cons₂ k)) ∪ (code_supp' fs (cont'.cons₂ k) ∪
  tr_stmts₁ (head stack $ Λ'.ret k))))
| c@(code.comp f g) k :=
  tr_stmts₁ (tr_normal c k) ∪ (code_supp' g (cont'.comp f k) ∪
  (tr_stmts₁ (tr_normal f k) ∪ code_supp' f k))
| c@(code.case f g) k := tr_stmts₁ (tr_normal c k) ∪ (code_supp' f k ∪ code_supp' g k)
| c@(code.fix f) k :=
  tr_stmts₁ (tr_normal c k) ∪ (code_supp' f (cont'.fix f k) ∪
  (tr_stmts₁ (Λ'.clear nat_end main $ tr_normal f (cont'.fix f k)) ∪ {Λ'.ret k}))

@[simp] theorem code_supp'_self (c k) : tr_stmts₁ (tr_normal c k) ⊆ code_supp' c k :=
by cases c; refl <|> exact finset.subset_union_left _ _

/-- The (finite!) set of machine states visited during the course of evaluation of a continuation
`k`, not including the initial state `ret k`. -/
def cont_supp : cont' → finset Λ'
| (cont'.cons₁ fs k) :=
  tr_stmts₁ (
    move₂ (λ _, ff) main aux $
    move₂ (λ s, s = Γ'.Cons) stack main $
    move₂ (λ _, ff) aux stack $
    tr_normal fs (cont'.cons₂ k)) ∪ (code_supp' fs (cont'.cons₂ k) ∪
  (tr_stmts₁ (head stack $ Λ'.ret k) ∪ cont_supp k))
| (cont'.cons₂ k) := tr_stmts₁ (head stack $ Λ'.ret k) ∪ cont_supp k
| (cont'.comp f k) := code_supp' f k ∪ cont_supp k
| (cont'.fix f k) := code_supp' (code.fix f) k ∪ cont_supp k
| cont'.halt := ∅

/-- The (finite!) set of machine states visited during the course of evaluation of `c` in
continuation `k`. This is actually closed under forward simulation (see `tr_supports`), and the
existence of this set means that the machine constructed in this section is in fact a proper
Turing machine, with a finite set of states. -/
def code_supp (c : code) (k : cont') : finset Λ' := code_supp' c k ∪ cont_supp k

@[simp] theorem code_supp_self (c k) : tr_stmts₁ (tr_normal c k) ⊆ code_supp c k :=
finset.subset.trans (code_supp'_self _ _) (finset.subset_union_left _ _)

@[simp] theorem code_supp_zero (k) : code_supp code.zero' k =
  tr_stmts₁ (tr_normal code.zero' k) ∪ cont_supp k := rfl

@[simp] theorem code_supp_succ (k) : code_supp code.succ k =
  tr_stmts₁ (tr_normal code.succ k) ∪ cont_supp k := rfl

@[simp] theorem code_supp_tail (k) : code_supp code.tail k =
  tr_stmts₁ (tr_normal code.tail k) ∪ cont_supp k := rfl

@[simp] theorem code_supp_cons (f fs k) : code_supp (code.cons f fs) k =
  tr_stmts₁ (tr_normal (code.cons f fs) k) ∪ code_supp f (cont'.cons₁ fs k) :=
by simp [code_supp, code_supp', cont_supp, finset.union_assoc]

@[simp] theorem code_supp_comp (f g k) : code_supp (code.comp f g) k =
  tr_stmts₁ (tr_normal (code.comp f g) k) ∪ code_supp g (cont'.comp f k) :=
begin
  simp [code_supp, code_supp', cont_supp, finset.union_assoc],
  rw [← finset.union_assoc _ _ (cont_supp k),
      finset.union_eq_right_iff_subset.2 (code_supp'_self _ _)]
end

@[simp] theorem code_supp_case (f g k) : code_supp (code.case f g) k =
  tr_stmts₁ (tr_normal (code.case f g) k) ∪ (code_supp f k ∪ code_supp g k) :=
by simp [code_supp, code_supp', cont_supp, finset.union_assoc, finset.union_left_comm]

@[simp] theorem code_supp_fix (f k) : code_supp (code.fix f) k =
  tr_stmts₁ (tr_normal (code.fix f) k) ∪ code_supp f (cont'.fix f k) :=
by simp [code_supp, code_supp', cont_supp, finset.union_assoc,
  finset.union_left_comm, finset.union_left_idem]

@[simp] theorem cont_supp_cons₁ (fs k) : cont_supp (cont'.cons₁ fs k) =
  tr_stmts₁ (move₂ (λ _, ff) main aux $ move₂ (λ s, s = Γ'.Cons) stack main $
    move₂ (λ _, ff) aux stack $ tr_normal fs (cont'.cons₂ k)) ∪ code_supp fs (cont'.cons₂ k) :=
by simp [code_supp, code_supp', cont_supp, finset.union_assoc]

@[simp] theorem cont_supp_cons₂ (k) : cont_supp (cont'.cons₂ k) =
  tr_stmts₁ (head stack $ Λ'.ret k) ∪ cont_supp k := rfl

@[simp] theorem cont_supp_comp (f k) : cont_supp (cont'.comp f k) = code_supp f k := rfl

theorem cont_supp_fix (f k) : cont_supp (cont'.fix f k) = code_supp f (cont'.fix f k) :=
by simp [code_supp, code_supp', cont_supp, finset.union_assoc,
  finset.subset_iff] {contextual := tt}

@[simp] theorem cont_supp_halt : cont_supp cont'.halt = ∅ := rfl

/-- The statement `Λ'.supports S q` means that `cont_supp k ⊆ S` for any `ret k`
reachable from `q`.
(This is a technical condition used in the proof that the machine is supported.) -/
def Λ'.supports (S : finset Λ') : Λ' → Prop
| Q@(Λ'.move p k₁ k₂ q) := Λ'.supports q
| Q@(Λ'.push k f q)     := Λ'.supports q
| Q@(Λ'.read q)         := ∀ s, Λ'.supports (q s)
| Q@(Λ'.clear p k q)    := Λ'.supports q
| Q@(Λ'.copy q)         := Λ'.supports q
| Q@(Λ'.succ q)         := Λ'.supports q
| Q@(Λ'.pred q₁ q₂)     := Λ'.supports q₁ ∧ Λ'.supports q₂
| Q@(Λ'.ret k)          := cont_supp k ⊆ S

/-- A shorthand for the predicate that we are proving in the main theorems `tr_stmts₁_supports`,
`code_supp'_supports`, `cont_supp_supports`, `code_supp_supports`. The set `S` is fixed throughout
the proof, and denotes the full set of states in the machine, while `K` is a subset that we are
currently proving a property about. The predicate asserts that every state in `K` is closed in `S`
under forward simulation, i.e. stepping forward through evaluation starting from any state in `K`
stays entirely within `S`. -/
def supports (K S : finset Λ') := ∀ q ∈ K, TM2.supports_stmt S (tr q)

theorem supports_insert {K S q} :
  supports (insert q K) S ↔ TM2.supports_stmt S (tr q) ∧ supports K S :=
by simp [supports]

theorem supports_singleton {S q} : supports {q} S ↔ TM2.supports_stmt S (tr q) :=
by simp [supports]

theorem supports_union {K₁ K₂ S} :
  supports (K₁ ∪ K₂) S ↔ supports K₁ S ∧ supports K₂ S :=
by simp [supports, or_imp_distrib, forall_and_distrib]

theorem supports_bUnion {K:option Γ' → finset Λ'} {S} :
  supports (finset.univ.bUnion K) S ↔ ∀ a, supports (K a) S :=
by simp [supports]; apply forall_swap

theorem head_supports {S k q} (H : (q:Λ').supports S) : (head k q).supports S :=
λ _, by dsimp only; split_ifs; exact H

theorem ret_supports {S k} (H₁: cont_supp k ⊆ S) : TM2.supports_stmt S (tr (Λ'.ret k)) :=
begin
  have W := λ {q}, tr_stmts₁_self q,
  cases k,
  case halt { trivial },
  case cons₁ { rw [cont_supp_cons₁, finset.union_subset_iff] at H₁, exact λ _, H₁.1 W },
  case cons₂ { rw [cont_supp_cons₂, finset.union_subset_iff] at H₁, exact λ _, H₁.1 W },
  case comp { rw [cont_supp_comp] at H₁, exact λ _, H₁ (code_supp_self _ _ W) },
  case fix {
    rw [cont_supp_fix] at H₁,
    have L := @finset.mem_union_left, have R := @finset.mem_union_right,
    intro s, dsimp only, cases nat_end s.iget,
    { refine H₁ (R _ $ L _ $ R _ $ R _ $ L _ W) },
    { exact H₁ (R _ $ L _ $ R _ $ R _ $ R _ $ finset.mem_singleton_self _) } }
end

theorem tr_stmts₁_supports {S q}
  (H₁ : (q:Λ').supports S) (HS₁ : tr_stmts₁ q ⊆ S) : supports (tr_stmts₁ q) S :=
begin
  have W := λ {q}, tr_stmts₁_self q,
  induction q; simp [tr_stmts₁] at HS₁ ⊢,
  any_goals {
    cases finset.insert_subset.1 HS₁ with h₁ h₂,
    id { have h₃ := h₂ W } <|> try { simp [finset.subset_iff] at h₂ } },
  { exact supports_insert.2 ⟨⟨λ _, h₃, λ _, h₁⟩, q_ih H₁ h₂⟩ }, -- move
  { exact supports_insert.2 ⟨⟨λ _, h₃, λ _, h₁⟩, q_ih H₁ h₂⟩ }, -- clear
  { exact supports_insert.2 ⟨⟨λ _, h₁, λ _, h₃⟩, q_ih H₁ h₂⟩ }, -- copy
  { exact supports_insert.2 ⟨⟨λ _, h₃, λ _, h₃⟩, q_ih H₁ h₂⟩ }, -- push
  -- read
  { refine supports_insert.2 ⟨λ _, h₂ _ W, _⟩,
    exact supports_bUnion.2 (λ _, q_ih _ (H₁ _) (λ _ h, h₂ _ h)) },
  -- succ
  { refine supports_insert.2 ⟨⟨λ _, h₁, λ _, h₂.1, λ _, h₂.1⟩, _⟩,
    exact supports_insert.2 ⟨⟨λ _, h₂.2 _ W, λ _, h₂.1⟩, q_ih H₁ h₂.2⟩ },
  -- pred
  { refine supports_insert.2 ⟨⟨λ _, h₁, λ _, h₂.2 _ (or.inl W), λ _, h₂.1, λ _, h₂.1⟩, _⟩,
    refine supports_insert.2 ⟨⟨λ _, h₂.2 _ (or.inr W), λ _, h₂.1⟩, _⟩,
    refine supports_union.2 ⟨_, _⟩,
    { exact q_ih_q₁ H₁.1 (λ _ h, h₂.2 _ (or.inl h)) },
    { exact q_ih_q₂ H₁.2 (λ _ h, h₂.2 _ (or.inr h)) } },
  -- ret
  { exact supports_singleton.2 (ret_supports H₁) },
end

theorem tr_stmts₁_supports' {S q K} (H₁ : (q:Λ').supports S) (H₂ : tr_stmts₁ q ∪ K ⊆ S)
  (H₃ : K ⊆ S → supports K S) : supports (tr_stmts₁ q ∪ K) S :=
begin
  simp [finset.union_subset_iff] at H₂,
  exact supports_union.2 ⟨tr_stmts₁_supports H₁ H₂.1, H₃ H₂.2⟩,
end

theorem subset_left {α} [decidable_eq α] {s₁ s₂ s₃ : finset α} (h : s₁ ∪ s₂ ⊆ s₃) : s₁ ⊆ s₃ :=
finset.subset.trans (finset.subset_union_left _ _) h

theorem subset_right {α} [decidable_eq α] {s₁ s₂ s₃ : finset α} (h : s₁ ∪ s₂ ⊆ s₃) : s₂ ⊆ s₃ :=
finset.subset.trans (finset.subset_union_right _ _) h

theorem tr_normal_supports {S c k} (Hk : code_supp c k ⊆ S) : (tr_normal c k).supports S :=
begin
  induction c generalizing k; simp [Λ'.supports, head],
  case zero' { exact subset_right Hk },
  case succ { intro, split_ifs; exact subset_right Hk },
  case tail { exact subset_right Hk },
  case cons : f fs IHf IHfs { apply IHf, rw code_supp_cons at Hk, exact subset_right Hk },
  case comp : f g IHf IHg { apply IHg, rw code_supp_comp at Hk, exact subset_right Hk },
  case case : f g IHf IHg {
    simp only [code_supp_case, finset.union_subset_iff] at Hk,
    exact ⟨IHf Hk.2.1, IHg Hk.2.2⟩ },
  case fix : f IHf { apply IHf, rw code_supp_fix at Hk, exact subset_right Hk },
end

theorem code_supp'_supports {S c k}
  (H : code_supp c k ⊆ S) : supports (code_supp' c k) S :=
begin
  induction c generalizing k,
  iterate 3 {
    exact tr_stmts₁_supports (tr_normal_supports H)
      (finset.subset.trans (code_supp_self _ _) H) },
  case cons : f fs IHf IHfs {
    have H' := H, simp only [code_supp_cons, finset.union_subset_iff] at H',
    refine tr_stmts₁_supports' (tr_normal_supports H) (subset_left H) (λ h, _),
    refine supports_union.2 ⟨IHf H'.2, _⟩,
    refine tr_stmts₁_supports' (tr_normal_supports _) (subset_right h) (λ h, _),
    { simp only [code_supp, finset.union_subset_iff, cont_supp] at h H ⊢,
      exact ⟨h.2.2.1, h.2.2.2, H.2⟩ },
    refine supports_union.2 ⟨IHfs _, _⟩,
    { rw [code_supp, cont_supp_cons₁] at H',
      exact subset_right (subset_right H'.2) },
    exact tr_stmts₁_supports (head_supports $ subset_right H) (subset_right h) },
  case comp : f g IHf IHg {
    have H' := H, rw [code_supp_comp] at H', have H' := subset_right H',
    refine tr_stmts₁_supports' (tr_normal_supports H) (subset_left H) (λ h, _),
    refine supports_union.2 ⟨IHg H', _⟩,
    refine tr_stmts₁_supports' (tr_normal_supports _) (subset_right h) (λ h, _),
    { simp only [code_supp', code_supp, finset.union_subset_iff, cont_supp] at h H ⊢,
      exact ⟨h.2.2, H.2⟩ },
    exact IHf (subset_right H') },
  case case : f g IHf IHg {
    have H' := H, simp only [code_supp_case, finset.union_subset_iff] at H',
    refine tr_stmts₁_supports' (tr_normal_supports H) (subset_left H) (λ h, _),
    exact supports_union.2 ⟨IHf H'.2.1, IHg H'.2.2⟩ },
  case fix : f IHf {
    have H' := H, simp only [code_supp_fix, finset.union_subset_iff] at H',
    refine tr_stmts₁_supports' (tr_normal_supports H) (subset_left H) (λ h, _),
    refine supports_union.2 ⟨IHf H'.2, _⟩,
    refine tr_stmts₁_supports' (tr_normal_supports _) (subset_right h) (λ h, _),
    { simp only [code_supp', code_supp, finset.union_subset_iff, cont_supp,
        tr_stmts₁, finset.insert_subset] at h H ⊢,
      exact ⟨h.1, ⟨H.1.1, h⟩, H.2⟩ },
    exact supports_singleton.2 (ret_supports $ subset_right H) },
end

theorem cont_supp_supports {S k}
  (H : cont_supp k ⊆ S) : supports (cont_supp k) S :=
begin
  induction k,
  { simp [cont_supp_halt, supports] },
  case cons₁ : f k IH {
    have H₁ := H, rw [cont_supp_cons₁] at H₁, have H₂ := subset_right H₁,
    refine tr_stmts₁_supports' (tr_normal_supports H₂) H₁ (λ h, _),
    refine supports_union.2 ⟨code_supp'_supports H₂, _⟩,
    simp only [code_supp, cont_supp_cons₂, finset.union_subset_iff] at H₂,
    exact tr_stmts₁_supports' (head_supports H₂.2.2) (subset_right h) IH },
  case cons₂ : k IH {
    have H' := H, rw [cont_supp_cons₂] at H',
    exact tr_stmts₁_supports' (head_supports $ subset_right H') H' IH },
  case comp : f k IH {
    have H' := H, rw [cont_supp_comp] at H', have H₂ := subset_right H',
    exact supports_union.2 ⟨code_supp'_supports H', IH H₂⟩ },
  case fix : f k IH {
    rw cont_supp at H,
    exact supports_union.2 ⟨code_supp'_supports H, IH (subset_right H)⟩ }
end

theorem code_supp_supports {S c k}
  (H : code_supp c k ⊆ S) : supports (code_supp c k) S :=
supports_union.2 ⟨code_supp'_supports H, cont_supp_supports (subset_right H)⟩

/-- The set `code_supp c k` is a finite set that witnesses the effective finiteness of the `tr`
Turing machine. Starting from the initial state `tr_normal c k`, forward simulation uses only
states in `code_supp c k`, so this is a finite state machine. Even though the underlying type of
state labels `Λ'` is infinite, for a given partial recursive function `c` and continuation `k`,
only finitely many states are accessed, corresponding roughly to subterms of `c`. -/
theorem tr_supports (c k) : @TM2.supports _ _ _ _ _ ⟨tr_normal c k⟩ tr (code_supp c k) :=
⟨code_supp_self _ _ (tr_stmts₁_self _),
  λ l', code_supp_supports (finset.subset.refl _) _⟩

end

end partrec_to_TM2

end turing
