/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.lazy_list.basic
import control.bifunctor
import tactic.linarith
import testing.slim_check.gen

/-!
# `sampleable` Class

This class permits the creation samples of a given type
controlling the size of those values using the `gen` monad`. It also
helps minimize examples by creating smaller versions of given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`slim_check` requires that `ℕ` have an instance of `sampleable` and for
`prime n` to be decidable.  `slim_check` will then use the instance of
`sampleable` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`slim_check` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `slim_check` moves on to trying more examples.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `sampleable` class
  * `sampleable_functor` and `sampleable_bifunctor` class
  * `sampleable_ext` class

### `sampleable`

`sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.

### `sampleable_ext`

`sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type.

### `sampleable_functor` and `sampleable_bifunctor`

`sampleable_functor F` and `sampleable_bifunctor F` makes it possible
to create samples of and shrink `F α` given a sampling function and a
shrinking function for arbitrary `α`.

This allows us to separate the logic for generating the shape of a
collection from the logic for generating its contents. Specifically,
the contents could be generated using either `sampleable` or
`sampleable_ext` instance and the `sampleable_(bi)functor` does not
need to use that information

## Shrinking

Shrinking happens when `slim_check` find a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `slim_check` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.

The `sampleable` class, beside having the `sample` function, has a
`shrink` function so that we can use specialized knowledge while
shrinking a value. It is not responsible for the whole shrinking process
however. It only has to take one step in the shrinking process.
`slim_check` will repeatedly call `shrink` until no more steps can
be taken. Because `shrink` guarantees that the size of the candidates
it produces is strictly smaller than the argument, we know that
`slim_check` is guaranteed to terminate.

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/
universes u v w

namespace slim_check

variables (α : Type u)

local infix ` ≺ `:50 := has_well_founded.r

/-- `sizeof_lt x y` compares the sizes of `x` and `y`. -/
def sizeof_lt {α} [has_sizeof α] (x y : α) := sizeof x < sizeof y

/-- `shrink_fn α` is the type of functions that shrink an
argument of type `α` -/
@[reducible]
def shrink_fn (α : Type*) [has_sizeof α] := Π x : α, lazy_list { y : α // sizeof_lt y x }

/-- `sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.  -/
class sampleable :=
[wf : has_sizeof α]
(sample [] : gen α)
(shrink : Π x : α, lazy_list { y : α // @sizeof _ wf y < @sizeof _ wf x } := λ _, lazy_list.nil)

attribute [instance, priority 100] has_well_founded_of_has_sizeof default_has_sizeof
attribute [instance, priority 200] sampleable.wf

/-- `sampleable_functor F` makes it possible to create samples of and
shrink `F α` given a sampling function and a shrinking function for
arbitrary `α` -/
class sampleable_functor (F : Type u → Type v) [functor F] :=
[wf : Π α [has_sizeof α], has_sizeof (F α)]
(sample [] : ∀ {α}, gen α → gen (F α))
(shrink : ∀ α [has_sizeof α], shrink_fn α → shrink_fn (F α))
(p_repr : ∀ α, has_repr α → has_repr (F α))

/-- `sampleable_bifunctor F` makes it possible to create samples of
and shrink `F α β` given a sampling function and a shrinking function
for arbitrary `α` and `β` -/
class sampleable_bifunctor (F : Type u → Type v → Type w) [bifunctor F] :=
[wf : Π α β [has_sizeof α] [has_sizeof β], has_sizeof (F α β)]
(sample [] : ∀ {α β}, gen α → gen β → gen (F α β))
(shrink : ∀ α β [has_sizeof α] [has_sizeof β], shrink_fn α → shrink_fn β → shrink_fn (F α β))
(p_repr : ∀ α β, has_repr α → has_repr β → has_repr (F α β))

export sampleable (sample shrink)

/-- This function helps infer the proxy representation and
interpretation in `sampleable_ext` instances. -/
meta def sampleable.mk_trivial_interp : tactic unit :=
tactic.refine ``(id)

/-- `sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class sampleable_ext (α : Sort u) :=
(proxy_repr : Type v)
[wf : has_sizeof proxy_repr]
(interp [] : proxy_repr → α . sampleable.mk_trivial_interp)
[p_repr : has_repr proxy_repr]
(sample [] : gen proxy_repr)
(shrink : shrink_fn proxy_repr)

attribute [instance, priority 100] sampleable_ext.p_repr sampleable_ext.wf

open nat lazy_list

section prio

open sampleable_ext

set_option default_priority 50

instance sampleable_ext.of_sampleable {α} [sampleable α] [has_repr α] : sampleable_ext α :=
{ proxy_repr := α,
  sample := sampleable.sample α,
  shrink := shrink }

instance sampleable.functor {α} {F} [functor F] [sampleable_functor F] [sampleable α] :
  sampleable (F α) :=
{ wf := _,
  sample := sampleable_functor.sample F (sampleable.sample α),
  shrink := sampleable_functor.shrink α sampleable.shrink }

instance sampleable.bifunctor {α β} {F} [bifunctor F] [sampleable_bifunctor F] [sampleable α]
  [sampleable β] : sampleable (F α β) :=
{ wf := _,
  sample := sampleable_bifunctor.sample F (sampleable.sample α) (sampleable.sample β),
  shrink := sampleable_bifunctor.shrink α β sampleable.shrink sampleable.shrink }

set_option default_priority 100

instance sampleable_ext.functor {α} {F} [functor F] [sampleable_functor F] [sampleable_ext α] :
  sampleable_ext (F α) :=
{ wf := _,
  proxy_repr := F (proxy_repr α),
  interp := functor.map (interp _),
  sample := sampleable_functor.sample F (sampleable_ext.sample α),
  shrink := sampleable_functor.shrink _ sampleable_ext.shrink,
  p_repr := sampleable_functor.p_repr _ sampleable_ext.p_repr
  }

instance sampleable_ext.bifunctor {α β} {F} [bifunctor F] [sampleable_bifunctor F]
  [sampleable_ext α] [sampleable_ext β] : sampleable_ext (F α β) :=
{ wf := _,
  proxy_repr := F (proxy_repr α) (proxy_repr β),
  interp := bifunctor.bimap (interp _) (interp _),
  sample := sampleable_bifunctor.sample F (sampleable_ext.sample α) (sampleable_ext.sample β),
  shrink := sampleable_bifunctor.shrink _ _ sampleable_ext.shrink sampleable_ext.shrink,
  p_repr := sampleable_bifunctor.p_repr _ _ sampleable_ext.p_repr sampleable_ext.p_repr
  }

end prio

/-- `nat.shrink' k n` creates a list of smaller natural numbers by
successively dividing `n` by 2 and subtracting the difference from
`k`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink' (k : ℕ) : Π n : ℕ, n ≤ k →
  list { m : ℕ // has_well_founded.r m k } → list { m : ℕ // has_well_founded.r m k }
| n hn ls :=
if h : n ≤ 1
  then ls.reverse
  else
    have h₂ : 0 < n, by linarith,
    have 1 * n / 2 < n,
      from nat.div_lt_of_lt_mul (nat.mul_lt_mul_of_pos_right (by norm_num) h₂),
    have n / 2 < n, by simpa,
    let m := n / 2 in
    have h₀ : m ≤ k, from le_trans (le_of_lt this) hn,
    have h₃ : 0 < m,
      by simp only [m, lt_iff_add_one_le, zero_add]; rw [le_div_iff_mul_le]; linarith,
    have h₁ : k - m < k,
      from nat.sub_lt (lt_of_lt_of_le h₂ hn) h₃,
    nat.shrink' m h₀ (⟨k - m, h₁⟩ :: ls)

/-- `nat.shrink n` creates a list of smaller natural numbers by
successively dividing by 2 and subtracting the difference from
`n`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink (n : ℕ) : list { m : ℕ // has_well_founded.r m n } :=
if h : n > 0 then
  have ∀ k, 1 < k → n / k < n, from
    λ k hk,
     nat.div_lt_of_lt_mul
       (suffices 1 * n < k * n, by simpa,
        nat.mul_lt_mul_of_pos_right hk h),
  ⟨n/11, this _ (by norm_num)⟩ :: ⟨n/3, this _ (by norm_num)⟩ :: nat.shrink' n n (le_refl _) []
else
  []

open gen

/--
Transport a `sampleable` instance from a type `α` to a type `β` using
functions between the two, going in both directions.

Function `g` is used to define the well-founded order that
`shrink` is expected to follow.
-/
def sampleable.lift (α : Type u) {β : Type u} [sampleable α] (f : α → β) (g : β → α)
  (h : ∀ (a : α), sizeof (g (f a)) ≤ sizeof a) : sampleable β :=
{ wf := ⟨ sizeof ∘ g ⟩,
  sample := f <$> sample α,
  shrink := λ x,
    have ∀ a,  sizeof a < sizeof (g x) → sizeof (g (f a)) < sizeof (g x),
      by introv h'; solve_by_elim [lt_of_le_of_lt],
    subtype.map f this <$> shrink (g x) }

instance nat.sampleable : sampleable ℕ :=
{ sample := sized $ λ sz, freq [(1, coe <$> choose_any (fin $ succ (sz^3))),
                                (3, coe <$> choose_any (fin $ succ sz))] dec_trivial,
  shrink :=  λ x, lazy_list.of_list $ nat.shrink x }

/-- `iterate_shrink p x` takes a decidable predicate `p` and a
value `x` of some sampleable type and recursively shrinks `x`.
It first calls `shrink x` to get a list of candidate sample,
finds the first that satisfies `p` and recursively tries
to shrink that one. -/
def iterate_shrink {α} [has_to_string α] [sampleable α]
  (p : α → Prop) [decidable_pred p] :
  α → option α :=
well_founded.fix has_well_founded.wf $ λ x f_rec,
  do trace sformat!"{x} : {(shrink x).to_list}" $ pure (),
     y ← (shrink x).find (λ a, p a),
     f_rec y y.property <|> some y.val .

instance fin.sampleable {n} [fact $ 0 < n] : sampleable (fin n) :=
sampleable.lift ℕ fin.of_nat' subtype.val $
λ i, (mod_le _ _ : i % n ≤ i)

@[priority 100]
instance fin.sampleable' {n} : sampleable (fin (succ n)) :=
sampleable.lift ℕ fin.of_nat subtype.val $
λ i, (mod_le _ _ : i % succ n ≤ i)

instance pnat.sampleable : sampleable ℕ+ :=
sampleable.lift ℕ nat.succ_pnat pnat.nat_pred $ λ a,
by unfold_wf; simp only [pnat.nat_pred, succ_pnat, pnat.mk_coe, nat.sub_zero, succ_sub_succ_eq_sub]

/-- Redefine `sizeof` for `int` to make it easier to use with `nat` -/
def int.has_sizeof : has_sizeof ℤ := ⟨ int.nat_abs ⟩

local attribute [instance, priority 2000] int.has_sizeof

instance int.sampleable : sampleable ℤ :=
{ wf := _,
  sample := sized $ λ sz,
          freq [(1, subtype.val <$> choose (-(sz^3 + 1) : ℤ) (sz^3 + 1) (neg_le_self dec_trivial)),
                (3, subtype.val <$> choose (-(sz + 1)) (sz + 1) (neg_le_self dec_trivial))]
               dec_trivial,
  shrink :=
    λ x, lazy_list.of_list $ (nat.shrink $ int.nat_abs x).bind $
    λ ⟨y,h⟩, [⟨y, h⟩, ⟨-y, by dsimp [sizeof,has_sizeof.sizeof]; rw int.nat_abs_neg; exact h ⟩] }

instance bool.sampleable : sampleable bool :=
{ wf := ⟨ λ b, if b then 1 else 0 ⟩,
  sample := do { x ← choose_any bool,
                 return x },
  shrink := λ b, if h : b then lazy_list.singleton ⟨ff, by cases h; unfold_wf⟩
                          else lazy_list.nil }

/--
Provided two shrinking functions `prod.shrink` shrinks a pair `(x, y)` by
first shrinking `x` and pairing the results with `y` and then shrinking
`y` and pairing the results with `x`.

All pairs either contain `x` untouched or `y` untouched. We rely on
shrinking being repeated for `x` to get maximally shrunken and then
for `y` to get shrunken too.
-/
def prod.shrink {α β} [has_sizeof α] [has_sizeof β]
  (shr_a : shrink_fn α) (shr_b : shrink_fn β) : shrink_fn (α × β)
| ⟨x₀,x₁⟩ :=
  let xs₀ : lazy_list { y : α × β // sizeof_lt y (x₀,x₁) } :=
          (shr_a x₀).map $ subtype.map (λ a, (a, x₁))
                           (λ x h, by dsimp [sizeof_lt]; unfold_wf; apply h),
      xs₁ : lazy_list { y : α × β // sizeof_lt y (x₀,x₁) } :=
          (shr_b x₁).map $ subtype.map (λ a, (x₀, a))
                           (λ x h, by dsimp [sizeof_lt]; unfold_wf; apply h) in
  xs₀.append xs₁

instance prod.sampleable : sampleable_bifunctor.{u v} prod :=
{ wf := _,
  sample := λ α β sama samb, do
              { ⟨x⟩ ← (uliftable.up $ sama : gen (ulift.{max u v} α)),
                ⟨y⟩ ← (uliftable.up $ samb : gen (ulift.{max u v} β)),
                pure (x,y) },
  shrink := @prod.shrink,
  p_repr := @prod.has_repr }

instance sigma.sampleable {α β} [sampleable α] [sampleable β] : sampleable (Σ _ : α, β) :=
sampleable.lift (α × β) (λ ⟨x,y⟩, ⟨x,y⟩) (λ ⟨x,y⟩, ⟨x,y⟩) $ λ ⟨x,y⟩, le_refl _

/-- shrinking function for sum types -/
def sum.shrink {α β} [has_sizeof α] [has_sizeof β] (shrink_α : shrink_fn α)
  (shrink_β : shrink_fn β) : shrink_fn (α ⊕ β)
| (sum.inr x) := (shrink_β x).map $ subtype.map sum.inr $ λ a,
  by dsimp [sizeof_lt]; unfold_wf; solve_by_elim
| (sum.inl x) := (shrink_α x).map $ subtype.map sum.inl $ λ a,
  by dsimp [sizeof_lt]; unfold_wf; solve_by_elim

instance sum.sampleable : sampleable_bifunctor.{u v} sum :=
{ wf := _,
  sample := λ (α : Type u) (β : Type v) sam_α sam_β,
            (@uliftable.up_map gen.{u} gen.{max u v} _ _ _ _ (@sum.inl α β) sam_α <|>
             @uliftable.up_map gen.{v} gen.{max v u} _ _ _ _ (@sum.inr α β) sam_β),
  shrink := λ α β Iα Iβ shr_α shr_β, @sum.shrink _ _ Iα Iβ shr_α shr_β,
  p_repr := @sum.has_repr }

instance rat.sampleable : sampleable ℚ :=
sampleable.lift (ℤ × ℕ+) (λ x, prod.cases_on x rat.mk_pnat) (λ r, (r.num, ⟨r.denom, r.pos⟩)) $
begin
  intro i,
  rcases i with ⟨x,⟨y,hy⟩⟩; unfold_wf;
  dsimp [rat.mk_pnat],
  mono*,
  { rw [← int.coe_nat_le, ← int.abs_eq_nat_abs, ← int.abs_eq_nat_abs],
    apply int.abs_div_le_abs },
  { change _ - 1 ≤ y-1,
    apply nat.sub_le_sub_right,
    apply nat.div_le_of_le_mul,
    suffices : 1 * y ≤ x.nat_abs.gcd y * y, { simpa },
    apply nat.mul_le_mul_right,
    apply gcd_pos_of_pos_right _ hy }
end

/-- `sampleable_char` can be specialized into customized `sampleable char` instances.

The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `characters` with uniform probabilities.  -/
def sampleable_char (length : nat) (characters : string) : sampleable char :=
{ sample := do { x ← choose_nat 0 length dec_trivial,
                 if x.val = 0 then do
                   n ← sample ℕ,
                   pure $ char.of_nat n
                 else do
                   i ← choose_nat 0 (characters.length - 1) dec_trivial,
                   pure (characters.mk_iterator.nextn i).curr },
  shrink := λ _, lazy_list.nil }

instance char.sampleable : sampleable char :=
sampleable_char 3 " 0123abcABC:,;`\\/"

variables {α}

section list_shrink

variables [has_sizeof α] (shr : Π x : α, lazy_list { y : α // sizeof_lt y x })

lemma list.sizeof_drop_lt_sizeof_of_lt_length {xs : list α} {k}
  (hk : 0 < k) (hk' : k < xs.length) :
  sizeof (list.drop k xs) < sizeof xs :=
begin
  induction xs with x xs generalizing k,
  { cases hk' },
  cases k,
  { cases hk },
  have : sizeof xs < sizeof (x :: xs),
  { unfold_wf, linarith },
  cases k,
  { simp only [this, list.drop] },
  { simp only [list.drop],
    transitivity,
    { solve_by_elim [xs_ih, lt_of_succ_lt_succ hk', zero_lt_succ] },
    { assumption } }
end

lemma list.sizeof_cons_lt_right (a b : α) {xs : list α} (h : sizeof a < sizeof b) :
  sizeof (a :: xs) < sizeof (b :: xs) :=
by unfold_wf; assumption

lemma list.sizeof_cons_lt_left (x : α) {xs xs' : list α} (h : sizeof xs < sizeof xs') :
  sizeof (x :: xs) < sizeof (x :: xs') :=
by unfold_wf; assumption

lemma list.sizeof_append_lt_left {xs ys ys' : list α} (h : sizeof ys < sizeof ys') :
  sizeof (xs ++ ys) < sizeof (xs ++ ys') :=
begin
  induction xs,
  { apply h },
  { unfold_wf,
    simp only [list.sizeof, add_lt_add_iff_left],
    exact xs_ih }
end

lemma list.one_le_sizeof (xs : list α) : 1 ≤ sizeof xs :=
by cases xs; unfold_wf; [refl, linarith]

/--
`list.shrink_removes` shrinks a list by removing chunks of size `k` in
the middle of the list.
-/
def list.shrink_removes (k : ℕ) (hk : 0 < k) : Π (xs : list α) n,
  n = xs.length → lazy_list { ys : list α // sizeof_lt ys xs }
| xs n hn :=
  if hkn : k > n then lazy_list.nil
  else
  if hkn' : k = n then
    have 1 < xs.sizeof,
      by { subst_vars, cases xs, { contradiction },
           unfold_wf, apply lt_of_lt_of_le,
           show 1 < 1 + has_sizeof.sizeof xs_hd + 1, { linarith },
           { mono, apply list.one_le_sizeof, } },
    lazy_list.singleton ⟨[], this ⟩
  else
    have h₂ : k < xs.length, from hn ▸ lt_of_le_of_ne (le_of_not_gt hkn) hkn',
    match list.split_at k xs, rfl : Π ys, ys = list.split_at k xs → _ with
    |  ⟨xs₁,xs₂⟩, h :=
      have h₄ : xs₁ = xs.take k,
        by simp only [list.split_at_eq_take_drop, prod.mk.inj_iff] at h; tauto,
      have h₃ : xs₂ = xs.drop k,
        by simp only [list.split_at_eq_take_drop, prod.mk.inj_iff] at h; tauto,
      have sizeof xs₂ < sizeof xs,
        by rw h₃; solve_by_elim [list.sizeof_drop_lt_sizeof_of_lt_length],
      have h₁ : n - k = xs₂.length,
        by simp only [h₃, ←hn, list.length_drop],
      have h₅ : ∀ (a : list α), sizeof_lt a xs₂ → sizeof_lt (xs₁ ++ a) xs,
        by intros a h; rw [← list.take_append_drop k xs, ← h₃, ← h₄];
          solve_by_elim [list.sizeof_append_lt_left],
      lazy_list.cons ⟨xs₂, this⟩ $ subtype.map ((++) xs₁) h₅ <$> list.shrink_removes xs₂ (n - k) h₁
    end

/--
`list.shrink_one xs` shrinks list `xs` by shrinking only one item in
the list.
-/
def list.shrink_one : shrink_fn (list α)
| [] := lazy_list.nil
| (x :: xs) :=
  lazy_list.append
    (subtype.map (λ x', x' :: xs) (λ a,  list.sizeof_cons_lt_right _ _) <$> shr x)
    (subtype.map ((::) x) (λ _, list.sizeof_cons_lt_left _) <$> list.shrink_one xs)


/-- `list.shrink_with shrink_f xs` shrinks `xs` by first
considering `xs` with chunks removed in the middle (starting with
chunks of size `xs.length` and halving down to `1`) and then
shrinks only one element of the list.

This strategy is taken directly from Haskell's QuickCheck -/
def list.shrink_with (xs : list α) :
  lazy_list { ys : list α // sizeof_lt ys xs } :=
let n := xs.length in
lazy_list.append
  ((lazy_list.cons n $ (shrink n).reverse.map subtype.val).bind (λ k,
    if hk : 0 < k
    then list.shrink_removes k hk xs n rfl
    else lazy_list.nil ))
  (list.shrink_one shr _)

end list_shrink

instance list.sampleable : sampleable_functor list.{u} :=
{ wf := _,
  sample := λ α sam_α, list_of sam_α,
  shrink := λ α Iα shr_α, @list.shrink_with _ Iα shr_α,
  p_repr := @list.has_repr }

instance prop.sampleable_ext : sampleable_ext Prop :=
{ proxy_repr := bool,
  interp := coe,
  sample := choose_any bool,
  shrink := λ _, lazy_list.nil }

/-- `no_shrink` is a type annotation to signal that
a certain type is not to be shrunk. It can be useful in
combination with other types: e.g. `xs : list (no_shrink ℤ)`
will result in the list being cut down but individual
integers being kept as is. -/
def no_shrink (α : Type*) := α

instance no_shrink.inhabited {α} [inhabited α] : inhabited (no_shrink α) :=
⟨ (default α : α) ⟩

/-- Introduction of the `no_shrink` type. -/
def no_shrink.mk {α} (x : α) : no_shrink α := x

/-- Selector of the `no_shrink` type. -/
def no_shrink.get {α} (x : no_shrink α) : α := x

instance no_shrink.sampleable {α} [sampleable α] : sampleable (no_shrink α) :=
{ sample := no_shrink.mk <$> sample α }

instance string.sampleable : sampleable string :=
{ sample := do { x ← list_of (sample char), pure x.as_string },
  .. sampleable.lift (list char) list.as_string string.to_list $ λ _, le_refl _ }

/-- implementation of `sampleable (tree α)` -/
def tree.sample (sample : gen α) : ℕ → gen (tree α) | n :=
if h : n > 0
then have n / 2 < n, from div_lt_self h (by norm_num),
     tree.node <$> sample <*> tree.sample (n / 2) <*> tree.sample (n / 2)
else pure tree.nil

/-- `rec_shrink x f_rec` takes the recursive call `f_rec` introduced
by `well_founded.fix` and turns it into a shrinking function whose
result is adequate to use in a recursive call. -/
def rec_shrink {α : Type*} [has_sizeof α] (t : α)
  (sh : Π x : α, sizeof_lt x t → lazy_list { y : α // sizeof_lt y x }) :
  shrink_fn { t' : α // sizeof_lt t' t }
| ⟨t',ht'⟩ := (λ t'' : { y : α // sizeof_lt y t' },
    ⟨⟨t''.val, lt_trans t''.property ht'⟩, t''.property⟩ ) <$> sh t' ht'

lemma tree.one_le_sizeof {α} [has_sizeof α] (t : tree α) : 1 ≤ sizeof t :=
by cases t; unfold_wf; linarith

instance : functor tree :=
{ map := @tree.map }

/--
Recursion principle for shrinking tree-like structures.
-/
def rec_shrink_with [has_sizeof α]
  (shrink_a : Π x : α, shrink_fn { y : α // sizeof_lt y x } →
    list (lazy_list { y : α // sizeof_lt y x })) :
  shrink_fn α :=
well_founded.fix (sizeof_measure_wf _) $ λ t f_rec,
lazy_list.join
    (lazy_list.of_list $
      shrink_a t $ λ ⟨t', h⟩, rec_shrink _ f_rec _)

lemma rec_shrink_with_eq [has_sizeof α]
  (shrink_a : Π x : α, shrink_fn { y : α // sizeof_lt y x } →
    list (lazy_list { y : α // sizeof_lt y x }))
  (x : α) :
  rec_shrink_with shrink_a x =
  lazy_list.join
    (lazy_list.of_list $ shrink_a x $ λ t', rec_shrink _ (λ x h', rec_shrink_with shrink_a x) _) :=
begin
  conv_lhs { rw [rec_shrink_with, well_founded.fix_eq], },
  congr, ext ⟨y, h⟩, refl
end

/-- `tree.shrink_with shrink_f t` shrinks `xs` by using the empty tree,
each subtrees, and by shrinking the subtree to recombine them.

This strategy is taken directly from Haskell's QuickCheck -/
def tree.shrink_with [has_sizeof α] (shrink_a : shrink_fn α) : shrink_fn (tree α) :=
rec_shrink_with $ λ t,
match t with
| tree.nil := λ f_rec, []
| (tree.node x t₀ t₁) :=
λ f_rec,
  have h₂ : sizeof_lt tree.nil (tree.node x t₀ t₁),
    by clear _match; have := tree.one_le_sizeof t₀;
       dsimp [sizeof_lt, sizeof, has_sizeof.sizeof] at *;
       unfold_wf; linarith,
  have h₀ : sizeof_lt t₀ (tree.node x t₀ t₁),
    by dsimp [sizeof_lt]; unfold_wf; linarith,
  have h₁ : sizeof_lt t₁ (tree.node x t₀ t₁),
    by dsimp [sizeof_lt]; unfold_wf; linarith,
  [lazy_list.of_list [⟨tree.nil, h₂⟩, ⟨t₀, h₀⟩, ⟨t₁, h₁⟩],
   (prod.shrink shrink_a (prod.shrink f_rec f_rec) (x, ⟨t₀, h₀⟩, ⟨t₁, h₁⟩)).map
    $ λ ⟨⟨y,⟨t'₀, _⟩,⟨t'₁, _⟩⟩,hy⟩, ⟨tree.node y t'₀ t'₁,
      by revert hy; dsimp [sizeof_lt]; unfold_wf; intro; linarith⟩]
end

instance sampleable_tree : sampleable_functor tree :=
{ wf := _,
  sample := λ α sam_α, sized $ tree.sample sam_α,
  shrink := λ α Iα shr_α, @tree.shrink_with _ Iα shr_α,
  p_repr := @tree.has_repr }

/-- Type tag that signals to `slim_check` to use small values for a given type. -/
def small (α : Type*) := α

/-- Add the `small` type tag -/
def small.mk {α} (x : α) : small α := x

/-- Type tag that signals to `slim_check` to use large values for a given type. -/
def large (α : Type*) := α

/-- Add the `large` type tag -/
def large.mk {α} (x : α) : large α := x

instance small.functor : functor small := id.monad.to_functor
instance large.functor : functor large := id.monad.to_functor
instance small.inhabited [inhabited α] : inhabited (small α) := ⟨ (default α : α) ⟩
instance large.inhabited [inhabited α] : inhabited (large α) := ⟨ (default α : α) ⟩

instance small.sampleable_functor : sampleable_functor small :=
{ wf := _,
  sample := λ α samp, gen.resize (λ n, n / 5 + 5) samp,
  shrink := λ α _, id,
  p_repr := λ α, id }

instance large.sampleable_functor : sampleable_functor large :=
{ wf := _,
  sample := λ α samp, gen.resize (λ n, n * 5) samp,
  shrink := λ α _, id,
  p_repr := λ α, id }

instance ulift.sampleable_functor : sampleable_functor ulift.{u v} :=
{ wf := λ α h, ⟨ λ ⟨x⟩, @sizeof α h x ⟩,
  sample := λ α samp, uliftable.up_map ulift.up $ samp,
  shrink := λ α _ shr ⟨x⟩, (shr x).map (subtype.map ulift.up (λ a h, h)),
  p_repr := λ α h, ⟨ @repr α h ∘ ulift.down ⟩ }

/-!
## Subtype instances

The following instances are meant to improve the testing of properties of the form
`∀ i j, i ≤ j, ...`

The naive way to test them is to choose two numbers `i` and `j` and check that
the proper ordering is satisfied. Instead, the following instances make it
so that `j` will be chosen with considerations to the required ordering
constraints. The benefit is that we will not have to discard any choice
of `j`.
 -/

/-! ### Subtypes of `ℕ` -/

instance nat_le.sampleable {y} : slim_check.sampleable { x : ℕ // x ≤ y } :=
{ sample :=
         do { ⟨x,h⟩ ← slim_check.gen.choose_nat 0 y dec_trivial,
              pure ⟨x, h.2⟩},
  shrink := λ ⟨x, h⟩, (λ a : subtype _, subtype.rec_on a $
    λ x' h', ⟨⟨x', le_trans (le_of_lt h') h⟩, h'⟩) <$> shrink x }

instance nat_ge.sampleable {x} : slim_check.sampleable { y : ℕ // x ≤ y } :=
{ sample :=
         do { (y : ℕ) ← slim_check.sampleable.sample ℕ,
              pure ⟨x+y, by norm_num⟩ },
  shrink := λ ⟨y, h⟩, (λ a : { y' // sizeof y' < sizeof (y - x) },
    subtype.rec_on a $ λ δ h', ⟨⟨x + δ, nat.le_add_right _ _⟩, nat.add_lt_of_lt_sub_left h'⟩) <$>
      shrink (y - x) }

/- there is no `nat_lt.sampleable` instance because if `y = 0`, there is no valid choice
to satisfy `x < y` -/

instance nat_gt.sampleable {x} : slim_check.sampleable { y : ℕ // x < y } :=
{ sample :=
         do { (y : ℕ) ← slim_check.sampleable.sample ℕ,
              pure ⟨x+y+1, by linarith⟩ },
  shrink := λ x, shrink _ }

/-! ### Subtypes of any `linear_ordered_add_comm_group` -/

instance le.sampleable {y : α} [sampleable α] [linear_ordered_add_comm_group α] :
  slim_check.sampleable { x : α // x ≤ y } :=
{ sample :=
         do { x ← sample α,
              pure ⟨y - abs x, sub_le_self _ (abs_nonneg _) ⟩ },
  shrink := λ _, lazy_list.nil }

instance ge.sampleable {x : α}  [sampleable α] [linear_ordered_add_comm_group α] :
  slim_check.sampleable { y : α // x ≤ y } :=
{ sample :=
         do { y ← sample α,
              pure ⟨x + abs y, by norm_num [abs_nonneg]⟩ },
  shrink := λ _, lazy_list.nil }


/-!
### Subtypes of `ℤ`

Specializations of `le.sampleable` and `ge.sampleable` for `ℤ` to help instance search.
-/

instance int_le.sampleable {y : ℤ} : slim_check.sampleable { x : ℤ // x ≤ y } :=
sampleable.lift ℕ (λ n, ⟨y - n, int.sub_left_le_of_le_add $ by simp⟩) (λ ⟨i, h⟩, (y - i).nat_abs)
  (λ n, by unfold_wf; simp [int_le.sampleable._match_1]; ring)

instance int_ge.sampleable {x : ℤ} : slim_check.sampleable { y : ℤ // x ≤ y } :=
sampleable.lift ℕ (λ n, ⟨x + n, by simp⟩) (λ ⟨i, h⟩, (i - x).nat_abs)
  (λ n, by unfold_wf; simp [int_ge.sampleable._match_1]; ring)

instance int_lt.sampleable {y} : slim_check.sampleable { x : ℤ // x < y } :=
sampleable.lift ℕ (λ n, ⟨y - (n+1), int.sub_left_lt_of_lt_add $
    by linarith [int.coe_nat_nonneg n]⟩)
  (λ ⟨i, h⟩, (y - i - 1).nat_abs)
  (λ n, by unfold_wf; simp [int_lt.sampleable._match_1]; ring)

instance int_gt.sampleable {x} : slim_check.sampleable { y : ℤ // x < y } :=
sampleable.lift ℕ (λ n, ⟨x + (n+1), by linarith⟩) (λ ⟨i, h⟩, (i - x - 1).nat_abs)
  (λ n, by unfold_wf; simp [int_gt.sampleable._match_1]; ring)

/-! ### Subtypes of any `list` -/

instance perm.slim_check {xs : list α} : slim_check.sampleable { ys : list α // list.perm xs ys } :=
{ sample := permutation_of xs,
  shrink := λ _, lazy_list.nil }

instance perm'.slim_check {xs : list α} :
  slim_check.sampleable { ys : list α // list.perm ys xs } :=
{ sample := subtype.map id (@list.perm.symm α _) <$> permutation_of xs,
  shrink := λ _, lazy_list.nil }

setup_tactic_parser
open tactic

/--
Print (at most) 10 samples of a given type to stdout for debugging.
-/
def print_samples {t : Type u} [has_repr t] (g : gen t) : io unit := do
xs ← io.run_rand $ uliftable.down $
  do { xs ← (list.range 10).mmap $ g.run ∘ ulift.up,
       pure ⟨xs.map repr⟩ },
xs.mmap' io.put_str_ln

/-- Create a `gen α` expression from the argument of `#sample` -/
meta def mk_generator (e : expr) : tactic (expr × expr) := do
t ← infer_type e,
match t with
| `(gen %%t) := do
  repr_inst ← mk_app ``has_repr [t] >>= mk_instance,
  pure (repr_inst, e)
| _ := do
  samp_inst ← to_expr ``(sampleable_ext %%e) >>= mk_instance,
  repr_inst ← mk_mapp ``sampleable_ext.p_repr [e, samp_inst],
  gen ← mk_mapp ``sampleable_ext.sample [none, samp_inst],
  pure (repr_inst, gen)
end

/--
`#sample my_type`, where `my_type` has an instance of `sampleable`, prints ten random
values of type `my_type` of using an increasing size parameter.

```lean
#sample nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample list int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```
-/
@[user_command]
meta def sample_cmd (_ : parse $ tk "#sample") : lean.parser unit :=
do e ← texpr,
   of_tactic $ do
     e ← i_to_expr e,
     (repr_inst, gen) ← mk_generator e,
     print_samples ← mk_mapp ``print_samples [none, repr_inst, gen],
     sample ← eval_expr (io unit) print_samples,
     unsafe_run_io sample

end slim_check
