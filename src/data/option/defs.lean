/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-!
# Extra definitions on `option`

This file defines more operations involving `option α`. Lemmas about them are located in other
files under `data.option.`.
Other basic operations on `option` are defined in the core library.
-/


namespace option
variables {α : Type*} {β : Type*}

attribute [inline] option.is_some option.is_none

/-- An elimination principle for `option`. It is a nondependent version of `option.rec_on`. -/
@[simp] protected def elim : option α → β → (α → β) → β
| (some x) y f := f x
| none     y f := y

instance has_mem : has_mem α (option α) := ⟨λ a b, b = some a⟩

@[simp] theorem mem_def {a : α} {b : option α} : a ∈ b ↔ b = some a :=
iff.rfl

theorem is_none_iff_eq_none {o : option α} : o.is_none = tt ↔ o = none :=
⟨option.eq_none_of_is_none, λ e, e.symm ▸ rfl⟩

theorem some_inj {a b : α} : some a = some b ↔ a = b := by simp

/--
`o = none` is decidable even if the wrapped type does not have decidable equality.

This is not an instance because it is not definitionally equal to `option.decidable_eq`.
Try to use `o.is_none` or `o.is_some` instead.
-/
@[inline]
def decidable_eq_none {o : option α} : decidable (o = none) :=
decidable_of_decidable_of_iff (bool.decidable_eq _ _) is_none_iff_eq_none

instance decidable_forall_mem {p : α → Prop} [decidable_pred p] :
  ∀ o : option α, decidable (∀ a ∈ o, p a)
| none     := is_true (by simp [false_implies_iff])
| (some a) := if h : p a
  then is_true $ λ o e, some_inj.1 e ▸ h
  else is_false $ mt (λ H, H _ rfl) h

instance decidable_exists_mem {p : α → Prop} [decidable_pred p] :
  ∀ o : option α, decidable (∃ a ∈ o, p a)
| none     := is_false (λ ⟨a, ⟨h, _⟩⟩, by cases h)
| (some a) := if h : p a
  then is_true $ ⟨_, rfl, h⟩
  else is_false $ λ ⟨_, ⟨rfl, hn⟩⟩, h hn

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[reducible] def iget [inhabited α] : option α → α
| (some x) := x
| none     := default α

@[simp] theorem iget_some [inhabited α] {a : α} : (some a).iget = a := rfl

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard (p : α → Prop) [decidable_pred p] (a : α) : option α :=
if p a then some a else none

/-- `filter p o` returns `some a` if `o` is `some a` and `p a` holds, otherwise `none`. -/
def filter (p : α → Prop) [decidable_pred p] (o : option α) : option α :=
o.bind (guard p)

/-- Cast of `option` to `list `. Returns `[a]` if the input is `some a`, and `[]` if it is
`none`. -/
def to_list : option α → list α
| none     := []
| (some a) := [a]

@[simp] theorem mem_to_list {a : α} {o : option α} : a ∈ to_list o ↔ a ∈ o :=
by cases o; simp [to_list, eq_comm]

/-- Two arguments failsafe function. Returns `f a b` if the inputs are `some a` and `some b`, and
"does nothing" otherwise. -/
def lift_or_get (f : α → α → α) : option α → option α → option α
| none     none     := none
| (some a) none     := some a       -- get a
| none     (some b) := some b       -- get b
| (some a) (some b) := some (f a b) -- lift f

instance lift_or_get_comm (f : α → α → α) [h : is_commutative α f] :
  is_commutative (option α) (lift_or_get f) :=
⟨λ a b, by cases a; cases b; simp [lift_or_get, h.comm]⟩

instance lift_or_get_assoc (f : α → α → α) [h : is_associative α f] :
  is_associative (option α) (lift_or_get f) :=
⟨λ a b c, by cases a; cases b; cases c; simp [lift_or_get, h.assoc]⟩

instance lift_or_get_idem (f : α → α → α) [h : is_idempotent α f] :
  is_idempotent (option α) (lift_or_get f) :=
⟨λ a, by cases a; simp [lift_or_get, h.idempotent]⟩

instance lift_or_get_is_left_id (f : α → α → α) :
  is_left_id (option α) (lift_or_get f) none :=
⟨λ a, by cases a; simp [lift_or_get]⟩

instance lift_or_get_is_right_id (f : α → α → α) :
  is_right_id (option α) (lift_or_get f) none :=
⟨λ a, by cases a; simp [lift_or_get]⟩

/-- Lifts a relation `α → β → Prop` to a relation `option α → option β → Prop` by just adding
`none ~ none`. -/
inductive rel (r : α → β → Prop) : option α → option β → Prop
/-- If `a ~ b`, then `some a ~ some b` -/
| some {a b} : r a b → rel (some a) (some b)
/-- `none ~ none` -/
| none       : rel none none

/-- Partial bind. If for some `x : option α`, `f : Π (a : α), a ∈ x → option β` is a
  partial function defined on `a : α` giving an `option β`, where `some a = x`,
  then `pbind x f h` is essentially the same as `bind x f`
  but is defined only when all `x = some a`, using the proof to apply `f`. -/
@[simp] def pbind : Π (x : option α), (Π (a : α), a ∈ x → option β) → option β
| none     _ := none
| (some a) f := f a rfl

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on `a : α` satisfying `p`,
then `pmap f x h` is essentially the same as `map f x` but is defined only when all members of `x`
satisfy `p`, using the proof to apply `f`. -/
@[simp] def pmap {p : α → Prop} (f : Π (a : α), p a → β) :
  Π x : option α, (∀ a ∈ x, p a) → option β
| none     _ := none
| (some a) H := some (f a (H a (mem_def.mpr rfl)))

/-- Flatten an `option` of `option`, a specialization of `mjoin`. -/
@[simp] def join : option (option α) → option α :=
λ x, bind x id

protected def {u v} traverse {F : Type u → Type v} [applicative F] {α β : Type*} (f : α → F β) :
  option α → F (option β)
| none     := pure none
| (some x) := some <$> f x

/- By analogy with `monad.sequence` in `init/category/combinators.lean`. -/

/-- If you maybe have a monadic computation in a `[monad m]` which produces a term of type `α`, then
there is a naturally associated way to always perform a computation in `m` which maybe produces a
result. -/
def {u v} maybe {m : Type u → Type v} [monad m] {α : Type u} : option (m α) → m (option α)
| none      := return none
| (some fn) := some <$> fn

/-- Map a monadic function `f : α → m β` over an `o : option α`, maybe producing a result. -/
def {u v w} mmap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β)
  (o : option α) : m (option β) := (o.map f).maybe

/-- A monadic analogue of `option.elim`. -/
def melim {α β : Type*} {m : Type* → Type*} [monad m] (x : m (option α)) (y : m β) (z : α → m β) :
  m β :=
x >>= λ o, option.elim o y z

/-- A monadic analogue of `option.get_or_else`. -/
def mget_or_else {α : Type*} {m : Type* → Type*} [monad m] (x : m (option α)) (y : m α) : m α :=
melim x y pure

end option
