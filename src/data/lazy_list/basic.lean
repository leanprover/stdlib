/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for lazy_lists.
-/
import control.traversable.equiv
import control.traversable.instances
import data.lazy_list

/-!
## Definitions on lazy lists

This file contains various definitions and proofs on lazy lists.

TODO: move the `lazy_list.lean` file from core to mathlib.
-/

universes u

namespace thunk

/-- Creates a thunk with a (non-lazy) constant value. -/
def mk {α} (x : α) : thunk α := λ _, x

instance {α : Type u} [decidable_eq α] : decidable_eq (thunk α) | a b :=
have a = b ↔ a () = b (), from ⟨by cc, by intro; ext x; cases x; assumption⟩,
by rw this; apply_instance

end thunk

namespace lazy_list

open function

/-- Isomorphism between strict and lazy lists. -/
def list_equiv_lazy_list (α : Type*) : list α ≃ lazy_list α :=
{ to_fun := lazy_list.of_list,
  inv_fun := lazy_list.to_list,
  right_inv := by { intro, induction x, refl, simp! [*],
                    ext, cases x, refl },
  left_inv := by { intro, induction x, refl, simp! [*] } }

instance {α : Type u} [decidable_eq α] : decidable_eq (lazy_list α)
| nil nil := is_true rfl
| (cons x xs) (cons y ys) :=
  if h : x = y then
    match decidable_eq (xs ()) (ys ()) with
    | is_false h2 := is_false (by intro; cc)
    | is_true h2 :=
      have xs = ys, by ext u; cases u; assumption,
      is_true (by cc)
    end
  else
    is_false (by intro; cc)
| nil (cons _ _) := is_false (by cc)
| (cons _ _) nil := is_false (by cc)

/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [applicative m] {α β : Type u}
    (f : α → m β) : lazy_list α → m (lazy_list β)
| lazy_list.nil := pure lazy_list.nil
| (lazy_list.cons x xs) := lazy_list.cons <$> f x <*> (thunk.mk <$> traverse (xs ()))

instance : traversable lazy_list :=
{ map := @lazy_list.traverse id _,
  traverse := @lazy_list.traverse }

instance : is_lawful_traversable lazy_list :=
begin
  apply equiv.is_lawful_traversable' list_equiv_lazy_list;
  intros ; resetI; ext,
  { induction x, refl,
    simp! [equiv.map,functor.map] at *,
    simp [*], refl, },
  { induction x, refl,
    simp! [equiv.map,functor.map_const] at *,
    simp [*], refl, },
  { induction x,
    { simp! [traversable.traverse,equiv.traverse] with functor_norm, refl },
    simp! [equiv.map,functor.map_const,traversable.traverse] at *, rw x_ih,
    dsimp [list_equiv_lazy_list,equiv.traverse,to_list,traversable.traverse,list.traverse],
    simp! with functor_norm, refl },
end

/-- `init xs`, if `xs` non-empty, drops the last element of the list.
Otherwise, return the empty list. -/
def init {α} : lazy_list α → lazy_list α
| lazy_list.nil := lazy_list.nil
| (lazy_list.cons x xs) :=
  let xs' := xs () in
  match xs' with
  | lazy_list.nil := lazy_list.nil
  | (lazy_list.cons _ _) := lazy_list.cons x (init xs')
  end

/-- Return the first object contained in the list that satisfies
predicate `p` -/
def find {α} (p : α → Prop) [decidable_pred p] : lazy_list α → option α
| nil        := none
| (cons h t) := if p h then some h else find (t ())

/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate. -/
def interleave {α} : lazy_list α → lazy_list α → lazy_list α
| lazy_list.nil xs := xs
| a@(lazy_list.cons x xs) lazy_list.nil := a
| (lazy_list.cons x xs) (lazy_list.cons y ys) :=
  lazy_list.cons x (lazy_list.cons y (interleave (xs ()) (ys ())))

/-- `interleave_all (xs::ys::zs::xss)` creates a list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on. -/
def interleave_all {α} : list (lazy_list α) → lazy_list α
| [] := lazy_list.nil
| (x :: xs) := interleave x (interleave_all xs)

/-- Monadic bind operation for `lazy_list`. -/
protected def bind {α β} : lazy_list α → (α → lazy_list β) → lazy_list β
| lazy_list.nil _ := lazy_list.nil
| (lazy_list.cons x xs) f := lazy_list.append (f x) (bind (xs ()) f)

/-- Reverse the order of a `lazy_list`.
It is done by converting to a `list` first because reversal involves evaluating all
the list and if the list is all evaluated, `list` is a better representation for
it than a series of thunks. -/
def reverse {α} (xs : lazy_list α) : lazy_list α :=
of_list xs.to_list.reverse

instance : monad lazy_list :=
{ pure := @lazy_list.singleton,
  bind := @lazy_list.bind }

lemma append_nil {α} (xs : lazy_list α) : xs.append lazy_list.nil = xs :=
begin
  induction xs, refl,
  simp [lazy_list.append, xs_ih],
  ext, congr,
end

lemma append_assoc {α} (xs ys zs : lazy_list α) :
  (xs.append ys).append zs = xs.append (ys.append zs) :=
by induction xs; simp [append, *]

lemma append_bind {α β} (xs : lazy_list α) (ys : thunk (lazy_list α)) (f : α → lazy_list β) :
  (@lazy_list.append _ xs ys).bind f = (xs.bind f).append ((ys ()).bind f) :=
by induction xs; simp [lazy_list.bind, append, *, append_assoc, append, lazy_list.bind]

instance : is_lawful_monad lazy_list :=
{ pure_bind := by { intros, apply append_nil },
  bind_assoc := by { intros, dsimp [(>>=)], induction x; simp [lazy_list.bind, append_bind, *], },
  id_map :=
  begin
    intros,
    simp [(<$>)],
    induction x; simp [lazy_list.bind, *, singleton, append],
    ext ⟨ ⟩, refl,
  end }

/-- Try applying function `f` to every element of a `lazy_list` and
return the result of the first attempt that succeeds. -/
def mfirst {m} [alternative m] {α β} (f : α → m β) : lazy_list α → m β
| nil := failure
| (cons x xs) :=
  f x <|> mfirst (xs ())

/-- Membership in lazy lists -/
protected def mem {α} (x : α) : lazy_list α → Prop
| lazy_list.nil := false
| (lazy_list.cons y ys) := x = y ∨ mem (ys ())

instance {α} : has_mem α (lazy_list α) :=
⟨ lazy_list.mem ⟩

instance mem.decidable {α} [decidable_eq α] (x : α) : Π xs : lazy_list α, decidable (x ∈ xs)
| lazy_list.nil := decidable.false
| (lazy_list.cons y ys) :=
  if h : x = y
    then decidable.is_true (or.inl h)
    else decidable_of_decidable_of_iff (mem.decidable (ys ())) (by simp [*, (∈), lazy_list.mem])

@[simp]
lemma mem_nil {α} (x : α) : x ∈ @lazy_list.nil α ↔ false := iff.rfl

@[simp]
lemma mem_cons {α} (x y : α) (ys : thunk (lazy_list α)) :
  x ∈ @lazy_list.cons α y ys ↔ x = y ∨ x ∈ ys () := iff.rfl

theorem forall_mem_cons {α} {p : α → Prop} {a : α} {l : thunk (lazy_list α)} :
  (∀ x ∈ @lazy_list.cons _ a l, p x) ↔ p a ∧ ∀ x ∈ l (), p x :=
by simp only [has_mem.mem, lazy_list.mem, or_imp_distrib, forall_and_distrib, forall_eq]

/-! ### map for partial functions -/

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {α β} {p : α → Prop} (f : Π a, p a → β) :
  Π l : lazy_list α, (∀ a ∈ l, p a) → lazy_list β
| lazy_list.nil         H := lazy_list.nil
| (lazy_list.cons x xs) H := lazy_list.cons (f x (forall_mem_cons.1 H).1)
                               (pmap (xs ()) (forall_mem_cons.1 H).2)

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `lazy_list`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α} (l : lazy_list α) : lazy_list {x // x ∈ l} := pmap subtype.mk l (λ a, id)

instance {α} [has_repr α] : has_repr (lazy_list α) :=
⟨ λ xs, repr xs.to_list ⟩

end lazy_list
