/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import tactic.lint

/-!
# Lazy lists

The type `lazy_list α` is a lazy list with elements of type `α`.
In the VM, these are potentially infinite lists
where all elements after the first are computed on-demand.
(This is only useful for execution in the VM,
logically we can prove that `lazy_list α` is isomorphic to `list α`.)
-/

universes u v w

/--
Lazy list.
All elements (except the first) are computed lazily.
-/
inductive lazy_list (α : Type u) : Type u
| nil : lazy_list
| cons (hd : α) (tl : thunk lazy_list) : lazy_list

namespace lazy_list
variables {α : Type u} {β : Type v} {δ : Type w}

instance : inhabited (lazy_list α) := ⟨nil⟩

/-- The singleton lazy list.  -/
def singleton : α → lazy_list α
| a := cons a nil

/-- Constructs a lazy list from a list. -/
def of_list : list α → lazy_list α
| []     := nil
| (h::t) := cons h (of_list t)

/--
Converts a lazy list to a list.
If the lazy list is infinite,
then this function does not terminate.
-/
def to_list : lazy_list α → list α
| nil        := []
| (cons h t) := h :: to_list (t ())

/--
Returns the first element of the lazy list,
or `default α` if the lazy list is empty.
-/
def head [inhabited α] : lazy_list α → α
| nil        := default α
| (cons h t) := h

/--
Removes the first element of the lazy list.
-/
def tail : lazy_list α → lazy_list α
| nil        := nil
| (cons h t) := t ()

/-- Appends two lazy lists.  -/
def append : lazy_list α → thunk (lazy_list α) → lazy_list α
| nil        l  := l ()
| (cons h t) l  := cons h (@append (t ()) l)

/-- Maps a function over a lazy list. -/
def map (f : α → β) : lazy_list α → lazy_list β
| nil        := nil
| (cons h t) := cons (f h) (map (t ()))

/--
Maps a binary function over two lazy list.
Like `lazy_list.zip`, the result is only as long as the smaller input.
-/
def map₂ (f : α → β → δ) : lazy_list α → lazy_list β → lazy_list δ
| nil          _            := nil
| _            nil          := nil
| (cons h₁ t₁) (cons h₂ t₂) := cons (f h₁ h₂) (map₂ (t₁ ()) (t₂ ()))

/-- Zips two lazy lists. -/
def zip : lazy_list α → lazy_list β → lazy_list (α × β) :=
map₂ prod.mk

/-- The monadic join operation for lazy lists. -/
def join : lazy_list (lazy_list α) → lazy_list α
| nil        := nil
| (cons h t) := append h (join (t ()))

/--
Maps a function over a lazy list.
Same as `lazy_list.map`, but with swapped arguments.
-/
def for (l : lazy_list α) (f : α → β) : lazy_list β :=
map f l

/-- The list containing the first `n` elements of a lazy list.  -/
def approx : nat → lazy_list α → list α
| 0     l          := []
| _     nil        := []
| (a+1) (cons h t) := h :: approx a (t ())

/--
The lazy list of all elements satisfying the predicate.
If the lazy list is infinite and none of the elements satisfy the predicate,
then this function will not terminate.
-/
def filter (p : α → Prop) [decidable_pred p] : lazy_list α → lazy_list α
| nil        := nil
| (cons h t) := if p h then cons h (filter (t ())) else filter (t ())

/-- The nth element of a lazy list as an option (like `list.nth`). -/
def nth : lazy_list α → nat → option α
| nil        n     := none
| (cons a l) 0     := some a
| (cons a l) (n+1) := nth (l ()) n

/--
The infinite lazy list `[x, f x, f (f x), ...]` of iterates of a function.
This definition is meta because it creates an infinite list.
-/
meta def iterates (f : α → α) : α → lazy_list α
| x := cons x (iterates (f x))

/-- The infinite lazy list `[i, i+1, i+2, ...]` -/
meta def iota (i : nat) : lazy_list nat :=
iterates nat.succ i

end lazy_list
