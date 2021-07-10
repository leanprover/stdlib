/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.dlist

/-!
# Difference list

This file provides a few results about `dlist`, which is defined in core Lean.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/

/-- Concatenates a list of difference lists to form a single difference list. Similar to
`list.join`. -/
def dlist.join {α : Type*} : list (dlist α) → dlist α
 | [] := dlist.empty
 | (x :: xs) := x ++ dlist.join xs

@[simp] lemma dlist_singleton {α : Type*} {a : α} :
  dlist.singleton a = dlist.lazy_of_list ([a]) := rfl

@[simp] lemma dlist_lazy {α : Type*} {l : list α} :
  dlist.lazy_of_list l = dlist.of_list l := rfl
