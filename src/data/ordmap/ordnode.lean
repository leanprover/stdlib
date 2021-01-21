/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.psub

/-!
# Ordered sets

This file defines a data structure for ordered sets, supporting a
variety of useful operations including insertion and deletion,
logarithmic time lookup, set operations, folds,
and conversion from lists.

The `ordnode α` operations all assume that `α` has the structure of
a total preorder, meaning a `≤` operation that is

* Transitive: `x ≤ y → y ≤ z → x ≤ z`
* Reflexive: `x ≤ x`
* Total: `x ≤ y ∨ y ≤ x`

For example, in order to use this data structure as a map type, one
can store pairs `(k, v)` where `(k, v) ≤ (k', v')` is defined to mean
`k ≤ k'` (assuming that the key values are linearly ordered).

Two values `x,y` are equivalent if `x ≤ y` and `y ≤ x`. An `ordnode α`
maintains the invariant that it never stores two equivalent nodes;
the insertion operation comes with two variants depending on whether
you want to keep the old value or the new value in case you insert a value
that is equivalent to one in the set.

The operations in this file are not verified, in the sense that they provide
"raw operations" that work for programming purposes but the invariants
are not explicitly in the structure. See `ordset` for a verified version
of this data structure.

## Main definitions

* `ordnode α`: A set of values of type `α`

## Implementation notes

Based on weight balanced trees:

 * Stephen Adams, "Efficient sets: a balancing act",
   Journal of Functional Programming 3(4):553-562, October 1993,
   <http://www.swiss.ai.mit.edu/~adams/BB/>.
 * J. Nievergelt and E.M. Reingold,
   "Binary search trees of bounded balance",
   SIAM journal of computing 2(1), March 1973.

Ported from Haskell's `Data.Set`.

## Tags

ordered map, ordered set, data structure

-/

universes u

/-- An `ordnode α` is a finite set of values, represented as a tree.
  The operations on this type maintain that the tree is balanced
  and correctly stores subtree sizes at each level. -/
inductive ordnode (α : Type u) : Type u
| nil {} : ordnode
| node (size : ℕ) (l : ordnode) (x : α) (r : ordnode) : ordnode

namespace ordnode
variable {α : Type u}

instance : has_emptyc (ordnode α) := ⟨nil⟩
instance : inhabited (ordnode α) := ⟨nil⟩

/-- **Internal use only**

The maximal relative difference between the sizes of
two trees, it corresponds with the `w` in Adams' paper.

According to the Haskell comment, only `(delta, ratio)` settings
of `(3, 2)` and `(4, 2)` will work, and the proofs in
`ordset.lean` assume `delta := 3` and `ratio := 2`. -/
@[inline] def delta := 3

/-- **Internal use only**

The ratio between an outer and inner sibling of the
heavier subtree in an unbalanced setting. It determines
whether a double or single rotation should be performed
to restore balance. It is corresponds with the inverse
of `α` in Adam's article. -/
@[inline] def ratio := 2

/-- O(1). Construct a singleton set containing value `a`.

     singleton 3 = {3} -/
@[inline] protected def singleton (a : α) : ordnode α := node 1 nil a nil
local prefix `ι`:max := ordnode.singleton

instance : has_singleton α (ordnode α) := ⟨ordnode.singleton⟩

/-- O(1). Get the size of the set.

     size {2, 1, 1, 4} = 3  -/
@[inline, simp] def size : ordnode α → ℕ
| nil := 0
| (node sz _ _ _) := sz

/-- O(1). Is the set empty?

     empty ∅ = tt
     empty {1, 2, 3} = ff -/
@[inline] def empty : ordnode α → bool
| nil := tt
| (node _ _ _ _) := ff

/-- **Internal use only**, because it violates the BST property on the original order.

O(n). The dual of a tree is a tree with its left and right sides reversed throughout.
The dual of a valid BST is valid under the dual order. This is convenient for exploiting
symmetries in the algorithms. -/
@[simp] def dual : ordnode α → ordnode α
| nil := nil
| (node s l x r) := node s (dual r) x (dual l)

/-- **Internal use only**

O(1). Construct a node with the correct size information, without rebalancing. -/
@[inline, reducible] def node' (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
node (size l + size r + 1) l x r

/-- Basic pretty printing for `ordnode α` that shows the structure of the tree.

     repr {3, 1, 2, 4} = ((∅ 1 ∅) 2 ((∅ 3 ∅) 4 ∅)) -/
def repr {α} [has_repr α] : ordnode α → string
| nil := "∅"
| (node _ l x r) := "(" ++ repr l ++ " " ++ _root_.repr x ++ " " ++ repr r ++ ")"

instance {α} [has_repr α] : has_repr (ordnode α) := ⟨repr⟩

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had its left
side grow by 1, or its right side shrink by 1. -/
-- Note: The function has been written with tactics to avoid extra junk
def balance_l (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
by clean begin
  cases id r with rs,
  { cases id l with ls ll lx lr,
    { exact ι x },
    { cases id ll with lls,
      { cases lr with _ _ lrx,
        { exact node 2 l x nil },
        { exact node 3 (ι lx) lrx (ι x) } },
      { cases id lr with lrs lrl lrx lrr,
        { exact node 3 ll lx (ι x) },
        { exact if lrs < ratio * lls then
            node (ls+1) ll lx (node (lrs+1) lr x nil)
          else
            node (ls+1)
              (node (lls + size lrl + 1) ll lx lrl) lrx
              (node (size lrr + 1) lrr x nil) } } } },
  { cases id l with ls ll lx lr,
    { exact node (rs+1) nil x r },
    { refine if ls > delta * rs then _ else node (ls + rs + 1) l x r,
      cases id ll with lls, {exact nil /-should not happen-/},
      cases id lr with lrs lrl lrx lrr, {exact nil /-should not happen-/},
      exact if lrs < ratio * lls then
        node (ls + rs + 1) ll lx (node (rs + lrs + 1) lr x r)
      else
        node (ls + rs + 1)
          (node (lls + size lrl + 1) ll lx lrl) lrx
          (node (size lrr + rs + 1) lrr x r) } }
end

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had its right
side grow by 1, or its left side shrink by 1. -/
def balance_r (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
by clean begin
  cases id l with ls,
  { cases id r with rs rl rx rr,
    { exact ι x },
    { cases id rr with rrs,
      { cases rl with _ _ rlx,
        { exact node 2 nil x r },
        { exact node 3 (ι x) rlx (ι rx) } },
      { cases id rl with rls rll rlx rlr,
        { exact node 3 (ι x) rx rr },
        { exact if rls < ratio * rrs then
            node (rs+1) (node (rls+1) nil x rl) rx rr
          else
            node (rs+1)
              (node (size rll + 1) nil x rll) rlx
              (node (size rlr + rrs + 1) rlr rx rr) } } } },
  { cases id r with rs rl rx rr,
    { exact node (ls+1) l x nil },
    { refine if rs > delta * ls then _ else node (ls + rs + 1) l x r,
      cases id rr with rrs, {exact nil /-should not happen-/},
      cases id rl with rls rll rlx rlr, {exact nil /-should not happen-/},
      exact if rls < ratio * rrs then
        node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
      else
        node (ls + rs + 1)
          (node (ls + size rll + 1) l x rll) rlx
          (node (size rlr + rrs + 1) rlr rx rr) } }
end

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had one side change
by at most 1. -/
def balance (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
by clean begin
  cases id l with ls ll lx lr,
  { cases id r with rs rl rx rr,
    { exact ι x },
    { cases id rl with rls rll rlx rlr,
      { cases id rr,
        { exact node 2 nil x r },
        { exact node 3 (ι x) rx rr } },
      { cases id rr with rrs,
        { exact node 3 (ι x) rlx (ι rx) },
        { exact if rls < ratio * rrs then
            node (rs+1) (node (rls+1) nil x rl) rx rr
          else
            node (rs+1)
              (node (size rll + 1) nil x rll) rlx
              (node (size rlr + rrs + 1) rlr rx rr) } } } },
  { cases id r with rs rl rx rr,
    { cases id ll with lls,
      { cases lr with _ _ lrx,
        { exact node 2 l x nil },
        { exact node 3 (ι lx) lrx (ι x) } },
      { cases id lr with lrs lrl lrx lrr,
        { exact node 3 ll lx (ι x) },
        { exact if lrs < ratio * lls then
            node (ls+1) ll lx (node (lrs+1) lr x nil)
          else
            node (ls+1)
              (node (lls + size lrl + 1) ll lx lrl) lrx
              (node (size lrr + 1) lrr x nil) } } },
    { refine
        if delta * ls < rs then _ else
        if delta * rs < ls then _ else
        node (ls+rs+1) l x r,
      { cases id rl with rls rll rlx rlr, {exact nil /-should not happen-/},
        cases id rr with rrs, {exact nil /-should not happen-/},
        exact if rls < ratio * rrs then
          node (ls+rs+1) (node (ls+rls+1) l x rl) rx rr
        else
          node (ls+rs+1)
            (node (ls + size rll + 1) l x rll) rlx
            (node (size rlr + rrs + 1) rlr rx rr) },
      { cases id ll with lls, {exact nil /-should not happen-/},
        cases id lr with lrs lrl lrx lrr, {exact nil /-should not happen-/},
        exact if lrs < ratio * lls then
          node (ls+rs+1) ll lx (node (lrs+rs+1) lr x r)
        else
          node (ls+rs+1)
            (node (lls + size lrl + 1) ll lx lrl) lrx
            (node (size lrr + rs + 1) lrr x r) } } }
end

/-- O(n). Does every element of the map satisfy property `P`?

     all (λ x, x < 5) {1, 2, 3} = true
     all (λ x, x < 5) {1, 2, 3, 5} = false -/
def all (P : α → Prop) : ordnode α → Prop
| nil := true
| (node _ l x r) := all l ∧ P x ∧ all r

instance all.decidable {P : α → Prop} [decidable_pred P] (t) : decidable (all P t) :=
by induction t; dunfold all; resetI; apply_instance

/-- O(n). Does any element of the map satisfy property `P`?

     any (λ x, x < 2) {1, 2, 3} = true
     any (λ x, x < 2) {2, 3, 5} = false -/
def any (P : α → Prop) : ordnode α → Prop
| nil := false
| (node _ l x r) := any l ∨ P x ∨ any r

instance any.decidable {P : α → Prop} [decidable_pred P] (t) : decidable (any P t) :=
by induction t; dunfold any; resetI; apply_instance

/-- O(n). Exact membership in the set. This is useful primarily for stating
correctness properties; use `∈` for a version that actually uses the BST property
of the tree.

    emem 2 {1, 2, 3} = true
    emem 4 {1, 2, 3} = false -/
def emem (x : α) : ordnode α → Prop := any (eq x)

instance emem.decidable [decidable_eq α] (x : α) : ∀ t, decidable (emem x t) :=
any.decidable

/-- O(n). Approximate membership in the set, that is, whether some element in the
set is equivalent to this one in the preorder. This is useful primarily for stating
correctness properties; use `∈` for a version that actually uses the BST property
of the tree.

    amem 2 {1, 2, 3} = true
    amem 4 {1, 2, 3} = false

To see the difference with `emem`, we need a preorder that is not a partial order.
For example, suppose we compare pairs of numbers using only their first coordinate. Then:

    emem (0, 1) {(0, 0), (1, 2)} = false
    amem (0, 1) {(0, 0), (1, 2)} = true
    (0, 1) ∈ {(0, 0), (1, 2)} = true

The `∈` relation is equivalent to `amem` as long as the `ordnode` is well formed,
and should always be used instead of `amem`. -/
def amem [has_le α] (x : α) : ordnode α → Prop := any (λ y, x ≤ y ∧ y ≤ x)

instance amem.decidable [has_le α] [@decidable_rel α (≤)] (x : α) : ∀ t, decidable (amem x t) :=
any.decidable

/-- O(log n). Return the minimum element of the tree, or the provided default value.

     find_min' 37 {1, 2, 3} = 1
     find_min' 37 ∅ = 37 -/
def find_min' : ordnode α → α → α
| nil x := x
| (node _ l x r) _ := find_min' l x

/-- O(log n). Return the minimum element of the tree, if it exists.

     find_min {1, 2, 3} = some 1
     find_min ∅ = none -/
def find_min : ordnode α → option α
| nil := none
| (node _ l x r) := some (find_min' l x)

/-- O(log n). Return the maximum element of the tree, or the provided default value.

     find_max' 37 {1, 2, 3} = 3
     find_max' 37 ∅ = 37 -/
def find_max' : α → ordnode α → α
| x nil := x
| _ (node _ l x r) := find_max' x r

/-- O(log n). Return the maximum element of the tree, if it exists.

     find_max {1, 2, 3} = some 3
     find_max ∅ = none -/
def find_max : ordnode α → option α
| nil := none
| (node _ l x r) := some (find_max' x r)

/-- O(log n). Remove the minimum element from the tree, or do nothing if it is already empty.

     erase_min {1, 2, 3} = {2, 3}
     erase_min ∅ = ∅ -/
def erase_min : ordnode α → ordnode α
| nil := nil
| (node _ nil x r) := r
| (node _ l x r) := balance_r (erase_min l) x r

/-- O(log n). Remove the maximum element from the tree, or do nothing if it is already empty.

     erase_max {1, 2, 3} = {1, 2}
     erase_max ∅ = ∅ -/
def erase_max : ordnode α → ordnode α
| nil := nil
| (node _ l x nil) := l
| (node _ l x r) := balance_l l x (erase_max r)

/-- **Internal use only**, because it requires a balancing constraint on the inputs.

O(log n). Extract and remove the minimum element from a nonempty tree. -/
def split_min' : ordnode α → α → ordnode α → α × ordnode α
| nil x r := (x, r)
| (node _ ll lx lr) x r :=
  let (xm, l') := split_min' ll lx lr in
  (xm, balance_r l' x r)

/-- O(log n). Extract and remove the minimum element from the tree, if it exists.

     split_min {1, 2, 3} = some (1, {2, 3})
     split_min ∅ = none -/
def split_min : ordnode α → option (α × ordnode α)
| nil := none
| (node _ l x r) := split_min' l x r

/-- **Internal use only**, because it requires a balancing constraint on the inputs.

O(log n). Extract and remove the maximum element from a nonempty tree. -/
def split_max' : ordnode α → α → ordnode α → ordnode α × α
| l x nil := (l, x)
| l x (node _ rl rx rr) :=
  let (r', xm) := split_max' rl rx rr in
  (balance_l l x r', xm)

/-- O(log n). Extract and remove the maximum element from the tree, if it exists.

     split_max {1, 2, 3} = some ({1, 2}, 3)
     split_max ∅ = none -/
def split_max : ordnode α → option (ordnode α × α)
| nil := none
| (node _ x l r) := split_max' x l r

/-- **Internal use only**

O(log(m+n)). Concatenate two trees that are balanced and ordered with respect to each other. -/
def glue : ordnode α → ordnode α → ordnode α
| nil r := r
| l@(node _ _ _ _) nil := l
| l@(node sl ll lx lr) r@(node sr rl rx rr) :=
  if sl > sr then
    let (l', m) := split_max' ll lx lr in balance_r l' m r
  else
    let (m, r') := split_min' rl rx rr in balance_l l m r'

/-- O(log(m+n)). Concatenate two trees that are ordered with respect to each other.

     merge {1, 2} {3, 4} = {1, 2, 3, 4}
     merge {3, 4} {1, 2} = precondition violation -/
def merge (l : ordnode α) : ordnode α → ordnode α :=
ordnode.rec_on l (λ r, r) $ λ ls ll lx lr IHll IHlr r,
ordnode.rec_on r (node ls ll lx lr) $ λ rs rl rx rr IHrl IHrr,
if delta * ls < rs then
  balance_l IHrl rx rr
else if delta * rs < ls then
  balance_r ll lx (IHlr $ node rs rl rx rr)
else glue (node ls ll lx lr) (node rs rl rx rr)

/-- O(log n). Insert an element above all the others, without any comparisons.
(Assumes that the element is in fact above all the others).

    insert_max {1, 2} 4 = {1, 2, 4}
    insert_max {1, 2} 0 = precondition violation -/
def insert_max : ordnode α → α → ordnode α
| nil x := ι x
| (node _ l y r) x := balance_r l y (insert_max r x)

/-- O(log n). Insert an element below all the others, without any comparisons.
(Assumes that the element is in fact below all the others).

    insert_min {1, 2} 0 = {0, 1, 2}
    insert_min {1, 2} 4 = precondition violation -/
def insert_min (x : α) : ordnode α → ordnode α
| nil := ι x
| (node _ l y r) := balance_r (insert_min l) y r

/-- O(log(m+n)). Build a tree from an element between two trees, without any
assumption on the relative sizes.

    link {1, 2} 4 {5, 6} = {1, 2, 4, 5, 6}
    link {1, 3} 2 {5} = precondition violation -/
def link (l : ordnode α) (x : α) : ordnode α → ordnode α :=
ordnode.rec_on l (insert_min x) $ λ ls ll lx lr IHll IHlr r,
ordnode.rec_on r (insert_max l x) $ λ rs rl rx rr IHrl IHrr,
if delta * ls < rs then
  balance_l IHrl rx rr
else if delta * rs < ls then
  balance_r ll lx (IHlr r)
else node' l x r

/-- O(n). Filter the elements of a tree satisfying a predicate.

     filter (λ x, x < 3) {1, 2, 4} = {1, 2}
     filter (λ x, x > 5) {1, 2, 4} = ∅ -/
def filter (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α
| nil := nil
| (node _ l x r) :=
  if p x then link (filter l) x (filter r)
  else merge (filter l) (filter r)

/-- O(n). Split the elements of a tree into those satisfying, and not satisfying, a predicate.

     partition (λ x, x < 3) {1, 2, 4} = ({1, 2}, {3}) -/
def partition (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α × ordnode α
| nil := (nil, nil)
| (node _ l x r) :=
  let (l₁, l₂) := partition l, (r₁, r₂) := partition r in
  if p x then (link l₁ x r₁, merge l₂ r₂)
  else (merge l₁ r₁, link l₂ x r₂)

/-- O(n). Map a function across a tree, without changing the structure. Only valid when
the function is strictly monotonic, i.e. `x < y → f x < f y`.

     partition (λ x, x + 2) {1, 2, 4} = {2, 3, 6}
     partition (λ x : ℕ, x - 2) {1, 2, 4} = precondition violation -/
def map {β} (f : α → β) : ordnode α → ordnode β
| nil := nil
| (node s l x r) := node s (map l) (f x) (map r)

/-- O(n). Fold a function across the structure of a tree.

     fold z f {1, 2, 4} = f (f z 1 z) 2 (f z 4 z)

The exact structure of function applications depends on the tree and so
is unspecified. -/
def fold {β} (z : β) (f : β → α → β → β) : ordnode α → β
| nil := z
| (node _ l x r) := f (fold l) x (fold r)

/-- O(n). Fold a function from left to right (in increasing order) across the tree.

     foldl f z {1, 2, 4} = f (f (f z 1) 2) 4 -/
def foldl {β} (f : β → α → β) : β → ordnode α → β
| z nil := z
| z (node _ l x r) := foldl (f (foldl z l) x) r

/-- O(n). Fold a function from right to left (in decreasing order) across the tree.

     foldl f {1, 2, 4} z = f 1 (f 2 (f 4 z)) -/
def foldr {β} (f : α → β → β) : ordnode α → β → β
| nil z := z
| (node _ l x r) z := foldr l (f x (foldr r z))

/-- O(n). Build a list of elements in ascending order from the tree.

     to_list {1, 2, 4} = [1, 2, 4]
     to_list {2, 1, 1, 4} = [1, 2, 4] -/
def to_list (t : ordnode α) : list α := foldr list.cons t []

/-- O(n). Build a list of elements in descending order from the tree.

     to_rev_list {1, 2, 4} = [4, 2, 1]
     to_rev_list {2, 1, 1, 4} = [4, 2, 1] -/
def to_rev_list (t : ordnode α) : list α := foldl (flip list.cons) [] t

instance [has_to_string α] : has_to_string (ordnode α) :=
⟨λ t, "{" ++ string.intercalate ", " (t.to_list.map to_string) ++ "}"⟩

meta instance [has_to_format α] : has_to_format (ordnode α) :=
⟨λ t, "{" ++ format.intercalate ", " (t.to_list.map to_fmt) ++ "}"⟩

/-- O(n). True if the trees have the same elements, ignoring structural differences.

     equiv {1, 2, 4} {2, 1, 1, 4} = true
     equiv {1, 2, 4} {1, 2, 3} = false -/
def equiv (t₁ t₂ : ordnode α) : Prop :=
t₁.size = t₂.size ∧ t₁.to_list = t₂.to_list

instance [decidable_eq α] : decidable_rel (@equiv α) := λ t₁ t₂, and.decidable

/-- O(2^n). Constructs the powerset of a given set, that is, the set of all subsets.

     powerset {1, 2, 3} = {∅, {1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}} -/
def powerset (t : ordnode α) : ordnode (ordnode α) :=
insert_min nil $ foldr (λ x ts, glue (insert_min (ι x) (map (insert_min x) ts)) ts) t nil

/-- O(m*n). The cartesian product of two sets: `(a, b) ∈ s.prod t` iff `a ∈ s` and `b ∈ t`.

     prod {1, 2} {2, 3} = {(1, 2), (1, 3), (2, 2), (2, 3)} -/
protected def prod {β} (t₁ : ordnode α) (t₂ : ordnode β) : ordnode (α × β) :=
fold nil (λ s₁ a s₂, merge s₁ $ merge (map (prod.mk a) t₂) s₂) t₁

/-- O(m+n). Build a set on the disjoint union by combining sets on the factors.
`inl a ∈ s.copair t` iff `a ∈ s`, and `inr b ∈ s.copair t` iff `b ∈ t`.

    copair {1, 2} {2, 3} = {inl 1, inl 2, inr 2, inr 3} -/
protected def copair {β} (t₁ : ordnode α) (t₂ : ordnode β) : ordnode (α ⊕ β) :=
merge (map sum.inl t₁) (map sum.inr t₂)

/-- O(n). Map a partial function across a set. The result depends on a proof
that the function is defined on all members of the set.

    pmap (fin.mk : ∀ n, n < 4 → fin 4) {1, 2} H = {(1 : fin 4), (2 : fin 4)} -/
def pmap {P : α → Prop} {β} (f : ∀ a, P a → β) : ∀ t : ordnode α, all P t → ordnode β
| nil _ := nil
| (node s l x r) ⟨hl, hx, hr⟩ := node s (pmap l hl) (f x hx) (pmap r hr)

/-- O(n). "Attach" the information that every element of `t` satisfies property
P to these elements inside the set, producing a set in the subtype.

    attach' (λ x, x < 4) {1, 2} H = ({1, 2} : ordnode {x // x<4}) -/
def attach' {P : α → Prop} : ∀ t, all P t → ordnode {a // P a} := pmap subtype.mk

/-- O(log n). Get the `i`th element of the set, by its index from left to right.

     nth {a, b, c, d} 2 = some c
     nth {a, b, c, d} 5 = none -/
def nth : ordnode α → ℕ → option α
| nil i := none
| (node _ l x r) i :=
  match nat.psub' i (size l) with
  | none         := nth l i
  | some 0       := some x
  | some (j + 1) := nth r j
  end

/-- O(log n). Remove the `i`th element of the set, by its index from left to right.

     remove_nth {a, b, c, d} 2 = {a, b, d}
     remove_nth {a, b, c, d} 5 = {a, b, c, d} -/
def remove_nth : ordnode α → ℕ → ordnode α
| nil i := nil
| (node _ l x r) i :=
  match nat.psub' i (size l) with
  | none         := balance_r (remove_nth l i) x r
  | some 0       := glue l r
  | some (j + 1) := balance_l l x (remove_nth r j)
  end

/-- Auxiliary definition for `take`. (Can also be used in lieu of `take` if you know the
index is within the range of the data structure.)

    take_aux {a, b, c, d} 2 = {a, b}
    take_aux {a, b, c, d} 5 = {a, b, c, d} -/
def take_aux : ordnode α → ℕ → ordnode α
| nil i := nil
| (node _ l x r) i :=
  if i = 0 then nil else
  match nat.psub' i (size l) with
  | none         := take_aux l i
  | some 0       := l
  | some (j + 1) := link l x (take_aux r j)
  end

/-- O(log n). Get the first `i` elements of the set, counted from the left.

     take 2 {a, b, c, d} = {a, b}
     take 5 {a, b, c, d} = {a, b, c, d} -/
def take (i : ℕ) (t : ordnode α) : ordnode α :=
if size t ≤ i then t else take_aux t i

/-- Auxiliary definition for `drop`. (Can also be used in lieu of `drop` if you know the
index is within the range of the data structure.)

    drop_aux {a, b, c, d} 2 = {c, d}
    drop_aux {a, b, c, d} 5 = ∅ -/
def drop_aux : ordnode α → ℕ → ordnode α
| nil i := nil
| t@(node _ l x r) i :=
  if i = 0 then t else
  match nat.psub' i (size l) with
  | none         := link (drop_aux l i) x r
  | some 0       := insert_min x r
  | some (j + 1) := drop_aux r j
  end

/-- O(log n). Remove the first `i` elements of the set, counted from the left.

     drop 2 {a, b, c, d} = {c, d}
     drop 5 {a, b, c, d} = ∅ -/
def drop (i : ℕ) (t : ordnode α) : ordnode α :=
if size t ≤ i then nil else drop_aux t i

/-- Auxiliary definition for `split_at`. (Can also be used in lieu of `split_at` if you know the
index is within the range of the data structure.)

    split_at_aux {a, b, c, d} 2 = ({a, b}, {c, d})
    split_at_aux {a, b, c, d} 5 = ({a, b, c, d}, ∅) -/
def split_at_aux : ordnode α → ℕ → ordnode α × ordnode α
| nil i := (nil, nil)
| t@(node _ l x r) i :=
  if i = 0 then (nil, t) else
  match nat.psub' i (size l) with
  | none         := let (l₁, l₂) := split_at_aux l i in (l₁, link l₂ x r)
  | some 0       := (glue l r, insert_min x r)
  | some (j + 1) := let (r₁, r₂) := split_at_aux r j in (link l x r₁, r₂)
  end

/-- O(log n). Split a set at the `i`th element, getting the first `i` and everything else.

     split_at 2 {a, b, c, d} = ({a, b}, {c, d})
     split_at 5 {a, b, c, d} = ({a, b, c, d}, ∅) -/
def split_at (i : ℕ) (t : ordnode α) : ordnode α × ordnode α :=
if size t ≤ i then (t, nil) else split_at_aux t i

/-- O(log n). Get an initial segment of the set that satisfies the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    take_while (λ x, x < 4) {1, 2, 3, 4, 5} = {1, 2, 3}
    take_while (λ x, x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def take_while (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α
| nil := nil
| (node _ l x r) := if p x then link l x (take_while r) else take_while l

/-- O(log n). Remove an initial segment of the set that satisfies the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    drop_while (λ x, x < 4) {1, 2, 3, 4, 5} = {4, 5}
    drop_while (λ x, x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def drop_while (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α
| nil := nil
| (node _ l x r) := if p x then drop_while r else link (drop_while l) x r

/-- O(log n). Split the set into those satisfying and not satisfying the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    span (λ x, x < 4) {1, 2, 3, 4, 5} = ({1, 2, 3}, {4, 5})
    span (λ x, x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def span (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α × ordnode α
| nil := (nil, nil)
| (node _ l x r) :=
  if p x then let (r₁, r₂) := span r in (link l x r₁, r₂)
  else        let (l₁, l₂) := span l in (l₁, link l₂ x r)

/-- Auxiliary definition for `of_asc_list`.

**Note:** This function is defined by well founded recursion, so it will probably not compute
in the kernel, meaning that you probably can't prove things like
`of_asc_list [1, 2, 3] = {1, 2, 3}` by `rfl`.
This implementation is optimized for VM evaluation. -/
def of_asc_list_aux₁ : ∀ l : list α, ℕ → ordnode α × {l' : list α // l'.length ≤ l.length}
| [] := λ s, (nil, ⟨[], le_refl _⟩)
| (x :: xs) := λ s,
  if s = 1 then (ι x, ⟨xs, nat.le_succ _⟩) else
  have _, from nat.lt_succ_self xs.length,
  match of_asc_list_aux₁ xs (s.shiftl 1) with
  | (t, ⟨[], h⟩) := (t, ⟨[], nat.zero_le _⟩)
  | (l, ⟨y :: ys, h⟩) :=
    have _, from nat.le_succ_of_le h,
    let (r, ⟨zs, h'⟩) := of_asc_list_aux₁ ys (s.shiftl 1) in
    (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
  end
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩],
  dec_tac := `[assumption] }

/-- Auxiliary definition for `of_asc_list`. -/
def of_asc_list_aux₂ : list α → ordnode α → ℕ → ordnode α
| [] := λ t s, t
| (x :: xs) := λ l s,
  have _, from nat.lt_succ_self xs.length,
  match of_asc_list_aux₁ xs s with
  | (r, ⟨ys, h⟩) :=
    have _, from nat.lt_succ_of_le h,
    of_asc_list_aux₂ ys (link l x r) (s.shiftl 1)
  end
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩],
  dec_tac := `[assumption] }

/-- O(n). Build a set from a list which is already sorted. Performs no comparisons.

     of_asc_list [1, 2, 3] = {1, 2, 3}
     of_asc_list [3, 2, 1] = precondition violation -/
def of_asc_list : list α → ordnode α
| [] := nil
| (x :: xs) := of_asc_list_aux₂ xs (ι x) 1

section
variables [has_le α] [@decidable_rel α (≤)]

/-- O(log n). Does the set (approximately) contain the element `x`? That is,
is there an element that is equivalent to `x` in the order?

    1 ∈ {1, 2, 3} = true
    4 ∈ {1, 2, 3} = false

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    (1, 1) ∈ {(0, 1), (1, 2)} = true
    (3, 1) ∈ {(0, 1), (1, 2)} = false -/
def mem (x : α) : ordnode α → bool
| nil := ff
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := mem l
  | ordering.eq := tt
  | ordering.gt := mem r
  end

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
if it exists.

    find 1 {1, 2, 3} = some 1
    find 4 {1, 2, 3} = none

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    find (1, 1) {(0, 1), (1, 2)} = some (1, 2)
    find (3, 1) {(0, 1), (1, 2)} = none -/
def find (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := find l
  | ordering.eq := some y
  | ordering.gt := find r
  end

instance : has_mem α (ordnode α) := ⟨λ x t, t.mem x⟩

instance mem.decidable (x : α) (t : ordnode α) : decidable (x ∈ t) :=
bool.decidable_eq _ _

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, the function `f` is used to generate
the element to insert (being passed the current value in the set).

    insert_with f 0 {1, 2, 3} = {0, 1, 2, 3}
    insert_with f 1 {1, 2, 3} = {f 1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert_with f (1, 1) {(0, 1), (1, 2)} = {(0, 1), f (1, 2)}
    insert_with f (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
def insert_with (f : α → α) (x : α) : ordnode α → ordnode α
| nil := ι x
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_l (insert_with l) y r
  | ordering.eq := node sz l (f y) r
  | ordering.gt := balance_r l y (insert_with r)
  end

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    adjust_with f 0 {1, 2, 3} = {1, 2, 3}
    adjust_with f 1 {1, 2, 3} = {f 1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    adjust_with f (1, 1) {(0, 1), (1, 2)} = {(0, 1), f (1, 2)}
    adjust_with f (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)} -/
def adjust_with (f : α → α) (x : α) : ordnode α → ordnode α
| nil := nil
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := node sz (adjust_with l) y r
  | ordering.eq := node sz l (f y) r
  | ordering.gt := node sz l y (adjust_with r)
  end

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    update_with f 0 {1, 2, 3} = {1, 2, 3}
    update_with f 1 {1, 2, 3} = {2, 3}     if f 1 = none
                              = {a, 2, 3}  if f 1 = some a -/
def update_with (f : α → option α) (x : α) : ordnode α → ordnode α
| nil := nil
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_r (update_with l) y r
  | ordering.eq :=
    match f y with
    | none := glue l r
    | some a := node sz l a r
    end
  | ordering.gt := balance_l l y (update_with r)
  end

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    alter f 0 {1, 2, 3} = {1, 2, 3}     if f none = none
                        = {a, 1, 2, 3}  if f none = some a
    alter f 1 {1, 2, 3} = {2, 3}     if f 1 = none
                        = {a, 2, 3}  if f 1 = some a -/
def alter (f : option α → option α) (x : α) : ordnode α → ordnode α
| nil := option.rec_on (f none) nil ordnode.singleton
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance (alter l) y r
  | ordering.eq :=
    match f (some y) with
    | none := glue l r
    | some a := node sz l a r
    end
  | ordering.gt := balance l y (alter r)
  end

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, this replaces it.

    insert 1 {1, 2, 3} = {1, 2, 3}
    insert 4 {1, 2, 3} = {1, 2, 3, 4}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert (1, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 1)}
    insert (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
protected def insert (x : α) : ordnode α → ordnode α
| nil := ι x
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_l (insert l) y r
  | ordering.eq := node sz l x r
  | ordering.gt := balance_r l y (insert r)
  end

instance : has_insert α (ordnode α) := ⟨ordnode.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, the set is returned as is.

    insert' 1 {1, 2, 3} = {1, 2, 3}
    insert' 4 {1, 2, 3} = {1, 2, 3, 4}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert' (1, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)}
    insert' (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
def insert' (x : α) : ordnode α → ordnode α
| nil := ι x
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_l (insert' l) y r
  | ordering.eq := t
  | ordering.gt := balance_r l y (insert' r)
  end

/-- O(log n). Split the tree into those smaller than `x` and those greater than it.
If an element equivalent to `x` is in the set, it is discarded.

    split 2 {1, 2, 4} = ({1}, {4})
    split 3 {1, 2, 4} = ({1, 2}, {4})
    split 4 {1, 2, 4} = ({1, 2}, ∅)

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    split (1, 1) {(0, 1), (1, 2)} = ({(0, 1)}, ∅)
    split (3, 1) {(0, 1), (1, 2)} = ({(0, 1), (1, 2)}, ∅) -/
def split (x : α) : ordnode α → ordnode α × ordnode α
| nil := (nil, nil)
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := let (lt, gt) := split l in (lt, link gt y r)
  | ordering.eq := (l, r)
  | ordering.gt := let (lt, gt) := split r in (link l y lt, gt)
  end

/-- O(log n). Split the tree into those smaller than `x` and those greater than it,
plus an element equivalent to `x`, if it exists.

    split 2 {1, 2, 4} = ({1}, some 2, {4})
    split 3 {1, 2, 4} = ({1, 2}, none, {4})
    split 4 {1, 2, 4} = ({1, 2}, some 4, ∅)

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    split (1, 1) {(0, 1), (1, 2)} = ({(0, 1)}, some (1, 2), ∅)
    split (3, 1) {(0, 1), (1, 2)} = ({(0, 1), (1, 2)}, none, ∅) -/
def split3 (x : α) : ordnode α → ordnode α × option α × ordnode α
| nil := (nil, none, nil)
| (node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := let (lt, f, gt) := split3 l in (lt, f, link gt y r)
  | ordering.eq := (l, some y, r)
  | ordering.gt := let (lt, f, gt) := split3 r in (link l y lt, f, gt)
  end

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element.

    erase 1 {1, 2, 3} = {2, 3}
    erase 4 {1, 2, 3} = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    erase (1, 1) {(0, 1), (1, 2)} = {(0, 1)}
    erase (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)} -/
def erase (x : α) : ordnode α → ordnode α
| nil := nil
| t@(node sz l y r) :=
  match cmp_le x y with
  | ordering.lt := balance_r (erase l) y r
  | ordering.eq := glue l r
  | ordering.gt := balance_l l y (erase r)
  end

/-- Auxiliary definition for `find_lt`. -/
def find_lt_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  if x ≤ y then find_lt_aux l best else find_lt_aux r y

/-- O(log n). Get the largest element in the tree that is `< x`.

     find_lt 2 {1, 2, 4} = some 1
     find_lt 3 {1, 2, 4} = some 2
     find_lt 0 {1, 2, 4} = none -/
def find_lt (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  if x ≤ y then find_lt l else some (find_lt_aux x r y)

/-- Auxiliary definition for `find_gt`. -/
def find_gt_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  if y ≤ x then find_gt_aux r best else find_gt_aux l y

/-- O(log n). Get the smallest element in the tree that is `> x`.

     find_lt 2 {1, 2, 4} = some 4
     find_lt 3 {1, 2, 4} = some 4
     find_lt 4 {1, 2, 4} = none -/
def find_gt (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  if y ≤ x then find_gt r else some (find_gt_aux x l y)

/-- Auxiliary definition for `find_le`. -/
def find_le_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  match cmp_le x y with
  | ordering.lt := find_le_aux l best
  | ordering.eq := y
  | ordering.gt := find_le_aux r y
  end

/-- O(log n). Get the largest element in the tree that is `≤ x`.

     find_le 2 {1, 2, 4} = some 2
     find_le 3 {1, 2, 4} = some 2
     find_le 0 {1, 2, 4} = none -/
def find_le (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := find_le l
  | ordering.eq := some y
  | ordering.gt := some (find_le_aux x r y)
  end

/-- Auxiliary definition for `find_ge`. -/
def find_ge_aux (x : α) : ordnode α → α → α
| nil best := best
| (node _ l y r) best :=
  match cmp_le x y with
  | ordering.lt := find_ge_aux l y
  | ordering.eq := y
  | ordering.gt := find_ge_aux r best
  end

/-- O(log n). Get the smallest element in the tree that is `≥ x`.

     find_le 2 {1, 2, 4} = some 2
     find_le 3 {1, 2, 4} = some 4
     find_le 5 {1, 2, 4} = none -/
def find_ge (x : α) : ordnode α → option α
| nil := none
| (node _ l y r) :=
  match cmp_le x y with
  | ordering.lt := some (find_ge_aux x l y)
  | ordering.eq := some y
  | ordering.gt := find_ge r
  end

/-- Auxiliary definition for `find_index`. -/
def find_index_aux (x : α) : ordnode α → ℕ → option ℕ
| nil i := none
| (node _ l y r) i :=
  match cmp_le x y with
  | ordering.lt := find_index_aux l i
  | ordering.eq := some (i + size l)
  | ordering.gt := find_index_aux r (i + size l + 1)
  end

/-- O(log n). Get the index, counting from the left,
of an element equivalent to `x` if it exists.

    find_index 2 {1, 2, 4} = some 1
    find_index 4 {1, 2, 4} = some 2
    find_index 5 {1, 2, 4} = none -/
def find_index (x : α) (t : ordnode α) : option ℕ := find_index_aux x t 0

/-- Auxiliary definition for `is_subset`. -/
def is_subset_aux : ordnode α → ordnode α → bool
| nil _ := tt
| _ nil := ff
| (node _ l x r) t :=
  let (lt, found, gt) := split3 x t in
  found.is_some && is_subset_aux l lt && is_subset_aux r gt

/-- O(m+n). Is every element of `t₁` equivalent to some element of `t₂`?

     is_subset {1, 4} {1, 2, 4} = tt
     is_subset {1, 3} {1, 2, 4} = ff -/
def is_subset (t₁ t₂ : ordnode α) : bool :=
to_bool (size t₁ ≤ size t₂) && is_subset_aux t₁ t₂

/-- O(m+n). Is every element of `t₁` not equivalent to any element of `t₂`?

     disjoint {1, 3} {2, 4} = tt
     disjoint {1, 2} {2, 4} = ff -/
def disjoint : ordnode α → ordnode α → bool
| nil _ := tt
| _ nil := tt
| (node _ l x r) t :=
  let (lt, found, gt) := split3 x t in
  found.is_none && disjoint l lt && disjoint r gt

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. The union of two sets, preferring members of
  `t₁` over those of `t₂` when equivalent elements are encountered.

    union {1, 2} {2, 3} = {1, 2, 3}
    union {1, 3} {2} = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    union {(1, 1)} {(0, 1), (1, 2)} = {(0, 1), (1, 1)} -/
def union : ordnode α → ordnode α → ordnode α
| t₁ nil := t₁
| nil t₂ := t₂
| t₁@(node s₁ l₁ x₁ r₁) t₂@(node s₂ l₂ x₂ r₂) :=
  if s₂ = 1 then insert' x₂ t₁ else
  if s₁ = 1 then insert x₁ t₂ else
  let (l₂', r₂') := split x₁ t₂ in
  link (union l₁ l₂') x₁ (union r₁ r₂')

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. Difference of two sets.

    diff {1, 2} {2, 3} = {1}
    diff {1, 2, 3} {2} = {1, 3} -/
def diff : ordnode α → ordnode α → ordnode α
| t₁ nil := t₁
| t₁ t₂@(node _ l₂ x r₂) := cond t₁.empty t₂ $
  let (l₁, r₁) := split x t₁,
      l₁₂ := diff l₁ l₂, r₁₂ := diff r₁ r₂ in
  if size l₁₂ + size r₁₂ = size t₁ then t₁ else
  merge l₁₂ r₁₂

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. Intersection of two sets, preferring members of
`t₁` over those of `t₂` when equivalent elements are encountered.

    inter {1, 2} {2, 3} = {2}
    inter {1, 3} {2} = ∅ -/
def inter : ordnode α → ordnode α → ordnode α
| nil t₂ := nil
| t₁@(node _ l₁ x r₁) t₂ := cond t₂.empty t₁ $
  let (l₂, y, r₂) := split3 x t₂,
      l₁₂ := inter l₁ l₂, r₁₂ := inter r₁ r₂ in
  cond y.is_some (link l₁₂ x r₁₂) (merge l₁₂ r₁₂)

/-- O(n * log n). Build a set from a list, preferring elements that appear earlier in the list
in the case of equivalent elements.

    of_list [1, 2, 3] = {1, 2, 3}
    of_list [2, 1, 1, 3] = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    of_list [(1, 1), (0, 1), (1, 2)] = {(0, 1), (1, 1)} -/
def of_list (l : list α) : ordnode α := l.foldr insert nil

/-- O(n * log n). Adaptively chooses between the linear and log-linear algorithm depending
  on whether the input list is already sorted.

    of_list' [1, 2, 3] = {1, 2, 3}
    of_list' [2, 1, 1, 3] = {1, 2, 3} -/
def of_list' : list α → ordnode α
| [] := nil
| (x :: xs) :=
  if list.chain (λ a b, ¬ b ≤ a) x xs
  then of_asc_list (x :: xs)
  else of_list (x :: xs)

/-- O(n * log n). Map a function on a set. Unlike `map` this has no requirements on
`f`, and the resulting set may be smaller than the input if `f` is noninjective.
Equivalent elements are selected with a preference for smaller source elements.

    image (λ x, x + 2) {1, 2, 4} = {3, 4, 6}
    image (λ x : ℕ, x - 2) {1, 2, 4} = {0, 2} -/
def image {α β} [has_le β] [@decidable_rel β (≤)]
  (f : α → β) (t : ordnode α) : ordnode β :=
of_list (t.to_list.map f)

end

end ordnode
