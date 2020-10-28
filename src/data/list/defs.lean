/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import data.option.defs
import logic.basic
import tactic.cache
/-!
## Definitions on lists

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `data/list`
-/

namespace list

open function nat
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- Returns whether a list is []. Returns a boolean even if `l = []` is not decidable. -/
def is_nil {α} : list α → bool
| [] := tt
| _  := ff

instance [decidable_eq α] : has_sdiff (list α) :=
⟨ list.diff ⟩

/-- Split a list at an index.

     split_at 2 [a, b, c] = ([a, b], [c]) -/
def split_at : ℕ → list α → list α × list α
| 0        a         := ([], a)
| (succ n) []        := ([], [])
| (succ n) (x :: xs) := let (l, r) := split_at n xs in (x :: l, r)


/-- An auxiliary function for `split_on_p`. -/
def split_on_p_aux {α : Type u} (P : α → Prop) [decidable_pred P] :
  list α → (list α → list α) → list (list α)
| [] f       := [f []]
| (h :: t) f :=
  if P h then f [] :: split_on_p_aux t id
  else split_on_p_aux t (λ l, f (h :: l))

/-- Split a list at every element satisfying a predicate. -/
def split_on_p {α : Type u} (P : α → Prop) [decidable_pred P] (l : list α) : list (list α) :=
split_on_p_aux P l id

/-- Split a list at every occurrence of an element.

    [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] -/
def split_on {α : Type u} [decidable_eq α] (a : α) (as : list α) : list (list α) :=
as.split_on_p (=a)

/-- Concatenate an element at the end of a list.

     concat [a, b] c = [a, b, c] -/
@[simp] def concat : list α → α → list α
| []     a := [a]
| (b::l) a := b :: concat l a

/-- `head' xs` returns the first element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp] def head' : list α → option α
| []       := none
| (a :: l) := some a

/-- Convert a list into an array (whose length is the length of `l`). -/
def to_array (l : list α) : array l.length α :=
{data := λ v, l.nth_le v.1 v.2}

/-- "inhabited" `nth` function: returns `default` instead of `none` in the case
  that the index is out of bounds. -/
@[simp] def inth [h : inhabited α] (l : list α) (n : nat) : α := (nth l n).iget

/-- Apply a function to the nth tail of `l`. Returns the input without
  using `f` if the index is larger than the length of the list.

     modify_nth_tail f 2 [a, b, c] = [a, b] ++ f [c] -/
@[simp] def modify_nth_tail (f : list α → list α) : ℕ → list α → list α
| 0     l      := f l
| (n+1) []     := []
| (n+1) (a::l) := a :: modify_nth_tail n l

/-- Apply `f` to the head of the list, if it exists. -/
@[simp] def modify_head (f : α → α) : list α → list α
| []     := []
| (a::l) := f a :: l

/-- Apply `f` to the nth element of the list, if it exists. -/
def modify_nth (f : α → α) : ℕ → list α → list α :=
modify_nth_tail (modify_head f)

/-- Apply `f` to the last element of `l`, if it exists. -/
@[simp] def modify_last (f : α → α) : list α → list α
| [] := []
| [x] := [f x]
| (x :: xs) := x :: modify_last xs

/-- `insert_nth n a l` inserts `a` into the list `l` after the first `n` elements of `l`
 `insert_nth 2 1 [1, 2, 3, 4] = [1, 2, 1, 3, 4]`-/
def insert_nth (n : ℕ) (a : α) : list α → list α := modify_nth_tail (list.cons a) n

section take'
variable [inhabited α]

/-- Take `n` elements from a list `l`. If `l` has less than `n` elements, append `n - length l`
elements `default α`. -/
def take' : ∀ n, list α → list α
| 0     l := []
| (n+1) l := l.head :: take' n l.tail

end take'

/-- Get the longest initial segment of the list whose members all satisfy `p`.

     take_while (λ x, x < 3) [0, 2, 5, 1] = [0, 2] -/
def take_while (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then a :: take_while l else []

/-- Fold a function `f` over the list from the left, returning the list
  of partial results.

     scanl (+) 0 [1, 2, 3] = [0, 1, 3, 6] -/
def scanl (f : α → β → α) : α → list β → list α
| a []     := [a]
| a (b::l) := a :: scanl (f a b) l

/-- Auxiliary definition used to define `scanr`. If `scanr_aux f b l = (b', l')`
then `scanr f b l = b' :: l'` -/
def scanr_aux (f : α → β → β) (b : β) : list α → β × list β
| []     := (b, [])
| (a::l) := let (b', l') := scanr_aux l in (f a b', b' :: l')

/-- Fold a function `f` over the list from the right, returning the list
  of partial results.

     scanr (+) 0 [1, 2, 3] = [6, 5, 3, 0] -/
def scanr (f : α → β → β) (b : β) (l : list α) : list β :=
let (b', l') := scanr_aux f b l in b' :: l'

/-- Product of a list.

     prod [a, b, c] = ((1 * a) * b) * c -/
def prod [has_mul α] [has_one α] : list α → α := foldl (*) 1

/-- Sum of a list.

     sum [a, b, c] = ((0 + a) + b) + c -/
-- Later this will be tagged with `to_additive`, but this can't be done yet because of import
-- dependencies.
def sum [has_add α] [has_zero α] : list α → α := foldl (+) 0

/-- The alternating sum of a list. -/
def alternating_sum {G : Type*} [has_zero G] [has_add G] [has_neg G] : list G → G
| [] := 0
| (g :: []) := g
| (g :: h :: t) := g + -h + alternating_sum t

/-- The alternating product of a list. -/
def alternating_prod {G : Type*} [has_one G] [has_mul G] [has_inv G] : list G → G
| [] := 1
| (g :: []) := g
| (g :: h :: t) := g * h⁻¹ * alternating_prod t

/-- Given a function `f : α → β ⊕ γ`, `partition_map f l` maps the list by `f`
  whilst partitioning the result it into a pair of lists, `list β × list γ`,
  partitioning the `sum.inl _` into the left list, and the `sum.inr _` into the right list.
  `partition_map (id : ℕ ⊕ ℕ → ℕ ⊕ ℕ) [inl 0, inr 1, inl 2] = ([0,2], [1])`    -/
def partition_map (f : α → β ⊕ γ) : list α → list β × list γ
| [] := ([],[])
| (x::xs) :=
match f x with
| (sum.inr r) := prod.map id (cons r) $ partition_map xs
| (sum.inl l) := prod.map (cons l) id $ partition_map xs
end

/-- `find p l` is the first element of `l` satisfying `p`, or `none` if no such
  element exists. -/
def find (p : α → Prop) [decidable_pred p] : list α → option α
| []     := none
| (a::l) := if p a then some a else find l

/-- `mfind tac l` returns the first element of `l` on which `tac` succeeds, and
fails otherwise. -/
def mfind {α} {m : Type u → Type v} [monad m] [alternative m] (tac : α → m punit) : list α → m α :=
list.mfirst $ λ a, tac a $> a

/-- `mbfind' p l` returns the first element `a` of `l` for which `p a` returns
true. `mbfind'` short-circuits, so `p` is not necessarily run on every `a` in
`l`. This is a monadic version of `list.find`. -/
def mbfind' {m : Type u → Type v} [monad m] {α : Type u} (p : α → m (ulift bool)) :
  list α → m (option α)
| [] := pure none
| (x :: xs) := do
  ⟨px⟩ ← p x,
  if px then pure (some x) else mbfind' xs

section

variables {m : Type → Type v} [monad m]

/-- A variant of `mbfind'` with more restrictive universe levels. -/
def mbfind {α} (p : α → m bool) (xs : list α) : m (option α) :=
xs.mbfind' (functor.map ulift.up ∘ p)

/-- `many p as` returns true iff `p` returns true for any element of `l`.
`many` short-circuits, so if `p` returns true for any element of `l`, later
elements are not checked. This is a monadic version of `list.any`. -/
-- Implementing this via `mbfind` would give us less universe polymorphism.
def many {α : Type u} (p : α → m bool) : list α → m bool
| [] := pure false
| (x :: xs) := do px ← p x, if px then pure tt else many xs

/-- `mall p as` returns true iff `p` returns true for all elements of `l`.
`mall` short-circuits, so if `p` returns false for any element of `l`, later
elements are not checked. This is a monadic version of `list.all`. -/
def mall {α : Type u} (p : α → m bool) (as : list α) : m bool :=
bnot <$> many (λ a, bnot <$> p a) as

/-- `mbor xs` runs the actions in `xs`, returning true if any of them returns
true. `mbor` short-circuits, so if an action returns true, later actions are
not run. This is a monadic version of `list.bor`. -/
def mbor : list (m bool) → m bool :=
many id

/-- `mband xs` runs the actions in `xs`, returning true if all of them return
true. `mband` short-circuits, so if an action returns false, later actions are
not run. This is a monadic version of `list.band`. -/
def mband : list (m bool) → m bool :=
mall id

end

/-- Auxiliary definition for `foldl_with_index`. -/
def foldl_with_index_aux (f : ℕ → α → β → α) : ℕ → α → list β → α
| _ a [] := a
| i a (b :: l) := foldl_with_index_aux (i + 1) (f i a b) l

/-- Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index. -/
def foldl_with_index (f : ℕ → α → β → α) (a : α) (l : list β) : α :=
foldl_with_index_aux f 0 a l

/-- Auxiliary definition for `foldr_with_index`. -/
def foldr_with_index_aux (f : ℕ → α → β → β) : ℕ → β → list α → β
| _ b [] := b
| i b (a :: l) := f i a (foldr_with_index_aux (i + 1) b l)

/-- Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index. -/
def foldr_with_index (f : ℕ → α → β → β) (b : β) (l : list α) : β :=
foldr_with_index_aux f 0 b l

/-- `find_indexes p l` is the list of indexes of elements of `l` that satisfy `p`. -/
def find_indexes (p : α → Prop) [decidable_pred p] (l : list α) : list nat :=
foldr_with_index (λ i a is, if p a then i :: is else is) [] l

/-- Returns the elements of `l` that satisfy `p` together with their indexes in
`l`. The returned list is ordered by index. -/
def indexes_values (p : α → Prop) [decidable_pred p] (l : list α) : list (ℕ × α) :=
foldr_with_index (λ i a l, if p a then (i , a) :: l else l) [] l

/-- `indexes_of a l` is the list of all indexes of `a` in `l`. For example:
```
indexes_of a [a, b, a, a] = [0, 2, 3]
```
-/
def indexes_of [decidable_eq α] (a : α) : list α → list nat := find_indexes (eq a)

section mfold_with_index

variables {m : Type v → Type w} [monad m]

/-- Monadic variant of `foldl_with_index`. -/
def mfoldl_with_index {α β} (f : ℕ → β → α → m β) (b : β) (as : list α) : m β :=
as.foldl_with_index (λ i ma b, do a ← ma, f i a b) (pure b)

/-- Monadic variant of `foldr_with_index`. -/
def mfoldr_with_index {α β} (f : ℕ → α → β → m β) (b : β) (as : list α) : m β :=
as.foldr_with_index (λ i a mb, do b ← mb, f i a b) (pure b)

end mfold_with_index

section zip_with

def zip_with₃ {α β γ φ} (f : α → β → γ → φ) : list α → list β → list γ → list φ
| (x::xs) (y::ys) (z::zs) := f x y z :: zip_with₃ xs ys zs
| _ _ _ := []

variables {m : Type v → Type w} [applicative m]

def mzip_with₃ {α β γ φ} (f : α → β → γ → m φ) : list α → list β → list γ → m (list φ)
| (x::xs) (y::ys) (z::zs) := (::) <$> f x y z <*> mzip_with₃ xs ys zs
| _ _ _ := pure []

def mzip_with₄ {α β γ φ ψ} (f : α → β → γ → φ → m ψ) :
  list α → list β → list γ → list φ → m (list ψ)
| (w :: ws) (x::xs) (y::ys) (z::zs) := (::) <$> f w x y z <*> mzip_with₄ ws xs ys zs
| _ _ _ _ := pure []

end zip_with

section mmap_with_index

variables {m : Type v → Type w} [applicative m]

/-- Auxiliary definition for `mmap_with_index`. -/
def mmap_with_index_aux {α β} (f : ℕ → α → m β) : ℕ → list α → m (list β)
| _ [] := pure []
| i (a :: as) := list.cons <$> f i a <*> mmap_with_index_aux (i + 1) as

/-- Applicative variant of `map_with_index`. -/
def mmap_with_index {α β} (f : ℕ → α → m β) (as : list α) : m (list β) :=
mmap_with_index_aux f 0 as

/-- Auxiliary definition for `mmap_with_index'`. -/
def mmap_with_index'_aux {α} (f : ℕ → α → m punit) : ℕ → list α → m punit
| _ [] := pure ⟨⟩
| i (a :: as) := f i a *> mmap_with_index'_aux (i + 1) as

/-- A variant of `mmap_with_index` specialised to applicative actions which
return `unit`. -/
def mmap_with_index' {α} (f : ℕ → α → m punit) (as : list α) : m punit :=
mmap_with_index'_aux f 0 as

end mmap_with_index

/-- `lookmap` is a combination of `lookup` and `filter_map`.
  `lookmap f l` will apply `f : α → option α` to each element of the list,
  replacing `a → b` at the first value `a` in the list such that `f a = some b`. -/
def lookmap (f : α → option α) : list α → list α
| []     := []
| (a::l) :=
  match f a with
  | some b := b :: l
  | none   := a :: lookmap l
  end

/-- `countp p l` is the number of elements of `l` that satisfy `p`. -/
def countp (p : α → Prop) [decidable_pred p] : list α → nat
| []      := 0
| (x::xs) := if p x then succ (countp xs) else countp xs

/-- `count a l` is the number of occurrences of `a` in `l`. -/
def count [decidable_eq α] (a : α) : list α → nat := countp (eq a)

/-- `is_prefix l₁ l₂`, or `l₁ <+: l₂`, means that `l₁` is a prefix of `l₂`,
  that is, `l₂` has the form `l₁ ++ t` for some `t`. -/
def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂

/-- `is_suffix l₁ l₂`, or `l₁ <:+ l₂`, means that `l₁` is a suffix of `l₂`,
  that is, `l₂` has the form `t ++ l₁` for some `t`. -/
def is_suffix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, t ++ l₁ = l₂

/-- `is_infix l₁ l₂`, or `l₁ <:+: l₂`, means that `l₁` is a contiguous
  substring of `l₂`, that is, `l₂` has the form `s ++ l₁ ++ t` for some `s, t`. -/
def is_infix (l₁ : list α) (l₂ : list α) : Prop := ∃ s t, s ++ l₁ ++ t = l₂

infix ` <+: `:50 := is_prefix
infix ` <:+ `:50 := is_suffix
infix ` <:+: `:50 := is_infix

/-- `inits l` is the list of initial segments of `l`.

     inits [1, 2, 3] = [[], [1], [1, 2], [1, 2, 3]] -/
@[simp] def inits : list α → list (list α)
| []     := [[]]
| (a::l) := [] :: map (λt, a::t) (inits l)

/-- `tails l` is the list of terminal segments of `l`.

     tails [1, 2, 3] = [[1, 2, 3], [2, 3], [3], []] -/
@[simp] def tails : list α → list (list α)
| []     := [[]]
| (a::l) := (a::l) :: tails l

def sublists'_aux : list α → (list α → list β) → list (list β) → list (list β)
| []     f r := f [] :: r
| (a::l) f r := sublists'_aux l f (sublists'_aux l (f ∘ cons a) r)

/-- `sublists' l` is the list of all (non-contiguous) sublists of `l`.
  It differs from `sublists` only in the order of appearance of the sublists;
  `sublists'` uses the first element of the list as the MSB,
  `sublists` uses the first element of the list as the LSB.

     sublists' [1, 2, 3] = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]] -/
def sublists' (l : list α) : list (list α) :=
sublists'_aux l id []

def sublists_aux : list α → (list α → list β → list β) → list β
| []     f := []
| (a::l) f := f [a] (sublists_aux l (λys r, f ys (f (a :: ys) r)))

/-- `sublists l` is the list of all (non-contiguous) sublists of `l`; cf. `sublists'`
  for a different ordering.

     sublists [1, 2, 3] = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]] -/
def sublists (l : list α) : list (list α) :=
[] :: sublists_aux l cons

def sublists_aux₁ : list α → (list α → list β) → list β
| []     f := []
| (a::l) f := f [a] ++ sublists_aux₁ l (λys, f ys ++ f (a :: ys))

section forall₂
variables {r : α → β → Prop} {p : γ → δ → Prop}

/-- `forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length,
  and whenever `a` is the nth element of `l₁`, and `b` is the nth element of `l₂`,
  then `R a b` is satisfied. -/
inductive forall₂ (R : α → β → Prop) : list α → list β → Prop
| nil : forall₂ [] []
| cons {a b l₁ l₂} : R a b → forall₂ l₁ l₂ → forall₂ (a::l₁) (b::l₂)

attribute [simp] forall₂.nil

end forall₂

/-- Auxiliary definition used to define `transpose`.
  `transpose_aux l L` takes each element of `l` and appends it to the start of
  each element of `L`.

  `transpose_aux [a, b, c] [l₁, l₂, l₃] = [a::l₁, b::l₂, c::l₃]` -/
def transpose_aux : list α → list (list α) → list (list α)
| []     ls      := ls
| (a::i) []      := [a] :: transpose_aux i []
| (a::i) (l::ls) := (a::l) :: transpose_aux i ls

/-- transpose of a list of lists, treated as a matrix.

     transpose [[1, 2], [3, 4], [5, 6]] = [[1, 3, 5], [2, 4, 6]] -/
def transpose : list (list α) → list (list α)
| []      := []
| (l::ls) := transpose_aux l (transpose ls)

/-- List of all sections through a list of lists. A section
  of `[L₁, L₂, ..., Lₙ]` is a list whose first element comes from
  `L₁`, whose second element comes from `L₂`, and so on. -/
def sections : list (list α) → list (list α)
| []     := [[]]
| (l::L) := bind (sections L) $ λ s, map (λ a, a::s) l

section permutations

def permutations_aux2 (t : α) (ts : list α) (r : list β) : list α → (list α → β) → list α × list β
| []      f := (ts, r)
| (y::ys) f := let (us, zs) := permutations_aux2 ys (λx : list α, f (y::x)) in
               (y :: us, f (t :: y :: us) :: zs)

private def meas : (Σ'_:list α, list α) → ℕ × ℕ | ⟨l, i⟩ := (length l + length i, length l)

local infix ` ≺ `:50 := inv_image (prod.lex (<) (<)) meas

@[elab_as_eliminator] def permutations_aux.rec {C : list α → list α → Sort v}
  (H0 : ∀ is, C [] is)
  (H1 : ∀ t ts is, C ts (t::is) → C is [] → C (t::ts) is) : ∀ l₁ l₂, C l₁ l₂
| []      is := H0 is
| (t::ts) is :=
  have h1 : ⟨ts, t :: is⟩ ≺ ⟨t :: ts, is⟩, from
    show prod.lex _ _ (succ (length ts + length is), length ts) (succ (length ts) + length is,
      length (t :: ts)),
    by rw nat.succ_add; exact prod.lex.right _ (lt_succ_self _),
  have h2 : ⟨is, []⟩ ≺ ⟨t :: ts, is⟩, from prod.lex.left _ _ (nat.lt_add_of_pos_left (succ_pos _)),
  H1 t ts is (permutations_aux.rec ts (t::is)) (permutations_aux.rec is [])
using_well_founded {
  dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨(≺), @inv_image.wf _ _ _ meas (prod.lex_wf lt_wf lt_wf)⟩] }

def permutations_aux : list α → list α → list (list α) :=
@@permutations_aux.rec (λ _ _, list (list α)) (λ is, [])
  (λ t ts is IH1 IH2, foldr (λy r, (permutations_aux2 t ts r y id).2) IH1 (is :: IH2))

/-- List of all permutations of `l`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]] -/
def permutations (l : list α) : list (list α) :=
l :: permutations_aux l []

end permutations

/-- `erase p l` removes all elements of `l` satisfying the predicate `p` -/
def erasep (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then l else a :: erasep l

/-- `extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`. -/
def extractp (p : α → Prop) [decidable_pred p] : list α → option α × list α
| []     := (none, [])
| (a::l) := if p a then (some a, l) else
  let (a', l') := extractp l in (a', a :: l')

/-- `revzip l` returns a list of pairs of the elements of `l` paired
  with the elements of `l` in reverse order.

`revzip [1,2,3,4,5] = [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)]`
 -/
def revzip (l : list α) : list (α × α) := zip l l.reverse

/-- `product l₁ l₂` is the list of pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂`.

     product [1, 2] [5, 6] = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
def product (l₁ : list α) (l₂ : list β) : list (α × β) :=
l₁.bind $ λ a, l₂.map $ prod.mk a

/-- `sigma l₁ l₂` is the list of dependent pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂ a`.

     sigma [1, 2] (λ_, [(5 : ℕ), 6]) = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
protected def sigma {σ : α → Type*} (l₁ : list α) (l₂ : Π a, list (σ a)) : list (Σ a, σ a) :=
l₁.bind $ λ a, (l₂ a).map $ sigma.mk a

/-- Auxliary definition used to define `of_fn`.

  `of_fn_aux f m h l` returns the first `m` elements of `of_fn f`
  appended to `l` -/
def of_fn_aux {n} (f : fin n → α) : ∀ m, m ≤ n → list α → list α
| 0        h l := l
| (succ m) h l := of_fn_aux m (le_of_lt h) (f ⟨m, h⟩ :: l)

/-- `of_fn f` with `f : fin n → α` returns the list whose ith element is `f i`
  `of_fun f = [f 0, f 1, ... , f(n - 1)]` -/
def of_fn {n} (f : fin n → α) : list α :=
of_fn_aux f n (le_refl _) []

/-- `of_fn_nth_val f i` returns `some (f i)` if `i < n` and `none` otherwise. -/
def of_fn_nth_val {n} (f : fin n → α) (i : ℕ) : option α :=
if h : i < n then some (f ⟨i, h⟩) else none

/-- `disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common. -/
def disjoint (l₁ l₂ : list α) : Prop := ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → false

section pairwise
variables (R : α → α → Prop)

/-- `pairwise R l` means that all the elements with earlier indexes are
  `R`-related to all the elements with later indexes.

     pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3

  For example if `R = (≠)` then it asserts `l` has no duplicates,
  and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
inductive pairwise : list α → Prop
| nil : pairwise []
| cons : ∀ {a : α} {l : list α}, (∀ a' ∈ l, R a a') → pairwise l → pairwise (a::l)

variables {R}
@[simp] theorem pairwise_cons {a : α} {l : list α} :
  pairwise R (a::l) ↔ (∀ a' ∈ l, R a a') ∧ pairwise R l :=
⟨λ p, by cases p with a l n p; exact ⟨n, p⟩, λ ⟨n, p⟩, p.cons n⟩

attribute [simp] pairwise.nil

instance decidable_pairwise [decidable_rel R] (l : list α) : decidable (pairwise R l) :=
by induction l with hd tl ih; [exact is_true pairwise.nil,
  exactI decidable_of_iff' _ pairwise_cons]

end pairwise

/-- `pw_filter R l` is a maximal sublist of `l` which is `pairwise R`.
  `pw_filter (≠)` is the erase duplicates function (cf. `erase_dup`), and `pw_filter (<)` finds
  a maximal increasing subsequence in `l`. For example,

     pw_filter (<) [0, 1, 5, 2, 6, 3, 4] = [0, 1, 2, 3, 4] -/
def pw_filter (R : α → α → Prop) [decidable_rel R] : list α → list α
| []        := []
| (x :: xs) := let IH := pw_filter xs in if ∀ y ∈ IH, R x y then x :: IH else IH

section chain
variable (R : α → α → Prop)

/-- `chain R a l` means that `R` holds between adjacent elements of `a::l`.

     chain R a [b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
inductive chain : α → list α → Prop
| nil {a : α} : chain a []
| cons : ∀ {a b : α} {l : list α}, R a b → chain b l → chain a (b::l)

/-- `chain' R l` means that `R` holds between adjacent elements of `l`.

     chain' R [a, b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
def chain' : list α → Prop
| [] := true
| (a :: l) := chain R a l

variable {R}
@[simp] theorem chain_cons {a b : α} {l : list α} :
  chain R a (b::l) ↔ R a b ∧ chain R b l :=
⟨λ p, by cases p with _ a b l n p; exact ⟨n, p⟩, λ ⟨n, p⟩, p.cons n⟩

attribute [simp] chain.nil

instance decidable_chain [decidable_rel R] (a : α) (l : list α) : decidable (chain R a l) :=
by induction l generalizing a; simp only [chain.nil, chain_cons]; resetI; apply_instance

instance decidable_chain' [decidable_rel R] (l : list α) : decidable (chain' R l) :=
by cases l; dunfold chain'; apply_instance

end chain

/-- `nodup l` means that `l` has no duplicates, that is, any element appears at most
  once in the list. It is defined as `pairwise (≠)`. -/
def nodup : list α → Prop := pairwise (≠)

instance nodup_decidable [decidable_eq α] : ∀ l : list α, decidable (nodup l) :=
list.decidable_pairwise

/-- `erase_dup l` removes duplicates from `l` (taking only the first occurrence).
  Defined as `pw_filter (≠)`.

     erase_dup [1, 0, 2, 2, 1] = [0, 2, 1] -/
def erase_dup [decidable_eq α] : list α → list α := pw_filter (≠)

/-- `range' s n` is the list of numbers `[s, s+1, ..., s+n-1]`.
  It is intended mainly for proving properties of `range` and `iota`. -/
@[simp] def range' : ℕ → ℕ → list ℕ
| s 0     := []
| s (n+1) := s :: range' (s+1) n

/-- Drop `none`s from a list, and replace each remaining `some a` with `a`. -/
def reduce_option {α} : list (option α) → list α :=
list.filter_map id

/-- `ilast' x xs` returns the last element of `xs` if `xs` is non-empty;
it returns `x` otherwise -/
@[simp] def ilast' {α} : α → list α → α
| a []     := a
| a (b::l) := ilast' b l

/-- `last' xs` returns the last element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp] def last' {α} : list α → option α
| []     := none
| [a]    := some a
| (b::l) := last' l

/-- `rotate l n` rotates the elements of `l` to the left by `n`

     rotate [0, 1, 2, 3, 4, 5] 2 = [2, 3, 4, 5, 0, 1] -/
def rotate (l : list α) (n : ℕ) : list α :=
let (l₁, l₂) := list.split_at (n % l.length) l in l₂ ++ l₁

/-- rotate' is the same as `rotate`, but slower. Used for proofs about `rotate`-/
def rotate' : list α → ℕ → list α
| []     n     := []
| l      0     := l
| (a::l) (n+1) := rotate' (l ++ [a]) n

section choose
variables (p : α → Prop) [decidable_pred p] (l : list α)

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns both `a` and proofs
of `a ∈ l` and `p a`. -/
def choose_x : Π l : list α, Π hp : (∃ a, a ∈ l ∧ p a), { a // a ∈ l ∧ p a }
| [] hp := false.elim (exists.elim hp (assume a h, not_mem_nil a h.left))
| (l :: ls) hp := if pl : p l then ⟨l, ⟨or.inl rfl, pl⟩⟩ else
let ⟨a, ⟨a_mem_ls, pa⟩⟩ := choose_x ls (hp.imp
  (λ b ⟨o, h₂⟩, ⟨o.resolve_left (λ e, pl $ e ▸ h₂), h₂⟩)) in
⟨a, ⟨or.inr a_mem_ls, pa⟩⟩

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns `a : α`, and properties
are given by `choose_mem` and `choose_property`. -/
def choose (hp : ∃ a, a ∈ l ∧ p a) : α := choose_x p l hp

end choose

/-- Filters and maps elements of a list -/
def mmap_filter {m : Type → Type v} [monad m] {α β} (f : α → m (option β)) :
  list α → m (list β)
| []       := return []
| (h :: t) := do b ← f h, t' ← t.mmap_filter, return $
  match b with none := t' | (some x) := x::t' end

/--
`mmap_upper_triangle f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap_upper_triangle f l` will produce the list
`[f 1 1, f 1 2, f 1 3, f 2 2, f 2 3, f 3 3]`.
-/
def mmap_upper_triangle {m} [monad m] {α β : Type u} (f : α → α → m β) : list α → m (list β)
| [] := return []
| (h::t) := do v ← f h h, l ← t.mmap (f h), t ← t.mmap_upper_triangle, return $ (v::l) ++ t

/--
`mmap'_diag f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap'_diag f l` will evaluate, in this order,
`f 1 1`, `f 1 2`, `f 1 3`, `f 2 2`, `f 2 3`, `f 3 3`.
-/
def mmap'_diag {m} [monad m] {α} (f : α → α → m unit) : list α → m unit
| [] := return ()
| (h::t) := f h h >> t.mmap' (f h) >> t.mmap'_diag

protected def traverse {F : Type u → Type v} [applicative F] {α β : Type*} (f : α → F β) :
  list α → F (list β)
| [] := pure []
| (x :: xs) := list.cons <$> f x <*> traverse xs

/-- `get_rest l l₁` returns `some l₂` if `l = l₁ ++ l₂`.
  If `l₁` is not a prefix of `l`, returns `none` -/
def get_rest [decidable_eq α] : list α → list α → option (list α)
| l      []      := some l
| []     _       := none
| (x::l) (y::l₁) := if x = y then get_rest l l₁ else none

/--
`list.slice n m xs` removes a slice of length `m` at index `n` in list `xs`.
-/
def slice {α} : ℕ → ℕ → list α → list α
| 0 n xs := xs.drop n
| (succ n) m [] := []
| (succ n) m (x :: xs) := x :: slice n m xs

/--
Left-biased version of `list.map₂`. `map₂_left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.

```
map₂_left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

map₂_left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp] def map₂_left' (f : α → option β → γ) : list α → list β → (list γ × list β)
| [] bs := ([], bs)
| (a :: as) [] :=
  ((a :: as).map (λ a, f a none), [])
| (a :: as) (b :: bs) :=
  let rec := map₂_left' as bs in
  (f a (some b) :: rec.fst, rec.snd)

/--
Right-biased version of `list.map₂`. `map₂_right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.

```
map₂_right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

map₂_right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
def map₂_right' (f : option α → β → γ) (as : list α) (bs : list β) : (list γ × list α) :=
map₂_left' (flip f) bs as

/--
Left-biased version of `list.zip`. `zip_left' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`. Also returns the remaining `bs`.

```
zip_left' [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

zip_left' [1] ['a', 'b'] = ([(1, some 'a')], ['b'])

zip_left' = map₂_left' prod.mk

```
-/
def zip_left' : list α → list β → list (α × option β) × list β :=
map₂_left' prod.mk

/--
Right-biased version of `list.zip`. `zip_right' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`. Also returns the remaining `as`.

```
zip_right' [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

zip_right' [1, 2] ['a'] = ([(some 1, 'a')], [2])

zip_right' = map₂_right' prod.mk
```
-/
def zip_right' : list α → list β → list (option α × β) × list α :=
map₂_right' prod.mk

/--
Left-biased version of `list.map₂`. `map₂_left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.

```
map₂_left prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]

map₂_left prod.mk [1] ['a', 'b'] = [(1, some 'a')]

map₂_left f as bs = (map₂_left' f as bs).fst
```
-/
@[simp] def map₂_left (f : α → option β → γ) : list α → list β → list γ
| [] _ := []
| (a :: as) [] := (a :: as).map (λ a, f a none)
| (a :: as) (b :: bs) := f a (some b) :: map₂_left as bs

/--
Right-biased version of `list.map₂`. `map₂_right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.

```
map₂_right prod.mk [1, 2] ['a'] = [(some 1, 'a')]

map₂_right prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

map₂_right f as bs = (map₂_right' f as bs).fst
```
-/
def map₂_right (f : option α → β → γ) (as : list α) (bs : list β) :
  list γ :=
map₂_left (flip f) bs as

/--
Left-biased version of `list.zip`. `zip_left as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`.

```
zip_left [1, 2] ['a'] = [(1, some 'a'), (2, none)]

zip_left [1] ['a', 'b'] = [(1, some 'a')]

zip_left = map₂_left prod.mk
```
-/
def zip_left : list α → list β → list (α × option β) :=
map₂_left prod.mk

/--
Right-biased version of `list.zip`. `zip_right as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`.

```
zip_right [1, 2] ['a'] = [(some 1, 'a')]

zip_right [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

zip_right = map₂_right prod.mk
```
-/
def zip_right : list α → list β → list (option α × β) :=
map₂_right prod.mk

end list
