/- © E.W.Ayers 2019 -/
import control.traversable

universes u v

/-- A list zipper represents a list and a 'cursor' at a particular point in the list. -/
@[derive decidable_eq]
structure list.zipper (α : Type u) :=
(left : list α)
(right : list α)

namespace list.zipper

open list

variables {α : Type u}

local notation `lz` := list.zipper α

instance : has_emptyc lz := ⟨⟨[],[]⟩⟩

/-- Get the list at the cursor of the zipper. -/
def cursor : lz → list α
| ⟨l,r⟩ := r

/-- Set the list at the cursor of the zipper. -/
def set : list α → lz → lz
| r ⟨l, _⟩ := ⟨l,r⟩

/-- Map the cursor list. -/
def map_cursor (f : list α → list α) : lz → lz
| ⟨l, r⟩ := ⟨l, f r⟩

/-- Move the cursor up one list element. -/
def up : lz → option lz
| ⟨h::l,r⟩ := some ⟨l,h::r⟩ | _ := none

/-- Move the cursor down one list element. -/
def down  : lz → option lz
| ⟨l,h::r⟩ := some ⟨h::l,r⟩ | _ := none

/-- Apply cons to the cursor. -/
def cons : α → lz → lz
|a ⟨l,r⟩ := ⟨l,a::r⟩

/-- Apply cons to the cursor and go down. -/
def cons_down : α → lz → lz
| a ⟨l,r⟩ := ⟨a::l,r⟩

/-- Get the path of the zipper. That is, a reversed list of the entries above the cursor. -/
def path : lz → list α
| ⟨l,_⟩ := l

/-- Pop the head of the cursor. -/
def decons : lz → option (α × lz)
| ⟨l,a::r⟩ := some (a,⟨l,r⟩) | _ := none

/-- Return the tail of the cursor. -/
def tail : lz → option (list α)
| ⟨_, _::t⟩ := some t | _ := none

/-- Return the head of the cursor. -/
def head : lz → option α
| ⟨l, a::_⟩ := some a | _ := none

/-- Get the length of the whole list. -/
def length : lz → nat
| ⟨l,r⟩ := l.length + r.length

/-- Perform `up` n times. If the zipper is already at the top then return none. -/
def n_up : nat → lz → option lz
|0 z := z |(n+1) z := up z >>= n_up n

/-- Perform `down` n times. If the zipper reaches the bottom then return none. -/
def n_down : nat → lz → option lz
|0 z := z |(n+1) z := down z >>= n_down n

/-- If the given integer is positive then move down else move up. Returns none if it moves out of range. -/
def move : int → lz → option lz
|(int.of_nat n) z := n_down n z
|(-[1+n]) z := n_up (n+1) z

/-- Check if the cursor is the entire list. -/
def is_top : lz → bool
| ⟨[],r⟩ := tt | _ := ff

/-- Check if the cursor is empty. -/
def is_bottom : lz → bool
| ⟨_,[]⟩ := tt | _ := ff

/-- Check if the entire list is empty. -/
def empty : lz → bool
| ⟨[],[]⟩ := tt | _ := ff

/-- Go up until you hit the top. -/
def top : lz → lz
| ⟨l,r⟩ := ⟨[], list.reverse_core l r⟩

/-- Go down until you hit the bottom. -/
def bottom : lz → lz
| ⟨l,r⟩ := ⟨list.reverse_core r l, []⟩

/-- How far down the list are you? -/
def depth : lz → nat
|⟨l,_⟩ := list.length l

/-- Move the zipper to the given index. Returns none if `index > z.length`-/
def goto  : nat → lz → option lz
| i z := move ((i : ℤ) - (depth z : ℤ)) z

/-- Convert a list to a zipper at the top of the list. -/
def zip : list α → lz
| l := ⟨[],l⟩

/-- Convert a zipper back to a list. -/
def unzip : lz → list α
| ⟨l,r⟩ := list.reverse_core l r

/-- Map a zipper. -/
protected def map {α : Type u} {β : Type v} (f : α → β) : zipper α → zipper β
| ⟨l,r⟩ := ⟨list.map f l, list.map f r⟩

instance : functor zipper := { map := @zipper.map }

/-- Mmap a zipper-/
def mmap {m : Type u → Type u} [monad m] {α : Type u} {β : Type u} (f : α → m β) : list.zipper α → m (list.zipper β)
| ⟨l,r⟩ := pure list.zipper.mk <*> list.mmap f l <*> list.mmap f r

/-- Map the path with index. Index is from cursor, so the path entry closest to the cursor gets index argument of 0. -/
def map_with_index_path (f : nat → α → α) : lz → lz
| ⟨l,r⟩ := ⟨list.map_with_index f l, r⟩

/-- `pinch i l` removes the `i`th entry of the list and returns that entry
and a list zipper with the cursor at the point where the entry was removed. -/
def pinch : nat → list α → option (α × lz)
| n l := (n_down n $ zip l) >>= decons

/-- Reverse of `pinch`. Cons an element at the cursor and unzip. -/
def unpinch : α → lz → list α
| a z := unzip $ cons a z

/-- `pinch` the last element in the list. -/
def pinch_last : list α → option (α × lz)
| l := (up $ bottom $ zip l) >>= decons

def reverse : lz → lz
| ⟨l, r⟩ := ⟨r.reverse, l.reverse⟩

def pinch_all_core : list α → list α → list (α × lz)
| l [] := []
| l (h :: r) := (h, ⟨l,r⟩) :: pinch_all_core (h::l) (r)

/-- Return pinches for all the elements of the given list. -/
def pinch_all : list α → list (α × lz) := pinch_all_core []

instance : traversable list.zipper :=
⟨λ t m α β f z, begin unfreezingI { exact pure list.zipper.mk <*> traverse f z.left <*> traverse f z.right} end⟩

protected def repr [has_repr α] : lz → string
| ⟨l,r⟩ := "⟨" ++ l.repr ++ ", " ++ r.repr ++ "⟩"

instance [has_repr α]: has_repr lz :=
⟨λ z, list.zipper.repr z⟩

protected def to_string [has_to_string α] : lz → string
| ⟨l,r⟩ :=
  let lp := string.intercalate ", " $ list.map _root_.to_string $ list.reverse $ l in
  let rp := string.intercalate ", " $ list.map _root_.to_string $ r in
  "[" ++ lp ++ ",| " ++ rp ++ "]"

instance [has_to_string α]: has_to_string lz :=
⟨λ z, list.zipper.to_string z⟩

protected meta def pp [has_to_tactic_format α] : lz → tactic format
| ⟨l,r⟩ := do
  lp ← list.mmap tactic.pp $ list.reverse l,
  rp ← list.mmap tactic.pp $ r,
  pure $ "[" ++ (format.intercalate ", " lp) ++ ",| " ++ (format.intercalate ", " rp) ++ "]"

meta instance [has_to_tactic_format α]: has_to_tactic_format lz :=
⟨λ z, list.zipper.pp z⟩

end list.zipper
