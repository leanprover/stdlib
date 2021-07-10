/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.ordmap.ordnode
import algebra.ordered_ring
import data.nat.dist
import tactic.linarith

/-!
# Verification of the `ordnode α` datatype

This file proves the correctness of the operations in `data.ordmap.ordnode`.
The public facing version is the type `ordset α`, which is a wrapper around
`ordnode α` which includes the correctness invariant of the type, and it exposes
parallel operations like `insert` as functions on `ordset` that do the same
thing but bundle the correctness proofs. The advantage is that it is possible
to, for example, prove that the result of `find` on `insert` will actually find
the element, while `ordnode` cannot guarantee this if the input tree did not
satisfy the type invariants.

## Main definitions

* `ordset α`: A well formed set of values of type `α`

## Implementation notes

The majority of this file is actually in the `ordnode` namespace, because we first
have to prove the correctness of all the operations (and defining what correctness
means here is actually somewhat subtle). So all the actual `ordset` operations are
at the very end, once we have all the theorems.

An `ordnode α` is an inductive type which describes a tree which stores the `size` at
internal nodes. The correctness invariant of an `ordnode α` is:

* `ordnode.sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `ordnode.balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `ordnode.bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬ (b ≤ a)`. We enforce this using `ordnode.bounded` which includes also a global
  upper and lower bound.

Because the `ordnode` file was ported from Haskell, the correctness invariants of some
of the functions have not been spelled out, and some theorems like
`ordnode.valid'.balance_l_aux` show very intricate assumptions on the sizes,
which may need to be revised if it turns out some operations violate these assumptions,
because there is a decent amount of slop in the actual data structure invariants, so the
theorem will go through with multiple choices of assumption.

**Note:** This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming

-/

variable {α : Type*}
namespace ordnode

/-! ### delta and ratio -/

theorem not_le_delta {s} (H : 1 ≤ s) : ¬ s ≤ delta * 0 :=
not_le_of_gt H

theorem delta_lt_false {a b : ℕ}
  (h₁ : delta * a < b) (h₂ : delta * b < a) : false :=
not_le_of_lt (lt_trans ((mul_lt_mul_left dec_trivial).2 h₁) h₂) $
by simpa [mul_assoc] using nat.mul_le_mul_right a (dec_trivial : 1 ≤ delta * delta)

/-! ### `singleton` -/

/-! ### `size` and `empty` -/

/-- O(n). Computes the actual number of elements in the set, ignoring the cached `size` field. -/
def real_size : ordnode α → ℕ
| nil := 0
| (node _ l _ r) := real_size l + real_size r + 1

/-! ### `sized` -/

/-- The `sized` property asserts that all the `size` fields in nodes match the actual size of the
respective subtrees. -/
def sized : ordnode α → Prop
| nil := true
| (node s l _ r) := s = size l + size r + 1 ∧ sized l ∧ sized r

theorem sized.node' {l x r} (hl : @sized α l) (hr : sized r) : sized (node' l x r) :=
⟨rfl, hl, hr⟩

theorem sized.eq_node' {s l x r} (h : @sized α (node s l x r)) : node s l x r = node' l x r :=
by rw h.1; refl

theorem sized.size_eq {s l x r} (H : sized (@node α s l x r)) :
  size (@node α s l x r) = size l + size r + 1 := H.1

@[elab_as_eliminator] theorem sized.induction {t} (hl : @sized α t)
  {C : ordnode α → Prop} (H0 : C nil)
  (H1 : ∀ l x r, C l → C r → C (node' l x r)) : C t :=
begin
  induction t, {exact H0},
  rw hl.eq_node',
  exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)
end

theorem size_eq_real_size : ∀ {t : ordnode α}, sized t → size t = real_size t
| nil _ := rfl
| (node s l x r) ⟨h₁, h₂, h₃⟩ :=
  by rw [size, h₁, size_eq_real_size h₂, size_eq_real_size h₃]; refl

@[simp] theorem sized.size_eq_zero {t : ordnode α} (ht : sized t) : size t = 0 ↔ t = nil :=
by cases t; [simp, simp [ht.1]]

theorem sized.pos {s l x r} (h : sized (@node α s l x r)) : 0 < s :=
by rw h.1; apply nat.le_add_left

/-! `dual` -/

theorem dual_dual : ∀ (t : ordnode α), dual (dual t) = t
| nil := rfl
| (node s l x r) := by rw [dual, dual, dual_dual, dual_dual]

@[simp] theorem size_dual (t : ordnode α) : size (dual t) = size t :=
by cases t; refl

/-! `balanced` -/

/-- The `balanced_sz l r` asserts that a hypothetical tree with children of sizes `l` and `r` is
balanced: either `l ≤ δ * r` and `r ≤ δ * r`, or the tree is trivial with a singleton on one side
and nothing on the other. -/
def balanced_sz (l r : ℕ) : Prop :=
l + r ≤ 1 ∨ (l ≤ delta * r ∧ r ≤ delta * l)

instance balanced_sz.dec : decidable_rel balanced_sz := λ l r, or.decidable

/-- The `balanced t` asserts that the tree `t` satisfies the balance invariants
(at every level). -/
def balanced : ordnode α → Prop
| nil := true
| (node _ l _ r) := balanced_sz (size l) (size r) ∧ balanced l ∧ balanced r

instance balanced.dec : decidable_pred (@balanced α) | t :=
by induction t; unfold balanced; resetI; apply_instance

theorem balanced_sz.symm {l r : ℕ} : balanced_sz l r → balanced_sz r l :=
or.imp (by rw add_comm; exact id) and.symm

theorem balanced_sz_zero {l : ℕ} : balanced_sz l 0 ↔ l ≤ 1 :=
by simp [balanced_sz] { contextual := tt }

theorem balanced_sz_up {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂)
  (h₂ : l + r₂ ≤ 1 ∨ r₂ ≤ delta * l)
  (H : balanced_sz l r₁) : balanced_sz l r₂ :=
begin
  refine or_iff_not_imp_left.2 (λ h, _),
  refine ⟨_, h₂.resolve_left h⟩,
  cases H,
  { cases r₂,
    { cases h (le_trans (nat.add_le_add_left (nat.zero_le _) _) H) },
    { exact le_trans (le_trans (nat.le_add_right _ _) H) (nat.le_add_left 1 _) } },
  { exact le_trans H.1 (nat.mul_le_mul_left _ h₁) }
end

theorem balanced_sz_down {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂)
  (h₂ : l + r₂ ≤ 1 ∨ l ≤ delta * r₁)
  (H : balanced_sz l r₂) : balanced_sz l r₁ :=
have l + r₂ ≤ 1 → balanced_sz l r₁, from
  λ H, or.inl (le_trans (nat.add_le_add_left h₁ _) H),
or.cases_on H this (λ H, or.cases_on h₂ this (λ h₂,
  or.inr ⟨h₂, le_trans h₁ H.2⟩))

theorem balanced.dual : ∀ {t : ordnode α}, balanced t → balanced (dual t)
| nil h := ⟨⟩
| (node s l x r) ⟨b, bl, br⟩ :=
  ⟨by rw [size_dual, size_dual]; exact b.symm, br.dual, bl.dual⟩

/-! ### `rotate` and `balance` -/

/-- Build a tree from three nodes, left associated (ignores the invariants). -/
def node3_l (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) : ordnode α :=
node' (node' l x m) y r

/-- Build a tree from three nodes, right associated (ignores the invariants). -/
def node3_r (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) : ordnode α :=
node' l x (node' m y r)

/-- Build a tree from three nodes, with `a () b -> (a ()) b` and `a (b c) d -> ((a b) (c d))`. -/
def node4_l : ordnode α → α → ordnode α → α → ordnode α → ordnode α
| l x (node _ ml y mr) z r := node' (node' l x ml) y (node' mr z r)
| l x nil z r := node3_l l x nil z r -- should not happen

/-- Build a tree from three nodes, with `a () b -> a (() b)` and `a (b c) d -> ((a b) (c d))`. -/
def node4_r : ordnode α → α → ordnode α → α → ordnode α → ordnode α
| l x (node _ ml y mr) z r := node' (node' l x ml) y (node' mr z r)
| l x nil z r := node3_r l x nil z r -- should not happen

/-- Concatenate two nodes, performing a left rotation `x (y z) -> ((x y) z)`
if balance is upset. -/
def rotate_l : ordnode α → α → ordnode α → ordnode α
| l x (node _ m y r) :=
  if size m < ratio * size r then node3_l l x m y r else node4_l l x m y r
| l x nil := node' l x nil -- should not happen

/-- Concatenate two nodes, performing a right rotation `(x y) z -> (x (y z))`
if balance is upset. -/
def rotate_r : ordnode α → α → ordnode α → ordnode α
| (node _ l x m) y r :=
  if size m < ratio * size l then node3_r l x m y r else node4_r l x m y r
| nil y r :=  node' nil y r -- should not happen

/-- A left balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balance_l' (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
if size l + size r ≤ 1 then node' l x r else
if size l > delta * size r then rotate_r l x r else
node' l x r

/-- A right balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balance_r' (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
if size l + size r ≤ 1 then node' l x r else
if size r > delta * size l then rotate_l l x r else
node' l x r

/-- The full balance operation. This is the same as `balance`, but with less manual inlining.
It is somewhat easier to work with this version in proofs. -/
def balance' (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
if size l + size r ≤ 1 then node' l x r else
if size r > delta * size l then rotate_l l x r else
if size l > delta * size r then rotate_r l x r else
node' l x r

theorem dual_node' (l : ordnode α) (x : α) (r : ordnode α) :
  dual (node' l x r) = node' (dual r) x (dual l) := by simp [node', add_comm]

theorem dual_node3_l (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node3_l l x m y r) = node3_r (dual r) y (dual m) x (dual l) :=
by simp [node3_l, node3_r, dual_node']

theorem dual_node3_r (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node3_r l x m y r) = node3_l (dual r) y (dual m) x (dual l) :=
by simp [node3_l, node3_r, dual_node']

theorem dual_node4_l (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node4_l l x m y r) = node4_r (dual r) y (dual m) x (dual l) :=
by cases m; simp [node4_l, node4_r, dual_node3_l, dual_node']

theorem dual_node4_r (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node4_r l x m y r) = node4_l (dual r) y (dual m) x (dual l) :=
by cases m; simp [node4_l, node4_r, dual_node3_r, dual_node']

theorem dual_rotate_l (l : ordnode α) (x : α) (r : ordnode α) :
  dual (rotate_l l x r) = rotate_r (dual r) x (dual l) :=
by cases r; simp [rotate_l, rotate_r, dual_node'];
   split_ifs; simp [dual_node3_l, dual_node4_l]

theorem dual_rotate_r (l : ordnode α) (x : α) (r : ordnode α) :
  dual (rotate_r l x r) = rotate_l (dual r) x (dual l) :=
by rw [← dual_dual (rotate_l _ _ _), dual_rotate_l, dual_dual, dual_dual]

theorem dual_balance' (l : ordnode α) (x : α) (r : ordnode α) :
  dual (balance' l x r) = balance' (dual r) x (dual l) :=
begin
  simp [balance', add_comm], split_ifs; simp [dual_node', dual_rotate_l, dual_rotate_r],
  cases delta_lt_false h_1 h_2
end

theorem dual_balance_l (l : ordnode α) (x : α) (r : ordnode α) :
  dual (balance_l l x r) = balance_r (dual r) x (dual l) :=
begin
  unfold balance_l balance_r,
  cases r with rs rl rx rr,
  { cases l with ls ll lx lr, {refl},
    cases ll with lls lll llx llr; cases lr with lrs lrl lrx lrr;
      dsimp only [dual]; try {refl},
    split_ifs; repeat {simp [h, add_comm]} },
  { cases l with ls ll lx lr, {refl},
    dsimp only [dual],
    split_ifs, swap, {simp [add_comm]},
    cases ll with lls lll llx llr; cases lr with lrs lrl lrx lrr; try {refl},
    dsimp only [dual],
    split_ifs; simp [h, add_comm] },
end

theorem dual_balance_r (l : ordnode α) (x : α) (r : ordnode α) :
  dual (balance_r l x r) = balance_l (dual r) x (dual l) :=
by rw [← dual_dual (balance_l _ _ _), dual_balance_l, dual_dual, dual_dual]

theorem sized.node3_l {l x m y r}
  (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node3_l l x m y r) :=
(hl.node' hm).node' hr

theorem sized.node3_r {l x m y r}
  (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node3_r l x m y r) :=
hl.node' (hm.node' hr)

theorem sized.node4_l {l x m y r}
  (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node4_l l x m y r) :=
by cases m; [exact (hl.node' hm).node' hr,
  exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

theorem node3_l_size {l x m y r} :
  size (@node3_l α l x m y r) = size l + size m + size r + 2 :=
by dsimp [node3_l, node', size]; rw add_right_comm _ 1

theorem node3_r_size {l x m y r} :
  size (@node3_r α l x m y r) = size l + size m + size r + 2 :=
by dsimp [node3_r, node', size]; rw [← add_assoc, ← add_assoc]

theorem node4_l_size {l x m y r} (hm : sized m) :
  size (@node4_l α l x m y r) = size l + size m + size r + 2 :=
by cases m; simp [node4_l, node3_l, node', add_comm, add_left_comm]; [skip, simp [size, hm.1]];
   rw [← add_assoc, ← bit0]; simp [add_comm, add_left_comm]

theorem sized.dual : ∀ {t : ordnode α} (h : sized t), sized (dual t)
| nil h := ⟨⟩
| (node s l x r) ⟨rfl, sl, sr⟩ := ⟨by simp [size_dual, add_comm], sized.dual sr, sized.dual sl⟩

theorem sized.dual_iff {t : ordnode α} : sized (dual t) ↔ sized t :=
⟨λ h, by rw ← dual_dual t; exact h.dual, sized.dual⟩

theorem sized.rotate_l {l x r} (hl : @sized α l) (hr : sized r) : sized (rotate_l l x r) :=
begin
  cases r, {exact hl.node' hr},
  rw rotate_l, split_ifs,
  { exact hl.node3_l hr.2.1 hr.2.2 },
  { exact hl.node4_l hr.2.1 hr.2.2 }
end

theorem sized.rotate_r {l x r} (hl : @sized α l) (hr : sized r) : sized (rotate_r l x r) :=
sized.dual_iff.1 $ by rw dual_rotate_r; exact hr.dual.rotate_l hl.dual

theorem sized.rotate_l_size {l x r} (hm : sized r) :
  size (@rotate_l α l x r) = size l + size r + 1 :=
begin
  cases r; simp [rotate_l],
  simp [size, hm.1, add_comm, add_left_comm], rw [← add_assoc, ← bit0], simp,
  split_ifs; simp [node3_l_size, node4_l_size hm.2.1, add_comm, add_left_comm]
end

theorem sized.rotate_r_size {l x r} (hl : sized l) :
  size (@rotate_r α l x r) = size l + size r + 1 :=
by rw [← size_dual, dual_rotate_r, hl.dual.rotate_l_size,
  size_dual, size_dual, add_comm (size l)]

theorem sized.balance' {l x r} (hl : @sized α l) (hr : sized r) : sized (balance' l x r) :=
begin
  unfold balance', split_ifs,
  { exact hl.node' hr },
  { exact hl.rotate_l hr },
  { exact hl.rotate_r hr },
  { exact hl.node' hr }
end

theorem size_balance' {l x r} (hl : @sized α l) (hr : sized r) :
  size (@balance' α l x r) = size l + size r + 1 :=
begin
  unfold balance', split_ifs,
  { refl },
  { exact hr.rotate_l_size },
  { exact hl.rotate_r_size },
  { refl }
end

/-! ## `all`, `any`, `emem`, `amem` -/

theorem all.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, all P t → all Q t
| nil h := ⟨⟩
| (node _ l x r) ⟨h₁, h₂, h₃⟩ := ⟨h₁.imp, H _ h₂, h₃.imp⟩

theorem any.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, any P t → any Q t
| nil := id
| (node _ l x r) := or.imp any.imp $ or.imp (H _) any.imp

theorem all_singleton {P : α → Prop} {x : α} : all P (singleton x) ↔ P x :=
⟨λ h, h.2.1, λ h, ⟨⟨⟩, h, ⟨⟩⟩⟩

theorem any_singleton {P : α → Prop} {x : α} : any P (singleton x) ↔ P x :=
⟨by rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩); exact h, λ h, or.inr (or.inl h)⟩

theorem all_dual {P : α → Prop} : ∀ {t : ordnode α},
  all P (dual t) ↔ all P t
| nil := iff.rfl
| (node s l x r) :=
  ⟨λ ⟨hr, hx, hl⟩, ⟨all_dual.1 hl, hx, all_dual.1 hr⟩,
   λ ⟨hl, hx, hr⟩, ⟨all_dual.2 hr, hx, all_dual.2 hl⟩⟩

theorem all_iff_forall {P : α → Prop} : ∀ {t}, all P t ↔ ∀ x, emem x t → P x
| nil := (iff_true_intro $ by rintro _ ⟨⟩).symm
| (node _ l x r) :=
  by simp [all, emem, all_iff_forall, any, or_imp_distrib, forall_and_distrib]

theorem any_iff_exists {P : α → Prop} : ∀ {t}, any P t ↔ ∃ x, emem x t ∧ P x
| nil := ⟨by rintro ⟨⟩, by rintro ⟨_, ⟨⟩, _⟩⟩
| (node _ l x r) :=
  by simp [any, emem, any_iff_exists, or_and_distrib_right, exists_or_distrib]

theorem emem_iff_all {x : α} {t} : emem x t ↔ ∀ P, all P t → P x :=
⟨λ h P al, all_iff_forall.1 al _ h,
 λ H, H _ $ all_iff_forall.2 $ λ _, id⟩

theorem all_node' {P l x r} :
  @all α P (node' l x r) ↔ all P l ∧ P x ∧ all P r := iff.rfl

theorem all_node3_l {P l x m y r} :
  @all α P (node3_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
by simp [node3_l, all_node', and_assoc]

theorem all_node3_r {P l x m y r} :
  @all α P (node3_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r := iff.rfl

theorem all_node4_l {P l x m y r} :
  @all α P (node4_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
by cases m; simp [node4_l, all_node', all, all_node3_l, and_assoc]

theorem all_node4_r {P l x m y r} :
  @all α P (node4_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
by cases m; simp [node4_r, all_node', all, all_node3_r, and_assoc]

theorem all_rotate_l {P l x r} :
  @all α P (rotate_l l x r) ↔ all P l ∧ P x ∧ all P r :=
by cases r; simp [rotate_l, all_node'];
   split_ifs; simp [all_node3_l, all_node4_l, all]

theorem all_rotate_r {P l x r} :
  @all α P (rotate_r l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw [← all_dual, dual_rotate_r, all_rotate_l];
   simp [all_dual, and_comm, and.left_comm]

theorem all_balance' {P l x r} :
  @all α P (balance' l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw balance'; split_ifs; simp [all_node', all_rotate_l, all_rotate_r]

/-! ### `to_list` -/

theorem foldr_cons_eq_to_list : ∀ (t : ordnode α) (r : list α),
  t.foldr list.cons r = to_list t ++ r
| nil r := rfl
| (node _ l x r) r' := by rw [foldr, foldr_cons_eq_to_list, foldr_cons_eq_to_list,
  ← list.cons_append, ← list.append_assoc, ← foldr_cons_eq_to_list]; refl

@[simp] theorem to_list_nil : to_list (@nil α) = [] := rfl

@[simp] theorem to_list_node (s l x r) : to_list (@node α s l x r) = to_list l ++ x :: to_list r :=
by rw [to_list, foldr, foldr_cons_eq_to_list]; refl

theorem emem_iff_mem_to_list {x : α} {t} : emem x t ↔ x ∈ to_list t :=
by unfold emem; induction t; simp [any, *, or_assoc]

theorem length_to_list' : ∀ t : ordnode α, (to_list t).length = t.real_size
| nil := rfl
| (node _ l _ r) := by rw [to_list_node, list.length_append, list.length_cons,
  length_to_list', length_to_list']; refl

theorem length_to_list {t : ordnode α} (h : sized t) : (to_list t).length = t.size :=
by rw [length_to_list', size_eq_real_size h]

theorem equiv_iff {t₁ t₂ : ordnode α} (h₁ : sized t₁) (h₂ : sized t₂) :
  equiv t₁ t₂ ↔ to_list t₁ = to_list t₂ :=
and_iff_right_of_imp $ λ h, by rw [← length_to_list h₁, h, length_to_list h₂]

/-! ### `mem` -/

theorem pos_size_of_mem [has_le α] [@decidable_rel α (≤)]
  {x : α} {t : ordnode α} (h : sized t) (h_mem : x ∈ t) : 0 < size t :=
by { cases t, { contradiction }, { simp [h.1] } }

/-! ### `(find/erase/split)_(min/max)` -/

theorem find_min'_dual : ∀ t (x : α), find_min' (dual t) x = find_max' x t
| nil x := rfl
| (node _ l x r) _ := find_min'_dual r x

theorem find_max'_dual (t) (x : α) : find_max' x (dual t) = find_min' t x :=
by rw [← find_min'_dual, dual_dual]

theorem find_min_dual : ∀ t : ordnode α, find_min (dual t) = find_max t
| nil := rfl
| (node _ l x r) := congr_arg some $ find_min'_dual _ _

theorem find_max_dual (t : ordnode α) : find_max (dual t) = find_min t :=
by rw [← find_min_dual, dual_dual]

theorem dual_erase_min : ∀ t : ordnode α, dual (erase_min t) = erase_max (dual t)
| nil := rfl
| (node _ nil x r) := rfl
| (node _ l@(node _ _ _ _) x r) :=
  by rw [erase_min, dual_balance_r, dual_erase_min, dual, dual, dual, erase_max]

theorem dual_erase_max (t : ordnode α) : dual (erase_max t) = erase_min (dual t) :=
by rw [← dual_dual (erase_min _), dual_erase_min, dual_dual]

theorem split_min_eq : ∀ s l (x : α) r,
  split_min' l x r = (find_min' l x, erase_min (node s l x r))
| _ nil x r := rfl
| _ (node ls ll lx lr) x r :=
  by rw [split_min', split_min_eq, split_min', find_min', erase_min]

theorem split_max_eq : ∀ s l (x : α) r,
  split_max' l x r = (erase_max (node s l x r), find_max' x r)
| _ l x nil := rfl
| _ l x (node ls ll lx lr) :=
  by rw [split_max', split_max_eq, split_max', find_max', erase_max]

@[elab_as_eliminator]
theorem find_min'_all {P : α → Prop} : ∀ t (x : α), all P t → P x → P (find_min' t x)
| nil x h hx := hx
| (node _ ll lx lr) x ⟨h₁, h₂, h₃⟩ hx := find_min'_all _ _ h₁ h₂

@[elab_as_eliminator]
theorem find_max'_all {P : α → Prop} : ∀ (x : α) t, P x → all P t → P (find_max' x t)
| x nil hx h := hx
| x (node _ ll lx lr) hx ⟨h₁, h₂, h₃⟩ := find_max'_all _ _ h₂ h₃

/-! ### `glue` -/

/-! ### `merge` -/

@[simp] theorem merge_nil_left (t : ordnode α) : merge t nil = t := by cases t; refl

@[simp] theorem merge_nil_right (t : ordnode α) : merge nil t = t := rfl

@[simp] theorem merge_node {ls ll lx lr rs rl rx rr} :
  merge (@node α ls ll lx lr) (node rs rl rx rr) =
  if delta * ls < rs then
    balance_l (merge (node ls ll lx lr) rl) rx rr
  else if delta * rs < ls then
    balance_r ll lx (merge lr (node rs rl rx rr))
  else glue (node ls ll lx lr) (node rs rl rx rr) := rfl

/-! ### `insert` -/

theorem dual_insert [preorder α] [is_total α (≤)] [@decidable_rel α (≤)] (x : α) :
  ∀ t : ordnode α, dual (ordnode.insert x t) = @ordnode.insert (order_dual α) _ _ x (dual t)
| nil := rfl
| (node _ l y r) := begin
  rw [ordnode.insert, dual, ordnode.insert, order_dual.cmp_le_flip, ← cmp_le_swap x y],
  cases cmp_le x y;
  simp [ordering.swap, ordnode.insert, dual_balance_l, dual_balance_r, dual_insert]
end

/-! ### `balance` properties -/

theorem balance_eq_balance' {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r) :
  @balance α l x r = balance' l x r :=
begin
  cases l with ls ll lx lr,
  { cases r with rs rl rx rr,
    { refl },
    { rw sr.eq_node' at hr ⊢,
      cases rl with rls rll rlx rlr; cases rr with rrs rrl rrx rrr;
      dsimp [balance, balance'],
      { refl },
      { have : size rrl = 0 ∧ size rrr = 0,
        { have := balanced_sz_zero.1 hr.1.symm,
          rwa [size, sr.2.2.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sr.2.2.2.1.size_eq_zero.1 this.1,
        cases sr.2.2.2.2.size_eq_zero.1 this.2,
        have : rrs = 1 := sr.2.2.1, subst rrs,
        rw [if_neg, if_pos, rotate_l, if_pos], {refl},
        all_goals {exact dec_trivial} },
      { have : size rll = 0 ∧ size rlr = 0,
        { have := balanced_sz_zero.1 hr.1,
          rwa [size, sr.2.1.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sr.2.1.2.1.size_eq_zero.1 this.1,
        cases sr.2.1.2.2.size_eq_zero.1 this.2,
        have : rls = 1 := sr.2.1.1, subst rls,
        rw [if_neg, if_pos, rotate_l, if_neg], {refl},
        all_goals {exact dec_trivial} },
      { symmetry, rw [zero_add, if_neg, if_pos, rotate_l],
        { split_ifs,
          { simp [node3_l, node', add_comm, add_left_comm] },
          { simp [node4_l, node', sr.2.1.1, add_comm, add_left_comm] } },
        { exact dec_trivial },
        { exact not_le_of_gt (nat.succ_lt_succ
            (add_pos sr.2.1.pos sr.2.2.pos)) } } } },
  { cases r with rs rl rx rr,
    { rw sl.eq_node' at hl ⊢,
      cases ll with lls lll llx llr; cases lr with lrs lrl lrx lrr;
      dsimp [balance, balance'],
      { refl },
      { have : size lrl = 0 ∧ size lrr = 0,
        { have := balanced_sz_zero.1 hl.1.symm,
          rwa [size, sl.2.2.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sl.2.2.2.1.size_eq_zero.1 this.1,
        cases sl.2.2.2.2.size_eq_zero.1 this.2,
        have : lrs = 1 := sl.2.2.1, subst lrs,
        rw [if_neg, if_neg, if_pos, rotate_r, if_neg], {refl},
        all_goals {exact dec_trivial} },
      { have : size lll = 0 ∧ size llr = 0,
        { have := balanced_sz_zero.1 hl.1,
          rwa [size, sl.2.1.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sl.2.1.2.1.size_eq_zero.1 this.1,
        cases sl.2.1.2.2.size_eq_zero.1 this.2,
        have : lls = 1 := sl.2.1.1, subst lls,
        rw [if_neg, if_neg, if_pos, rotate_r, if_pos], {refl},
        all_goals {exact dec_trivial} },
      { symmetry, rw [if_neg, if_neg, if_pos, rotate_r],
        { split_ifs,
          { simp [node3_r, node', add_comm, add_left_comm] },
          { simp [node4_r, node', sl.2.2.1, add_comm, add_left_comm] } },
        { exact dec_trivial },
        { exact dec_trivial },
        { exact not_le_of_gt (nat.succ_lt_succ
            (add_pos sl.2.1.pos sl.2.2.pos)) } } },
    { simp [balance, balance'],
      symmetry, rw [if_neg],
      { split_ifs,
        { have rd : delta ≤ size rl + size rr,
          { have := lt_of_le_of_lt (nat.mul_le_mul_left _ sl.pos) h,
            rwa [sr.1, nat.lt_succ_iff] at this },
          cases rl with rls rll rlx rlr,
          { rw [size, zero_add] at rd,
            exact absurd (le_trans rd (balanced_sz_zero.1 hr.1.symm)) dec_trivial },
          cases rr with rrs rrl rrx rrr,
          { exact absurd (le_trans rd (balanced_sz_zero.1 hr.1)) dec_trivial },
          dsimp [rotate_l], split_ifs,
          { simp [node3_l, node', sr.1, add_comm, add_left_comm] },
          { simp [node4_l, node', sr.1, sr.2.1.1, add_comm, add_left_comm] } },
        { have ld : delta ≤ size ll + size lr,
          { have := lt_of_le_of_lt (nat.mul_le_mul_left _ sr.pos) h_1,
            rwa [sl.1, nat.lt_succ_iff] at this },
          cases ll with lls lll llx llr,
          { rw [size, zero_add] at ld,
            exact absurd (le_trans ld (balanced_sz_zero.1 hl.1.symm)) dec_trivial },
          cases lr with lrs lrl lrx lrr,
          { exact absurd (le_trans ld (balanced_sz_zero.1 hl.1)) dec_trivial },
          dsimp [rotate_r], split_ifs,
          { simp [node3_r, node', sl.1, add_comm, add_left_comm] },
          { simp [node4_r, node', sl.1, sl.2.2.1, add_comm, add_left_comm] } },
        { simp [node'] } },
      { exact not_le_of_gt (add_le_add sl.pos sr.pos : 2 ≤ ls + rs) } } }
end

theorem balance_l_eq_balance {l x r}
  (sl : sized l) (sr : sized r)
  (H1 : size l = 0 → size r ≤ 1)
  (H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) :
  @balance_l α l x r = balance l x r :=
begin
  cases r with rs rl rx rr,
  { refl },
  { cases l with ls ll lx lr,
    { have : size rl = 0 ∧ size rr = 0,
      { have := H1 rfl,
        rwa [size, sr.1, nat.succ_le_succ_iff,
          nat.le_zero_iff, add_eq_zero_iff] at this },
      cases sr.2.1.size_eq_zero.1 this.1,
      cases sr.2.2.size_eq_zero.1 this.2,
      rw sr.eq_node', refl },
    { replace H2 : ¬ rs > delta * ls := not_lt_of_le (H2 sl.pos sr.pos),
      simp [balance_l, balance, H2]; split_ifs; simp [add_comm] } }
end

/-- `raised n m` means `m` is either equal or one up from `n`. -/
def raised (n m : ℕ) : Prop := m = n ∨ m = n + 1

theorem raised_iff {n m} : raised n m ↔ n ≤ m ∧ m ≤ n + 1 :=
begin
  split, rintro (rfl | rfl),
  { exact ⟨le_refl _, nat.le_succ _⟩ },
  { exact ⟨nat.le_succ _, le_refl _⟩ },
  { rintro ⟨h₁, h₂⟩,
    rcases eq_or_lt_of_le h₁ with rfl | h₁,
    { exact or.inl rfl },
    { exact or.inr (le_antisymm h₂ h₁) } }
end

theorem raised.dist_le {n m} (H : raised n m) : nat.dist n m ≤ 1 :=
by cases raised_iff.1 H with H1 H2;
  rwa [nat.dist_eq_sub_of_le H1, nat.sub_le_left_iff_le_add]

theorem raised.dist_le' {n m} (H : raised n m) : nat.dist m n ≤ 1 :=
by rw nat.dist_comm; exact H.dist_le

theorem raised.add_left (k) {n m} (H : raised n m) : raised (k + n) (k + m) :=
begin
  rcases H with rfl | rfl,
  { exact or.inl rfl },
  { exact or.inr rfl }
end

theorem raised.add_right (k) {n m} (H : raised n m) : raised (n + k) (m + k) :=
by rw [add_comm, add_comm m]; exact H.add_left _

theorem raised.right {l x₁ x₂ r₁ r₂} (H : raised (size r₁) (size r₂)) :
  raised (size (@node' α l x₁ r₁)) (size (@node' α l x₂ r₂)) :=
begin
  dsimp [node', size], generalize_hyp : size r₂ = m at H ⊢,
  rcases H with rfl | rfl,
  { exact or.inl rfl },
  { exact or.inr rfl }
end

theorem balance_l_eq_balance' {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised (size r) r' ∧ balanced_sz (size l) r')) :
  @balance_l α l x r = balance' l x r :=
begin
  rw [← balance_eq_balance' hl hr sl sr, balance_l_eq_balance sl sr],
  { intro l0, rw l0 at H,
    rcases H with ⟨_, ⟨⟨⟩⟩|⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩,
    { exact balanced_sz_zero.1 H.symm },
    exact le_trans (raised_iff.1 e).1 (balanced_sz_zero.1 H.symm) },
  { intros l1 r1,
    rcases H with ⟨l', e, H | ⟨H₁, H₂⟩⟩ | ⟨r', e, H | ⟨H₁, H₂⟩⟩,
    { exact le_trans (le_trans (nat.le_add_left _ _) H)
        (mul_pos dec_trivial l1 : (0:ℕ)<_) },
    { exact le_trans H₂ (nat.mul_le_mul_left _ (raised_iff.1 e).1) },
    { cases raised_iff.1 e, unfold delta, linarith },
    { exact le_trans (raised_iff.1 e).1 H₂ } }
end

theorem balance_sz_dual {l r}
  (H : (∃ l', raised (@size α l) l' ∧ balanced_sz l' (@size α r)) ∨
    ∃ r', raised r' (size r) ∧ balanced_sz (size l) r') :
  (∃ l', raised l' (size (dual r)) ∧ balanced_sz l' (size (dual l))) ∨
    ∃ r', raised (size (dual l)) r' ∧ balanced_sz (size (dual r)) r' :=
begin
  rw [size_dual, size_dual],
  exact H.symm.imp
    (Exists.imp $ λ _, and.imp_right balanced_sz.symm)
    (Exists.imp $ λ _, and.imp_right balanced_sz.symm)
end

theorem size_balance_l {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised (size r) r' ∧ balanced_sz (size l) r')) :
  size (@balance_l α l x r) = size l + size r + 1 :=
by rw [balance_l_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balance_l {P l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised (size r) r' ∧ balanced_sz (size l) r')) :
  all P (@balance_l α l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw [balance_l_eq_balance' hl hr sl sr H, all_balance']

theorem balance_r_eq_balance' {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised r' (size r) ∧ balanced_sz (size l) r')) :
  @balance_r α l x r = balance' l x r :=
by rw [← dual_dual (balance_r l x r), dual_balance_r,
  balance_l_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H),
  ← dual_balance', dual_dual]

theorem size_balance_r {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised r' (size r) ∧ balanced_sz (size l) r')) :
  size (@balance_r α l x r) = size l + size r + 1 :=
by rw [balance_r_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balance_r {P l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised r' (size r) ∧ balanced_sz (size l) r')) :
  all P (@balance_r α l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw [balance_r_eq_balance' hl hr sl sr H, all_balance']

/-! ### `bounded` -/

section
variable [preorder α]

/-- `bounded t lo hi` says that every element `x ∈ t` is in the range `lo < x < hi`, and also this
property holds recursively in subtrees, making the full tree a BST. The bounds can be set to
`lo = ⊥` and `hi = ⊤` if we care only about the internal ordering constraints. -/
def bounded : ordnode α → with_bot α → with_top α → Prop
| nil (some a) (some b) := a < b
| nil _ _ := true
| (node _ l x r) o₁ o₂ := bounded l o₁ ↑x ∧ bounded r ↑x o₂

theorem bounded.dual : ∀ {t : ordnode α} {o₁ o₂} (h : bounded t o₁ o₂),
  @bounded (order_dual α) _ (dual t) o₂ o₁
| nil o₁ o₂ h := by cases o₁; cases o₂; try {trivial}; exact h
| (node s l x r) _ _ ⟨ol, or⟩ := ⟨or.dual, ol.dual⟩

theorem bounded.dual_iff {t : ordnode α} {o₁ o₂} : bounded t o₁ o₂ ↔
  @bounded (order_dual α) _ (dual t) o₂ o₁ :=
⟨bounded.dual, λ h, by have := bounded.dual h;
  rwa [dual_dual, order_dual.preorder.dual_dual] at this⟩

theorem bounded.weak_left : ∀ {t : ordnode α} {o₁ o₂}, bounded t o₁ o₂ → bounded t ⊥ o₂
| nil o₁ o₂ h := by cases o₂; try {trivial}; exact h
| (node s l x r) _ _ ⟨ol, or⟩ := ⟨ol.weak_left, or⟩

theorem bounded.weak_right : ∀ {t : ordnode α} {o₁ o₂}, bounded t o₁ o₂ → bounded t o₁ ⊤
| nil o₁ o₂ h := by cases o₁; try {trivial}; exact h
| (node s l x r) _ _ ⟨ol, or⟩ := ⟨ol, or.weak_right⟩

theorem bounded.weak {t : ordnode α} {o₁ o₂} (h : bounded t o₁ o₂) : bounded t ⊥ ⊤ :=
h.weak_left.weak_right

theorem bounded.mono_left {x y : α} (xy : x ≤ y) :
  ∀ {t : ordnode α} {o}, bounded t ↑y o → bounded t ↑x o
| nil none h := ⟨⟩
| nil (some z) h := lt_of_le_of_lt xy h
| (node s l z r) o ⟨ol, or⟩ := ⟨ol.mono_left, or⟩

theorem bounded.mono_right {x y : α} (xy : x ≤ y) :
  ∀ {t : ordnode α} {o}, bounded t o ↑x → bounded t o ↑y
| nil none h := ⟨⟩
| nil (some z) h := lt_of_lt_of_le h xy
| (node s l z r) o ⟨ol, or⟩ := ⟨ol, or.mono_right⟩

theorem bounded.to_lt : ∀ {t : ordnode α} {x y : α}, bounded t x y → x < y
| nil x y h := h
| (node _ l y r) x z ⟨h₁, h₂⟩ := lt_trans h₁.to_lt h₂.to_lt

theorem bounded.to_nil {t : ordnode α} : ∀ {o₁ o₂}, bounded t o₁ o₂ → bounded nil o₁ o₂
| none _ h := ⟨⟩
| (some _) none h := ⟨⟩
| (some x) (some y) h := h.to_lt

theorem bounded.trans_left {t₁ t₂ : ordnode α} {x : α} :
  ∀ {o₁ o₂}, bounded t₁ o₁ ↑x → bounded t₂ ↑x o₂ → bounded t₂ o₁ o₂
| none o₂ h₁ h₂ := h₂.weak_left
| (some y) o₂ h₁ h₂ := h₂.mono_left (le_of_lt h₁.to_lt)

theorem bounded.trans_right {t₁ t₂ : ordnode α} {x : α} :
  ∀ {o₁ o₂}, bounded t₁ o₁ ↑x → bounded t₂ ↑x o₂ → bounded t₁ o₁ o₂
| o₁ none h₁ h₂ := h₁.weak_right
| o₁ (some y) h₁ h₂ := h₁.mono_right (le_of_lt h₂.to_lt)

theorem bounded.mem_lt : ∀ {t o} {x : α}, bounded t o ↑x → all (< x) t
| nil o x _ := ⟨⟩
| (node _ l y r) o x ⟨h₁, h₂⟩ :=
  ⟨h₁.mem_lt.imp (λ z h, lt_trans h h₂.to_lt), h₂.to_lt, h₂.mem_lt⟩

theorem bounded.mem_gt : ∀ {t o} {x : α}, bounded t ↑x o → all (> x) t
| nil o x _ := ⟨⟩
| (node _ l y r) o x ⟨h₁, h₂⟩ :=
  ⟨h₁.mem_gt, h₁.to_lt, h₂.mem_gt.imp (λ z, lt_trans h₁.to_lt)⟩

theorem bounded.of_lt : ∀ {t o₁ o₂} {x : α},
  bounded t o₁ o₂ → bounded nil o₁ ↑x → all (< x) t → bounded t o₁ ↑x
| nil o₁ o₂ x _ hn _ := hn
| (node _ l y r) o₁ o₂ x ⟨h₁, h₂⟩ hn ⟨al₁, al₂, al₃⟩ := ⟨h₁, h₂.of_lt al₂ al₃⟩

theorem bounded.of_gt : ∀ {t o₁ o₂} {x : α},
  bounded t o₁ o₂ → bounded nil ↑x o₂ → all (> x) t → bounded t ↑x o₂
| nil o₁ o₂ x _ hn _ := hn
| (node _ l y r) o₁ o₂ x ⟨h₁, h₂⟩ hn ⟨al₁, al₂, al₃⟩ := ⟨h₁.of_gt al₂ al₁, h₂⟩

theorem bounded.to_sep {t₁ t₂ o₁ o₂} {x : α}
  (h₁ : bounded t₁ o₁ ↑x) (h₂ : bounded t₂ ↑x o₂) : t₁.all (λ y, t₂.all (λ z : α, y < z)) :=
h₁.mem_lt.imp $ λ y yx, h₂.mem_gt.imp $ λ z xz, lt_trans yx xz

end

/-! ### `valid` -/

section
variable [preorder α]

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. This version of `valid` also puts all elements in the tree in the interval `(lo, hi)`. -/
structure valid' (lo : with_bot α) (t : ordnode α) (hi : with_top α) : Prop :=
(ord : t.bounded lo hi)
(sz : t.sized)
(bal : t.balanced)

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. -/
def valid (t : ordnode α) : Prop := valid' ⊥ t ⊤

theorem valid'.mono_left {x y : α} (xy : x ≤ y)
  {t : ordnode α} {o} (h : valid' ↑y t o) : valid' ↑x t o :=
⟨h.1.mono_left xy, h.2, h.3⟩

theorem valid'.mono_right {x y : α} (xy : x ≤ y)
  {t : ordnode α} {o} (h : valid' o t ↑x) : valid' o t ↑y :=
⟨h.1.mono_right xy, h.2, h.3⟩

theorem valid'.trans_left {t₁ t₂ : ordnode α} {x : α} {o₁ o₂}
  (h : bounded t₁ o₁ ↑x) (H : valid' ↑x t₂ o₂) : valid' o₁ t₂ o₂ :=
⟨h.trans_left H.1, H.2, H.3⟩

theorem valid'.trans_right {t₁ t₂ : ordnode α} {x : α} {o₁ o₂}
  (H : valid' o₁ t₁ ↑x) (h : bounded t₂ ↑x o₂) : valid' o₁ t₁ o₂ :=
⟨H.1.trans_right h, H.2, H.3⟩

theorem valid'.of_lt {t : ordnode α} {x : α} {o₁ o₂}
  (H : valid' o₁ t o₂) (h₁ : bounded nil o₁ ↑x) (h₂ : all (< x) t) : valid' o₁ t ↑x :=
⟨H.1.of_lt h₁ h₂, H.2, H.3⟩

theorem valid'.of_gt {t : ordnode α} {x : α} {o₁ o₂}
  (H : valid' o₁ t o₂) (h₁ : bounded nil ↑x o₂) (h₂ : all (> x) t) : valid' ↑x t o₂ :=
⟨H.1.of_gt h₁ h₂, H.2, H.3⟩

theorem valid'.valid {t o₁ o₂} (h : @valid' α _ o₁ t o₂) : valid t := ⟨h.1.weak, h.2, h.3⟩

theorem valid'_nil {o₁ o₂} (h : bounded nil o₁ o₂) : valid' o₁ (@nil α) o₂ := ⟨h, ⟨⟩, ⟨⟩⟩

theorem valid_nil : valid (@nil α) := valid'_nil ⟨⟩

theorem valid'.node {s l x r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : balanced_sz (size l) (size r)) (hs : s = size l + size r + 1) :
  valid' o₁ (@node α s l x r) o₂ :=
⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

theorem valid'.dual : ∀ {t : ordnode α} {o₁ o₂} (h : valid' o₁ t o₂),
  @valid' (order_dual α) _ o₂ (dual t) o₁
| nil o₁ o₂ h := valid'_nil h.1.dual
| (node s l x r) o₁ o₂ ⟨⟨ol, or⟩, ⟨rfl, sl, sr⟩, ⟨b, bl, br⟩⟩ :=
  let ⟨ol', sl', bl'⟩ := valid'.dual ⟨ol, sl, bl⟩,
      ⟨or', sr', br'⟩ := valid'.dual ⟨or, sr, br⟩ in
  ⟨⟨or', ol'⟩,
   ⟨by simp [size_dual, add_comm], sr', sl'⟩,
   ⟨by rw [size_dual, size_dual]; exact b.symm, br', bl'⟩⟩

theorem valid'.dual_iff {t : ordnode α} {o₁ o₂} : valid' o₁ t o₂ ↔
  @valid' (order_dual α) _ o₂ (dual t) o₁ :=
⟨valid'.dual, λ h, by have := valid'.dual h;
  rwa [dual_dual, order_dual.preorder.dual_dual] at this⟩

theorem valid.dual {t : ordnode α} : valid t →
  @valid (order_dual α) _ (dual t) := valid'.dual

theorem valid.dual_iff {t : ordnode α} : valid t ↔
  @valid (order_dual α) _ (dual t) := valid'.dual_iff

theorem valid'.left {s l x r o₁ o₂} (H : valid' o₁ (@node α s l x r) o₂) : valid' o₁ l x :=
⟨H.1.1, H.2.2.1, H.3.2.1⟩

theorem valid'.right {s l x r o₁ o₂} (H : valid' o₁ (@node α s l x r) o₂) : valid' ↑x r o₂ :=
⟨H.1.2, H.2.2.2, H.3.2.2⟩

theorem valid.left {s l x r} (H : valid (@node α s l x r)) : valid l := H.left.valid

theorem valid.right {s l x r} (H : valid (@node α s l x r)) : valid r := H.right.valid

theorem valid.size_eq {s l x r} (H : valid (@node α s l x r)) :
  size (@node α s l x r) = size l + size r + 1 := H.2.1

theorem valid'.node' {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : balanced_sz (size l) (size r)) : valid' o₁ (@node' α l x r) o₂ :=
hl.node hr H rfl

theorem valid'_singleton {x : α} {o₁ o₂}
  (h₁ : bounded nil o₁ ↑x) (h₂ : bounded nil ↑x o₂) : valid' o₁ (singleton x : ordnode α) o₂ :=
(valid'_nil h₁).node (valid'_nil h₂) (or.inl zero_le_one) rfl

theorem valid_singleton {x : α} : valid (singleton x : ordnode α) := valid'_singleton ⟨⟩ ⟨⟩

theorem valid'.node3_l {l x m y r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hm : valid' ↑x m ↑y) (hr : valid' ↑y r o₂)
  (H1 : balanced_sz (size l) (size m))
  (H2 : balanced_sz (size l + size m + 1) (size r)) :
  valid' o₁ (@node3_l α l x m y r) o₂ :=
(hl.node' hm H1).node' hr H2

theorem valid'.node3_r {l x m y r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hm : valid' ↑x m ↑y) (hr : valid' ↑y r o₂)
  (H1 : balanced_sz (size l) (size m + size r + 1))
  (H2 : balanced_sz (size m) (size r)) :
  valid' o₁ (@node3_r α l x m y r) o₂ :=
hl.node' (hm.node' hr H2) H1

theorem valid'.node4_l_lemma₁ {a b c d : ℕ}
  (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9)
  (mr₂ : b + c + 1 ≤ 3 * d)
  (mm₁ : b ≤ 3 * c) : b < 3 * a + 1 := by linarith

theorem valid'.node4_l_lemma₂ {b c d : ℕ} (mr₂ : b + c + 1 ≤ 3 * d) : c ≤ 3 * d := by linarith

theorem valid'.node4_l_lemma₃ {b c d : ℕ}
  (mr₁ : 2 * d ≤ b + c + 1)
  (mm₁ : b ≤ 3 * c) : d ≤ 3 * c := by linarith

theorem valid'.node4_l_lemma₄ {a b c d : ℕ}
  (lr₁ : 3 * a ≤ b + c + 1 + d)
  (mr₂ : b + c + 1 ≤ 3 * d)
  (mm₁ : b ≤ 3 * c) : a + b + 1 ≤ 3 * (c + d + 1) := by linarith

theorem valid'.node4_l_lemma₅ {a b c d : ℕ}
  (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9)
  (mr₁ : 2 * d ≤ b + c + 1)
  (mm₂ : c ≤ 3 * b) : c + d + 1 ≤ 3 * (a + b + 1) := by linarith

theorem valid'.node4_l {l x m y r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hm : valid' ↑x m ↑y) (hr : valid' ↑y r o₂)
  (Hm : 0 < size m)
  (H : (size l = 0 ∧ size m = 1 ∧ size r ≤ 1) ∨
    (0 < size l ∧ ratio * size r ≤ size m ∧
      delta * size l ≤ size m + size r ∧
      3 * (size m + size r) ≤ 16 * size l + 9 ∧
      size m ≤ delta * size r)) :
  valid' o₁ (@node4_l α l x m y r) o₂ :=
begin
  cases m with s ml z mr, {cases Hm},
  suffices : balanced_sz (size l) (size ml) ∧
    balanced_sz (size mr) (size r) ∧
    balanced_sz (size l + size ml + 1) (size mr + size r + 1),
  from (valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2),
  rcases H with ⟨l0, m1, r0⟩ | ⟨l0, mr₁, lr₁, lr₂, mr₂⟩,
  { rw [hm.2.size_eq, nat.succ_inj', add_eq_zero_iff] at m1,
    rw [l0, m1.1, m1.2], rcases size r with _|_|_; exact dec_trivial },
  { cases nat.eq_zero_or_pos (size r) with r0 r0,
    { rw r0 at mr₂, cases not_le_of_lt Hm mr₂ },
    rw [hm.2.size_eq] at lr₁ lr₂ mr₁ mr₂,
    by_cases mm : size ml + size mr ≤ 1,
    { have r1 := le_antisymm ((mul_le_mul_left dec_trivial).1
        (le_trans mr₁ (nat.succ_le_succ mm) : _ ≤ ratio * 1)) r0,
      rw [r1, add_assoc] at lr₁,
      have l1 := le_antisymm ((mul_le_mul_left dec_trivial).1
        (le_trans lr₁ (add_le_add_right mm 2) : _ ≤ delta * 1)) l0,
      rw [l1, r1],
      cases size ml; cases size mr,
      { exact dec_trivial },
      { rw zero_add at mm, rcases mm with _|⟨_,⟨⟩⟩,
        exact dec_trivial },
      { rcases mm with _|⟨_,⟨⟩⟩, exact dec_trivial },
      { rw nat.succ_add at mm, rcases mm with _|⟨_,⟨⟩⟩ } },
    rcases hm.3.1.resolve_left mm with ⟨mm₁, mm₂⟩,
    cases nat.eq_zero_or_pos (size ml) with ml0 ml0,
    { rw [ml0, mul_zero, nat.le_zero_iff] at mm₂,
      rw [ml0, mm₂] at mm, cases mm dec_trivial },
    cases nat.eq_zero_or_pos (size mr) with mr0 mr0,
    { rw [mr0, mul_zero, nat.le_zero_iff] at mm₁,
      rw [mr0, mm₁] at mm, cases mm dec_trivial },
    have : 2 * size l ≤ size ml + size mr + 1,
    { have := nat.mul_le_mul_left _ lr₁,
      rw [mul_left_comm, mul_add] at this,
      have := le_trans this (add_le_add_left mr₁ _),
      rw [← nat.succ_mul] at this,
      exact (mul_le_mul_left dec_trivial).1 this },
    refine ⟨or.inr ⟨_, _⟩, or.inr ⟨_, _⟩, or.inr ⟨_, _⟩⟩,
    { refine (mul_le_mul_left dec_trivial).1 (le_trans this _),
      rw [two_mul, nat.succ_le_iff],
      refine add_lt_add_of_lt_of_le _ mm₂,
      simpa using (mul_lt_mul_right ml0).2 (dec_trivial:1<3) },
    { exact nat.le_of_lt_succ (valid'.node4_l_lemma₁ lr₂ mr₂ mm₁) },
    { exact valid'.node4_l_lemma₂ mr₂ },
    { exact valid'.node4_l_lemma₃ mr₁ mm₁ },
    { exact valid'.node4_l_lemma₄ lr₁ mr₂ mm₁ },
    { exact valid'.node4_l_lemma₅ lr₂ mr₁ mm₂ } }
end

theorem valid'.rotate_l_lemma₁ {a b c : ℕ}
  (H2 : 3 * a ≤ b + c) (hb₂ : c ≤ 3 * b) : a ≤ 3 * b := by linarith

theorem valid'.rotate_l_lemma₂ {a b c : ℕ}
  (H3 : 2 * (b + c) ≤ 9 * a + 3) (h : b < 2 * c) : b < 3 * a + 1 := by linarith

theorem valid'.rotate_l_lemma₃ {a b c : ℕ}
  (H2 : 3 * a ≤ b + c) (h : b < 2 * c) : a + b < 3 * c := by linarith

theorem valid'.rotate_l_lemma₄ {a b : ℕ}
  (H3 : 2 * b ≤ 9 * a + 3) : 3 * b ≤ 16 * a + 9 := by linarith

theorem valid'.rotate_l {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H1 : ¬ size l + size r ≤ 1)
  (H2 : delta * size l < size r)
  (H3 : 2 * size r ≤ 9 * size l + 5 ∨ size r ≤ 3) :
  valid' o₁ (@rotate_l α l x r) o₂ :=
begin
  cases r with rs rl rx rr, {cases H2},
  rw [hr.2.size_eq, nat.lt_succ_iff] at H2,
  rw [hr.2.size_eq] at H3,
  replace H3 : 2 * (size rl + size rr) ≤ 9 * size l + 3 ∨ size rl + size rr ≤ 2 :=
    H3.imp (@nat.le_of_add_le_add_right 2 _ _) nat.le_of_succ_le_succ,
  have H3_0 : size l = 0 → size rl + size rr ≤ 2,
  { intro l0, rw l0 at H3,
    exact (or_iff_right_of_imp $ by exact λ h,
      (mul_le_mul_left dec_trivial).1 (le_trans h dec_trivial)).1 H3 },
  have H3p : size l > 0 → 2 * (size rl + size rr) ≤ 9 * size l + 3 :=
    λ l0 : 1 ≤ size l, (or_iff_left_of_imp $ by intro; linarith).1 H3,
  have ablem : ∀ {a b : ℕ}, 1 ≤ a → a + b ≤ 2 → b ≤ 1, {intros, linarith},
  have hlp : size l > 0 → ¬ size rl + size rr ≤ 1 := λ l0 hb, absurd
    (le_trans (le_trans (nat.mul_le_mul_left _ l0) H2) hb) dec_trivial,
  rw rotate_l, split_ifs,
  { have rr0 : size rr > 0 := (mul_lt_mul_left dec_trivial).1
      (lt_of_le_of_lt (nat.zero_le _) h : ratio * 0 < _),
    suffices : balanced_sz (size l) (size rl) ∧ balanced_sz (size l + size rl + 1) (size rr),
    { exact hl.node3_l hr.left hr.right this.1 this.2 },
    cases nat.eq_zero_or_pos (size l) with l0 l0,
    { rw l0, replace H3 := H3_0 l0,
      have := hr.3.1,
      cases nat.eq_zero_or_pos (size rl) with rl0 rl0,
      { rw rl0 at this ⊢,
        rw le_antisymm (balanced_sz_zero.1 this.symm) rr0,
        exact dec_trivial },
      have rr1 : size rr = 1 := le_antisymm (ablem rl0 H3) rr0,
      rw add_comm at H3,
      rw [rr1, show size rl = 1, from le_antisymm (ablem rr0 H3) rl0],
      exact dec_trivial },
    replace H3 := H3p l0,
    rcases hr.3.1.resolve_left (hlp l0) with ⟨hb₁, hb₂⟩,
    cases nat.eq_zero_or_pos (size rl) with rl0 rl0,
    { rw rl0 at hb₂, cases not_le_of_gt rr0 hb₂ },
    cases eq_or_lt_of_le (show 1 ≤ size rr, from rr0) with rr1 rr1,
    { rw [← rr1] at h H2 ⊢,
      have : size rl = 1 := le_antisymm (nat.lt_succ_iff.1 h) rl0,
      rw this at H2,
      exact absurd (le_trans (nat.mul_le_mul_left _ l0) H2) dec_trivial },
    refine ⟨or.inr ⟨_, _⟩, or.inr ⟨_, _⟩⟩,
    { exact valid'.rotate_l_lemma₁ H2 hb₂ },
    { exact nat.le_of_lt_succ (valid'.rotate_l_lemma₂ H3 h) },
    { exact valid'.rotate_l_lemma₃ H2 h },
    { exact le_trans hb₂ (nat.mul_le_mul_left _ $
        le_trans (nat.le_add_left _ _) (nat.le_add_right _ _)) } },
  { cases nat.eq_zero_or_pos (size rl) with rl0 rl0,
    { rw [rl0, not_lt, nat.le_zero_iff, nat.mul_eq_zero] at h,
      replace h := h.resolve_left dec_trivial,
      rw [rl0, h, nat.le_zero_iff, nat.mul_eq_zero] at H2,
      rw [hr.2.size_eq, rl0, h, H2.resolve_left dec_trivial] at H1,
      cases H1 dec_trivial },
    refine hl.node4_l hr.left hr.right rl0 _,
    cases nat.eq_zero_or_pos (size l) with l0 l0,
    { replace H3 := H3_0 l0,
      cases nat.eq_zero_or_pos (size rr) with rr0 rr0,
      { have := hr.3.1,
        rw rr0 at this,
        exact or.inl ⟨l0,
          le_antisymm (balanced_sz_zero.1 this) rl0,
          rr0.symm ▸ zero_le_one⟩ },
      exact or.inl ⟨l0,
        le_antisymm (ablem rr0 $ by rwa add_comm) rl0,
        ablem rl0 H3⟩ },
    exact or.inr ⟨l0, not_lt.1 h, H2,
      valid'.rotate_l_lemma₄ (H3p l0),
      (hr.3.1.resolve_left (hlp l0)).1⟩ }
end

theorem valid'.rotate_r {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H1 : ¬ size l + size r ≤ 1)
  (H2 : delta * size r < size l)
  (H3 : 2 * size l ≤ 9 * size r + 5 ∨ size l ≤ 3) :
  valid' o₁ (@rotate_r α l x r) o₂ :=
begin
  refine valid'.dual_iff.2 _,
  rw dual_rotate_r,
  refine hr.dual.rotate_l hl.dual _ _ _,
  { rwa [size_dual, size_dual, add_comm] },
  { rwa [size_dual, size_dual] },
  { rwa [size_dual, size_dual] }
end

theorem valid'.balance'_aux {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H₁ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3)
  (H₂ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) :
  valid' o₁ (@balance' α l x r) o₂ :=
begin
  rw balance', split_ifs,
  { exact hl.node' hr (or.inl h) },
  { exact hl.rotate_l hr h h_1 H₁ },
  { exact hl.rotate_r hr h h_2 H₂ },
  { exact hl.node' hr (or.inr ⟨not_lt.1 h_2, not_lt.1 h_1⟩) }
end

theorem valid'.balance'_lemma {α l l' r r'}
  (H1 : balanced_sz l' r')
  (H2 : nat.dist (@size α l) l' ≤ 1 ∧ size r = r' ∨
        nat.dist (size r) r' ≤ 1 ∧ size l = l') :
  2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3 :=
begin
  suffices : @size α r ≤ 3 * (size l + 1),
  { cases nat.eq_zero_or_pos (size l) with l0 l0,
    { apply or.inr, rwa l0 at this },
    change 1 ≤ _ at l0, apply or.inl, linarith },
  rcases H2 with ⟨hl, rfl⟩ | ⟨hr, rfl⟩;
  rcases H1 with h | ⟨h₁, h₂⟩,
  { exact le_trans (nat.le_add_left _ _) (le_trans h (nat.le_add_left _ _)) },
  { exact le_trans h₂ (nat.mul_le_mul_left _ $
      le_trans (nat.dist_tri_right _ _) (nat.add_le_add_left hl _)) },
  { exact le_trans (nat.dist_tri_left' _ _)
      (le_trans (add_le_add hr (le_trans (nat.le_add_left _ _) h)) dec_trivial) },
  { rw nat.mul_succ,
    exact le_trans (nat.dist_tri_right' _ _)
      (add_le_add h₂ (le_trans hr dec_trivial)) },
end

theorem valid'.balance' {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : ∃ l' r', balanced_sz l' r' ∧
    (nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨
     nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
  valid' o₁ (@balance' α l x r) o₂ :=
let ⟨l', r', H1, H2⟩ := H in
valid'.balance'_aux hl hr (valid'.balance'_lemma H1 H2) (valid'.balance'_lemma H1.symm H2.symm)

theorem valid'.balance {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : ∃ l' r', balanced_sz l' r' ∧
    (nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨
     nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
  valid' o₁ (@balance α l x r) o₂ :=
by rw balance_eq_balance' hl.3 hr.3 hl.2 hr.2; exact hl.balance' hr H

theorem valid'.balance_l_aux {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H₁ : size l = 0 → size r ≤ 1)
  (H₂ : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l)
  (H₃ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) :
  valid' o₁ (@balance_l α l x r) o₂ :=
begin
  rw [balance_l_eq_balance hl.2 hr.2 H₁ H₂, balance_eq_balance' hl.3 hr.3 hl.2 hr.2],
  refine hl.balance'_aux hr (or.inl _) H₃,
  cases nat.eq_zero_or_pos (size r) with r0 r0,
  { rw r0, exact nat.zero_le _ },
  cases nat.eq_zero_or_pos (size l) with l0 l0,
  { rw l0, exact le_trans (nat.mul_le_mul_left _ (H₁ l0)) dec_trivial },
  replace H₂ : _ ≤ 3 * _ := H₂ l0 r0, linarith
end

theorem valid'.balance_l {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised (size r) r' ∧ balanced_sz (size l) r')) :
  valid' o₁ (@balance_l α l x r) o₂ :=
begin
  rw balance_l_eq_balance' hl.3 hr.3 hl.2 hr.2 H,
  refine hl.balance' hr _,
  rcases H with ⟨l', e, H⟩ | ⟨r', e, H⟩,
  { exact ⟨_, _, H, or.inl ⟨e.dist_le', rfl⟩⟩ },
  { exact ⟨_, _, H, or.inr ⟨e.dist_le, rfl⟩⟩ },
end

theorem valid'.balance_r_aux {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H₁ : size r = 0 → size l ≤ 1)
  (H₂ : 1 ≤ size r → 1 ≤ size l → size l ≤ delta * size r)
  (H₃ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3) :
  valid' o₁ (@balance_r α l x r) o₂ :=
begin
  rw [valid'.dual_iff, dual_balance_r],
  have := hr.dual.balance_l_aux hl.dual,
  rw [size_dual, size_dual] at this,
  exact this H₁ H₂ H₃
end

theorem valid'.balance_r {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨
       (∃ r', raised r' (size r) ∧ balanced_sz (size l) r')) :
  valid' o₁ (@balance_r α l x r) o₂ :=
by rw [valid'.dual_iff, dual_balance_r]; exact
hr.dual.balance_l hl.dual (balance_sz_dual H)

theorem valid'.erase_max_aux {s l x r o₁ o₂}
  (H : valid' o₁ (node s l x r) o₂) :
  valid' o₁ (@erase_max α (node' l x r)) ↑(find_max' x r) ∧
  size (node' l x r) = size (erase_max (node' l x r)) + 1 :=
begin
  have := H.2.eq_node', rw this at H, clear this,
  induction r with rs rl rx rr IHrl IHrr generalizing l x o₁,
  { exact ⟨H.left, rfl⟩ },
  have := H.2.2.2.eq_node', rw this at H ⊢,
  rcases IHrr H.right with ⟨h, e⟩,
  refine ⟨valid'.balance_l H.left h (or.inr ⟨_, or.inr e, H.3.1⟩), _⟩,
  rw [erase_max, size_balance_l H.3.2.1 h.3 H.2.2.1 h.2 (or.inr ⟨_, or.inr e, H.3.1⟩)],
  rw [size, e], refl
end

theorem valid'.erase_min_aux {s l x r o₁ o₂}
  (H : valid' o₁ (node s l x r) o₂) :
  valid' ↑(find_min' l x) (@erase_min α (node' l x r)) o₂ ∧
  size (node' l x r) = size (erase_min (node' l x r)) + 1 :=
by have := H.dual.erase_max_aux;
   rwa [← dual_node', size_dual, ← dual_erase_min,
     size_dual, ← valid'.dual_iff, find_max'_dual] at this

theorem erase_min.valid : ∀ {t} (h : @valid α _ t), valid (erase_min t)
| nil _ := valid_nil
| (node _ l x r) h := by rw h.2.eq_node'; exact h.erase_min_aux.1.valid

theorem erase_max.valid {t} (h : @valid α _ t) : valid (erase_max t) :=
by rw [valid.dual_iff, dual_erase_max]; exact erase_min.valid h.dual

theorem valid'.glue_aux {l r o₁ o₂}
  (hl : valid' o₁ l o₂) (hr : valid' o₁ r o₂)
  (sep : l.all (λ x, r.all (λ y, x < y)))
  (bal : balanced_sz (size l) (size r)) :
  valid' o₁ (@glue α l r) o₂ ∧ size (glue l r) = size l + size r :=
begin
  cases l with ls ll lx lr, {exact ⟨hr, (zero_add _).symm⟩ },
  cases r with rs rl rx rr, {exact ⟨hl, rfl⟩ },
  dsimp [glue], split_ifs,
  { rw [split_max_eq, glue],
    cases valid'.erase_max_aux hl with v e,
    suffices H,
    refine ⟨valid'.balance_r v (hr.of_gt _ _) H, _⟩,
    { refine find_max'_all lx lr hl.1.2.to_nil (sep.2.2.imp _),
      exact λ x h, hr.1.2.to_nil.mono_left (le_of_lt h.2.1) },
    { exact @find_max'_all _ (λ a, all (> a) (node rs rl rx rr)) lx lr sep.2.1 sep.2.2 },
    { rw [size_balance_r v.3 hr.3 v.2 hr.2 H, add_right_comm, ← e, hl.2.1], refl },
    { refine or.inl ⟨_, or.inr e, _⟩,
      rwa hl.2.eq_node' at bal } },
  { rw [split_min_eq, glue],
    cases valid'.erase_min_aux hr with v e,
    suffices H,
    refine ⟨valid'.balance_l (hl.of_lt _ _) v H, _⟩,
    { refine @find_min'_all _ (λ a, bounded nil o₁ ↑a) rl rx (sep.2.1.1.imp _) hr.1.1.to_nil,
      exact λ y h, hl.1.1.to_nil.mono_right (le_of_lt h) },
    { exact @find_min'_all _ (λ a, all (< a) (node ls ll lx lr)) rl rx
        (all_iff_forall.2 $ λ x hx, sep.imp $ λ y hy, all_iff_forall.1 hy.1 _ hx)
        (sep.imp $ λ y hy, hy.2.1) },
    { rw [size_balance_l hl.3 v.3 hl.2 v.2 H, add_assoc, ← e, hr.2.1], refl },
    { refine or.inr ⟨_, or.inr e, _⟩,
      rwa hr.2.eq_node' at bal } },
end

theorem valid'.glue {l x r o₁ o₂}
  (hl : valid' o₁ l ↑(x:α)) (hr : valid' ↑x r o₂) :
  balanced_sz (size l) (size r) →
  valid' o₁ (@glue α l r) o₂ ∧ size (@glue α l r) = size l + size r :=
valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)

theorem valid'.merge_lemma {a b c : ℕ}
  (h₁ : 3 * a < b + c + 1) (h₂ : b ≤ 3 * c) : 2 * (a + b) ≤ 9 * c + 5 :=
by linarith

theorem valid'.merge_aux₁ {o₁ o₂ ls ll lx lr rs rl rx rr t}
  (hl : valid' o₁ (@node α ls ll lx lr) o₂)
  (hr : valid' o₁ (node rs rl rx rr) o₂)
  (h : delta * ls < rs)
  (v : valid' o₁ t ↑rx)
  (e : size t = ls + size rl) :
  valid' o₁ (balance_l t rx rr) o₂ ∧ size (balance_l t rx rr) = ls + rs :=
begin
  rw hl.2.1 at e,
  rw [hl.2.1, hr.2.1, delta] at h,
  rcases hr.3.1 with H|⟨hr₁, hr₂⟩, {linarith},
  suffices H₂, suffices H₁,
  refine ⟨valid'.balance_l_aux v hr.right H₁ H₂ _, _⟩,
  { rw e, exact or.inl (valid'.merge_lemma h hr₁) },
  { rw [balance_l_eq_balance v.2 hr.2.2.2 H₁ H₂, balance_eq_balance' v.3 hr.3.2.2 v.2 hr.2.2.2,
      size_balance' v.2 hr.2.2.2, e, hl.2.1, hr.2.1], simp [add_comm, add_left_comm] },
  { rw [e, add_right_comm], rintro ⟨⟩ },
  { intros _ h₁, rw e, unfold delta at hr₂ ⊢, linarith }
end

theorem valid'.merge_aux {l r o₁ o₂}
  (hl : valid' o₁ l o₂) (hr : valid' o₁ r o₂)
  (sep : l.all (λ x, r.all (λ y, x < y))) :
  valid' o₁ (@merge α l r) o₂ ∧ size (merge l r) = size l + size r :=
begin
  induction l with ls ll lx lr IHll IHlr generalizing o₁ o₂ r,
  { exact ⟨hr, (zero_add _).symm⟩ },
  induction r with rs rl rx rr IHrl IHrr generalizing o₁ o₂,
  { exact ⟨hl, rfl⟩ },
  rw [merge_node], split_ifs,
  { cases IHrl (sep.imp $ λ x h, h.1)
      (hl.of_lt hr.1.1.to_nil $ sep.imp $ λ x h, h.2.1) hr.left with v e,
    exact valid'.merge_aux₁ hl hr h v e },
  { cases IHlr hl.right (hr.of_gt hl.1.2.to_nil sep.2.1) sep.2.2 with v e,
    have := valid'.merge_aux₁ hr.dual hl.dual h_1 v.dual,
    rw [size_dual, add_comm, size_dual,
      ← dual_balance_r, ← valid'.dual_iff, size_dual, add_comm rs] at this,
    exact this e },
  { refine valid'.glue_aux hl hr sep (or.inr ⟨not_lt.1 h_1, not_lt.1 h⟩) }
end

theorem valid.merge {l r} (hl : valid l) (hr : valid r)
  (sep : l.all (λ x, r.all (λ y, x < y))) : valid (@merge α l r) :=
(valid'.merge_aux hl hr sep).1

theorem insert_with.valid_aux [is_total α (≤)] [@decidable_rel α (≤)]
  (f : α → α) (x : α) (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) : ∀ {t o₁ o₂},
  valid' o₁ t o₂ → bounded nil o₁ ↑x → bounded nil ↑x o₂ →
  valid' o₁ (insert_with f x t) o₂ ∧
  raised (size t) (size (insert_with f x t))
| nil o₁ o₂ _ bl br := ⟨valid'_singleton bl br, or.inr rfl⟩
| (node sz l y r) o₁ o₂ h bl br := begin
    rw [insert_with, cmp_le],
    split_ifs; rw [insert_with],
    { rcases h with ⟨⟨lx, xr⟩, hs, hb⟩,
      rcases hf _ ⟨h_1, h_2⟩ with ⟨xf, fx⟩,
      refine ⟨⟨⟨lx.mono_right (le_trans h_2 xf),
        xr.mono_left (le_trans fx h_1)⟩, hs, hb⟩, or.inl rfl⟩ },
    { rcases insert_with.valid_aux h.left bl (lt_of_le_not_le h_1 h_2) with ⟨vl, e⟩,
      suffices H,
      { refine ⟨vl.balance_l h.right H, _⟩,
        rw [size_balance_l vl.3 h.3.2.2 vl.2 h.2.2.2 H, h.2.size_eq],
        refine (e.add_right _).add_right _ },
      { exact or.inl ⟨_, e, h.3.1⟩ } },
    { have : y < x := lt_of_le_not_le ((total_of (≤) _ _).resolve_left h_1) h_1,
      rcases insert_with.valid_aux h.right this br with ⟨vr, e⟩,
      suffices H,
      { refine ⟨h.left.balance_r vr H, _⟩,
        rw [size_balance_r h.3.2.1 vr.3 h.2.2.1 vr.2 H, h.2.size_eq],
        refine (e.add_left _).add_right _ },
      { exact or.inr ⟨_, e, h.3.1⟩ } },
  end

theorem insert_with.valid [is_total α (≤)] [@decidable_rel α (≤)]
  (f : α → α) (x : α) (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x)
  {t} (h : valid t) : valid (insert_with f x t) :=
(insert_with.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1

theorem insert_eq_insert_with [@decidable_rel α (≤)]
  (x : α) : ∀ t, ordnode.insert x t = insert_with (λ _, x) x t
| nil := rfl
| (node _ l y r) := by unfold ordnode.insert insert_with;
  cases cmp_le x y; unfold ordnode.insert insert_with; simp [insert_eq_insert_with]

theorem insert.valid [is_total α (≤)] [@decidable_rel α (≤)]
  (x : α) {t} (h : valid t) : valid (ordnode.insert x t) :=
by rw insert_eq_insert_with; exact
insert_with.valid _ _ (λ _ _, ⟨le_refl _, le_refl _⟩) h

theorem insert'_eq_insert_with [@decidable_rel α (≤)]
  (x : α) : ∀ t, insert' x t = insert_with id x t
| nil := rfl
| (node _ l y r) := by unfold insert' insert_with;
  cases cmp_le x y; unfold insert' insert_with; simp [insert'_eq_insert_with]

theorem insert'.valid [is_total α (≤)] [@decidable_rel α (≤)]
  (x : α) {t} (h : valid t) : valid (insert' x t) :=
by rw insert'_eq_insert_with; exact insert_with.valid _ _ (λ _, id) h

theorem valid'.map_aux {β} [preorder β] {f : α → β} (f_strict_mono : strict_mono f)
  {t a₁ a₂} (h : valid' a₁ t a₂) :
  valid' (option.map f a₁) (map f t) (option.map f a₂) ∧ (map f t).size = t.size :=
begin
  induction t generalizing a₁ a₂,
  { simp [map], apply valid'_nil,
    cases a₁, { trivial },
    cases a₂, { trivial },
    simp [bounded],
    exact f_strict_mono h.ord },
  { have t_ih_l' := t_ih_l h.left,
    have t_ih_r' := t_ih_r h.right,
    clear t_ih_l t_ih_r,
    cases t_ih_l' with t_l_valid t_l_size,
    cases t_ih_r' with t_r_valid t_r_size,
    simp [map],
    split,
    { exact and.intro t_l_valid.ord t_r_valid.ord },
    { repeat { split },
      { rw [t_l_size, t_r_size], exact h.sz.1 },
      { exact t_l_valid.sz },
      { exact t_r_valid.sz } },
    { repeat { split },
      { rw [t_l_size, t_r_size], exact h.bal.1 },
      { exact t_l_valid.bal },
      { exact t_r_valid.bal } } },
end

theorem map.valid {β} [preorder β] {f : α → β} (f_strict_mono : strict_mono f)
  {t} (h : valid t) : valid (map f t) :=
(valid'.map_aux f_strict_mono h).1

theorem valid'.erase_aux [@decidable_rel α (≤)] (x : α) {t a₁ a₂} (h : valid' a₁ t a₂) :
  valid' a₁ (erase x t) a₂ ∧ raised (erase x t).size t.size :=
begin
  induction t generalizing a₁ a₂,
  { simp [erase, raised], exact h },
  { simp [erase],
    have t_ih_l' := t_ih_l h.left,
    have t_ih_r' := t_ih_r h.right,
    clear t_ih_l t_ih_r,
    cases t_ih_l' with t_l_valid t_l_size,
    cases t_ih_r' with t_r_valid t_r_size,
    cases (cmp_le x t_x);
      simp [erase._match_1]; rw h.sz.1,
    { suffices h_balanceable,
      split,
      { exact valid'.balance_r t_l_valid h.right h_balanceable },
      { rw size_balance_r t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz h_balanceable,
        repeat { apply raised.add_right },
        exact t_l_size },
      { left, existsi t_l.size, exact (and.intro t_l_size h.bal.1) } },
    { have h_glue := valid'.glue h.left h.right h.bal.1,
      cases h_glue with h_glue_valid h_glue_sized,
      split,
      { exact h_glue_valid },
      { right, rw h_glue_sized } },
    { suffices h_balanceable,
      split,
      { exact valid'.balance_l h.left t_r_valid h_balanceable },
      { rw size_balance_l h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz h_balanceable,
        apply raised.add_right,
        apply raised.add_left,
        exact t_r_size },
      { right, existsi t_r.size, exact (and.intro t_r_size h.bal.1) } } },
end

theorem erase.valid [@decidable_rel α (≤)] (x : α) {t} (h : valid t) : valid (erase x t) :=
(valid'.erase_aux x h).1

theorem size_erase_of_mem [@decidable_rel α (≤)]
  {x : α} {t a₁ a₂} (h : valid' a₁ t a₂) (h_mem : x ∈ t) :
  size (erase x t) = size t - 1 :=
begin
  induction t generalizing a₁ a₂ h h_mem,
  { contradiction },
  { have t_ih_l' := t_ih_l h.left,
    have t_ih_r' := t_ih_r h.right,
    clear t_ih_l t_ih_r,
    unfold has_mem.mem mem at h_mem,
    unfold erase,
    cases (cmp_le x t_x);
      simp [mem._match_1] at h_mem; simp [erase._match_1],
    { have t_ih_l := t_ih_l' h_mem,
      clear t_ih_l' t_ih_r',
      have t_l_h := valid'.erase_aux x h.left,
      cases t_l_h with t_l_valid t_l_size,
      rw size_balance_r t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz
        (or.inl (exists.intro t_l.size (and.intro t_l_size h.bal.1))),
      rw [t_ih_l, h.sz.1],
      have h_pos_t_l_size := pos_size_of_mem h.left.sz h_mem,
      cases t_l.size with t_l_size, { cases h_pos_t_l_size },
      simp [nat.succ_add] },
    { rw [(valid'.glue h.left h.right h.bal.1).2, h.sz.1], refl },
    { have t_ih_r := t_ih_r' h_mem,
      clear t_ih_l' t_ih_r',
      have t_r_h := valid'.erase_aux x h.right,
      cases t_r_h with t_r_valid t_r_size,
      rw size_balance_l h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz
        (or.inr (exists.intro t_r.size (and.intro t_r_size h.bal.1))),
      rw [t_ih_r, h.sz.1],
      have h_pos_t_r_size := pos_size_of_mem h.right.sz h_mem,
      cases t_r.size with t_r_size, { cases h_pos_t_r_size },
      simp [nat.succ_add] } },
end

end

end ordnode

/-- An `ordset α` is a finite set of values, represented as a tree. The operations on this type
maintain that the tree is balanced and correctly stores subtree sizes at each level. The
correctness property of the tree is baked into the type, so all operations on this type are correct
by construction. -/
def ordset (α : Type*) [preorder α] := {t : ordnode α // t.valid}

namespace ordset
open ordnode
variable [preorder α]

/-- O(1). The empty set. -/
def nil : ordset α := ⟨nil, ⟨⟩, ⟨⟩, ⟨⟩⟩

/-- O(1). Get the size of the set. -/
def size (s : ordset α) : ℕ := s.1.size

/-- O(1). Construct a singleton set containing value `a`. -/
protected def singleton (a : α) : ordset α := ⟨singleton a, valid_singleton⟩

instance : has_emptyc (ordset α) := ⟨nil⟩
instance : inhabited (ordset α) := ⟨nil⟩
instance : has_singleton α (ordset α) := ⟨ordset.singleton⟩

/-- O(1). Is the set empty? -/
def empty (s : ordset α) : Prop := s = ∅

theorem empty_iff {s : ordset α} : s = ∅ ↔ s.1.empty :=
⟨λ h, by cases h; exact rfl,
 λ h, by cases s; cases s_val; [exact rfl, cases h]⟩

instance : decidable_pred (@empty α _) :=
λ s, decidable_of_iff' _ empty_iff

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, this replaces it. -/
protected def insert [is_total α (≤)] [@decidable_rel α (≤)] (x : α) (s : ordset α) : ordset α :=
⟨ordnode.insert x s.1, insert.valid _ s.2⟩

instance [is_total α (≤)] [@decidable_rel α (≤)] : has_insert α (ordset α) := ⟨ordset.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, the set is returned as is. -/
def insert' [is_total α (≤)] [@decidable_rel α (≤)] (x : α) (s : ordset α) : ordset α :=
⟨insert' x s.1, insert'.valid _ s.2⟩

section
variables [@decidable_rel α (≤)]

/-- O(log n). Does the set contain the element `x`? That is,
  is there an element that is equivalent to `x` in the order? -/
def mem (x : α) (s : ordset α) : bool := x ∈ s.val

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
  if it exists. -/
def find (x : α) (s : ordset α) : option α := ordnode.find x s.val

instance : has_mem α (ordset α) := ⟨λ x s, mem x s⟩

instance mem.decidable (x : α) (s : ordset α) : decidable (x ∈ s) := bool.decidable_eq _ _

theorem pos_size_of_mem {x : α} {t : ordset α} (h_mem : x ∈ t) : 0 < size t :=
begin
  simp [has_mem.mem, mem] at h_mem,
  apply ordnode.pos_size_of_mem t.property.sz h_mem,
end

end

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element. -/
def erase [@decidable_rel α (≤)] (x : α) (s : ordset α) : ordset α :=
⟨ordnode.erase x s.val, ordnode.erase.valid x s.property⟩

/-- O(n). Map a function across a tree, without changing the structure. -/
def map {β} [preorder β] (f : α → β) (f_strict_mono : strict_mono f) (s : ordset α) : ordset β :=
⟨ordnode.map f s.val, ordnode.map.valid f_strict_mono s.property⟩

end ordset
