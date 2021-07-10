/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.fintype.card
import data.finset.sort
import algebra.big_operators.order

/-!
# Compositions

A composition of a natural number `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum
of positive integers. Combinatorially, it corresponds to a decomposition of `{0, ..., n-1}` into
non-empty blocks of consecutive integers, where the `iⱼ` are the lengths of the blocks.
This notion is closely related to that of a partition of `n`, but in a composition of `n` the
order of the `iⱼ`s matters.

We implement two different structures covering these two viewpoints on compositions. The first
one, made of a list of positive integers summing to `n`, is the main one and is called
`composition n`. The second one is useful for combinatorial arguments (for instance to show that
the number of compositions of `n` is `2^(n-1)`). It is given by a subset of `{0, ..., n}`
containing `0` and `n`, where the elements of the subset (other than `n`) correspond to the leftmost
points of each block. The main API is built on `composition n`, and we provide an equivalence
between the two types.

## Main functions

* `c : composition n` is a structure, made of a list of integers which are all positive and
  add up to `n`.
* `composition_card` states that the cardinality of `composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with `composition_as_set n` (see below), which
  is itself in bijection with the subsets of `fin (n-1)` (this holds even for `n = 0`, where `-` is
  nat subtraction).

Let `c : composition n` be a composition of `n`. Then
* `c.blocks` is the list of blocks in `c`.
* `c.length` is the number of blocks in the composition.
* `c.blocks_fun : fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.size_up_to : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : fin (c.blocks_fun i) → fin n` is the increasing embedding of the `i`-th block in
  `fin n`;
* `c.index j`, for `j : fin n`, is the index of the block containing `j`.

* `composition.ones n` is the composition of `n` made of ones, i.e., `[1, ..., 1]`.
* `composition.single n (hn : 0 < n)` is the composition of `n` made of a single block of size `n`.

Compositions can also be used to split lists. Let `l` be a list of length `n` and `c` a composition
of `n`.
* `l.split_wrt_composition c` is a list of lists, made of the slices of `l` corresponding to the
  blocks of `c`.
* `join_split_wrt_composition` states that splitting a list and then joining it gives back the
  original list.
* `split_wrt_composition_join` states that joining a list of lists, and then splitting it back
  according to the right composition, gives back the original list of lists.

We turn to the second viewpoint on compositions, that we realize as a finset of `fin (n+1)`.
`c : composition_as_set n` is a structure made of a finset of `fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `composition n` and `composition_as_set n`. We
only construct basic API on `composition_as_set` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `composition_equiv n`. Since there is a straightforward equiv
between `composition_as_set n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `composition_as_set` and called `composition_as_set_equiv n`), we deduce that
`composition_as_set n` and `composition n` are both fintypes of cardinality `2^(n - 1)`
(see `composition_as_set_card` and `composition_card`).

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>
-/

open list
open_locale big_operators

variable {n : ℕ}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext] structure composition (n : ℕ) :=
(blocks : list ℕ)
(blocks_pos : ∀ {i}, i ∈ blocks → 0 < i)
(blocks_sum : blocks.sum = n)

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`composition_as_set n`. -/
@[ext] structure composition_as_set (n : ℕ) :=
(boundaries : finset (fin n.succ))
(zero_mem   : (0 : fin n.succ) ∈ boundaries)
(last_mem   : fin.last n ∈ boundaries)

instance {n : ℕ} : inhabited (composition_as_set n) :=
⟨⟨finset.univ, finset.mem_univ _, finset.mem_univ _⟩⟩

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/

namespace composition

variables (c : composition n)

instance (n : ℕ) : has_to_string (composition n) :=
⟨λ c, to_string c.blocks⟩

/-- The length of a composition, i.e., the number of blocks in the composition. -/
@[reducible] def length : ℕ := c.blocks.length

lemma blocks_length : c.blocks.length = c.length := rfl

/-- The blocks of a composition, seen as a function on `fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocks_fun : fin c.length → ℕ := λ i, nth_le c.blocks i i.2

lemma of_fn_blocks_fun : of_fn c.blocks_fun = c.blocks :=
of_fn_nth_le _

lemma sum_blocks_fun : ∑ i, c.blocks_fun i = n :=
by conv_rhs { rw [← c.blocks_sum, ← of_fn_blocks_fun, sum_of_fn] }

lemma blocks_fun_mem_blocks (i : fin c.length) : c.blocks_fun i ∈ c.blocks :=
nth_le_mem _ _ _

@[simp] lemma one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
c.blocks_pos h

@[simp] lemma one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ nth_le c.blocks i h:=
c.one_le_blocks (nth_le_mem (blocks c) i h)

@[simp] lemma blocks_pos' (i : ℕ) (h : i < c.length) : 0 < nth_le c.blocks i h:=
c.one_le_blocks' h

lemma one_le_blocks_fun (i : fin c.length) : 1 ≤ c.blocks_fun i :=
c.one_le_blocks (c.blocks_fun_mem_blocks i)

lemma length_le : c.length ≤ n :=
begin
  conv_rhs { rw ← c.blocks_sum },
  exact length_le_sum_of_one_le _ (λ i hi, c.one_le_blocks hi)
end

lemma length_pos_of_pos (h : 0 < n) : 0 < c.length :=
begin
  apply length_pos_of_sum_pos,
  convert h,
  exact c.blocks_sum
end

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def size_up_to (i : ℕ) : ℕ := (c.blocks.take i).sum

@[simp] lemma size_up_to_zero : c.size_up_to 0 = 0 := by simp [size_up_to]

lemma size_up_to_of_length_le (i : ℕ) (h : c.length ≤ i) : c.size_up_to i = n :=
begin
  dsimp [size_up_to],
  convert c.blocks_sum,
  exact take_all_of_le h
end

@[simp] lemma size_up_to_length : c.size_up_to c.length = n :=
c.size_up_to_of_length_le c.length (le_refl _)

lemma size_up_to_le (i : ℕ) : c.size_up_to i ≤ n :=
begin
  conv_rhs { rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i] },
  exact nat.le_add_right _ _
end

lemma size_up_to_succ {i : ℕ} (h : i < c.length) :
  c.size_up_to (i+1) = c.size_up_to i + c.blocks.nth_le i h :=
by { simp only [size_up_to], rw sum_take_succ _ _ h }

lemma size_up_to_succ' (i : fin c.length) :
  c.size_up_to ((i : ℕ) + 1) = c.size_up_to i + c.blocks_fun i :=
c.size_up_to_succ i.2

lemma size_up_to_strict_mono {i : ℕ} (h : i < c.length) : c.size_up_to i < c.size_up_to (i+1) :=
by { rw c.size_up_to_succ h, simp }

lemma monotone_size_up_to : monotone c.size_up_to :=
monotone_sum_take _

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundary : fin (c.length + 1) ↪o fin (n+1) :=
order_embedding.of_strict_mono (λ i, ⟨c.size_up_to i, nat.lt_succ_of_le (c.size_up_to_le i)⟩) $
 fin.strict_mono_iff_lt_succ.2 $ λ i hi, c.size_up_to_strict_mono $
   lt_of_add_lt_add_right hi

@[simp] lemma boundary_zero : c.boundary 0 = 0 :=
by simp [boundary, fin.ext_iff]

@[simp] lemma boundary_last : c.boundary (fin.last c.length) = fin.last n :=
by simp [boundary, fin.ext_iff]

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundaries : finset (fin (n+1)) :=
finset.univ.map c.boundary.to_embedding

lemma card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
by simp [boundaries]

/-- To `c : composition n`, one can associate a `composition_as_set n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def to_composition_as_set : composition_as_set n :=
{ boundaries := c.boundaries,
  zero_mem := begin
    simp only [boundaries, finset.mem_univ, exists_prop_of_true, finset.mem_map],
    exact ⟨0, rfl⟩,
  end,
  last_mem := begin
    simp only [boundaries, finset.mem_univ, exists_prop_of_true, finset.mem_map],
    exact ⟨fin.last c.length, c.boundary_last⟩,
  end }

/-- The canonical increasing bijection between `fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
lemma order_emb_of_fin_boundaries :
  c.boundaries.order_emb_of_fin c.card_boundaries_eq_succ_length = c.boundary :=
begin
  refine (finset.order_emb_of_fin_unique' _ _).symm,
  exact λ i, (finset.mem_map' _).2 (finset.mem_univ _)
end

/-- Embedding the `i`-th block of a composition (identified with `fin (c.blocks_fun i)`) into
`fin n` at the relevant position. -/
def embedding (i : fin c.length) : fin (c.blocks_fun i) ↪o fin n :=
(fin.nat_add $ c.size_up_to i).trans $ fin.cast_le $
calc c.size_up_to i + c.blocks_fun i = c.size_up_to (i + 1) : (c.size_up_to_succ _).symm
... ≤ c.size_up_to c.length : monotone_sum_take _ i.2
... = n : c.size_up_to_length

@[simp] lemma coe_embedding (i : fin c.length) (j : fin (c.blocks_fun i)) :
  (c.embedding i j : ℕ) = c.size_up_to i + j := rfl

/--
`index_exists` asserts there is some `i` with `j < c.size_up_to (i+1)`.
In the next definition `index` we use `nat.find` to produce the minimal such index.
-/
lemma index_exists {j : ℕ} (h : j < n) :
  ∃ i : ℕ, j < c.size_up_to i.succ ∧ i < c.length :=
begin
  have n_pos : 0 < n := lt_of_le_of_lt (zero_le j) h,
  have : 0 < c.blocks.sum, by rwa [← c.blocks_sum] at n_pos,
  have length_pos : 0 < c.blocks.length := length_pos_of_sum_pos (blocks c) this,
  refine ⟨c.length.pred, _, nat.pred_lt (ne_of_gt length_pos)⟩,
  have : c.length.pred.succ = c.length := nat.succ_pred_eq_of_pos length_pos,
  simp [this, h]
end

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
def index (j : fin n) : fin c.length :=
⟨nat.find (c.index_exists j.2), (nat.find_spec (c.index_exists j.2)).2⟩

lemma lt_size_up_to_index_succ (j : fin n) : (j : ℕ) < c.size_up_to (c.index j).succ :=
(nat.find_spec (c.index_exists j.2)).1

lemma size_up_to_index_le (j : fin n) : c.size_up_to (c.index j) ≤ j :=
begin
  by_contradiction H,
  set i := c.index j with hi,
  push_neg at H,
  have i_pos : (0 : ℕ) < i,
  { by_contradiction i_pos,
    push_neg at i_pos,
    revert H, simp [nonpos_iff_eq_zero.1 i_pos, c.size_up_to_zero] },
  let i₁ := (i : ℕ).pred,
  have i₁_lt_i : i₁ < i := nat.pred_lt (ne_of_gt i_pos),
  have i₁_succ : i₁.succ = i := nat.succ_pred_eq_of_pos i_pos,
  have := nat.find_min (c.index_exists j.2) i₁_lt_i,
  simp [lt_trans i₁_lt_i (c.index j).2, i₁_succ] at this,
  exact nat.lt_le_antisymm H this
end

/-- Mapping an element `j` of `fin n` to the element in the block containing it, identified with
`fin (c.blocks_fun (c.index j))` through the canonical increasing bijection. -/
def inv_embedding (j : fin n) : fin (c.blocks_fun (c.index j)) :=
⟨j - c.size_up_to (c.index j),
begin
  rw [nat.sub_lt_right_iff_lt_add, add_comm, ← size_up_to_succ'],
  { exact lt_size_up_to_index_succ _ _ },
  { exact size_up_to_index_le _ _ }
end⟩

@[simp] lemma coe_inv_embedding (j : fin n) :
  (c.inv_embedding j : ℕ) = j - c.size_up_to (c.index j) := rfl

lemma embedding_comp_inv (j : fin n) :
  c.embedding (c.index j) (c.inv_embedding j) = j :=
begin
  rw fin.ext_iff,
  apply nat.add_sub_cancel' (c.size_up_to_index_le j),
end

lemma mem_range_embedding_iff {j : fin n} {i : fin c.length} :
  j ∈ set.range (c.embedding i) ↔
  c.size_up_to i ≤ j ∧ (j : ℕ) < c.size_up_to (i : ℕ).succ :=
begin
  split,
  { assume h,
    rcases set.mem_range.2 h with ⟨k, hk⟩,
    rw fin.ext_iff at hk,
    change c.size_up_to i + k = (j : ℕ) at hk,
    rw ← hk,
    simp [size_up_to_succ', k.is_lt] },
  { assume h,
    apply set.mem_range.2,
    refine ⟨⟨j - c.size_up_to i, _⟩, _⟩,
    { rw [nat.sub_lt_left_iff_lt_add, ← size_up_to_succ'],
      { exact h.2 },
      { exact h.1 } },
    { rw fin.ext_iff,
      exact nat.add_sub_cancel' h.1 } }
end

/-- The embeddings of different blocks of a composition are disjoint. -/
lemma disjoint_range {i₁ i₂ : fin c.length} (h : i₁ ≠ i₂) :
  disjoint (set.range (c.embedding i₁)) (set.range (c.embedding i₂)) :=
begin
  classical,
  wlog h' : i₁ ≤ i₂ using i₁ i₂,
  swap, exact (this h.symm).symm,
  by_contradiction d,
  obtain ⟨x, hx₁, hx₂⟩ :
    ∃ x : fin n, (x ∈ set.range (c.embedding i₁) ∧ x ∈ set.range (c.embedding i₂)) :=
  set.not_disjoint_iff.1 d,
  have : i₁ < i₂ := lt_of_le_of_ne h' h,
  have A : (i₁ : ℕ).succ ≤ i₂ := nat.succ_le_of_lt this,
  apply lt_irrefl (x : ℕ),
  calc (x : ℕ) < c.size_up_to (i₁ : ℕ).succ : (c.mem_range_embedding_iff.1 hx₁).2
  ... ≤ c.size_up_to (i₂ : ℕ) : monotone_sum_take _ A
  ... ≤ x : (c.mem_range_embedding_iff.1 hx₂).1
end

lemma mem_range_embedding (j : fin n) :
  j ∈ set.range (c.embedding (c.index j)) :=
begin
  have : c.embedding (c.index j) (c.inv_embedding j)
    ∈ set.range (c.embedding (c.index j)) := set.mem_range_self _,
  rwa c.embedding_comp_inv j at this
end

lemma mem_range_embedding_iff' {j : fin n} {i : fin c.length} :
  j ∈ set.range (c.embedding i) ↔ i = c.index j :=
begin
  split,
  { rw ← not_imp_not,
    assume h,
    exact set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j) },
  { assume h,
    rw h,
    exact c.mem_range_embedding j }
end

lemma index_embedding (i : fin c.length) (j : fin (c.blocks_fun i)) :
  c.index (c.embedding i j) = i :=
begin
  symmetry,
  rw ← mem_range_embedding_iff',
  apply set.mem_range_self
end

lemma inv_embedding_comp (i : fin c.length) (j : fin (c.blocks_fun i)) :
  (c.inv_embedding (c.embedding i j) : ℕ) = j :=
by simp_rw [coe_inv_embedding, index_embedding, coe_embedding, nat.add_sub_cancel_left]

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`fin (c.blocks_fun i)`) with `fin n`. -/
def blocks_fin_equiv : (Σ i : fin c.length, fin (c.blocks_fun i)) ≃ fin n :=
{ to_fun := λ x, c.embedding x.1 x.2,
  inv_fun := λ j, ⟨c.index j, c.inv_embedding j⟩,
  left_inv := λ x, begin
    rcases x with ⟨i, y⟩,
    dsimp,
    congr, { exact c.index_embedding _ _ },
    rw fin.heq_ext_iff,
    { exact c.inv_embedding_comp _ _ },
    { rw c.index_embedding }
  end,
  right_inv := λ j, c.embedding_comp_inv j }

lemma blocks_fun_congr {n₁ n₂ : ℕ} (c₁ : composition n₁) (c₂ : composition n₂)
  (i₁ : fin c₁.length) (i₂ : fin c₂.length) (hn : n₁ = n₂)
  (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
  c₁.blocks_fun i₁ = c₂.blocks_fun i₂ :=
by { cases hn, rw ← composition.ext_iff at hc, cases hc, congr, rwa fin.ext_iff }

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
lemma sigma_eq_iff_blocks_eq {c : Σ n, composition n} {c' : Σ n, composition n} :
  c = c' ↔ c.2.blocks = c'.2.blocks :=
begin
  refine ⟨λ H, by rw H, λ H, _⟩,
  rcases c with ⟨n, c⟩,
  rcases c' with ⟨n', c'⟩,
  have : n = n', by { rw [← c.blocks_sum, ← c'.blocks_sum, H] },
  induction this,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext1,
  exact H
end

/-! ### The composition `composition.ones` -/

/-- The composition made of blocks all of size `1`. -/
def ones (n : ℕ) : composition n :=
⟨repeat (1 : ℕ) n, λ i hi, by simp [list.eq_of_mem_repeat hi], by simp⟩

instance {n : ℕ} : inhabited (composition n) :=
⟨composition.ones n⟩

@[simp] lemma ones_length (n : ℕ) : (ones n).length = n :=
list.length_repeat 1 n

@[simp] lemma ones_blocks (n : ℕ) : (ones n).blocks = repeat (1 : ℕ) n := rfl

@[simp] lemma ones_blocks_fun (n : ℕ) (i : fin (ones n).length) :
  (ones n).blocks_fun i = 1 :=
by simp [blocks_fun, ones, blocks, i.2]

@[simp] lemma ones_size_up_to (n : ℕ) (i : ℕ) : (ones n).size_up_to i = min i n :=
by simp [size_up_to, ones_blocks, take_repeat]

@[simp] lemma ones_embedding (i : fin (ones n).length) (h : 0 < (ones n).blocks_fun i) :
  (ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i.2 (ones n).length_le⟩ :=
by { ext, simpa using i.2.le }

lemma eq_ones_iff {c : composition n} :
  c = ones n ↔ ∀ i ∈ c.blocks, i = 1 :=
begin
  split,
  { rintro rfl,
    exact λ i, eq_of_mem_repeat },
  { assume H,
    ext1,
    have A : c.blocks = repeat 1 c.blocks.length := eq_repeat_of_mem H,
    have : c.blocks.length = n, by { conv_rhs { rw [← c.blocks_sum, A] }, simp },
    rw [A, this, ones_blocks] },
end

lemma ne_ones_iff {c : composition n} :
  c ≠ ones n ↔ ∃ i ∈ c.blocks, 1 < i :=
begin
  refine (not_congr eq_ones_iff).trans _,
  have : ∀ j ∈ c.blocks, j = 1 ↔ j ≤ 1 := λ j hj, by simp [le_antisymm_iff, c.one_le_blocks hj],
  simp [this] {contextual := tt}
end

lemma eq_ones_iff_length {c : composition n} :
  c = ones n ↔ c.length = n :=
begin
  split,
  { rintro rfl,
    exact ones_length n },
  { contrapose,
    assume H length_n,
    apply lt_irrefl n,
    calc
      n = ∑ (i : fin c.length), 1 : by simp [length_n]
      ... < ∑ (i : fin c.length), c.blocks_fun i :
      begin
        obtain ⟨i, hi, i_blocks⟩ : ∃ i ∈ c.blocks, 1 < i := ne_ones_iff.1 H,
        rw [← of_fn_blocks_fun, mem_of_fn c.blocks_fun, set.mem_range] at hi,
        obtain ⟨j : fin c.length, hj : c.blocks_fun j = i⟩ := hi,
        rw ← hj at i_blocks,
        exact finset.sum_lt_sum (λ i hi, by simp [blocks_fun]) ⟨j, finset.mem_univ _, i_blocks⟩,
      end
      ... = n : c.sum_blocks_fun }
end

lemma eq_ones_iff_le_length {c : composition n} :
  c = ones n ↔ n ≤ c.length :=
by simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]

/-! ### The composition `composition.single` -/

/-- The composition made of a single block of size `n`. -/
def single (n : ℕ) (h : 0 < n) : composition n :=
⟨[n], by simp [h], by simp⟩

@[simp] lemma single_length {n : ℕ} (h : 0 < n) : (single n h).length = 1 := rfl

@[simp] lemma single_blocks {n : ℕ} (h : 0 < n) : (single n h).blocks = [n] := rfl

@[simp] lemma single_blocks_fun {n : ℕ} (h : 0 < n) (i : fin (single n h).length) :
  (single n h).blocks_fun i = n :=
by simp [blocks_fun, single, blocks, i.2]

@[simp] lemma single_embedding {n : ℕ} (h : 0 < n) (i : fin n) :
  (single n h).embedding ⟨0, single_length h ▸ zero_lt_one⟩ i = i :=
by { ext, simp }

lemma eq_single_iff_length {n : ℕ} (h : 0 < n) {c : composition n} :
  c = single n h ↔ c.length = 1 :=
begin
  split,
  { assume H,
    rw H,
    exact single_length h },
  { assume H,
    ext1,
    have A : c.blocks.length = 1 := H ▸ c.blocks_length,
    have B : c.blocks.sum = n := c.blocks_sum,
    rw eq_cons_of_length_one A at B ⊢,
    simpa [single_blocks] using B }
end

lemma ne_single_iff {n : ℕ} (hn : 0 < n) {c : composition n} :
  c ≠ single n hn ↔ ∀ i, c.blocks_fun i < n :=
begin
  rw ← not_iff_not,
  push_neg,
  split,
  { rintros rfl,
    exact ⟨⟨0, by simp⟩, by simp⟩ },
  { rintros ⟨i, hi⟩,
    rw eq_single_iff_length,
    have : ∀ j : fin c.length, j = i,
    { intros j,
      by_contradiction ji,
      apply lt_irrefl ∑ k, c.blocks_fun k,
      calc ∑ k, c.blocks_fun k ≤ c.blocks_fun i      : by simp only [c.sum_blocks_fun, hi]
                           ... < ∑ k, c.blocks_fun k :
        finset.single_lt_sum ji (finset.mem_univ _) (finset.mem_univ _) (c.one_le_blocks_fun j)
          (λ _ _ _, zero_le _) },
    simpa using fintype.card_eq_one_of_forall_eq this }
end

end composition

/-!
### Splitting a list

Given a list of length `n` and a composition `c` of `n`, one can split `l` into `c.length` sublists
of respective lengths `c.blocks_fun 0`, ..., `c.blocks_fun (c.length-1)`. This is inverse to the
join operation.
-/
namespace list
variable {α : Type*}

/-- Auxiliary for `list.split_wrt_composition`. -/
def split_wrt_composition_aux : list α → list ℕ → list (list α)
| l [] := []
| l (n :: ns) :=
  let (l₁, l₂) := l.split_at n in
  l₁ :: split_wrt_composition_aux l₂ ns

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
def split_wrt_composition (l : list α) (c : composition n) : list (list α) :=
split_wrt_composition_aux l c.blocks

local attribute [simp] split_wrt_composition_aux.equations._eqn_1

local attribute [simp]
lemma split_wrt_composition_aux_cons (l : list α) (n ns) :
  l.split_wrt_composition_aux (n :: ns) = take n l :: (drop n l).split_wrt_composition_aux ns :=
by simp [split_wrt_composition_aux]

lemma length_split_wrt_composition_aux (l : list α) (ns) :
  length (l.split_wrt_composition_aux ns) = ns.length :=
by induction ns generalizing l; simp *

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp] lemma length_split_wrt_composition (l : list α) (c : composition n) :
  length (l.split_wrt_composition c) = c.length :=
length_split_wrt_composition_aux _ _

lemma map_length_split_wrt_composition_aux {ns : list ℕ} :
  ∀ {l : list α}, ns.sum ≤ l.length → map length (l.split_wrt_composition_aux ns) = ns :=
begin
  induction ns with n ns IH; intros l h; simp at h ⊢,
  have := le_trans (nat.le_add_right _ _) h,
  rw IH, {simp [this]},
  rwa [length_drop, nat.le_sub_left_iff_add_le this]
end

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
lemma map_length_split_wrt_composition (l : list α) (c : composition l.length) :
  map length (l.split_wrt_composition c) = c.blocks :=
map_length_split_wrt_composition_aux (le_of_eq c.blocks_sum)

lemma length_pos_of_mem_split_wrt_composition {l l' : list α} {c : composition l.length}
  (h : l' ∈ l.split_wrt_composition c) : 0 < length l' :=
begin
  have : l'.length ∈ (l.split_wrt_composition c).map list.length :=
    list.mem_map_of_mem list.length h,
  rw map_length_split_wrt_composition at this,
  exact c.blocks_pos this
end

lemma sum_take_map_length_split_wrt_composition
  (l : list α) (c : composition l.length) (i : ℕ) :
  (((l.split_wrt_composition c).map length).take i).sum = c.size_up_to i :=
by { congr, exact map_length_split_wrt_composition l c }

lemma nth_le_split_wrt_composition_aux (l : list α) (ns : list ℕ) {i : ℕ} (hi) :
  nth_le (l.split_wrt_composition_aux ns) i hi =
  (l.take (ns.take (i+1)).sum).drop (ns.take i).sum :=
begin
  induction ns with n ns IH generalizing l i, {cases hi},
  cases i; simp [IH],
  rw [add_comm n, drop_add, drop_take],
end

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.size_up_to i` and `c.size_up_to (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
lemma nth_le_split_wrt_composition (l : list α) (c : composition n)
  {i : ℕ} (hi : i < (l.split_wrt_composition c).length) :
  nth_le (l.split_wrt_composition c) i hi = (l.take (c.size_up_to (i+1))).drop (c.size_up_to i) :=
nth_le_split_wrt_composition_aux _ _ _

theorem join_split_wrt_composition_aux {ns : list ℕ} :
  ∀ {l : list α}, ns.sum = l.length → (l.split_wrt_composition_aux ns).join = l :=
begin
  induction ns with n ns IH; intros l h; simp at h ⊢,
  { exact (length_eq_zero.1 h.symm).symm },
  rw IH, {simp},
  rwa [length_drop, ← h, nat.add_sub_cancel_left]
end

/-- If one splits a list along a composition, and then joins the sublists, one gets back the
original list. -/
@[simp] theorem join_split_wrt_composition (l : list α) (c : composition l.length) :
  (l.split_wrt_composition c).join = l :=
join_split_wrt_composition_aux c.blocks_sum

/-- If one joins a list of lists and then splits the join along the right composition, one gets
back the original list of lists. -/
@[simp] theorem split_wrt_composition_join (L : list (list α)) (c : composition L.join.length)
  (h : map length L = c.blocks) : split_wrt_composition (join L) c = L :=
by simp only [eq_self_iff_true, and_self, eq_iff_join_eq, join_split_wrt_composition,
              map_length_split_wrt_composition, h]

end list

/-!
### Compositions as sets

Combinatorial viewpoints on compositions, seen as finite subsets of `fin (n+1)` containing `0` and
`n`, where the points of the set (other than `n`) correspond to the leftmost points of each block.
-/

/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
def composition_as_set_equiv (n : ℕ) : composition_as_set n ≃ finset (fin (n - 1)) :=
{ to_fun := λ c, {i : fin (n-1) |
    (⟨1 + (i : ℕ), begin
       apply (add_lt_add_left i.is_lt 1).trans_le,
       rw [nat.succ_eq_add_one, add_comm],
       exact add_le_add (nat.sub_le n 1) (le_refl 1)
    end ⟩ : fin n.succ) ∈ c.boundaries}.to_finset,
  inv_fun := λ s,
    { boundaries := {i : fin n.succ | (i = 0) ∨ (i = fin.last n)
        ∨ (∃ (j : fin (n-1)) (hj : j ∈ s), (i : ℕ) = j + 1)}.to_finset,
      zero_mem   := by simp,
      last_mem   := by simp },
  left_inv := begin
    assume c,
    ext i,
    simp only [exists_prop, add_comm, set.mem_to_finset, true_or, or_true, set.mem_set_of_eq],
    split,
    { rintro (rfl | rfl | ⟨j, hj1, hj2⟩),
      { exact c.zero_mem },
      { exact c.last_mem },
      { convert hj1, rwa fin.ext_iff } },
    { simp only [or_iff_not_imp_left],
      assume i_mem i_ne_zero i_ne_last,
      simp [fin.ext_iff] at i_ne_zero i_ne_last,
      have A : (1 + (i-1) : ℕ) = (i : ℕ),
        by { rw add_comm, exact nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr i_ne_zero) },
      refine ⟨⟨i - 1, _⟩, _, _⟩,
      { have : (i : ℕ) < n + 1 := i.2,
        simp [nat.lt_succ_iff_lt_or_eq, i_ne_last] at this,
        exact nat.pred_lt_pred i_ne_zero this },
      { convert i_mem,
        rw fin.ext_iff,
        simp only [fin.coe_mk, A] },
      { simp [A] } },
  end,
  right_inv := begin
    assume s,
    ext i,
    have : 1 + (i : ℕ) ≠ n,
    { apply ne_of_lt,
      convert add_lt_add_left i.is_lt 1,
      rw add_comm,
      apply (nat.succ_pred_eq_of_pos _).symm,
      exact (zero_le i.val).trans_lt (i.2.trans_le (nat.sub_le n 1)) },
    simp only [fin.ext_iff, exists_prop, fin.coe_zero, add_comm,
      set.mem_to_finset, set.mem_set_of_eq, fin.coe_last],
    erw [set.mem_set_of_eq],
    simp only [this, false_or, add_right_inj, add_eq_zero_iff, one_ne_zero, false_and, fin.coe_mk],
    split,
    { rintros ⟨j, js, hj⟩, convert js, exact (fin.ext_iff _ _).2 hj },
    { assume h, exact ⟨i, h, rfl⟩ }
  end }

instance composition_as_set_fintype (n : ℕ) : fintype (composition_as_set n) :=
fintype.of_equiv _ (composition_as_set_equiv n).symm

lemma composition_as_set_card (n : ℕ) : fintype.card (composition_as_set n) = 2 ^ (n - 1) :=
begin
  have : fintype.card (finset (fin (n-1))) = 2 ^ (n - 1), by simp,
  rw ← this,
  exact fintype.card_congr (composition_as_set_equiv n)
end

namespace composition_as_set

variables (c : composition_as_set n)

lemma boundaries_nonempty : c.boundaries.nonempty :=
⟨0, c.zero_mem⟩

lemma card_boundaries_pos : 0 < finset.card c.boundaries :=
finset.card_pos.mpr c.boundaries_nonempty

/-- Number of blocks in a `composition_as_set`. -/
def length : ℕ := finset.card c.boundaries - 1

lemma card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
(nat.sub_eq_iff_eq_add c.card_boundaries_pos).mp rfl

lemma length_lt_card_boundaries : c.length < c.boundaries.card :=
by { rw c.card_boundaries_eq_succ_length, exact lt_add_one _ }

lemma lt_length (i : fin c.length) : (i : ℕ) + 1 < c.boundaries.card :=
nat.add_lt_of_lt_sub_right i.2

lemma lt_length' (i : fin c.length) : (i : ℕ) < c.boundaries.card :=
lt_of_le_of_lt (nat.le_succ i) (c.lt_length i)

/-- Canonical increasing bijection from `fin c.boundaries.card` to `c.boundaries`. -/
def boundary : fin c.boundaries.card ↪o fin (n + 1) := c.boundaries.order_emb_of_fin rfl

@[simp] lemma boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : fin (n + 1)) = 0 :=
begin
  rw [boundary, finset.order_emb_of_fin_zero rfl c.card_boundaries_pos],
  exact le_antisymm (finset.min'_le _ _ c.zero_mem) (fin.zero_le _),
end

@[simp] lemma boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = fin.last n :=
begin
  convert finset.order_emb_of_fin_last rfl c.card_boundaries_pos,
  exact le_antisymm (finset.le_max' _ _ c.last_mem) (fin.le_last _)
end

/-- Size of the `i`-th block in a `composition_as_set`, seen as a function on `fin c.length`. -/
def blocks_fun (i : fin c.length) : ℕ :=
(c.boundary ⟨(i : ℕ) + 1, c.lt_length i⟩) - (c.boundary ⟨i, c.lt_length' i⟩)

lemma blocks_fun_pos (i : fin c.length) : 0 < c.blocks_fun i :=
begin
  have : (⟨i, c.lt_length' i⟩ : fin c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ :=
    nat.lt_succ_self _,
  exact nat.lt_sub_left_of_add_lt ((c.boundaries.order_emb_of_fin rfl).strict_mono this)
end

/-- List of the sizes of the blocks in a `composition_as_set`. -/
def blocks (c : composition_as_set n) : list ℕ :=
of_fn c.blocks_fun

@[simp] lemma blocks_length : c.blocks.length = c.length :=
length_of_fn _

lemma blocks_partial_sum {i : ℕ} (h : i < c.boundaries.card) :
  (c.blocks.take i).sum = c.boundary ⟨i, h⟩ :=
begin
  induction i with i IH, { simp },
  have A : i < c.blocks.length,
  { rw c.card_boundaries_eq_succ_length at h,
    simp [blocks, nat.lt_of_succ_lt_succ h] },
  have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length, nat.sub_le]),
  rw [sum_take_succ _ _ A, IH B],
  simp only [blocks, blocks_fun, nth_le_of_fn'],
  apply nat.add_sub_cancel',
  simp
end

lemma mem_boundaries_iff_exists_blocks_sum_take_eq {j : fin (n+1)} :
  j ∈ c.boundaries ↔ ∃ i < c.boundaries.card, (c.blocks.take i).sum = j :=
begin
  split,
  { assume hj,
    rcases (c.boundaries.order_iso_of_fin rfl).surjective ⟨j, hj⟩ with ⟨i, hi⟩,
    rw [subtype.ext_iff, subtype.coe_mk] at hi,
    refine ⟨i.1, i.2, _⟩,
    rw [← hi, c.blocks_partial_sum i.2],
    refl },
  { rintros ⟨i, hi, H⟩,
    convert (c.boundaries.order_iso_of_fin rfl ⟨i, hi⟩).2,
    have : c.boundary ⟨i, hi⟩ = j, by rwa [fin.ext_iff, ← c.blocks_partial_sum hi],
    exact this.symm }
end

lemma blocks_sum : c.blocks.sum = n :=
begin
  have : c.blocks.take c.length = c.blocks := take_all_of_le (by simp [blocks]),
  rw [← this, c.blocks_partial_sum c.length_lt_card_boundaries, c.boundary_length],
  refl
end

/-- Associating a `composition n` to a `composition_as_set n`, by registering the sizes of the
blocks as a list of positive integers. -/
def to_composition : composition n :=
{ blocks     := c.blocks,
  blocks_pos := by simp only [blocks, forall_mem_of_fn_iff, blocks_fun_pos c, forall_true_iff],
  blocks_sum := c.blocks_sum }

end composition_as_set


/-!
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `composition` and a
`composition_as_set`, by showing that their `blocks` and `length` and `boundaries` correspond to
each other, and construct an equivalence between them called `composition_equiv`.
-/

@[simp] lemma composition.to_composition_as_set_length (c : composition n) :
  c.to_composition_as_set.length = c.length :=
by simp [composition.to_composition_as_set, composition_as_set.length,
         c.card_boundaries_eq_succ_length]

@[simp] lemma composition_as_set.to_composition_length (c : composition_as_set n) :
  c.to_composition.length = c.length :=
by simp [composition_as_set.to_composition, composition.length, composition.blocks]

@[simp] lemma composition.to_composition_as_set_blocks (c : composition n) :
  c.to_composition_as_set.blocks = c.blocks :=
begin
  let d := c.to_composition_as_set,
  change d.blocks = c.blocks,
  have length_eq : d.blocks.length = c.blocks.length,
  { convert c.to_composition_as_set_length,
    simp [composition_as_set.blocks] },
  suffices H : ∀ (i ≤ d.blocks.length), (d.blocks.take i).sum = (c.blocks.take i).sum,
    from eq_of_sum_take_eq length_eq H,
  assume i hi,
  have i_lt : i < d.boundaries.card,
  { convert nat.lt_succ_iff.2 hi,
    convert d.card_boundaries_eq_succ_length,
    exact length_of_fn _ },
  have i_lt' : i < c.boundaries.card := i_lt,
  have i_lt'' : i < c.length + 1, by rwa c.card_boundaries_eq_succ_length at i_lt',
  have A : d.boundaries.order_emb_of_fin rfl ⟨i, i_lt⟩
    = c.boundaries.order_emb_of_fin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩ := rfl,
  have B : c.size_up_to i = c.boundary ⟨i, i_lt''⟩ := rfl,
  rw [d.blocks_partial_sum i_lt, composition_as_set.boundary, ← composition.size_up_to, B,
    A, c.order_emb_of_fin_boundaries]
end

@[simp] lemma composition_as_set.to_composition_blocks (c : composition_as_set n) :
  c.to_composition.blocks = c.blocks := rfl

@[simp] lemma composition_as_set.to_composition_boundaries (c : composition_as_set n) :
  c.to_composition.boundaries = c.boundaries :=
begin
  ext j,
  simp [c.mem_boundaries_iff_exists_blocks_sum_take_eq, c.card_boundaries_eq_succ_length,
    composition.boundary, fin.ext_iff, composition.size_up_to, exists_prop, finset.mem_univ,
    take, exists_prop_of_true, finset.mem_image, composition_as_set.to_composition_blocks,
    composition.boundaries],
  split,
  { rintros ⟨i, hi⟩,
    refine ⟨i.1, _, hi⟩,
    convert i.2,
    simp },
  { rintros ⟨i, i_lt, hi⟩,
    have : i < c.to_composition.length + 1, by simpa using i_lt,
    exact ⟨⟨i, this⟩, hi⟩ }
end

@[simp] lemma composition.to_composition_as_set_boundaries (c : composition n) :
  c.to_composition_as_set.boundaries = c.boundaries := rfl

/-- Equivalence between `composition n` and `composition_as_set n`. -/
def composition_equiv (n : ℕ) : composition n ≃ composition_as_set n :=
{ to_fun    := λ c, c.to_composition_as_set,
  inv_fun   := λ c, c.to_composition,
  left_inv  := λ c, by { ext1, exact c.to_composition_as_set_blocks },
  right_inv := λ c, by { ext1, exact c.to_composition_boundaries } }

instance composition_fintype (n : ℕ) : fintype (composition n) :=
fintype.of_equiv _ (composition_equiv n).symm

lemma composition_card (n : ℕ) : fintype.card (composition n) = 2 ^ (n - 1) :=
begin
  rw ← composition_as_set_card n,
  exact fintype.card_congr (composition_equiv n)
end
