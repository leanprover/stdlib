/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.real.basic
import data.set.disjointed
import data.set.intervals
import set_theory.cardinal
/-!
Proof that a cube (in dimension n ≥ 3) cannot be cubed:
There does not exist a partition of a cube into finitely many smaller cubes (at least two)
of different sizes.

We follow the proof described here:
http://www.alaricstephen.com/main-featured/2017/9/28/cubing-a-cube-proof
-/


open real set function fin

noncomputable theory

variable {n : ℕ}

/-- Given three intervals `I, J, K` such that `J ⊂ I`,
  neither endpoint of `J` coincides with an endpoint of `I`, `¬ (K ⊆ J)` and
  `K` does not lie completely to the left nor completely to the right of `J`.
  Then `I ∩ K \ J` is nonempty. -/
lemma Ico_lemma {α} [linear_order α] {x₁ x₂ y₁ y₂ z₁ z₂ w : α}
  (h₁ : x₁ < y₁) (hy : y₁ < y₂) (h₂ : y₂ < x₂)
  (hz₁ : z₁ ≤ y₂) (hz₂ : y₁ ≤ z₂) (hw : w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂) :
  ∃w, w ∈ Ico x₁ x₂ ∧ w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂ :=
begin
  simp only [not_and, not_lt, mem_Ico] at hw,
  refine ⟨max x₁ (min w y₂), _, _, _⟩,
  { simp [le_refl, lt_trans h₁ (lt_trans hy h₂), h₂] },
  { simp [hw, lt_irrefl, not_le_of_lt h₁] {contextual := tt} },
  { simp [hw.2.1, hw.2.2, hz₁, lt_of_lt_of_le h₁ hz₂] at ⊢ }
end

/-- A (hyper)-cube (in standard orientation) is a vector `b` consisting of the bottom-left point
of the cube, a width `w` and a proof that `w > 0`. We use functions from `fin n` to denote vectors.
-/
structure cube (n : ℕ) : Type :=
(b : fin n → ℝ) -- bottom-left coordinate
(w : ℝ) -- width
(hw : 0 < w)

namespace cube
lemma hw' (c : cube n) : 0 ≤ c.w := le_of_lt c.hw

/-- The j-th side of a cube is the half-open interval `[b j, b j + w)` -/
def side (c : cube n) (j : fin n) : set ℝ :=
Ico (c.b j) (c.b j + c.w)

@[simp] lemma b_mem_side (c : cube n) (j : fin n) : c.b j ∈ c.side j :=
by simp [side, cube.hw, le_refl]

def to_set (c : cube n) : set (fin n → ℝ) :=
{ x | ∀j, x j ∈ side c j }

def to_set_subset {c c' : cube n} : c.to_set ⊆ c'.to_set ↔ ∀j, c.side j ⊆ c'.side j :=
begin
  split, intros h j x hx,
  let f : fin n → ℝ := λ j', if j' = j then x else c.b j',
  have : f ∈ c.to_set,
  { intro j', by_cases hj' : j' = j; simp [f, hj', if_pos, if_neg, hx] },
  convert h this j, { simp [f, if_pos] },
  intros h f hf j, exact h j (hf j)
end

def to_set_disjoint {c c' : cube n} : disjoint c.to_set c'.to_set ↔
  ∃j, disjoint (c.side j) (c'.side j) :=
begin
  split, intros h, classical, by_contra h',
  simp only [not_disjoint_iff, classical.skolem, not_exists] at h',
  cases h' with f hf,
  apply not_disjoint_iff.mpr ⟨f, _, _⟩ h; intro j, exact (hf j).1, exact (hf j).2,
  rintro ⟨j, hj⟩, rw [set.disjoint_iff], rintros f ⟨h1f, h2f⟩,
  apply not_disjoint_iff.mpr ⟨f j, h1f j, h2f j⟩ hj
end

lemma b_mem_to_set (c : cube n) : c.b ∈ c.to_set :=
by simp [to_set]

protected def tail (c : cube (n+1)) : cube n :=
⟨tail c.b, c.w, c.hw⟩

lemma side_tail (c : cube (n+1)) (j : fin n) : c.tail.side j = c.side j.succ := rfl

def bottom (c : cube (n+1)) : set (fin (n+1) → ℝ) :=
{ x | x 0 = c.b 0 ∧ tail x ∈ c.tail.to_set }

lemma b_mem_bottom (c : cube (n+1)) : c.b ∈ c.bottom :=
by simp [bottom, to_set, side, cube.hw, le_refl, cube.tail]

def xm (c : cube (n+1)) : ℝ :=
c.b 0 + c.w

lemma b_lt_xm (c : cube (n+1)) : c.b 0 < c.xm := by simp [xm, hw]
lemma b_ne_xm (c : cube (n+1)) : c.b 0 ≠ c.xm := ne_of_lt c.b_lt_xm

def shift_up (c : cube (n+1)) : cube (n+1) :=
⟨cons c.xm $ tail c.b, c.w, c.hw⟩

@[simp] lemma tail_shift_up (c : cube (n+1)) : c.shift_up.tail = c.tail :=
by simp [shift_up, cube.tail]

@[simp] lemma head_shift_up (c : cube (n+1)) : c.shift_up.b 0 = c.xm := rfl

def unit_cube : cube n :=
⟨λ _, 0, 1, by norm_num⟩

@[simp] lemma side_unit_cube {j : fin n} : unit_cube.side j = Ico 0 1 :=
by norm_num [unit_cube, side]

end cube
open cube

variables {ι : Type} [fintype ι] {cs : ι → cube (n+1)} {i i' : ι}

/-- A finite family of (at least 2) cubes partitioning the unit cube with different sizes -/
def correct (cs : ι → cube n) : Prop :=
pairwise (disjoint on (cube.to_set ∘ cs)) ∧
(⋃(i : ι), (cs i).to_set) = unit_cube.to_set ∧
injective (cube.w ∘ cs) ∧
2 ≤ cardinal.mk ι ∧
3 ≤ n

variable (h : correct cs)

include h
lemma to_set_subset_unit_cube {i} : (cs i).to_set ⊆ unit_cube.to_set :=
by { rw [←h.2.1], exact subset_Union _ i }

lemma side_subset {i j} : (cs i).side j ⊆ Ico 0 1 :=
by { have := to_set_subset_unit_cube h, rw [to_set_subset] at this,
     convert this j, norm_num [unit_cube] }

lemma zero_le_of_mem_side {i j x} (hx : x ∈ (cs i).side j) : 0 ≤ x :=
(side_subset h hx).1

lemma zero_le_of_mem {i p} (hp : p ∈ (cs i).to_set) (j) : 0 ≤ p j :=
zero_le_of_mem_side h (hp j)

lemma zero_le_b {i j} : 0 ≤ (cs i).b j :=
zero_le_of_mem h (cs i).b_mem_to_set j

lemma b_add_w_le_one {j} : (cs i).b j + (cs i).w ≤ 1 :=
by { have := side_subset h, rw [side, Ico_subset_Ico_iff] at this, convert this.2, simp [hw] }

/-- The width of any cube in the partition cannot be 1. -/
lemma w_ne_one (i : ι) : (cs i).w ≠ 1 :=
begin
  intro hi,
  have := h.2.2.2.1, rw [cardinal.two_le_iff' i] at this, cases this with i' hi',
  let p := (cs i').b,
  have hp : p ∈ (cs i').to_set := (cs i').b_mem_to_set,
  have h2p : p ∈ (cs i).to_set,
  { intro j, split,
    transitivity (0 : ℝ),
    { rw [←add_le_add_iff_right (1 : ℝ)], convert b_add_w_le_one h, rw hi, rw zero_add },
    apply zero_le_b h, apply lt_of_lt_of_le (side_subset h $ (cs i').b_mem_side j).2,
    simp [hi, zero_le_b h] },
  apply not_disjoint_iff.mpr ⟨p, hp, h2p⟩,
  apply h.1, exact hi'.symm
end

/-- The top of a cube (which is the bottom of the cube shifted up by its width) must be covered by
  bottoms of (other) cubes in the family. -/
lemma shift_up_bottom_subset_bottoms (hc : (cs i).xm ≠ 1) :
  (cs i).shift_up.bottom ⊆ ⋃(i : ι), (cs i).bottom :=
begin
  intros p hp, cases hp with hp0 hps, rw [tail_shift_up] at hps,
  have : p ∈ (unit_cube : cube (n+1)).to_set,
  { simp only [to_set, forall_fin_succ, hp0, side_unit_cube, mem_set_of_eq, mem_Ico,
      head_shift_up], refine ⟨⟨_, _⟩, _⟩,
    { rw [←zero_add (0 : ℝ)], apply add_le_add, apply zero_le_b h, apply (cs i).hw' },
    { exact lt_of_le_of_ne (b_add_w_le_one h) hc },
    intro j, exact side_subset h (hps j) },
  rw [←h.2.1] at this, rcases this with ⟨_, ⟨i', rfl⟩, hi'⟩,
  rw [mem_Union], use i', refine ⟨_, λ j, hi' j.succ⟩,
  have : i ≠ i', { rintro rfl, apply not_le_of_lt (hi' 0).2, rw [hp0], refl },
  have := h.1 i i' this, rw [on_fun, to_set_disjoint, exists_fin_succ] at this,
  rcases this with h0|⟨j, hj⟩,
  rw [hp0], symmetry, apply eq_of_Ico_disjoint h0 (by simp [hw]) _,
  convert hi' 0, rw [hp0], refl,
  exfalso, apply not_disjoint_iff.mpr ⟨tail p j, hps j, hi' j.succ⟩ hj
end
omit h

/-- A valley is a square on which cubes in the family of cubes are placed, so that the cubes
  completely cover the valley and none of those cubes is partially outside the square.
  We also require that no cube on it has the same size as the valley (so that there are at least
  two cubes on the valley).
  This is the main concept in the formalization.
  We prove that the smallest cube on a valley has another valley on the top of it, which
  gives an infinite sequence of cubes in the partition, which contradicts the finiteness.
  A valley is characterized by a cube `c` (which is not a cube in the family cs) by considering
  the bottom face of `c`. -/
def valley (cs : ι → cube (n+1)) (c : cube (n+1)) : Prop :=
c.bottom ⊆ (⋃(i : ι), (cs i).bottom) ∧
(∀i, (cs i).b 0 = c.b 0 → (∃x, x ∈ (cs i).tail.to_set ∩ c.tail.to_set) →
  (cs i).tail.to_set ⊆ c.tail.to_set) ∧
∀(i : ι), (cs i).b 0 = c.b 0 → (cs i).w ≠ c.w

variables {c : cube (n+1)} (v : valley cs c)

/-- The bottom of the unit cube is a valley -/
lemma valley_unit_cube (h : correct cs) : valley cs unit_cube :=
begin
  refine ⟨_, _, _⟩,
  { intro v,
    simp only [bottom, and_imp, mem_Union, mem_set_of_eq],
    intros h0 hv,
    have : v ∈ (unit_cube : cube (n+1)).to_set,
    { dsimp only [to_set, unit_cube, mem_set_of_eq],
      rw [forall_fin_succ, h0], split, norm_num [side, unit_cube], exact hv },
    rw [←h.2.1] at this, rcases this with ⟨_, ⟨i, rfl⟩, hi⟩,
    use i,
    split, { apply le_antisymm, rw h0, exact zero_le_b h, exact (hi 0).1 },
    intro j, exact hi _ },
  { intros i hi h', rw to_set_subset, intro j, convert side_subset h using 1, simp [side_tail] },
  { intros i hi, exact w_ne_one h i }
end

/-- the cubes which lie in the valley `c` -/
def bcubes (cs : ι → cube (n+1)) (c : cube (n+1)) : set ι :=
{ i : ι | (cs i).b 0 = c.b 0 ∧ (cs i).tail.to_set ⊆ c.tail.to_set }

/-- A cube which lies on the boundary of a valley in dimension `j` -/
def on_boundary (hi : i ∈ bcubes cs c) (j : fin n) : Prop :=
c.b j.succ = (cs i).b j.succ ∨ (cs i).b j.succ + (cs i).w = c.b j.succ + c.w

lemma tail_sub (hi : i ∈ bcubes cs c) : ∀j, (cs i).tail.side j ⊆ c.tail.side j :=
by { rw [←to_set_subset], exact hi.2 }

lemma bottom_mem_side (hi : i ∈ bcubes cs c) : c.b 0 ∈ (cs i).side 0 :=
by { convert b_mem_side (cs i) _ using 1, rw hi.1 }

lemma b_le_b (hi : i ∈ bcubes cs c) (j : fin n) : c.b j.succ ≤ (cs i).b j.succ :=
(tail_sub hi j $ b_mem_side _ _).1

lemma t_le_t (hi : i ∈ bcubes cs c) (j : fin n) :
  (cs i).b j.succ + (cs i).w ≤ c.b j.succ + c.w  :=
begin
  have h' := tail_sub hi j, dsimp only [side] at h', rw [Ico_subset_Ico_iff] at h',
  exact h'.2, simp [hw]
end

include h v
/-- Every cube in the valley must be smaller than it -/
lemma w_lt_w (hi : i ∈ bcubes cs c) : (cs i).w < c.w :=
begin
  apply lt_of_le_of_ne _ (v.2.2 i hi.1),
  have j : fin n := ⟨1, nat.le_of_succ_le_succ h.2.2.2.2⟩,
  rw [←add_le_add_iff_left ((cs i).b j.succ)],
  apply le_trans (t_le_t hi j), rw [add_le_add_iff_right], apply b_le_b hi,
end

open cardinal
/-- There are at least two cubes in a valley -/
lemma two_le_mk_bcubes : 2 ≤ cardinal.mk (bcubes cs c) :=
begin
  rw [two_le_iff],
  rcases v.1 c.b_mem_bottom with ⟨_, ⟨i, rfl⟩, hi⟩,
  have h2i : i ∈ bcubes cs c :=
    ⟨hi.1.symm, v.2.1 i hi.1.symm ⟨tail c.b, hi.2, λ j, c.b_mem_side j.succ⟩⟩,
  let j : fin (n+1) := ⟨2, h.2.2.2.2⟩,
  have hj : 0 ≠ j := by { simp only [fin.ext_iff, ne.def], contradiction },
  let p : fin (n+1) → ℝ := λ j', if j' = j then c.b j + (cs i).w else c.b j',
  have hp : p ∈ c.bottom,
  { split, { simp only [bottom, p, if_neg hj] },
    intro j', simp only [tail, side_tail],
    by_cases hj' : j'.succ = j,
    { simp [p, -add_comm, if_pos, side, hj', hw', w_lt_w h v h2i] },
    { simp [p, -add_comm, if_neg hj'] }},
  rcases v.1 hp with ⟨_, ⟨i', rfl⟩, hi'⟩,
  have h2i' : i' ∈ bcubes cs c := ⟨hi'.1.symm, v.2.1 i' hi'.1.symm ⟨tail p, hi'.2, hp.2⟩⟩,
  refine ⟨⟨i, h2i⟩, ⟨i', h2i'⟩, _⟩,
  intro hii', cases congr_arg subtype.val hii',
  apply not_le_of_lt (hi'.2 ⟨1, nat.le_of_succ_le_succ h.2.2.2.2⟩).2,
  simp only [-add_comm, tail, cube.tail, p],
  rw [if_pos, add_le_add_iff_right],
  { exact (hi.2 _).1 },
  refl
end

/-- There is a cube in the valley -/
lemma nonempty_bcubes : (bcubes cs c).nonempty :=
begin
  rw [←set.ne_empty_iff_nonempty], intro h', have := two_le_mk_bcubes h v, rw h' at this,
  apply not_lt_of_le this, rw mk_emptyc, norm_cast, norm_num
end

/-- There is a smallest cube in the valley -/
lemma exists_mi : ∃(i : ι), i ∈ bcubes cs c ∧ ∀(i' ∈ bcubes cs c),
  (cs i).w ≤ (cs i').w :=
by simpa
  using (bcubes cs c).exists_min_image (λ i, (cs i).w) (finite.of_fintype _) (nonempty_bcubes h v)

/-- We let `mi` be the (index for the) smallest cube in the valley `c` -/
def mi : ι := classical.some $ exists_mi h v

variables {h v}
lemma mi_mem_bcubes : mi h v ∈ bcubes cs c :=
(classical.some_spec $ exists_mi h v).1

lemma mi_minimal (hi : i ∈ bcubes cs c) : (cs $ mi h v).w ≤ (cs i).w :=
(classical.some_spec $ exists_mi h v).2 i hi

lemma mi_strict_minimal (hii' : mi h v ≠ i) (hi : i ∈ bcubes cs c) :
  (cs $ mi h v).w < (cs i).w :=
by { apply lt_of_le_of_ne (mi_minimal hi), apply h.2.2.1.ne, apply hii' }

/-- The top of `mi` cannot be 1, since there is a larger cube in the valley -/
lemma mi_xm_ne_one : (cs $ mi h v).xm ≠ 1 :=
begin
  apply ne_of_lt, rcases (two_le_iff' _).mp (two_le_mk_bcubes h v) with ⟨⟨i, hi⟩, h2i⟩,
  swap, exact ⟨mi h v, mi_mem_bcubes⟩,
  apply lt_of_lt_of_le _ (b_add_w_le_one h), exact i, exact 0,
  rw [xm, mi_mem_bcubes.1, hi.1, _root_.add_lt_add_iff_left],
  apply mi_strict_minimal _ hi, intro h', apply h2i, rw subtype.ext_iff_val, exact h'
end

/-- If `mi` lies on the boundary of the valley in dimension j, then this lemma expresses that all
  other cubes on the same boundary extend further from the boundary.
  More precisely, there is a j-th coordinate `x : ℝ` in the valley, but not in `mi`,
  such that every cube that shares a (particular) j-th coordinate with `mi` also contains j-th
  coordinate `x` -/
lemma smallest_on_boundary {j} (bi : on_boundary (mi_mem_bcubes : mi h v ∈ _) j) :
  ∃(x : ℝ), x ∈ c.side j.succ \ (cs $ mi h v).side j.succ ∧
  ∀{{i'}} (hi' : i' ∈ bcubes cs c), i' ≠ mi h v →
    (cs $ mi h v).b j.succ ∈ (cs i').side j.succ → x ∈ (cs i').side j.succ :=
begin
  let i := mi h v, have hi : i ∈ bcubes cs c := mi_mem_bcubes,
  cases bi,
  { refine ⟨(cs i).b j.succ + (cs i).w, ⟨_, _⟩, _⟩,
    { simp [side, bi, hw', w_lt_w h v hi] },
    { intro h', simpa [i, lt_irrefl] using h'.2 },
    intros i' hi' i'_i h2i', split,
    apply le_trans h2i'.1, { simp [hw'] },
    apply lt_of_lt_of_le (add_lt_add_left (mi_strict_minimal i'_i.symm hi') _),
    simp [bi.symm, b_le_b hi'] },
  let s := bcubes cs c \ { i },
  have hs : s.nonempty,
  { rcases (two_le_iff' (⟨i, hi⟩ : bcubes cs c)).mp (two_le_mk_bcubes h v) with ⟨⟨i', hi'⟩, h2i'⟩,
    refine ⟨i', hi', _⟩, simp only [mem_singleton_iff], intro h, apply h2i', simp [h] },
  rcases set.exists_min_image s (w ∘ cs) (finite.of_fintype _) hs with ⟨i', ⟨hi', h2i'⟩, h3i'⟩,
  rw [mem_singleton_iff] at h2i',
  let x := c.b j.succ + c.w - (cs i').w,
  have hx : x < (cs i).b j.succ,
  { dsimp only [x], rw [←bi, add_sub_assoc, add_lt_iff_neg_left, sub_lt_zero],
    apply mi_strict_minimal (ne.symm h2i') hi' },
  refine ⟨x, ⟨_, _⟩, _⟩,
  { simp only [side, x, -add_comm, -add_assoc, neg_lt_zero, hw, add_lt_iff_neg_left, and_true,
      mem_Ico, sub_eq_add_neg],
    rw [add_assoc, le_add_iff_nonneg_right, ←sub_eq_add_neg, sub_nonneg],
    apply le_of_lt (w_lt_w h v hi') },
  { simp only [side, not_and_distrib, not_lt, add_comm, not_le, mem_Ico], left, exact hx },
  intros i'' hi'' h2i'' h3i'', split, swap, apply lt_trans hx h3i''.2,
  simp only [x], rw [le_sub_iff_add_le],
  refine le_trans _ (t_le_t hi'' j), rw [add_le_add_iff_left], apply h3i' i'' ⟨hi'', _⟩,
  simp [mem_singleton, h2i'']
end

variables (h v)
/-- `mi` cannot lie on the boundary of the valley. Otherwise, the cube adjacent to it in the `j`-th
  direction will intersect one of the neighbouring cubes on the same boundary as `mi`. -/
lemma mi_not_on_boundary (j : fin n) : ¬on_boundary (mi_mem_bcubes : mi h v ∈ _) j :=
begin
  let i := mi h v, have hi : i ∈ bcubes cs c := mi_mem_bcubes,
  rcases (two_le_iff' j).mp _ with ⟨j', hj'⟩, swap,
  { rw [mk_fin, ←nat.cast_two, nat_cast_le], apply nat.le_of_succ_le_succ h.2.2.2.2 },
  intro hj,
  rcases smallest_on_boundary hj with ⟨x, ⟨hx, h2x⟩, h3x⟩,
  let p : fin (n+1) → ℝ := cons (c.b 0) (λ j₂, if j₂ = j then x else (cs i).b j₂.succ),
  have hp : p ∈ c.bottom,
  { suffices : ∀ (j' : fin n), ite (j' = j) x ((cs i).b j'.succ) ∈ c.side j'.succ,
    { simpa [bottom, p, to_set, tail, side_tail] },
    intro j₂,
    by_cases hj₂ : j₂ = j, { simp [hj₂, hx] },
    simp only [hj₂, if_false], apply tail_sub hi, apply b_mem_side },
  rcases v.1 hp with ⟨_, ⟨i', rfl⟩, hi'⟩,
  have h2i' : i' ∈ bcubes cs c := ⟨hi'.1.symm, v.2.1 i' hi'.1.symm ⟨tail p, hi'.2, hp.2⟩⟩,
  have i_i' : i ≠ i', { rintro rfl, simpa [p, side_tail, i, h2x] using hi'.2 j },
  have : nonempty ↥((cs i').tail.side j' \ (cs i).tail.side j'),
  { apply nonempty_Ico_sdiff, apply mi_strict_minimal i_i' h2i', apply hw },
  rcases this with ⟨⟨x', hx'⟩⟩,
  let p' : fin (n+1) → ℝ :=
  cons (c.b 0) (λ j₂, if j₂ = j' then x' else (cs i).b j₂.succ),
  have hp' : p' ∈ c.bottom,
  { suffices : ∀ (j : fin n), ite (j = j') x' ((cs i).b j.succ) ∈ c.side j.succ,
    { simpa [bottom, p', to_set, tail, side_tail] },
    intro j₂,
    by_cases hj₂ : j₂ = j', simp [hj₂], apply tail_sub h2i', apply hx'.1,
    simp only [if_congr, if_false, hj₂], apply tail_sub hi, apply b_mem_side },
  rcases v.1 hp' with ⟨_, ⟨i'', rfl⟩, hi''⟩,
  have h2i'' : i'' ∈ bcubes cs c := ⟨hi''.1.symm, v.2.1 i'' hi''.1.symm ⟨tail p', hi''.2, hp'.2⟩⟩,
  have i'_i'' : i' ≠ i'',
  { rintro ⟨⟩,
    have : (cs i).b ∈ (cs i').to_set,
    { simp only [to_set, forall_fin_succ, hi.1, bottom_mem_side h2i', true_and, mem_set_of_eq],
    intro j₂, by_cases hj₂ : j₂ = j,
    { simpa [side_tail, p', hj', hj₂] using hi''.2 j },
    { simpa [hj₂] using hi'.2 j₂ } },
    apply not_disjoint_iff.mpr ⟨(cs i).b, (cs i).b_mem_to_set, this⟩ (h.1 i i' i_i') },
  have i_i'' : i ≠ i'', { intro h, induction h, simpa [hx'.2] using hi''.2 j' },
  apply not.elim _ (h.1 i' i'' i'_i''),
  simp only [on_fun, to_set_disjoint, not_disjoint_iff, forall_fin_succ, not_exists, comp_app],
  refine ⟨⟨c.b 0, bottom_mem_side h2i', bottom_mem_side h2i''⟩, _⟩,
  intro j₂,
  by_cases hj₂ : j₂ = j,
  { cases hj₂, refine ⟨x, _, _⟩,
    { convert hi'.2 j, simp [p] },
    apply h3x h2i'' i_i''.symm, convert hi''.2 j, simp [p', hj'] },
  by_cases h2j₂ : j₂ = j',
  { cases h2j₂, refine ⟨x', hx'.1, _⟩, convert hi''.2 j', simp },
  refine ⟨(cs i).b j₂.succ, _, _⟩,
  { convert hi'.2 j₂, simp [hj₂] },
  { convert hi''.2 j₂, simp [h2j₂] }
end

variables {h v}
/-- The same result that `mi` cannot lie on the boundary of the valley written as inequalities. -/
lemma mi_not_on_boundary' (j : fin n) : c.tail.b j < (cs (mi h v)).tail.b j ∧
  (cs (mi h v)).tail.b j + (cs (mi h v)).w < c.tail.b j + c.w :=
begin
  have := mi_not_on_boundary h v j,
  simp only [on_boundary, not_or_distrib] at this, cases this with h1 h2,
  split,
  apply lt_of_le_of_ne (b_le_b mi_mem_bcubes _) h1,
  apply lt_of_le_of_ne _ h2,
  apply ((Ico_subset_Ico_iff _).mp (tail_sub mi_mem_bcubes j)).2,
  simp [hw]
end

/-- The top of `mi` gives rise to a new valley, since the neighbouring cubes extend further upward
  than `mi`. -/
def valley_mi : valley cs ((cs (mi h v)).shift_up) :=
begin
  let i := mi h v, have hi : i ∈ bcubes cs c := mi_mem_bcubes,
  refine ⟨_, _, _⟩,
  { intro p, apply shift_up_bottom_subset_bottoms h mi_xm_ne_one },
  { rintros i' hi' ⟨p2, hp2, h2p2⟩, simp only [head_shift_up] at hi', classical, by_contra h2i',
    rw [tail_shift_up] at h2p2, simp only [not_subset, tail_shift_up] at h2i',
    rcases h2i' with ⟨p1, hp1, h2p1⟩,
    have : ∃p3, p3 ∈ (cs i').tail.to_set ∧ p3 ∉ (cs i).tail.to_set ∧ p3 ∈ c.tail.to_set,
    { simp only [to_set, not_forall, mem_set_of_eq] at h2p1, cases h2p1 with j hj,
      rcases Ico_lemma (mi_not_on_boundary' j).1 (by simp [hw]) (mi_not_on_boundary' j).2
        (le_trans (hp2 j).1 $ le_of_lt (h2p2 j).2)
        (le_trans (h2p2 j).1 $ le_of_lt (hp2 j).2) ⟨hj, hp1 j⟩ with ⟨w, hw, h2w, h3w⟩,
      refine ⟨λ j', if j' = j then w else p2 j', _, _, _⟩,
      { intro j', by_cases h : j' = j,
        { simp only [if_pos h], convert h3w },
        { simp only [if_neg h], exact hp2 j' } },
      { simp only [to_set, not_forall, mem_set_of_eq], use j, rw [if_pos rfl], convert h2w },
      { intro j', by_cases h : j' = j,
        { simp only [if_pos h, side_tail], convert hw },
        { simp only [if_neg h], apply hi.2, apply h2p2 } } },
    rcases this with ⟨p3, h1p3, h2p3, h3p3⟩,
    let p := @cons n (λ_, ℝ) (c.b 0) p3,
    have hp : p ∈ c.bottom, { refine ⟨rfl, _⟩, rwa [tail_cons] },
    rcases v.1 hp with ⟨_, ⟨i'', rfl⟩, hi''⟩,
    have h2i'' : i'' ∈ bcubes cs c,
    { use hi''.1.symm, apply v.2.1 i'' hi''.1.symm,
      use tail p, split, exact hi''.2, rw [tail_cons], exact h3p3 },
    have h3i'' : (cs i).w < (cs i'').w,
    { apply mi_strict_minimal _ h2i'', rintro rfl, apply h2p3, convert hi''.2, rw [tail_cons] },
    let p' := @cons n (λ_, ℝ) (cs i).xm p3,
    have hp' : p' ∈ (cs i').to_set,
    { simpa [to_set, forall_fin_succ, p', hi'.symm] using h1p3 },
    have h2p' : p' ∈ (cs i'').to_set,
    { simp only [to_set, forall_fin_succ, p', cons_succ, cons_zero, mem_set_of_eq],
      refine ⟨_, by simpa [to_set, p] using hi''.2⟩,
      have : (cs i).b 0 = (cs i'').b 0, { by rw [hi.1, h2i''.1] },
      simp [side, hw', xm, this, h3i''] },
    apply not_disjoint_iff.mpr ⟨p', hp', h2p'⟩,
    apply h.1, rintro rfl, apply (cs i).b_ne_xm, rw [←hi', ←hi''.1, hi.1], refl },
  { intros i' hi' h2i',
    dsimp only [shift_up] at h2i',
    replace h2i' := h.2.2.1 h2i'.symm,
    induction h2i',
    exact b_ne_xm (cs i) hi' }
end

variables (h)
omit v

/-- We get a sequence of cubes whose size is decreasing -/
noncomputable def sequence_of_cubes : ℕ → { i : ι // valley cs ((cs i).shift_up) }
| 0     := let v := valley_unit_cube h      in ⟨mi h v, valley_mi⟩
| (k+1) := let v := (sequence_of_cubes k).2 in ⟨mi h v, valley_mi⟩

def decreasing_sequence (k : ℕ) : order_dual ℝ :=
(cs (sequence_of_cubes h k).1).w

lemma strict_mono_sequence_of_cubes : strict_mono $ decreasing_sequence h :=
strict_mono.nat $
begin
  intro k, let v := (sequence_of_cubes h k).2, dsimp only [decreasing_sequence, sequence_of_cubes],
  apply w_lt_w h v (mi_mem_bcubes : mi h v ∈ _),
end

omit h
/-- The infinite sequence of cubes contradicts the finiteness of the family. -/
theorem not_correct : ¬correct cs :=
begin
  intro h, apply not_le_of_lt (lt_omega_iff_fintype.mpr ⟨_inst_1⟩),
  rw [omega, lift_id], fapply mk_le_of_injective, exact λ n, (sequence_of_cubes h n).1,
  intros n m hnm, apply strict_mono.injective (strict_mono_sequence_of_cubes h),
  dsimp only [decreasing_sequence], rw hnm
end

/-- **Dissection of Cubes**: A cube cannot be cubed. -/
theorem cannot_cube_a_cube :
  ∀{n : ℕ}, n ≥ 3 →                              -- In ℝ^n for n ≥ 3
  ∀{ι : Type} [fintype ι] {cs : ι → cube n},     -- given a finite collection of (hyper)cubes
  2 ≤ cardinal.mk ι →                            -- containing at least two elements
  pairwise (disjoint on (cube.to_set ∘ cs)) →    -- which is pairwise disjoint
  (⋃(i : ι), (cs i).to_set) = unit_cube.to_set → -- whose union is the unit cube
  injective (cube.w ∘ cs) →                      -- such that the widths of all cubes are different
  false :=                                       -- then we can derive a contradiction
begin
  intros n hn ι hι cs h1 h2 h3 h4, resetI,
  rcases n, cases hn,
  exact not_correct ⟨h2, h3, h4, h1, hn⟩
end
