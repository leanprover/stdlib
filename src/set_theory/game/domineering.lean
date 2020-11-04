/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import set_theory.game.state

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/

namespace pgame

namespace domineering

open function

/-- The embedding `(x, y) ↦ (x, y+1)`. -/
def shift_up : ℤ × ℤ ↪ ℤ × ℤ :=
(embedding.refl ℤ).prod_map ⟨λ n, n + 1, add_left_injective 1⟩
/-- The embedding `(x, y) ↦ (x+1, y)`. -/
def shift_right : ℤ × ℤ ↪ ℤ × ℤ :=
embedding.prod_map ⟨λ n, n + 1, add_left_injective 1⟩ (embedding.refl ℤ)

/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
@[derive inhabited]
def board := finset (ℤ × ℤ)
local attribute [reducible] board

/-- Left can play anywhere that a square and the square below it are open. -/
def left  (b : board) : finset (ℤ × ℤ) := b ∩ b.map shift_up
/-- Right can play anywhere that a square and the square to the left are open. -/
def right (b : board) : finset (ℤ × ℤ) := b ∩ b.map shift_right

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def move_left (b : board) (m : ℤ × ℤ) : board :=
(b.erase m).erase (m.1, m.2 - 1)
/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def move_right (b : board) (m : ℤ × ℤ) : board :=
(b.erase m).erase (m.1 - 1, m.2)

lemma card_of_mem_left {b : board} {m : ℤ × ℤ} (h : m ∈ left b) : 2 ≤ finset.card b :=
begin
  dsimp [left] at h,
  have w₁ : m ∈ b,
  { rw finset.mem_inter at h,
    exact h.1 },
  have w₂ : (m.1, m.2 - 1) ∈ b.erase m,
  { simp only [finset.mem_erase],
    fsplit,
    { exact λ w, pred_ne_self m.2 (congr_arg prod.snd w) },
    { rw finset.mem_inter at h,
      have h₂ := h.2, clear h,
      rw finset.mem_map at h₂,
      rcases h₂ with ⟨m', ⟨h₂, rfl⟩⟩,
      dsimp [shift_up],
      simpa, }, },
  have i₁ := finset.card_erase_lt_of_mem w₁,
  have i₂ := nat.lt_of_le_of_lt (nat.zero_le _) (finset.card_erase_lt_of_mem w₂),
  exact nat.lt_of_le_of_lt i₂ i₁,
end

lemma card_of_mem_right {b : board} {m : ℤ × ℤ} (h : m ∈ right b) : 2 ≤ finset.card b :=
begin
  dsimp [right] at h,
  have w₁ : m ∈ b,
  { rw finset.mem_inter at h,
    exact h.1 },
  have w₂ : (m.1 - 1, m.2) ∈ b.erase m,
  { simp only [finset.mem_erase],
    fsplit,
    { exact λ w, pred_ne_self m.1 (congr_arg prod.fst w) },
    { rw finset.mem_inter at h,
      have h₂ := h.2, clear h,
      rw finset.mem_map at h₂,
      rcases h₂ with ⟨m', ⟨h₂, rfl⟩⟩,
      dsimp [shift_right],
      simpa, }, },
  have i₁ := finset.card_erase_lt_of_mem w₁,
  have i₂ := nat.lt_of_le_of_lt (nat.zero_le _) (finset.card_erase_lt_of_mem w₂),
  exact nat.lt_of_le_of_lt i₂ i₁,
end

lemma move_left_card {b : board} {m : ℤ × ℤ} (h : m ∈ left b) :
  finset.card (move_left b m) + 2 = finset.card b :=
begin
  dsimp [move_left],
  rw finset.card_erase_of_mem,
  { rw finset.card_erase_of_mem,
    { exact nat.sub_add_cancel (card_of_mem_left h), },
    { exact finset.mem_of_mem_inter_left h, } },
  { apply finset.mem_erase_of_ne_of_mem,
    { exact λ w, pred_ne_self m.2 (congr_arg prod.snd w), },
    { have t := finset.mem_of_mem_inter_right h,
      dsimp [shift_up] at t,
      simp only [finset.mem_map, prod.exists] at t,
      rcases t with ⟨x,y,w,h⟩,
      rw ←h,
      convert w; simp } }
end
lemma move_right_card {b : board} {m : ℤ × ℤ} (h : m ∈ right b) :
  finset.card (move_right b m) + 2 = finset.card b :=
begin
  dsimp [move_right],
  rw finset.card_erase_of_mem,
  { rw finset.card_erase_of_mem,
    { exact nat.sub_add_cancel (card_of_mem_right h), },
    { exact finset.mem_of_mem_inter_left h, } },
  { apply finset.mem_erase_of_ne_of_mem,
    { exact λ w, pred_ne_self m.1 (congr_arg prod.fst w), },
    { have t := finset.mem_of_mem_inter_right h,
      dsimp [shift_right] at t,
      simp only [finset.mem_map, prod.exists] at t,
      rcases t with ⟨x,y,w,h⟩,
      rw ←h,
      convert w; simp } }
end

lemma move_left_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ left b) :
  finset.card (move_left b m) / 2 < finset.card b / 2 :=
by simp [←move_left_card h, lt_add_one]
lemma move_right_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ right b) :
  finset.card (move_right b m) / 2 < finset.card b / 2 :=
by simp [←move_right_card h, lt_add_one]

/-- The instance describing allowed moves on a Domineering board. -/
instance state : state board :=
{ turn_bound := λ s, s.card / 2,
  L := λ s, (left s).image (move_left s),
  R := λ s, (right s).image (move_right s),
  left_bound := λ s t m,
  begin
    simp only [finset.mem_image, prod.exists] at m,
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩,
    exact move_left_smaller h
  end,
  right_bound := λ s t m,
  begin
    simp only [finset.mem_image, prod.exists] at m,
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩,
    exact move_right_smaller h
  end, }

end domineering

/-- Construct a pre-game from a Domineering board. -/
def domineering (b : domineering.board) : pgame := pgame.of b

/-- All games of Domineering are short, because each move removes two squares. -/
instance short_domineering (b : domineering.board) : short (domineering b) :=
by { dsimp [domineering], apply_instance }

/-- The Domineering board with two squares arranged vertically, in which Left has the only move. -/
def domineering.one := domineering ([(0,0), (0,1)].to_finset)

/-- The `L` shaped Domineering board, in which Left is exactly half a move ahead. -/
def domineering.L := domineering ([(0,2), (0,1), (0,0), (1,0)].to_finset)

instance short_one : short domineering.one := by { dsimp [domineering.one], apply_instance }
instance short_L : short domineering.L := by { dsimp [domineering.L], apply_instance }

-- The VM can play small games successfully:
-- #eval to_bool (domineering.one ≈ 1)
-- #eval to_bool (domineering.L + domineering.L ≈ 1)

-- We can check that `decidable` instances reduce as expected,
-- and so our implementation of domineering is computable.
-- run_cmd tactic.whnf `(by apply_instance : decidable (domineering.one ≤ 1)) >>= tactic.trace

-- dec_trivial can handle most of the dictionary of small games described in [conway2001]
example : domineering.one ≈ 1 := dec_trivial
example : domineering.L + domineering.L ≈ 1 := dec_trivial
example : domineering.L ≈ pgame.of_lists [0] [1] := dec_trivial
example : (domineering ([(0,0), (0,1), (0,2), (0,3)].to_finset) ≈ 2) := dec_trivial
example : (domineering ([(0,0), (0,1), (1,0), (1,1)].to_finset) ≈ pgame.of_lists [1] [-1]) :=
  dec_trivial.

-- The 3x3 grid is doable, but takes a minute...
-- example :
--   (domineering ([(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)].to_finset) ≈
--     pgame.of_lists [1] [-1]) := dec_trivial

-- The 5x5 grid is actually 0, but brute-forcing this is too challenging even for the VM.
-- #eval to_bool (domineering ([
--   (0,0), (0,1), (0,2), (0,3), (0,4),
--   (1,0), (1,1), (1,2), (1,3), (1,4),
--   (2,0), (2,1), (2,2), (2,3), (2,4),
--   (3,0), (3,1), (3,2), (3,3), (3,4),
--   (4,0), (4,1), (4,2), (4,3), (4,4)
--   ].to_finset) ≈ 0)


end pgame
