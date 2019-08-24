/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import set_theory.game.short
import tactic.norm_num

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape (possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development; in order to successfully analyse positions we would
need some more theorems. Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact the disjoint parts of the chessboard give sums of games.
-/

open pgame

namespace domineering_aux

/-- The embedding `(x, y) ↦ (x, y+1)`. -/
def shift_up : ℤ × ℤ ↪ ℤ × ℤ :=
⟨λ p : ℤ × ℤ, (p.1, p.2 + 1),
 have function.injective (λ (n : ℤ), n + 1) := λ _ _, (add_right_inj 1).mp,
 function.injective_prod function.injective_id this⟩
/-- The embedding `(x, y) ↦ (x+1, y)`. -/
def shift_right : ℤ × ℤ ↪ ℤ × ℤ :=
⟨λ p : ℤ × ℤ, (p.1 + 1, p.2),
 have function.injective (λ (n : ℤ), n + 1) := λ _ _, (add_right_inj 1).mp,
 function.injective_prod this function.injective_id⟩

/-- Left can play anywhere that a square and the square above it are open. -/
def left  (b : finset (ℤ × ℤ)) : Type := { p | p ∈ b ∩ b.map shift_up }
/-- Right can play anywhere that a square and the square to the right are open. -/
def right (b : finset (ℤ × ℤ)) : Type := { p | p ∈ b ∩ b.map shift_right }

instance fintype_left (b : finset (ℤ × ℤ)) : fintype (left b) :=
fintype.subtype _ (λ x, iff.refl _)

instance fintype_right (b : finset (ℤ × ℤ)) : fintype (right b) :=
fintype.subtype _ (λ x, iff.refl _)

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def move_left (b : finset (ℤ × ℤ)) (m : left b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1, m.val.2 - 1)
/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def move_right (b : finset (ℤ × ℤ)) (m : right b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1 - 1, m.val.2)

lemma move_left_smaller (b : finset (ℤ × ℤ)) (m : left b) :
  finset.card (move_left b m) < finset.card b :=
lt_of_le_of_lt finset.card_erase_le $
  finset.card_erase_lt_of_mem (finset.mem_of_mem_inter_left m.property)
lemma move_right_smaller (b : finset (ℤ × ℤ)) (m : right b) :
  finset.card (move_right b m) < finset.card b :=
lt_of_le_of_lt finset.card_erase_le $
  finset.card_erase_lt_of_mem (finset.mem_of_mem_inter_left m.property)

end domineering_aux

section
open domineering_aux

instance : has_well_founded (finset (ℤ × ℤ)) := ⟨measure finset.card, measure_wf finset.card⟩

/-- We construct a domineering game from any finite subset of `ℤ × ℤ`. -/
def domineering : finset (ℤ × ℤ) → pgame
| b := pgame.mk
    (left b) (right b)
    (λ m, have _, from move_left_smaller b m,  domineering (move_left b m))
    (λ m, have _, from move_right_smaller b m, domineering (move_right b m))

@[simp] lemma domineering_left_moves (b : finset (ℤ × ℤ)) :
  (domineering b).left_moves = left b :=
by { rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩; refl }
@[simp] lemma domineering_right_moves (b : finset (ℤ × ℤ)) :
  (domineering b).right_moves = right b :=
by { rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩; refl }
@[simp] lemma domineering_move_left (b : finset (ℤ × ℤ)) (i : left_moves (domineering b)) :
  (domineering b).move_left i = domineering (move_left b (by { convert i, simp })) :=
begin
  rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩,
  { dsimp, rcases i with ⟨i, ⟨⟩⟩, },
  { refl }
end
@[simp] lemma domineering_move_right (b : finset (ℤ × ℤ)) (j : right_moves (domineering b)) :
  (domineering b).move_right j = domineering (move_right b (by { convert j, simp })) :=
begin
  rcases b with ⟨⟨b, _⟩|⟨h, t⟩, n⟩,
  { dsimp, rcases j with ⟨j, ⟨⟩⟩, },
  { refl }
end

instance fintype_left_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).left_moves) :=
begin
  unfold domineering {single_pass := tt},
  exact domineering_aux.fintype_left b,
end
instance fintype_right_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).right_moves) :=
begin
  unfold domineering {single_pass := tt},
  exact domineering_aux.fintype_right b,
end

/-- Domineering is always a short game, because the board is finite. -/
-- Implementation note:
-- This instance isn't usable inside `dec_trivial`, because the `unfold domineering` below
-- is not a definitional unfolding, and so the `decidable` instances don't reduce fully.
instance short_domineering : Π (b : finset (ℤ × ℤ)), short (domineering b)
| b :=
begin
  unfold domineering {single_pass := tt},
  exact short.mk
  (λ i, by exact have _, from move_left_smaller b i, short_domineering (move_left b i))
  (λ j, by exact have _, from move_right_smaller b j, short_domineering (move_right b j))
end


def domineering.one := domineering ([(0,0), (0,1)].to_finset)

/-- The `L` shaped board, in which Left is exactly half a move ahead. -/
def domineering.L := domineering ([(0,2), (0,1), (0,0), (1,0)].to_finset)

instance : short domineering.one := by { dsimp [domineering.one], apply_instance }
instance : short domineering.L := by { dsimp [domineering.L], apply_instance }

-- The VM can play small games successfully:
-- #eval to_bool (domineering.one ≈ 1)
-- #eval to_bool (domineering.L + domineering.L ≈ 1)

-- Unfortunately dec_trivial can't keep up:
-- example : domineering.one ≈ 1 := dec_trivial
-- example : domineering.L + domineering.L ≈ 1 := dec_trivial

-- It's not clear why the decidable instances do not reduce to `is_true _`:
-- set_option pp.implicit true
-- set_option pp.proofs true
-- set_option pp.max_steps 1000000
-- set_option pp.max_depth 1000000
-- run_cmd tactic.whnf `(by apply_instance : decidable (domineering.one ≤ 1)) >>= tactic.trace


-- instance : short (pgame.of_lists [0] [1]) :=
-- @pgame.short_of_lists [0] [1]
-- begin
--  intros l h, simp at h, subst h, apply_instance
-- end
-- begin
--  intros l h, simp at h, subst h, apply_instance
-- end

-- #eval to_bool (domineering.L ≈ pgame.of_lists [0] [1])
-- example : domineering.L ≈ pgame.of_lists [0] [1] := dec_trivial

-- TODO: It would be nice to analyse the first interesting game in Domineering, the "L", in which
-- Left is exactly half a move ahead. The following comments sketch the beginning of this argument.

end
