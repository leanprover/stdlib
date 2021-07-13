/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.game.winner
import tactic.nth_rewrite.default
import tactic.equiv_rw

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/

universe u

namespace pgame

local infix ` ≈ ` := equiv

/-- The definition for a impartial game, defined using Conway induction -/
def impartial_aux : pgame → Prop
| G := G ≈ -G ∧ (∀ i, impartial_aux (G.move_left i)) ∧ (∀ j, impartial_aux (G.move_right j))
using_well_founded { dec_tac := pgame_wf_tac }

lemma impartial_aux_def {G : pgame} : G.impartial_aux ↔ G ≈ -G ∧
  (∀ i, impartial_aux (G.move_left i)) ∧ (∀ j, impartial_aux (G.move_right j)) :=
begin
  split,
  { intro hi,
    unfold1 impartial_aux at hi,
    exact hi },
  { intro hi,
    unfold1 impartial_aux,
    exact hi }
end

/-- A typeclass on impartial games. -/
class impartial (G : pgame) : Prop := (out : impartial_aux G)

lemma impartial_iff_aux {G : pgame} : G.impartial ↔ G.impartial_aux :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma impartial_def {G : pgame} : G.impartial ↔ G ≈ -G ∧
  (∀ i, impartial (G.move_left i)) ∧ (∀ j, impartial (G.move_right j)) :=
by simpa only [impartial_iff_aux] using impartial_aux_def

namespace impartial

instance impartial_zero : impartial 0 :=
by { rw impartial_def, dsimp, simp }

lemma neg_equiv_self (G : pgame) [h : G.impartial] : G ≈ -G := (impartial_def.1 h).1

instance move_left_impartial {G : pgame} [h : G.impartial] (i : G.left_moves) :
  (G.move_left i).impartial :=
(impartial_def.1 h).2.1 i

instance move_right_impartial {G : pgame} [h : G.impartial] (j : G.right_moves) :
  (G.move_right j).impartial :=
(impartial_def.1 h).2.2 j

instance impartial_add : ∀ (G H : pgame) [G.impartial] [H.impartial], (G + H).impartial
| G H :=
begin
  introsI hG hH,
  rw impartial_def,
  split,
  { apply equiv_trans _ (neg_add_relabelling G H).equiv.symm,
    exact add_congr (neg_equiv_self _) (neg_equiv_self _) },
  split,
  all_goals
  { intro i,
    equiv_rw pgame.left_moves_add G H at i <|> equiv_rw pgame.right_moves_add G H at i,
    cases i },
  all_goals
  { simp only [add_move_left_inl, add_move_right_inl, add_move_left_inr, add_move_right_inr],
    exact impartial_add _ _ }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance impartial_neg : ∀ (G : pgame) [G.impartial], (-G).impartial
| G :=
begin
  introI hG,
  rw impartial_def,
  split,
  { rw neg_neg,
    symmetry,
    exact neg_equiv_self G },
  split,
  all_goals
  { intro i,
    equiv_rw G.left_moves_neg at i <|> equiv_rw G.right_moves_neg at i,
    simp only [move_left_left_moves_neg_symm, move_right_right_moves_neg_symm],
    exact impartial_neg _ }
end
using_well_founded { dec_tac := pgame_wf_tac }

lemma winner_cases (G : pgame) [G.impartial] : G.first_loses ∨ G.first_wins :=
begin
  rcases G.winner_cases with hl | hr | hp | hn,
  { cases hl with hpos hnonneg,
    rw ←not_lt at hnonneg,
    have hneg := lt_of_lt_of_equiv hpos (neg_equiv_self G),
    rw [lt_iff_neg_gt, neg_neg, neg_zero] at hneg,
    contradiction },
  { cases hr with hnonpos hneg,
    rw ←not_lt at hnonpos,
    have hpos := lt_of_equiv_of_lt (neg_equiv_self G).symm hneg,
    rw [lt_iff_neg_gt, neg_neg, neg_zero] at hpos,
    contradiction },
  { left, assumption },
  { right, assumption }
end

lemma not_first_wins (G : pgame) [G.impartial] : ¬G.first_wins ↔ G.first_loses :=
by cases winner_cases G; finish using [not_first_loses_of_first_wins]

lemma not_first_loses (G : pgame) [G.impartial] : ¬G.first_loses ↔ G.first_wins :=
iff.symm $ iff_not_comm.1 $ iff.symm $ not_first_wins G

lemma add_self (G : pgame) [G.impartial] : (G + G).first_loses :=
  first_loses_is_zero.2 $ equiv_trans (add_congr (neg_equiv_self G) G.equiv_refl)
  add_left_neg_equiv

lemma equiv_iff_sum_first_loses (G H : pgame) [G.impartial] [H.impartial] :
  G ≈ H ↔ (G + H).first_loses :=
begin
  split,
  { intro heq,
    exact first_loses_of_equiv (add_congr (equiv_refl _) heq) (add_self G) },
  { intro hGHp,
    split,
    { rw le_iff_sub_nonneg,
      exact le_trans hGHp.2
        (le_trans add_comm_le $ le_of_le_of_equiv (pgame.le_refl _) $ add_congr (equiv_refl _)
        (neg_equiv_self G)) },
    { rw le_iff_sub_nonneg,
      exact le_trans hGHp.2
        (le_of_le_of_equiv (pgame.le_refl _) $ add_congr (equiv_refl _) (neg_equiv_self H)) } }
end

lemma le_zero_iff {G : pgame} [G.impartial] : G ≤ 0 ↔ 0 ≤ G :=
by rw [le_zero_iff_zero_le_neg, le_congr (equiv_refl 0) (neg_equiv_self G)]

lemma lt_zero_iff {G : pgame} [G.impartial] : G < 0 ↔ 0 < G :=
by rw [lt_iff_neg_gt, neg_zero, lt_congr (equiv_refl 0) (neg_equiv_self G)]

lemma first_loses_symm (G : pgame) [G.impartial] : G.first_loses ↔ G ≤ 0 :=
⟨and.left, λ h, ⟨h, le_zero_iff.1 h⟩⟩

lemma first_wins_symm (G : pgame) [G.impartial] : G.first_wins ↔ G < 0 :=
⟨and.right, λ h, ⟨lt_zero_iff.1 h, h⟩⟩

lemma first_loses_symm' (G : pgame) [G.impartial] : G.first_loses ↔ 0 ≤ G :=
⟨and.right, λ h, ⟨le_zero_iff.2 h, h⟩⟩

lemma first_wins_symm' (G : pgame) [G.impartial] : G.first_wins ↔ 0 < G :=
⟨and.left, λ h, ⟨h, lt_zero_iff.2 h⟩⟩

lemma no_good_left_moves_iff_first_loses (G : pgame) [G.impartial] :
  (∀ (i : G.left_moves), (G.move_left i).first_wins) ↔ G.first_loses :=
begin
  split,
  { intro hbad,
    rw [first_loses_symm G, le_def_lt],
    split,
    { intro i,
      specialize hbad i,
      exact hbad.2 },
    { intro j,
      exact pempty.elim j } },
  { intros hp i,
    rw first_wins_symm,
    exact (le_def_lt.1 $ (first_loses_symm G).1 hp).1 i }
end

lemma no_good_right_moves_iff_first_loses (G : pgame) [G.impartial] :
  (∀ (j : G.right_moves), (G.move_right j).first_wins) ↔ G.first_loses :=
begin
  rw [first_loses_of_equiv_iff (neg_equiv_self G), ←no_good_left_moves_iff_first_loses],
  refine ⟨λ h i, _, λ h i, _⟩,
  { simpa [first_wins_of_equiv_iff (neg_equiv_self ((-G).move_left i))]
    using h (left_moves_neg _ i) },
  { simpa [first_wins_of_equiv_iff (neg_equiv_self (G.move_right i))]
      using h ((left_moves_neg _).symm i) }
end

lemma good_left_move_iff_first_wins (G : pgame) [G.impartial] :
  (∃ (i : G.left_moves), (G.move_left i).first_loses) ↔ G.first_wins :=
begin
  refine ⟨λ ⟨i, hi⟩, (first_wins_symm' G).2 (lt_def_le.2 $ or.inl ⟨i, hi.2⟩), λ hn, _⟩,
  rw [first_wins_symm' G, lt_def_le] at hn,
  rcases hn with ⟨i, hi⟩ | ⟨j, _⟩,
  { exact ⟨i, (first_loses_symm' _).2 hi⟩ },
  { exact pempty.elim j }
end

lemma good_right_move_iff_first_wins (G : pgame) [G.impartial] :
  (∃ j : G.right_moves, (G.move_right j).first_loses) ↔ G.first_wins :=
begin
  refine ⟨λ ⟨j, hj⟩, (first_wins_symm G).2 (lt_def_le.2 $ or.inr ⟨j, hj.1⟩), λ hn, _⟩,
  rw [first_wins_symm G, lt_def_le] at hn,
  rcases hn with ⟨i, _⟩ | ⟨j, hj⟩,
  { exact pempty.elim i },
  { exact ⟨j, (first_loses_symm _).2 hj⟩ }
end

end impartial
end pgame
