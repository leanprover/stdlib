/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.pgame

/-!
# Basic definitions about who has a winning stratergy

We define `G.first_loses`, `G.first_wins`, `G.left_wins` and `G.right_wins` for a pgame `G`, which
means the second, first, left and right players have a winning strategy respectively.
These are defined by inequalities which can be unfolded with `pgame.lt_def` and `pgame.le_def`.
-/

namespace pgame

local infix ` ≈ ` := equiv

/-- The player who goes first loses -/
def first_loses (G : pgame) : Prop := G ≤ 0 ∧ 0 ≤ G

/-- The player who goes first wins -/
def first_wins (G : pgame) : Prop := 0 < G ∧ G < 0

/-- The left player can always win -/
def left_wins (G : pgame) : Prop := 0 < G ∧ 0 ≤ G

/-- The right player can always win -/
def right_wins (G : pgame) : Prop := G ≤ 0 ∧ G < 0

theorem zero_first_loses : first_loses 0 := by tidy
theorem one_left_wins : left_wins 1 :=
⟨by { rw lt_def_le, tidy }, by rw le_def; tidy⟩

theorem star_first_wins : first_wins star := ⟨zero_lt_star, star_lt_zero⟩
theorem omega_left_wins : left_wins omega :=
⟨by { rw lt_def_le, exact or.inl ⟨ulift.up 0, by tidy⟩ }, by rw le_def; tidy⟩

lemma winner_cases (G : pgame) : G.left_wins ∨ G.right_wins ∨ G.first_loses ∨ G.first_wins :=
begin
  classical,
  by_cases hpos : 0 < G;
  by_cases hneg : G < 0;
  { try { rw not_lt at hpos },
    try { rw not_lt at hneg },
    try { left, exact ⟨hpos, hneg⟩ },
    try { right, left, exact ⟨hpos, hneg⟩ },
    try { right, right, left, exact ⟨hpos, hneg⟩ },
    try { right, right, right, exact ⟨hpos, hneg⟩ } }
end

lemma first_loses_is_zero {G : pgame} : G.first_loses ↔ G ≈ 0 := by refl

lemma first_loses_of_equiv {G H : pgame} (h : G ≈ H) : G.first_loses → H.first_loses :=
λ hGp, ⟨le_of_equiv_of_le h.symm hGp.1, le_of_le_of_equiv hGp.2 h⟩
lemma first_wins_of_equiv {G H : pgame} (h : G ≈ H) : G.first_wins → H.first_wins :=
λ hGn, ⟨lt_of_lt_of_equiv hGn.1 h, lt_of_equiv_of_lt h.symm hGn.2⟩
lemma left_wins_of_equiv {G H : pgame} (h : G ≈ H) : G.left_wins → H.left_wins :=
λ hGl, ⟨lt_of_lt_of_equiv hGl.1 h, le_of_le_of_equiv hGl.2 h⟩
lemma right_wins_of_equiv {G H : pgame} (h : G ≈ H) : G.right_wins → H.right_wins :=
λ hGr, ⟨le_of_equiv_of_le h.symm hGr.1, lt_of_equiv_of_lt h.symm hGr.2⟩

lemma first_loses_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.first_loses ↔ H.first_loses :=
⟨first_loses_of_equiv h, first_loses_of_equiv h.symm⟩
lemma first_wins_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.first_wins ↔ H.first_wins :=
⟨first_wins_of_equiv h, first_wins_of_equiv h.symm⟩
lemma left_wins_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.left_wins ↔ H.left_wins :=
⟨left_wins_of_equiv h, left_wins_of_equiv h.symm⟩
lemma right_wins_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.right_wins ↔ H.right_wins :=
⟨right_wins_of_equiv h, right_wins_of_equiv h.symm⟩

lemma not_first_wins_of_first_loses {G : pgame} : G.first_loses → ¬G.first_wins :=
begin
  rw first_loses_is_zero,
  rintros h ⟨h₀, -⟩,
  exact pgame.lt_irrefl 0 (lt_of_lt_of_equiv h₀ h)
end

lemma not_first_loses_of_first_wins {G : pgame} : G.first_wins → ¬G.first_loses :=
imp_not_comm.1 $ not_first_wins_of_first_loses

end pgame
