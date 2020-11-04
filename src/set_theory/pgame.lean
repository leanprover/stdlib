/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import logic.embedding
import data.nat.cast
import data.fin

/-!
# Combinatorial (pre-)games.

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`. We
construct "pregames", define an ordering and arithmetic operations on them, then show that the
operations descend to "games", defined via the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a quotient of a subtype of pregames.

A pregame (`pgame` below) is axiomatised via an inductive type, whose sole constructor takes two
types (thought of as indexing the the possible moves for the players Left and Right), and a pair of
functions out of these types to `pgame` (thought of as describing the resulting game after making a
move).

Combinatorial games themselves, as a quotient of pregames, are constructed in `game.lean`.

## Conway induction

By construction, the induction principle for pregames is exactly "Conway induction". That is, to
prove some predicate `pgame → Prop` holds for all pregames, it suffices to prove that for every
pregame `g`, if the predicate holds for every game resulting from making a move, then it also holds
for `g`.

While it is often convenient to work "by induction" on pregames, in some situations this becomes
awkward, so we also define accessor functions `left_moves`, `right_moves`, `move_left` and
`move_right`. There is a relation `subsequent p q`, saying that `p` can be reached by playing some
non-empty sequence of moves starting from `q`, an instance `well_founded subsequent`, and a local
tactic `pgame_wf_tac` which is helpful for discharging proof obligations in inductive proofs relying
on this relation.

## Order properties

Pregames have both a `≤` and a `<` relation, which are related in quite a subtle way. In particular,
it is worth noting that in Lean's (perhaps unfortunate?) definition of a `preorder`, we have
`lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`, but this is _not_ satisfied by the usual
`≤` and `<` relations on pregames. (It is satisfied once we restrict to the surreal numbers.) In
particular, `<` is not transitive; there is an example below showing `0 < star ∧ star < 0`.

We do have
```
theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := ...
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := ...
```

The statement `0 ≤ x` means that Left has a good response to any move by Right; in particular, the
theorem `zero_le` below states
```
0 ≤ x ↔ ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i
```
On the other hand the statement `0 < x` means that Left has a good move right now; in particular the
theorem `zero_lt` below states
```
0 < x ↔ ∃ i : left_moves x, ∀ j : right_moves (x.move_left i), 0 < (x.move_left i).move_right j
```

The theorems `le_def`, `lt_def`, give a recursive characterisation of each relation, in terms of
themselves two moves later. The theorems `le_def_lt` and `lt_def_lt` give recursive
characterisations of each relation in terms of the other relation one move later.

We define an equivalence relation `equiv p q ↔ p ≤ q ∧ q ≤ p`. Later, games will be defined as the
quotient by this relation.

## Algebraic structures

We next turn to defining the operations necessary to make games into a commutative additive group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by $x + y = \{xL + y, x + yL | xR +
y, x + yR\}$. Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$.

The order structures interact in the expected way with addition, so we have
```
theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry
theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x := sorry
```

We show that these operations respect the equivalence relation, and hence descend to games. At the
level of games, these operations satisfy all the laws of a commutative group. To prove the necessary
equivalence relations at the level of pregames, we introduce the notion of a `relabelling` of a
game, and show, for example, that there is a relabelling between `x + (y + z)` and `(x + y) + z`.

## Future work
* The theory of dominated and reversible positions, and unique normal form for short games.
* Analysis of basic domineering positions.
* Hex.
* Temperature.
* The development of surreal numbers, based on this development of combinatorial games, is still
  quite incomplete.

## References

The material here is all drawn from
* [Conway, *On numbers and games*][conway2001]

An interested reader may like to formalise some of the material from
* [Andreas Blass, *A game semantics for linear logic*][MR1167694]
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1997]
-/

universes u

/-- The type of pre-games, before we have quotiented
  by extensionality. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive pgame : Type (u+1)
| mk : ∀ α β : Type u, (α → pgame) → (β → pgame) → pgame

namespace pgame

/--
Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
-- TODO provide some API describing the interaction with
-- `left_moves`, `right_moves`, `move_left` and `move_right` below.
-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
def of_lists (L R : list pgame.{0}) : pgame.{0} :=
pgame.mk (fin L.length) (fin R.length) (λ i, L.nth_le i i.is_lt) (λ j, R.nth_le j.val j.is_lt)

/-- The indexing type for allowable moves by Left. -/
def left_moves : pgame → Type u
| (mk l _ _ _) := l
/-- The indexing type for allowable moves by Right. -/
def right_moves : pgame → Type u
| (mk _ r _ _) := r

/-- The new game after Left makes an allowed move. -/
def move_left : Π (g : pgame), left_moves g → pgame
| (mk l _ L _) i := L i
/-- The new game after Right makes an allowed move. -/
def move_right : Π (g : pgame), right_moves g → pgame
| (mk _ r _ R) j := R j

@[simp] lemma left_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).left_moves = xl := rfl
@[simp] lemma move_left_mk {xl xr xL xR i} : (⟨xl, xr, xL, xR⟩ : pgame).move_left i = xL i := rfl
@[simp] lemma right_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).right_moves = xr := rfl
@[simp] lemma move_right_mk {xl xr xL xR j} : (⟨xl, xr, xL, xR⟩ : pgame).move_right j = xR j := rfl

/-- `subsequent p q` says that `p` can be obtained by playing
  some nonempty sequence of moves from `q`. -/
inductive subsequent : pgame → pgame → Prop
| left : Π (x : pgame) (i : x.left_moves), subsequent (x.move_left i) x
| right : Π (x : pgame) (j : x.right_moves), subsequent (x.move_right j) x
| trans : Π (x y z : pgame), subsequent x y → subsequent y z → subsequent x z

theorem wf_subsequent : well_founded subsequent :=
⟨λ x, begin
  induction x with l r L R IHl IHr,
  refine ⟨_, λ y h, _⟩,
  generalize_hyp e : mk l r L R = x at h,
  induction h with _ i _ j a b _ h1 h2 IH1 IH2; subst e,
  { apply IHl },
  { apply IHr },
  { exact acc.inv (IH2 rfl) h1 }
end⟩

instance : has_well_founded pgame :=
{ r := subsequent,
  wf := wf_subsequent }

/-- A move by Left produces a subsequent game. (For use in pgame_wf_tac.) -/
lemma subsequent.left_move {xl xr} {xL : xl → pgame} {xR : xr → pgame} {i : xl} :
  subsequent (xL i) (mk xl xr xL xR) :=
subsequent.left (mk xl xr xL xR) i
/-- A move by Right produces a subsequent game. (For use in pgame_wf_tac.) -/
lemma subsequent.right_move {xl xr} {xL : xl → pgame} {xR : xr → pgame} {j : xr} :
  subsequent (xR j) (mk xl xr xL xR) :=
subsequent.right (mk xl xr xL xR) j

/-- A local tactic for proving well-foundedness of recursive definitions involving pregames. -/
meta def pgame_wf_tac :=
`[solve_by_elim
  [psigma.lex.left, psigma.lex.right,
   subsequent.left_move, subsequent.right_move,
   subsequent.left, subsequent.right, subsequent.trans]
  { max_depth := 6 }]

/-- The pre-game `zero` is defined by `0 = { | }`. -/
instance : has_zero pgame := ⟨⟨pempty, pempty, pempty.elim, pempty.elim⟩⟩

@[simp] lemma zero_left_moves : (0 : pgame).left_moves = pempty := rfl
@[simp] lemma zero_right_moves : (0 : pgame).right_moves = pempty := rfl

instance : inhabited pgame := ⟨0⟩

/-- The pre-game `one` is defined by `1 = { 0 | }`. -/
instance : has_one pgame := ⟨⟨punit, pempty, λ _, 0, pempty.elim⟩⟩

@[simp] lemma one_left_moves : (1 : pgame).left_moves = punit := rfl
@[simp] lemma one_move_left : (1 : pgame).move_left punit.star = 0 := rfl
@[simp] lemma one_right_moves : (1 : pgame).right_moves = pempty := rfl

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on pre-games. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  The solution is to define `x < y` and `x <= y` simultaneously. -/
def le_lt : Π (x y : pgame), Prop × Prop
| (mk xl xr xL xR) (mk yl yr yL yR) :=
  -- the orderings of the clauses here are carefully chosen so that
  --   and.left/or.inl refer to moves by Left, and
  --   and.right/or.inr refer to moves by Right.
((∀ i : xl, (le_lt (xL i) ⟨yl, yr, yL, yR⟩).2) ∧ (∀ j : yr, (le_lt ⟨xl, xr, xL, xR⟩ (yR j)).2),
  (∃ i : yl, (le_lt ⟨xl, xr, xL, xR⟩ (yL i)).1) ∨ (∃ j : xr, (le_lt (xR j) ⟨yl, yr, yL, yR⟩).1))
using_well_founded { dec_tac := pgame_wf_tac }

instance : has_le pgame := ⟨λ x y, (le_lt x y).1⟩
instance : has_lt pgame := ⟨λ x y, (le_lt x y).2⟩

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ ⟨yl, yr, yL, yR⟩ ↔
  (∀ i, xL i < ⟨yl, yr, yL, yR⟩) ∧
  (∀ j, (⟨xl, xr, xL, xR⟩ : pgame) < yR j) := iff.rfl

/-- Definition of `x ≤ y` on pre-games, in terms of `<` -/
theorem le_def_lt {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves, x.move_left i < y) ∧
  (∀ j : y.right_moves, x < y.move_right j) :=
by { cases x, cases y, refl }

/-- Definition of `x < y` on pre-games built using the constructor. -/
@[simp] theorem mk_lt_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) < ⟨yl, yr, yL, yR⟩ ↔
  (∃ i, (⟨xl, xr, xL, xR⟩ : pgame) ≤ yL i) ∨
  (∃ j, xR j ≤ ⟨yl, yr, yL, yR⟩) := iff.rfl

/-- Definition of `x < y` on pre-games, in terms of `≤` -/
theorem lt_def_le {x y : pgame} : x < y ↔
  (∃ i : y.left_moves, x ≤ y.move_left i) ∨
  (∃ j : x.right_moves, x.move_right j ≤ y) :=
by { cases x, cases y, refl }

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves,
   (∃ i' : y.left_moves, x.move_left i ≤ y.move_left i') ∨
   (∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ y)) ∧
  (∀ j : y.right_moves,
   (∃ i : (y.move_right j).left_moves, x ≤ (y.move_right j).move_left i) ∨
   (∃ j' : x.right_moves, x.move_right j' ≤ y.move_right j)) :=
begin
  rw [le_def_lt],
  conv { to_lhs, simp only [lt_def_le] },
end

/-- The definition of `x < y` on pre-games, in terms of `<` two moves later. -/
theorem lt_def {x y : pgame} : x < y ↔
  (∃ i : y.left_moves,
    (∀ i' : x.left_moves, x.move_left i' < y.move_left i) ∧
    (∀ j : (y.move_left i).right_moves, x < (y.move_left i).move_right j)) ∨
  (∃ j : x.right_moves,
    (∀ i : (x.move_right j).left_moves, (x.move_right j).move_left i < y) ∧
    (∀ j' : y.right_moves, x.move_right j < y.move_right j')) :=
begin
  rw [lt_def_le],
  conv { to_lhs, simp only [le_def_lt] },
end

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : pgame} : x ≤ 0 ↔
  ∀ i : x.left_moves, ∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ 0 :=
begin
  rw le_def,
  dsimp,
  simp [forall_pempty, exists_pempty]
end

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : pgame} : 0 ≤ x ↔
  ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i :=
begin
  rw le_def,
  dsimp,
  simp [forall_pempty, exists_pempty]
end

/-- The definition of `x < 0` on pre-games, in terms of `< 0` two moves later. -/
theorem lt_zero {x : pgame} : x < 0 ↔
  ∃ j : x.right_moves, ∀ i : (x.move_right j).left_moves, (x.move_right j).move_left i < 0 :=
begin
  rw lt_def,
  dsimp,
  simp [forall_pempty, exists_pempty]
end

/-- The definition of `0 < x` on pre-games, in terms of `< x` two moves later. -/
theorem zero_lt {x : pgame} : 0 < x ↔
  ∃ i : x.left_moves, ∀ j : (x.move_left i).right_moves, 0 < (x.move_left i).move_right j :=
begin
  rw lt_def,
  dsimp,
  simp [forall_pempty, exists_pempty]
end

/-- Given a right-player-wins game, provide a response to any move by left. -/
noncomputable def right_response {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).right_moves :=
classical.some $ (le_zero.1 h) i

/-- Show that the response for right provided by `right_response`
    preserves the right-player-wins condition. -/
lemma right_response_spec {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).move_right (right_response h i) ≤ 0 :=
classical.some_spec $ (le_zero.1 h) i

/-- Given a left-player-wins game, provide a response to any move by right. -/
noncomputable def left_response {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  (x.move_right j).left_moves :=
classical.some $ (zero_le.1 h) j

/-- Show that the response for left provided by `left_response`
    preserves the left-player-wins condition. -/
lemma left_response_spec {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  0 ≤ (x.move_right j).move_left (left_response h j) :=
classical.some_spec $ (zero_le.1 h) j

theorem lt_of_le_mk {xl xr xL xR y i} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ y → xL i < y :=
by cases y; exact λ h, h.1 i

theorem lt_of_mk_le {x : pgame} {yl yr yL yR i} :
  x ≤ ⟨yl, yr, yL, yR⟩ → x < yR i :=
by cases x; exact λ h, h.2 i

theorem mk_lt_of_le {xl xr xL xR y i} :
  (by exact xR i ≤ y) → (⟨xl, xr, xL, xR⟩ : pgame) < y :=
by cases y; exact λ h, or.inr ⟨i, h⟩

theorem lt_mk_of_le {x : pgame} {yl yr yL yR i} :
  (by exact x ≤ yL i) → x < ⟨yl, yr, yL, yR⟩ :=
by cases x; exact λ h, or.inl ⟨i, h⟩

theorem not_le_lt {x y : pgame} :
  (¬ x ≤ y ↔ y < x) ∧ (¬ x < y ↔ y ≤ x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  classical,
  simp only [mk_le_mk, mk_lt_mk,
    not_and_distrib, not_or_distrib, not_forall, not_exists,
    and_comm, or_comm, IHxl, IHxr, IHyl, IHyr, iff_self, and_self]
end

theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := not_le_lt.1
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := not_le_lt.2

@[refl] theorem le_refl : ∀ x : pgame, x ≤ x
| ⟨l, r, L, R⟩ :=
⟨λ i, lt_mk_of_le (le_refl _), λ i, mk_lt_of_le (le_refl _)⟩

theorem lt_irrefl (x : pgame) : ¬ x < x :=
not_lt.2 (le_refl _)

theorem ne_of_lt : ∀ {x y : pgame}, x < y → x ≠ y
| x _ h rfl := lt_irrefl x h

theorem le_trans_aux
  {xl xr} {xL : xl → pgame} {xR : xr → pgame}
  {yl yr} {yL : yl → pgame} {yR : yr → pgame}
  {zl zr} {zL : zl → pgame} {zR : zr → pgame}
  (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
  (h₂ : ∀ i, zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) :
  mk xl xr xL xR ≤ mk yl yr yL yR →
  mk yl yr yL yR ≤ mk zl zr zL zR →
  mk xl xr xL xR ≤ mk zl zr zL zR :=
λ ⟨xLy, xyR⟩ ⟨yLz, yzR⟩, ⟨
  λ i, not_le.1 (λ h, not_lt.2 (h₁ _ ⟨yLz, yzR⟩ h) (xLy _)),
  λ i, not_le.1 (λ h, not_lt.2 (h₂ _ h ⟨xLy, xyR⟩) (yzR _))⟩

@[trans] theorem le_trans {x y z : pgame} : x ≤ y → y ≤ z → x ≤ z :=
suffices ∀ {x y z : pgame},
  (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y),
from this.1, begin
  clear x y z, intros,
  induction x with xl xr xL xR IHxl IHxr generalizing y z,
  induction y with yl yr yL yR IHyl IHyr generalizing z,
  induction z with zl zr zL zR IHzl IHzr,
  exact ⟨
    le_trans_aux (λ i, (IHxl _).2.1) (λ i, (IHzr _).2.2),
    le_trans_aux (λ i, (IHyl _).2.2) (λ i, (IHxr _).1),
    le_trans_aux (λ i, (IHzl _).1) (λ i, (IHyr _).2.1)⟩,
end

@[trans] theorem lt_of_le_of_lt {x y z : pgame} (hxy : x ≤ y) (hyz : y < z) : x < z :=
begin
  rw ←not_le at ⊢ hyz,
  exact mt (λ H, le_trans H hxy) hyz
end

@[trans] theorem lt_of_lt_of_le {x y z : pgame} (hxy : x < y) (hyz : y ≤ z) : x < z :=
begin
  rw ←not_le at ⊢ hxy,
  exact mt (λ H, le_trans hyz H) hxy
end

/-- Define the equivalence relation on pre-games. Two pre-games
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def equiv (x y : pgame) : Prop := x ≤ y ∧ y ≤ x

local infix ` ≈ ` := pgame.equiv

@[refl] theorem equiv_refl (x) : x ≈ x := ⟨le_refl _, le_refl _⟩
@[symm] theorem equiv_symm {x y} : x ≈ y → y ≈ x | ⟨xy, yx⟩ := ⟨yx, xy⟩
@[trans] theorem equiv_trans {x y z} : x ≈ y → y ≈ z → x ≈ z
| ⟨xy, yx⟩ ⟨yz, zy⟩ := ⟨le_trans xy yz, le_trans zy yx⟩

theorem lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z := lt_of_lt_of_le h₁ h₂.1
theorem le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z := le_trans h₁ h₂.1
theorem lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) (h₂ : y < z) : x < z := lt_of_le_of_lt h₁.1 h₂
theorem le_of_equiv_of_le {x y z} (h₁ : x ≈ y) (h₂ : y ≤ z) : x ≤ z := le_trans h₁.1 h₂

theorem le_congr {x₁ y₁ x₂ y₂} : x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ≤ y₁ ↔ x₂ ≤ y₂)
| ⟨x12, x21⟩ ⟨y12, y21⟩ := ⟨λ h, le_trans x21 (le_trans h y12), λ h, le_trans x12 (le_trans h y21)⟩

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
not_le.symm.trans $ (not_congr (le_congr hy hx)).trans not_le

theorem equiv_congr_left {y₁ y₂} : y₁ ≈ y₂ ↔ ∀ x₁, x₁ ≈ y₁ ↔ x₁ ≈ y₂ :=
⟨λ h x₁, ⟨λ h', equiv_trans h' h, λ h', equiv_trans h' (equiv_symm h)⟩,
 λ h, (h y₁).1 $ equiv_refl _⟩

theorem equiv_congr_right {x₁ x₂} : x₁ ≈ x₂ ↔ ∀ y₁, x₁ ≈ y₁ ↔ x₂ ≈ y₁ :=
⟨λ h y₁, ⟨λ h', equiv_trans (equiv_symm h) h', λ h', equiv_trans h h'⟩,
 λ h, (h x₂).2 $ equiv_refl _⟩

/-- `restricted x y` says that Left always has no more moves in `x` than in `y`,
     and Right always has no more moves in `y` than in `x` -/
inductive restricted : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π {x y : pgame} (L : x.left_moves → y.left_moves) (R : y.right_moves → x.right_moves),
         (∀ (i : x.left_moves), restricted (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), restricted (x.move_right (R j)) (y.move_right j)) → restricted x y

/-- The identity restriction. -/
@[refl] def restricted.refl : Π (x : pgame), restricted x x
| (mk xl xr xL xR) :=
  restricted.mk
    id id
    (λ i, restricted.refl _) (λ j, restricted.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

-- TODO trans for restricted

theorem le_of_restricted : Π {x y : pgame} (r : restricted x y), x ≤ y
| (mk xl xr xL xR) (mk yl yr yL yR)
  (restricted.mk L_embedding R_embedding L_restriction R_restriction) :=
begin
  rw le_def,
  exact
    ⟨λ i, or.inl ⟨L_embedding i, le_of_restricted (L_restriction i)⟩,
     λ i, or.inr ⟨R_embedding i, le_of_restricted (R_restriction i)⟩⟩
end

/--
`relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `relabelling`s for the consequent games.
-/
inductive relabelling : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π {x y : pgame} (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ (i : x.left_moves), relabelling (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), relabelling (x.move_right (R.symm j)) (y.move_right j)) →
       relabelling x y

/-- If `x` is a relabelling of `y`, then Left and Right have the same moves in either game,
    so `x` is a restriction of `y`. -/
def restricted_of_relabelling : Π {x y : pgame} (r : relabelling x y), restricted x y
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk L_equiv R_equiv L_relabelling R_relabelling) :=
restricted.mk L_equiv.to_embedding R_equiv.symm.to_embedding
  (λ i, restricted_of_relabelling (L_relabelling i))
  (λ j, restricted_of_relabelling (R_relabelling j))

-- It's not the case that `restricted x y → restricted y x → relabelling x y`,
-- but if we insisted that the maps in a restriction were injective, then one
-- could use Schröder-Bernstein for do this.

/-- The identity relabelling. -/
@[refl] def relabelling.refl : Π (x : pgame), relabelling x x
| (mk xl xr xL xR) :=
  relabelling.mk (equiv.refl _) (equiv.refl _)
    (λ i, relabelling.refl _) (λ j, relabelling.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

/-- Reverse a relabelling. -/
@[symm] def relabelling.symm : Π {x y : pgame}, relabelling x y → relabelling y x
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk L_equiv R_equiv L_relabelling R_relabelling) :=
begin
  refine relabelling.mk L_equiv.symm R_equiv.symm _ _,
  { intro i, simpa using (L_relabelling (L_equiv.symm i)).symm },
  { intro j, simpa using (R_relabelling (R_equiv j)).symm }
end

/-- Transitivity of relabelling -/
@[trans] def relabelling.trans :
  Π {x y z : pgame}, relabelling x y → relabelling y z → relabelling x z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR)
  (relabelling.mk L_equiv₁ R_equiv₁ L_relabelling₁ R_relabelling₁)
  (relabelling.mk L_equiv₂ R_equiv₂ L_relabelling₂ R_relabelling₂) :=
begin
  refine relabelling.mk (L_equiv₁.trans L_equiv₂) (R_equiv₁.trans R_equiv₂) _ _,
  { intro i, simpa using (L_relabelling₁ _).trans (L_relabelling₂ _) },
  { intro j, simpa using (R_relabelling₁ _).trans (R_relabelling₂ _) },
end

theorem le_of_relabelling {x y : pgame} (r : relabelling x y) : x ≤ y :=
le_of_restricted (restricted_of_relabelling r)

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv_of_relabelling {x y : pgame} (r : relabelling x y) : x ≈ y :=
⟨le_of_relabelling r, le_of_relabelling r.symm⟩

instance {x y : pgame} : has_coe (relabelling x y) (x ≈ y) := ⟨equiv_of_relabelling⟩

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : pgame} {xl' xr'} (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') :=
pgame.mk xl' xr' (λ i, x.move_left (el.symm i)) (λ j, x.move_right (er.symm j))

@[simp] lemma relabel_move_left' {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (i : xl') :
  move_left (relabel el er) i = x.move_left (el.symm i) :=
rfl
@[simp] lemma relabel_move_left {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (i : x.left_moves) :
  move_left (relabel el er) (el i) = x.move_left i :=
by simp

@[simp] lemma relabel_move_right' {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (j : xr') :
  move_right (relabel el er) j = x.move_right (er.symm j) :=
rfl
@[simp] lemma relabel_move_right {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (j : x.right_moves) :
  move_right (relabel el er) (er j) = x.move_right j :=
by simp

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabel_relabelling {x : pgame} {xl' xr'} (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') :
  relabelling x (relabel el er) :=
relabelling.mk el er (λ i, by simp) (λ j, by simp)

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : pgame → pgame
| ⟨l, r, L, R⟩ := ⟨r, l, λ i, neg (R i), λ i, neg (L i)⟩

instance : has_neg pgame := ⟨neg⟩

@[simp] lemma neg_def {xl xr xL xR} : -(mk xl xr xL xR) = mk xr xl (λ j, -(xR j)) (λ i, -(xL i)) :=
rfl

@[simp] theorem neg_neg : Π {x : pgame}, -(-x) = x
| (mk xl xr xL xR) :=
begin
  dsimp [has_neg.neg, neg],
  congr; funext i; apply neg_neg
end

@[simp] theorem neg_zero : -(0 : pgame) = 0 :=
begin
  dsimp [has_zero.zero, has_neg.neg, neg],
  congr; funext i; cases i
end

/-- An explicit equivalence between the moves for Left in `-x` and the moves for Right in `x`. -/
-- This equivalence is useful to avoid having to use `cases` unnecessarily.
def left_moves_neg (x : pgame) : (-x).left_moves ≃ x.right_moves :=
by { cases x, refl }

/-- An explicit equivalence between the moves for Right in `-x` and the moves for Left in `x`. -/
def right_moves_neg (x : pgame) : (-x).right_moves ≃ x.left_moves :=
by { cases x, refl }

@[simp] lemma move_right_left_moves_neg {x : pgame} (i : left_moves (-x)) :
  move_right x ((left_moves_neg x) i) = -(move_left (-x) i) :=
begin
  induction x,
  exact neg_neg.symm
end
@[simp] lemma move_left_left_moves_neg_symm {x : pgame} (i : right_moves x) :
  move_left (-x) ((left_moves_neg x).symm i) = -(move_right x i) :=
by { cases x, refl }
@[simp] lemma move_left_right_moves_neg {x : pgame} (i : right_moves (-x)) :
  move_left x ((right_moves_neg x) i) = -(move_right (-x) i) :=
begin
  induction x,
  exact neg_neg.symm
end
@[simp] lemma move_right_right_moves_neg_symm {x : pgame} (i : left_moves x) :
  move_right (-x) ((right_moves_neg x).symm i) = -(move_left x i) :=
by { cases x, refl }

theorem le_iff_neg_ge : Π {x y : pgame}, x ≤ y ↔ -y ≤ -x
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  rw [le_def],
  rw [le_def],
  dsimp [neg],
  split,
  { intro h,
    split,
    { intro i, have t := h.right i, cases t,
      { right, cases t,
        use (@right_moves_neg (yR i)).symm t_w, convert le_iff_neg_ge.1 t_h; simp <|> refl },
      { left, cases t,
        use t_w, exact le_iff_neg_ge.1 t_h, } },
    { intro j, have t := h.left j, cases t,
      { right, cases t,
        use t_w, exact le_iff_neg_ge.1 t_h, },
      { left, cases t,
        use (@left_moves_neg (xL j)).symm t_w, convert le_iff_neg_ge.1 t_h; simp <|> refl } } },
  { intro h,
    split,
    { intro i, have t := h.right i, cases t,
      { right, cases t,
        use (@left_moves_neg (xL i)) t_w, convert le_iff_neg_ge.2 _, convert t_h; simp <|> refl },
      { left, cases t,
        use t_w, exact le_iff_neg_ge.2 t_h, } },
    { intro j, have t := h.left j, cases t,
      { right, cases t,
        use t_w, exact le_iff_neg_ge.2 t_h, },
      { left, cases t,
        use (@right_moves_neg (yR j)) t_w, convert le_iff_neg_ge.2 _,
        convert t_h; simp <|> refl } } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_congr {x y : pgame} (h : x ≈ y) : -x ≈ -y :=
⟨le_iff_neg_ge.1 h.2, le_iff_neg_ge.1 h.1⟩

theorem lt_iff_neg_gt : Π {x y : pgame}, x < y ↔ -y < -x :=
begin
  classical,
  intros,
  rw [←not_le, ←not_le, not_iff_not],
  apply le_iff_neg_ge
end

theorem zero_le_iff_neg_le_zero {x : pgame} : 0 ≤ x ↔ -x ≤ 0 :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
end

theorem le_zero_iff_zero_le_neg {x : pgame} : x ≤ 0 ↔ 0 ≤ -x :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
end

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add (x y : pgame) : pgame :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
  { exact λ i, IHxl i y },
  { exact λ i, IHyl i },
  { exact λ i, IHxr i y },
  { exact λ i, IHyr i }
end

instance : has_add pgame := ⟨add⟩

/-- `x + 0` has exactly the same moves as `x`. -/
def add_zero_relabelling : Π (x : pgame.{u}), relabelling (x + 0) x
| (mk xl xr xL xR) :=
begin
  refine ⟨equiv.sum_pempty xl, equiv.sum_pempty xr, _, _⟩,
  { rintro (⟨i⟩|⟨⟨⟩⟩),
    apply add_zero_relabelling, },
  { rintro j,
    apply add_zero_relabelling, }
end

/-- `x + 0` is equivalent to `x`. -/
lemma add_zero_equiv (x : pgame.{u}) : x + 0 ≈ x :=
equiv_of_relabelling (add_zero_relabelling x)

/-- `0 + x` has exactly the same moves as `x`. -/
def zero_add_relabelling : Π (x : pgame.{u}), relabelling (0 + x) x
| (mk xl xr xL xR) :=
begin
  refine ⟨equiv.pempty_sum xl, equiv.pempty_sum xr, _, _⟩,
  { rintro (⟨⟨⟩⟩|⟨i⟩),
    apply zero_add_relabelling, },
  { rintro j,
    apply zero_add_relabelling, }
end

/-- `0 + x` is equivalent to `x`. -/
lemma zero_add_equiv (x : pgame.{u}) : 0 + x ≈ x :=
equiv_of_relabelling (zero_add_relabelling x)

/-- An explicit equivalence between the moves for Left in `x + y` and the type-theory sum
    of the moves for Left in `x` and in `y`. -/
def left_moves_add (x y : pgame) : (x + y).left_moves ≃ x.left_moves ⊕ y.left_moves :=
by { cases x, cases y, refl, }

/-- An explicit equivalence between the moves for Right in `x + y` and the type-theory sum
    of the moves for Right in `x` and in `y`. -/
def right_moves_add (x y : pgame) : (x + y).right_moves ≃ x.right_moves ⊕ y.right_moves :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inl i) =
    (mk xl xr xL xR).move_left i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_left_inl {x y : pgame} {i} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inl i)) = x.move_left i + y :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inl i) =
    (mk xl xr xL xR).move_right i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_right_inl {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inl i)) = x.move_right i + y :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_left i :=
rfl
@[simp] lemma add_move_left_inr {x y : pgame} {i : y.left_moves} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inr i)) = x + y.move_left i :=
by { cases x, cases y, refl, }

@[simp] lemma mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_right i :=
rfl
@[simp] lemma add_move_right_inr {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inr i)) = x + y.move_right i :=
by { cases x, cases y, refl, }

instance : has_sub pgame := ⟨λ x y, x + -y⟩

/-- `-(x+y)` has exactly the same moves as `-x + -y`. -/
def neg_add_relabelling : Π (x y : pgame), relabelling (-(x + y)) (-x + -y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
⟨equiv.refl _, equiv.refl _,
 λ j, sum.cases_on j
   (λ j, neg_add_relabelling (xR j) (mk yl yr yL yR))
   (λ j, neg_add_relabelling (mk xl xr xL xR) (yR j)),
 λ i, sum.cases_on i
   (λ i, neg_add_relabelling (xL i) (mk yl yr yL yR))
   (λ i, neg_add_relabelling (mk xl xr xL xR) (yL i))⟩
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_add_le {x y : pgame} : -(x + y) ≤ -x + -y :=
le_of_relabelling (neg_add_relabelling x y)

/-- `x+y` has exactly the same moves as `y+x`. -/
def add_comm_relabelling : Π (x y : pgame.{u}), relabelling (x + y) (y + x)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  refine ⟨equiv.sum_comm _ _, equiv.sum_comm _ _, _, _⟩;
  rintros (_|_);
  { simp [left_moves_add, right_moves_add], apply add_comm_relabelling }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_comm_le {x y : pgame} : x + y ≤ y + x :=
le_of_relabelling (add_comm_relabelling x y)

theorem add_comm_equiv {x y : pgame} : x + y ≈ y + x :=
equiv_of_relabelling (add_comm_relabelling x y)

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def add_assoc_relabelling : Π (x y z : pgame.{u}), relabelling ((x + y) + z) (x + (y + z))
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  refine ⟨equiv.sum_assoc _ _ _, equiv.sum_assoc _ _ _, _, _⟩,
  { rintro (⟨i|i⟩|i),
    { apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + yL i + mk zl zr zL zR) (mk xl xr xL xR + (yL i + mk zl zr zL zR)),
      apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + mk yl yr yL yR + zL i) (mk xl xr xL xR + (mk yl yr yL yR + zL i)),
      apply add_assoc_relabelling, } },
  { rintro (j|⟨j|j⟩),
    { apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + yR j + mk zl zr zL zR) (mk xl xr xL xR + (yR j + mk zl zr zL zR)),
      apply add_assoc_relabelling, },
    { change relabelling
        (mk xl xr xL xR + mk yl yr yL yR + zR j) (mk xl xr xL xR + (mk yl yr yL yR + zR j)),
      apply add_assoc_relabelling, } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_assoc_equiv {x y z : pgame} : (x + y) + z ≈ x + (y + z) :=
equiv_of_relabelling (add_assoc_relabelling x y z)

theorem add_le_add_right : Π {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  intros h,
  rw le_def,
  split,
  { -- if Left plays first
    intros i,
    change xl ⊕ zl at i,
    cases i,
    { -- either they play in x
      rw le_def at h,
      cases h,
      have t := h_left i,
      rcases t with ⟨i', ih⟩ | ⟨j, jh⟩,
      { left,
        refine ⟨(left_moves_add _ _).inv_fun (sum.inl i'), _⟩,
        exact add_le_add_right ih, },
      { right,
        refine ⟨(right_moves_add _ _).inv_fun (sum.inl j), _⟩,
        convert add_le_add_right jh,
        apply add_move_right_inl },
      },
    { -- or play in z
      left,
      refine ⟨(left_moves_add _ _).inv_fun (sum.inr i), _⟩,
      exact add_le_add_right h, }, },
  { -- if Right plays first
    intros j,
    change yr ⊕ zr at j,
    cases j,
    { -- either they play in y
      rw le_def at h,
      cases h,
      have t := h_right j,
      rcases t with ⟨i, ih⟩ | ⟨j', jh⟩,
      { left,
        refine ⟨(left_moves_add _ _).inv_fun (sum.inl i), _⟩,
        convert add_le_add_right ih,
        apply add_move_left_inl },
      { right,
        refine ⟨(right_moves_add _ _).inv_fun (sum.inl j'), _⟩,
        exact add_le_add_right jh } },
    { -- or play in z
      right,
      refine ⟨(right_moves_add _ _).inv_fun (sum.inr j), _⟩,
      exact add_le_add_right h } }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_le_add_left {x y z : pgame} (h : y ≤ z) : x + y ≤ x + z :=
calc x + y ≤ y + x : add_comm_le
     ... ≤ z + x : add_le_add_right h
     ... ≤ x + z : add_comm_le

theorem add_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
⟨calc w + y ≤ w + z : add_le_add_left h₂.1
        ... ≤ x + z : add_le_add_right h₁.1,
 calc x + z ≤ x + y : add_le_add_left h₂.2
        ... ≤ w + y : add_le_add_right h₁.2⟩

theorem add_left_neg_le_zero : Π {x : pgame}, (-x) + x ≤ 0
| ⟨xl, xr, xL, xR⟩ :=
begin
  rw [le_def],
  split,
  { intro i,
    change xr ⊕ xl at i,
    cases i,
    { -- If Left played in -x, Right responds with the same move in x.
      right,
      refine ⟨(right_moves_add _ _).inv_fun (sum.inr i), _⟩,
      convert @add_left_neg_le_zero (xR i),
      exact add_move_right_inr },
    { -- If Left in x, Right responds with the same move in -x.
      right,
      dsimp,
      refine ⟨(right_moves_add _ _).inv_fun (sum.inl i), _⟩,
      convert @add_left_neg_le_zero (xL i),
      exact add_move_right_inl }, },
  { rintro ⟨⟩, }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem zero_le_add_left_neg : Π {x : pgame}, 0 ≤ (-x) + x :=
begin
  intro x,
  rw [le_iff_neg_ge, neg_zero],
  exact le_trans neg_add_le add_left_neg_le_zero
end

theorem add_left_neg_equiv {x : pgame} : (-x) + x ≈ 0 :=
⟨add_left_neg_le_zero, zero_le_add_left_neg⟩

theorem add_right_neg_le_zero {x : pgame} : x + (-x) ≤ 0 :=
calc x + (-x) ≤ (-x) + x : add_comm_le
     ... ≤ 0 : add_left_neg_le_zero

theorem zero_le_add_right_neg {x : pgame} : 0 ≤ x + (-x) :=
calc 0 ≤ (-x) + x : zero_le_add_left_neg
     ... ≤ x + (-x) : add_comm_le

theorem add_lt_add_right {x y z : pgame} (h : x < y) : x + z < y + z :=
suffices y + z ≤ x + z → y ≤ x, by { rw ←not_le at ⊢ h, exact mt this h },
assume w,
calc y ≤ y + 0            : le_of_relabelling (add_zero_relabelling _).symm
     ... ≤ y + (z + -z)   : add_le_add_left zero_le_add_right_neg
     ... ≤ (y + z) + (-z) : le_of_relabelling (add_assoc_relabelling _ _ _).symm
     ... ≤ (x + z) + (-z) : add_le_add_right w
     ... ≤ x + (z + -z)   : le_of_relabelling (add_assoc_relabelling _ _ _)
     ... ≤ x + 0          : add_le_add_left add_right_neg_le_zero
     ... ≤ x              : le_of_relabelling (add_zero_relabelling _)

theorem add_lt_add_left {x y z : pgame} (h : y < z) : x + y < x + z :=
calc x + y ≤ y + x : add_comm_le
     ... < z + x   : add_lt_add_right h
     ... ≤ x + z   : add_comm_le

theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x :=
⟨λ h, le_trans zero_le_add_right_neg (add_le_add_right h),
 λ h,
  calc x ≤ 0 + x : le_of_relabelling (zero_add_relabelling x).symm
     ... ≤ (y - x) + x : add_le_add_right h
     ... ≤ y + (-x + x) : le_of_relabelling (add_assoc_relabelling _ _ _)
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero)
     ... ≤ y : le_of_relabelling (add_zero_relabelling y)⟩
theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x :=
⟨λ h, lt_of_le_of_lt zero_le_add_right_neg (add_lt_add_right h),
 λ h,
  calc x ≤ 0 + x : le_of_relabelling (zero_add_relabelling x).symm
     ... < (y - x) + x : add_lt_add_right h
     ... ≤ y + (-x + x) : le_of_relabelling (add_assoc_relabelling _ _ _)
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero)
     ... ≤ y : le_of_relabelling (add_zero_relabelling y)⟩

/-- The pre-game `star`, which is fuzzy/confused with zero. -/
def star : pgame := pgame.of_lists [0] [0]

theorem star_lt_zero : star < 0 :=
or.inr ⟨⟨0, zero_lt_one⟩, (by split; rintros ⟨⟩)⟩

theorem zero_lt_star : 0 < star :=
or.inl ⟨⟨0, zero_lt_one⟩, (by split; rintros ⟨⟩)⟩

/-- The pre-game `ω`. (In fact all ordinals have game and surreal representatives.) -/
def omega : pgame := ⟨ulift ℕ, pempty, λ n, ↑n.1, pempty.elim⟩

end pgame
