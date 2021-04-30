/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.order
import data.fintype.basic
import data.pfun
import tactic.apply_fun
import logic.function.iterate

/-!
# Turing machines

This file defines a sequence of simple machine languages, starting with Turing machines and working
up to more complex languages based on Wang B-machines.

## Naming conventions

Each model of computation in this file shares a naming convention for the elements of a model of
computation. These are the parameters for the language:

* `Γ` is the alphabet on the tape.
* `Λ` is the set of labels, or internal machine states.
* `σ` is the type of internal memory, not on the tape. This does not exist in the TM0 model, and
  later models achieve this by mixing it into `Λ`.
* `K` is used in the TM2 model, which has multiple stacks, and denotes the number of such stacks.

All of these variables denote "essentially finite" types, but for technical reasons it is
convenient to allow them to be infinite anyway. When using an infinite type, we will be interested
to prove that only finitely many values of the type are ever interacted with.

Given these parameters, there are a few common structures for the model that arise:

* `stmt` is the set of all actions that can be performed in one step. For the TM0 model this set is
  finite, and for later models it is an infinite inductive type representing "possible program
  texts".
* `cfg` is the set of instantaneous configurations, that is, the state of the machine together with
  its environment.
* `machine` is the set of all machines in the model. Usually this is approximately a function
  `Λ → stmt`, although different models have different ways of halting and other actions.
* `step : cfg → option cfg` is the function that describes how the state evolves over one step.
  If `step c = none`, then `c` is a terminal state, and the result of the computation is read off
  from `c`. Because of the type of `step`, these models are all deterministic by construction.
* `init : input → cfg` sets up the initial state. The type `input` depends on the model;
  in most cases it is `list Γ`.
* `eval : machine → input → roption output`, given a machine `M` and input `i`, starts from
  `init i`, runs `step` until it reaches an output, and then applies a function `cfg → output` to
  the final state to obtain the result. The type `output` depends on the model.
* `supports : machine → finset Λ → Prop` asserts that a machine `M` starts in `S : finset Λ`, and
  can only ever jump to other states inside `S`. This implies that the behavior of `M` on any input
  cannot depend on its values outside `S`. We use this to allow `Λ` to be an infinite set when
  convenient, and prove that only finitely many of these states are actually accessible. This
  formalizes "essentially finite" mentioned above.
-/

open relation
open nat (iterate)
open function (update iterate_succ iterate_succ_apply iterate_succ'
  iterate_succ_apply' iterate_zero_apply)

namespace turing

/-- The `blank_extends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by adding
blanks (`default Γ`) to the end of `l₁`. -/
def blank_extends {Γ} [inhabited Γ] (l₁ l₂ : list Γ) : Prop :=
∃ n, l₂ = l₁ ++ list.repeat (default Γ) n

@[refl] theorem blank_extends.refl {Γ} [inhabited Γ] (l : list Γ) : blank_extends l l :=
⟨0, by simp⟩

@[trans] theorem blank_extends.trans {Γ} [inhabited Γ] {l₁ l₂ l₃ : list Γ} :
  blank_extends l₁ l₂ → blank_extends l₂ l₃ → blank_extends l₁ l₃ :=
by rintro ⟨i, rfl⟩ ⟨j, rfl⟩; exact ⟨i+j, by simp [list.repeat_add]⟩

theorem blank_extends.below_of_le {Γ} [inhabited Γ] {l l₁ l₂ : list Γ} :
  blank_extends l l₁ → blank_extends l l₂ →
  l₁.length ≤ l₂.length → blank_extends l₁ l₂ :=
begin
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h, use j - i,
  simp only [list.length_append, add_le_add_iff_left, list.length_repeat] at h,
  simp only [← list.repeat_add, nat.add_sub_cancel' h, list.append_assoc],
end

/-- Any two extensions by blank `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
def blank_extends.above {Γ} [inhabited Γ] {l l₁ l₂ : list Γ}
  (h₁ : blank_extends l l₁) (h₂ : blank_extends l l₂) :
  {l' // blank_extends l₁ l' ∧ blank_extends l₂ l'} :=
if h : l₁.length ≤ l₂.length then
  ⟨l₂, h₁.below_of_le h₂ h, blank_extends.refl _⟩
else
  ⟨l₁, blank_extends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩

theorem blank_extends.above_of_le {Γ} [inhabited Γ] {l l₁ l₂ : list Γ} :
  blank_extends l₁ l → blank_extends l₂ l →
  l₁.length ≤ l₂.length → blank_extends l₁ l₂ :=
begin
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h, use i - j,
  refine list.append_right_cancel (e.symm.trans _),
  rw [list.append_assoc, ← list.repeat_add, nat.sub_add_cancel],
  apply_fun list.length at e,
  simp only [list.length_append, list.length_repeat] at e,
  rwa [← add_le_add_iff_left, e, add_le_add_iff_right]
end

/-- `blank_rel` is the symmetric closure of `blank_extends`, turning it into an equivalence
relation. Two lists are related by `blank_rel` if one extends the other by blanks. -/
def blank_rel {Γ} [inhabited Γ] (l₁ l₂ : list Γ) : Prop :=
blank_extends l₁ l₂ ∨ blank_extends l₂ l₁

@[refl] theorem blank_rel.refl {Γ} [inhabited Γ] (l : list Γ) : blank_rel l l :=
or.inl (blank_extends.refl _)

@[symm] theorem blank_rel.symm {Γ} [inhabited Γ] {l₁ l₂ : list Γ} :
  blank_rel l₁ l₂ → blank_rel l₂ l₁ := or.symm

@[trans] theorem blank_rel.trans {Γ} [inhabited Γ] {l₁ l₂ l₃ : list Γ} :
  blank_rel l₁ l₂ → blank_rel l₂ l₃ → blank_rel l₁ l₃ :=
begin
  rintro (h₁|h₁) (h₂|h₂),
  { exact or.inl (h₁.trans h₂) },
  { cases le_total l₁.length l₃.length with h h,
    { exact or.inl (h₁.above_of_le h₂ h) },
    { exact or.inr (h₂.above_of_le h₁ h) } },
  { cases le_total l₁.length l₃.length with h h,
    { exact or.inl (h₁.below_of_le h₂ h) },
    { exact or.inr (h₂.below_of_le h₁ h) } },
  { exact or.inr (h₂.trans h₁) },
end

/-- Given two `blank_rel` lists, there exists (constructively) a common join. -/
def blank_rel.above {Γ} [inhabited Γ] {l₁ l₂ : list Γ} (h : blank_rel l₁ l₂) :
  {l // blank_extends l₁ l ∧ blank_extends l₂ l} :=
begin
  refine if hl : l₁.length ≤ l₂.length
    then ⟨l₂, or.elim h id (λ h', _), blank_extends.refl _⟩
    else ⟨l₁, blank_extends.refl _, or.elim h (λ h', _) id⟩,
  exact (blank_extends.refl _).above_of_le h' hl,
  exact (blank_extends.refl _).above_of_le h' (le_of_not_ge hl)
end

/-- Given two `blank_rel` lists, there exists (constructively) a common meet. -/
def blank_rel.below {Γ} [inhabited Γ] {l₁ l₂ : list Γ} (h : blank_rel l₁ l₂) :
  {l // blank_extends l l₁ ∧ blank_extends l l₂} :=
begin
  refine if hl : l₁.length ≤ l₂.length
    then ⟨l₁, blank_extends.refl _, or.elim h id (λ h', _)⟩
    else ⟨l₂, or.elim h (λ h', _) id, blank_extends.refl _⟩,
  exact (blank_extends.refl _).above_of_le h' hl,
  exact (blank_extends.refl _).above_of_le h' (le_of_not_ge hl)
end

theorem blank_rel.equivalence (Γ) [inhabited Γ] : equivalence (@blank_rel Γ _) :=
⟨blank_rel.refl, @blank_rel.symm _ _, @blank_rel.trans _ _⟩

/-- Construct a setoid instance for `blank_rel`. -/
def blank_rel.setoid (Γ) [inhabited Γ] : setoid (list Γ) := ⟨_, blank_rel.equivalence _⟩

/-- A `list_blank Γ` is a quotient of `list Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the list continues
infinitely with blanks. -/
def list_blank (Γ) [inhabited Γ] := quotient (blank_rel.setoid Γ)

instance list_blank.inhabited {Γ} [inhabited Γ] : inhabited (list_blank Γ) := ⟨quotient.mk' []⟩
instance list_blank.has_emptyc {Γ} [inhabited Γ] : has_emptyc (list_blank Γ) := ⟨quotient.mk' []⟩

/-- A modified version of `quotient.lift_on'` specialized for `list_blank`, with the stronger
precondition `blank_extends` instead of `blank_rel`. -/
@[elab_as_eliminator, reducible]
protected def list_blank.lift_on {Γ} [inhabited Γ] {α} (l : list_blank Γ) (f : list Γ → α)
  (H : ∀ a b, blank_extends a b → f a = f b) : α :=
l.lift_on' f $ by rintro a b (h|h); [exact H _ _ h, exact (H _ _ h).symm]

/-- The quotient map turning a `list` into a `list_blank`. -/
def list_blank.mk {Γ} [inhabited Γ] : list Γ → list_blank Γ := quotient.mk'

@[elab_as_eliminator]
protected lemma list_blank.induction_on {Γ} [inhabited Γ]
  {p : list_blank Γ → Prop} (q : list_blank Γ)
  (h : ∀ a, p (list_blank.mk a)) : p q := quotient.induction_on' q h

/-- The head of a `list_blank` is well defined. -/
def list_blank.head {Γ} [inhabited Γ] (l : list_blank Γ) : Γ :=
l.lift_on list.head begin
  rintro _ _ ⟨i, rfl⟩,
  cases a, {cases i; refl}, refl
end

@[simp] theorem list_blank.head_mk {Γ} [inhabited Γ] (l : list Γ) :
  list_blank.head (list_blank.mk l) = l.head := rfl

/-- The tail of a `list_blank` is well defined (up to the tail of blanks). -/
def list_blank.tail {Γ} [inhabited Γ] (l : list_blank Γ) : list_blank Γ :=
l.lift_on (λ l, list_blank.mk l.tail) begin
  rintro _ _ ⟨i, rfl⟩,
  refine quotient.sound' (or.inl _),
  cases a; [{cases i; [exact ⟨0, rfl⟩, exact ⟨i, rfl⟩]}, exact ⟨i, rfl⟩]
end

@[simp] theorem list_blank.tail_mk {Γ} [inhabited Γ] (l : list Γ) :
  list_blank.tail (list_blank.mk l) = list_blank.mk l.tail := rfl

/-- We can cons an element onto a `list_blank`. -/
def list_blank.cons {Γ} [inhabited Γ] (a : Γ) (l : list_blank Γ) : list_blank Γ :=
l.lift_on (λ l, list_blank.mk (list.cons a l)) begin
  rintro _ _ ⟨i, rfl⟩,
  exact quotient.sound' (or.inl ⟨i, rfl⟩),
end

@[simp] theorem list_blank.cons_mk {Γ} [inhabited Γ] (a : Γ) (l : list Γ) :
  list_blank.cons a (list_blank.mk l) = list_blank.mk (a :: l) := rfl

@[simp] theorem list_blank.head_cons {Γ} [inhabited Γ] (a : Γ) :
  ∀ (l : list_blank Γ), (l.cons a).head = a :=
quotient.ind' $ by exact λ l, rfl

@[simp] theorem list_blank.tail_cons {Γ} [inhabited Γ] (a : Γ) :
  ∀ (l : list_blank Γ), (l.cons a).tail = l :=
quotient.ind' $ by exact λ l, rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
@[simp] theorem list_blank.cons_head_tail {Γ} [inhabited Γ] :
  ∀ (l : list_blank Γ), l.tail.cons l.head = l :=
quotient.ind' begin
  refine (λ l, quotient.sound' (or.inr _)),
  cases l, {exact ⟨1, rfl⟩}, {refl},
end

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
theorem list_blank.exists_cons {Γ} [inhabited Γ] (l : list_blank Γ) :
  ∃ a l', l = list_blank.cons a l' :=
⟨_, _, (list_blank.cons_head_tail _).symm⟩

/-- The n-th element of a `list_blank` is well defined for all `n : ℕ`, unlike in a `list`. -/
def list_blank.nth {Γ} [inhabited Γ] (l : list_blank Γ) (n : ℕ) : Γ :=
l.lift_on (λ l, list.inth l n) begin
  rintro l _ ⟨i, rfl⟩,
  simp only [list.inth],
  cases lt_or_le _ _ with h h, {rw list.nth_append h},
  rw list.nth_len_le h,
  cases le_or_lt _ _ with h₂ h₂, {rw list.nth_len_le h₂},
  rw [list.nth_le_nth h₂, list.nth_le_append_right h, list.nth_le_repeat]
end

@[simp] theorem list_blank.nth_mk {Γ} [inhabited Γ] (l : list Γ) (n : ℕ) :
  (list_blank.mk l).nth n = l.inth n := rfl

@[simp] theorem list_blank.nth_zero {Γ} [inhabited Γ] (l : list_blank Γ) : l.nth 0 = l.head :=
begin
  conv {to_lhs, rw [← list_blank.cons_head_tail l]},
  exact quotient.induction_on' l.tail (λ l, rfl)
end

@[simp] theorem list_blank.nth_succ {Γ} [inhabited Γ] (l : list_blank Γ) (n : ℕ) :
  l.nth (n + 1) = l.tail.nth n :=
begin
  conv {to_lhs, rw [← list_blank.cons_head_tail l]},
  exact quotient.induction_on' l.tail (λ l, rfl)
end

@[ext] theorem list_blank.ext {Γ} [inhabited Γ] {L₁ L₂ : list_blank Γ} :
  (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ :=
list_blank.induction_on L₁ $ λ l₁, list_blank.induction_on L₂ $ λ l₂ H,
begin
  wlog h : l₁.length ≤ l₂.length using l₁ l₂,
  swap, { exact (this $ λ i, (H i).symm).symm },
  refine quotient.sound' (or.inl ⟨l₂.length - l₁.length, _⟩),
  refine list.ext_le _ (λ i h h₂, eq.symm _),
  { simp only [nat.add_sub_of_le h, list.length_append, list.length_repeat] },
  simp at H,
  cases lt_or_le i l₁.length with h' h',
  { simpa only [list.nth_le_append _ h',
      list.nth_le_nth h, list.nth_le_nth h', option.iget] using H i },
  { simpa only [list.nth_le_append_right h', list.nth_le_repeat,
      list.nth_le_nth h, list.nth_len_le h', option.iget] using H i },
end

/-- Apply a function to a value stored at the nth position of the list. -/
@[simp] def list_blank.modify_nth {Γ} [inhabited Γ] (f : Γ → Γ) : ℕ → list_blank Γ → list_blank Γ
| 0     L := L.tail.cons (f L.head)
| (n+1) L := (L.tail.modify_nth n).cons L.head

theorem list_blank.nth_modify_nth {Γ} [inhabited Γ] (f : Γ → Γ) (n i) (L : list_blank Γ) :
  (L.modify_nth f n).nth i = if i = n then f (L.nth i) else L.nth i :=
begin
  induction n with n IH generalizing i L,
  { cases i; simp only [list_blank.nth_zero, if_true,
      list_blank.head_cons, list_blank.modify_nth, eq_self_iff_true,
      list_blank.nth_succ, if_false, list_blank.tail_cons] },
  { cases i,
    { rw if_neg (nat.succ_ne_zero _).symm,
      simp only [list_blank.nth_zero, list_blank.head_cons, list_blank.modify_nth] },
    { simp only [IH, list_blank.modify_nth, list_blank.nth_succ, list_blank.tail_cons],
      congr } }
end

/-- A pointed map of `inhabited` types is a map that sends one default value to the other. -/
structure {u v} pointed_map (Γ : Type u) (Γ' : Type v)
  [inhabited Γ] [inhabited Γ'] : Type (max u v) :=
(f : Γ → Γ') (map_pt' : f (default _) = default _)

instance {Γ Γ'} [inhabited Γ] [inhabited Γ'] : inhabited (pointed_map Γ Γ') :=
⟨⟨λ _, default _, rfl⟩⟩

instance {Γ Γ'} [inhabited Γ] [inhabited Γ'] : has_coe_to_fun (pointed_map Γ Γ') :=
⟨_, pointed_map.f⟩

@[simp] theorem pointed_map.mk_val {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : Γ → Γ') (pt) : (pointed_map.mk f pt : Γ → Γ') = f := rfl

@[simp] theorem pointed_map.map_pt {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') : f (default _) = default _ := pointed_map.map_pt' _

@[simp] theorem pointed_map.head_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list Γ) : (l.map f).head = f l.head :=
by cases l; [exact (pointed_map.map_pt f).symm, refl]

/-- The `map` function on lists is well defined on `list_blank`s provided that the map is
pointed. -/
def list_blank.map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) : list_blank Γ' :=
l.lift_on (λ l, list_blank.mk (list.map f l)) begin
  rintro l _ ⟨i, rfl⟩, refine quotient.sound' (or.inl ⟨i, _⟩),
  simp only [pointed_map.map_pt, list.map_append, list.map_repeat],
end

@[simp] theorem list_blank.map_mk {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list Γ) : (list_blank.mk l).map f = list_blank.mk (l.map f) := rfl

@[simp] theorem list_blank.head_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) : (l.map f).head = f l.head :=
begin
  conv {to_lhs, rw [← list_blank.cons_head_tail l]},
  exact quotient.induction_on' l (λ a, rfl)
end

@[simp] theorem list_blank.tail_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) : (l.map f).tail = l.tail.map f :=
begin
  conv {to_lhs, rw [← list_blank.cons_head_tail l]},
  exact quotient.induction_on' l (λ a, rfl)
end

@[simp] theorem list_blank.map_cons {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) :=
begin
  refine (list_blank.cons_head_tail _).symm.trans _,
  simp only [list_blank.head_map, list_blank.head_cons, list_blank.tail_map, list_blank.tail_cons]
end

@[simp] theorem list_blank.nth_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) :=
l.induction_on begin
  intro l, simp only [list.nth_map, list_blank.map_mk, list_blank.nth_mk, list.inth],
  cases l.nth n, {exact f.2.symm}, {refl}
end

/-- The `i`-th projection as a pointed map. -/
def proj {ι : Type*} {Γ : ι → Type*} [∀ i, inhabited (Γ i)] (i : ι) :
  pointed_map (∀ i, Γ i) (Γ i) := ⟨λ a, a i, rfl⟩

theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, inhabited (Γ i)] (i : ι)
  (L n) : (list_blank.map (@proj ι Γ _ i) L).nth n = L.nth n i :=
by rw list_blank.nth_map; refl

theorem list_blank.map_modify_nth {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (F : pointed_map Γ Γ') (f : Γ → Γ) (f' : Γ' → Γ')
  (H : ∀ x, F (f x) = f' (F x)) (n) (L : list_blank Γ) :
  (L.modify_nth f n).map F = (L.map F).modify_nth f' n :=
by induction n with n IH generalizing L; simp only [*,
  list_blank.head_map, list_blank.modify_nth, list_blank.map_cons, list_blank.tail_map]

/-- Append a list on the left side of a list_blank. -/
@[simp] def list_blank.append {Γ} [inhabited Γ] : list Γ → list_blank Γ → list_blank Γ
| [] L := L
| (a :: l) L := list_blank.cons a (list_blank.append l L)

@[simp] theorem list_blank.append_mk {Γ} [inhabited Γ] (l₁ l₂ : list Γ) :
  list_blank.append l₁ (list_blank.mk l₂) = list_blank.mk (l₁ ++ l₂) :=
by induction l₁; simp only [*,
     list_blank.append, list.nil_append, list.cons_append, list_blank.cons_mk]

theorem list_blank.append_assoc {Γ} [inhabited Γ] (l₁ l₂ : list Γ) (l₃ : list_blank Γ) :
  list_blank.append (l₁ ++ l₂) l₃ = list_blank.append l₁ (list_blank.append l₂ l₃) :=
l₃.induction_on $ by intro; simp only [list_blank.append_mk, list.append_assoc]

/-- The `bind` function on lists is well defined on `list_blank`s provided that the default element
is sent to a sequence of default elements. -/
def list_blank.bind {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (l : list_blank Γ) (f : Γ → list Γ')
  (hf : ∃ n, f (default _) = list.repeat (default _) n) : list_blank Γ' :=
l.lift_on (λ l, list_blank.mk (list.bind l f)) begin
  rintro l _ ⟨i, rfl⟩, cases hf with n e, refine quotient.sound' (or.inl ⟨i * n, _⟩),
  rw [list.bind_append, mul_comm], congr,
  induction i with i IH, refl,
  simp only [IH, e, list.repeat_add, nat.mul_succ, add_comm, list.repeat_succ, list.cons_bind],
end

@[simp] lemma list_blank.bind_mk {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (l : list Γ) (f : Γ → list Γ') (hf) :
  (list_blank.mk l).bind f hf = list_blank.mk (l.bind f) := rfl

@[simp] lemma list_blank.cons_bind {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (a : Γ) (l : list_blank Γ) (f : Γ → list Γ') (hf) :
  (l.cons a).bind f hf = (l.bind f hf).append (f a) :=
l.induction_on $ by intro; simp only [list_blank.append_mk,
  list_blank.bind_mk, list_blank.cons_mk, list.cons_bind]

/-- The tape of a Turing machine is composed of a head element (which we imagine to be the
current position of the head), together with two `list_blank`s denoting the portions of the tape
going off to the left and right. When the Turing machine moves right, an element is pulled from the
right side and becomes the new head, while the head element is consed onto the left side. -/
structure tape (Γ : Type*) [inhabited Γ] :=
(head : Γ)
(left : list_blank Γ)
(right : list_blank Γ)

instance tape.inhabited {Γ} [inhabited Γ] : inhabited (tape Γ) :=
⟨by constructor; apply default⟩

/-- A direction for the turing machine `move` command, either
  left or right. -/
@[derive decidable_eq, derive inhabited]
inductive dir | left | right

/-- The "inclusive" left side of the tape, including both `left` and `head`. -/
def tape.left₀ {Γ} [inhabited Γ] (T : tape Γ) : list_blank Γ := T.left.cons T.head

/-- The "inclusive" right side of the tape, including both `right` and `head`. -/
def tape.right₀ {Γ} [inhabited Γ] (T : tape Γ) : list_blank Γ := T.right.cons T.head

/-- Move the tape in response to a motion of the Turing machine. Note that `T.move dir.left` makes
`T.left` smaller; the Turing machine is moving left and the tape is moving right. -/
def tape.move {Γ} [inhabited Γ] : dir → tape Γ → tape Γ
| dir.left ⟨a, L, R⟩ := ⟨L.head, L.tail, R.cons a⟩
| dir.right ⟨a, L, R⟩ := ⟨R.head, L.cons a, R.tail⟩

@[simp] theorem tape.move_left_right {Γ} [inhabited Γ] (T : tape Γ) :
  (T.move dir.left).move dir.right = T :=
by cases T; simp [tape.move]

@[simp] theorem tape.move_right_left {Γ} [inhabited Γ] (T : tape Γ) :
  (T.move dir.right).move dir.left = T :=
by cases T; simp [tape.move]

/-- Construct a tape from a left side and an inclusive right side. -/
def tape.mk' {Γ} [inhabited Γ] (L R : list_blank Γ) : tape Γ := ⟨R.head, L, R.tail⟩

@[simp] theorem tape.mk'_left {Γ} [inhabited Γ] (L R : list_blank Γ) :
  (tape.mk' L R).left = L := rfl

@[simp] theorem tape.mk'_head {Γ} [inhabited Γ] (L R : list_blank Γ) :
  (tape.mk' L R).head = R.head := rfl

@[simp] theorem tape.mk'_right {Γ} [inhabited Γ] (L R : list_blank Γ) :
  (tape.mk' L R).right = R.tail := rfl

@[simp] theorem tape.mk'_right₀ {Γ} [inhabited Γ] (L R : list_blank Γ) :
  (tape.mk' L R).right₀ = R := list_blank.cons_head_tail _

@[simp] theorem tape.mk'_left_right₀ {Γ} [inhabited Γ] (T : tape Γ) :
  tape.mk' T.left T.right₀ = T :=
by cases T; simp only [tape.right₀, tape.mk',
     list_blank.head_cons, list_blank.tail_cons, eq_self_iff_true, and_self]

theorem tape.exists_mk' {Γ} [inhabited Γ] (T : tape Γ) :
  ∃ L R, T = tape.mk' L R := ⟨_, _, (tape.mk'_left_right₀ _).symm⟩

@[simp] theorem tape.move_left_mk' {Γ} [inhabited Γ] (L R : list_blank Γ) :
  (tape.mk' L R).move dir.left = tape.mk' L.tail (R.cons L.head) :=
by simp only [tape.move, tape.mk', list_blank.head_cons, eq_self_iff_true,
  list_blank.cons_head_tail, and_self, list_blank.tail_cons]

@[simp] theorem tape.move_right_mk' {Γ} [inhabited Γ] (L R : list_blank Γ) :
  (tape.mk' L R).move dir.right = tape.mk' (L.cons R.head) R.tail :=
by simp only [tape.move, tape.mk', list_blank.head_cons, eq_self_iff_true,
  list_blank.cons_head_tail, and_self, list_blank.tail_cons]

/-- Construct a tape from a left side and an inclusive right side. -/
def tape.mk₂ {Γ} [inhabited Γ] (L R : list Γ) : tape Γ :=
tape.mk' (list_blank.mk L) (list_blank.mk R)

/-- Construct a tape from a list, with the head of the list at the TM head and the rest going
to the right. -/
def tape.mk₁ {Γ} [inhabited Γ] (l : list Γ) : tape Γ :=
tape.mk₂ [] l

/-- The `nth` function of a tape is integer-valued, with index `0` being the head, negative indexes
on the left and positive indexes on the right. (Picture a number line.) -/
def tape.nth {Γ} [inhabited Γ] (T : tape Γ) : ℤ → Γ
| 0 := T.head
| (n+1:ℕ) := T.right.nth n
| -[1+ n] := T.left.nth n

@[simp] theorem tape.nth_zero {Γ} [inhabited Γ] (T : tape Γ) : T.nth 0 = T.1 := rfl

theorem tape.right₀_nth {Γ} [inhabited Γ] (T : tape Γ) (n : ℕ) : T.right₀.nth n = T.nth n :=
by cases n; simp only [tape.nth, tape.right₀, int.coe_nat_zero,
  list_blank.nth_zero, list_blank.nth_succ, list_blank.head_cons, list_blank.tail_cons]

@[simp] theorem tape.mk'_nth_nat {Γ} [inhabited Γ] (L R : list_blank Γ) (n : ℕ) :
  (tape.mk' L R).nth n = R.nth n :=
by rw [← tape.right₀_nth, tape.mk'_right₀]

@[simp] theorem tape.move_left_nth {Γ} [inhabited Γ] :
  ∀ (T : tape Γ) (i : ℤ), (T.move dir.left).nth i = T.nth (i-1)
| ⟨a, L, R⟩ -[1+ n]     := (list_blank.nth_succ _ _).symm
| ⟨a, L, R⟩ 0           := (list_blank.nth_zero _).symm
| ⟨a, L, R⟩ 1           := (list_blank.nth_zero _).trans (list_blank.head_cons _ _)
| ⟨a, L, R⟩ ((n+1:ℕ)+1) := begin
    rw add_sub_cancel,
    change (R.cons a).nth (n+1) = R.nth n,
    rw [list_blank.nth_succ, list_blank.tail_cons]
  end

@[simp] theorem tape.move_right_nth {Γ} [inhabited Γ] (T : tape Γ) (i : ℤ) :
  (T.move dir.right).nth i = T.nth (i+1) :=
by conv {to_rhs, rw ← T.move_right_left}; rw [tape.move_left_nth, add_sub_cancel]

@[simp] theorem tape.move_right_n_head {Γ} [inhabited Γ] (T : tape Γ) (i : ℕ) :
  ((tape.move dir.right)^[i] T).head = T.nth i :=
by induction i generalizing T; [refl, simp only [*,
  tape.move_right_nth, int.coe_nat_succ, iterate_succ]]

/-- Replace the current value of the head on the tape. -/
def tape.write {Γ} [inhabited Γ] (b : Γ) (T : tape Γ) : tape Γ := {head := b, ..T}

@[simp] theorem tape.write_self {Γ} [inhabited Γ] : ∀ (T : tape Γ), T.write T.1 = T :=
by rintro ⟨⟩; refl

@[simp] theorem tape.write_nth {Γ} [inhabited Γ] (b : Γ) :
  ∀ (T : tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
| ⟨a, L, R⟩ 0       := rfl
| ⟨a, L, R⟩ (n+1:ℕ) := rfl
| ⟨a, L, R⟩ -[1+ n] := rfl

@[simp] theorem tape.write_mk' {Γ} [inhabited Γ] (a b : Γ) (L R : list_blank Γ) :
  (tape.mk' L (R.cons a)).write b = tape.mk' L (R.cons b) :=
by simp only [tape.write, tape.mk', list_blank.head_cons, list_blank.tail_cons,
  eq_self_iff_true, and_self]

/-- Apply a pointed map to a tape to change the alphabet. -/
def tape.map {Γ Γ'} [inhabited Γ] [inhabited Γ'] (f : pointed_map Γ Γ') (T : tape Γ) : tape Γ' :=
⟨f T.1, T.2.map f, T.3.map f⟩

@[simp] theorem tape.map_fst {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') : ∀ (T : tape Γ), (T.map f).1 = f T.1 :=
by rintro ⟨⟩; refl

@[simp] theorem tape.map_write {Γ Γ'} [inhabited Γ] [inhabited Γ'] (f : pointed_map Γ Γ') (b : Γ) :
  ∀ (T : tape Γ), (T.write b).map f = (T.map f).write (f b) :=
by rintro ⟨⟩; refl

@[simp] theorem tape.write_move_right_n {Γ} [inhabited Γ] (f : Γ → Γ) (L R : list_blank Γ) (n : ℕ) :
  ((tape.move dir.right)^[n] (tape.mk' L R)).write (f (R.nth n)) =
  ((tape.move dir.right)^[n] (tape.mk' L (R.modify_nth f n))) :=
begin
  induction n with n IH generalizing L R,
  { simp only [list_blank.nth_zero, list_blank.modify_nth, iterate_zero_apply],
    rw [← tape.write_mk', list_blank.cons_head_tail] },
  simp only [list_blank.head_cons, list_blank.nth_succ, list_blank.modify_nth,
    tape.move_right_mk', list_blank.tail_cons, iterate_succ_apply, IH]
end

theorem tape.map_move {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (T : tape Γ) (d) : (T.move d).map f = (T.map f).move d :=
by cases T; cases d; simp only [tape.move, tape.map,
  list_blank.head_map, eq_self_iff_true, list_blank.map_cons, and_self, list_blank.tail_map]

theorem tape.map_mk' {Γ Γ'} [inhabited Γ] [inhabited Γ'] (f : pointed_map Γ Γ')
  (L R : list_blank Γ) : (tape.mk' L R).map f = tape.mk' (L.map f) (R.map f) :=
by simp only [tape.mk', tape.map, list_blank.head_map,
  eq_self_iff_true, and_self, list_blank.tail_map]

theorem tape.map_mk₂ {Γ Γ'} [inhabited Γ] [inhabited Γ'] (f : pointed_map Γ Γ')
  (L R : list Γ) : (tape.mk₂ L R).map f = tape.mk₂ (L.map f) (R.map f) :=
by simp only [tape.mk₂, tape.map_mk', list_blank.map_mk]

theorem tape.map_mk₁ {Γ Γ'} [inhabited Γ] [inhabited Γ'] (f : pointed_map Γ Γ')
  (l : list Γ) : (tape.mk₁ l).map f = tape.mk₁ (l.map f) := tape.map_mk₂ _ _ _

/-- Run a state transition function `σ → option σ` "to completion". The return value is the last
state returned before a `none` result. If the state transition function always returns `some`,
then the computation diverges, returning `roption.none`. -/
def eval {σ} (f : σ → option σ) : σ → roption σ :=
pfun.fix (λ s, roption.some $ (f s).elim (sum.inl s) sum.inr)

/-- The reflexive transitive closure of a state transition function. `reaches f a b` means
there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation permits zero steps of the state transition function. -/
def reaches {σ} (f : σ → option σ) : σ → σ → Prop :=
refl_trans_gen (λ a b, b ∈ f a)

/-- The transitive closure of a state transition function. `reaches₁ f a b` means there is a
nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation does not permit zero steps of the state transition function. -/
def reaches₁ {σ} (f : σ → option σ) : σ → σ → Prop :=
trans_gen (λ a b, b ∈ f a)

theorem reaches₁_eq {σ} {f : σ → option σ} {a b c}
  (h : f a = f b) : reaches₁ f a c ↔ reaches₁ f b c :=
trans_gen.head'_iff.trans (trans_gen.head'_iff.trans $ by rw h).symm

theorem reaches_total {σ} {f : σ → option σ}
  {a b c} : reaches f a b → reaches f a c →
  reaches f b c ∨ reaches f c b :=
refl_trans_gen.total_of_right_unique ⟨λ _ _ _, option.mem_unique⟩

theorem reaches₁_fwd {σ} {f : σ → option σ}
  {a b c} (h₁ : reaches₁ f a c) (h₂ : b ∈ f a) : reaches f b c :=
begin
  rcases trans_gen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩,
  cases option.mem_unique hab h₂, exact hbc
end

/-- A variation on `reaches`. `reaches₀ f a b` holds if whenever `reaches₁ f b c` then
`reaches₁ f a c`. This is a weaker property than `reaches` and is useful for replacing states with
equivalent states without taking a step. -/
def reaches₀ {σ} (f : σ → option σ) (a b : σ) : Prop :=
∀ c, reaches₁ f b c → reaches₁ f a c

theorem reaches₀.trans {σ} {f : σ → option σ} {a b c : σ}
  (h₁ : reaches₀ f a b) (h₂ : reaches₀ f b c) : reaches₀ f a c
| d h₃ := h₁ _ (h₂ _ h₃)

@[refl] theorem reaches₀.refl {σ} {f : σ → option σ} (a : σ) : reaches₀ f a a
| b h := h

theorem reaches₀.single {σ} {f : σ → option σ} {a b : σ}
  (h : b ∈ f a) : reaches₀ f a b
| c h₂ := h₂.head h

theorem reaches₀.head {σ} {f : σ → option σ} {a b c : σ}
  (h : b ∈ f a) (h₂ : reaches₀ f b c) : reaches₀ f a c :=
(reaches₀.single h).trans h₂

theorem reaches₀.tail {σ} {f : σ → option σ} {a b c : σ}
  (h₁ : reaches₀ f a b) (h : c ∈ f b) : reaches₀ f a c :=
h₁.trans (reaches₀.single h)

theorem reaches₀_eq {σ} {f : σ → option σ} {a b}
  (e : f a = f b) : reaches₀ f a b
| d h := (reaches₁_eq e).2 h

theorem reaches₁.to₀ {σ} {f : σ → option σ} {a b : σ}
  (h : reaches₁ f a b) : reaches₀ f a b
| c h₂ := h.trans h₂

theorem reaches.to₀ {σ} {f : σ → option σ} {a b : σ}
  (h : reaches f a b) : reaches₀ f a b
| c h₂ := h₂.trans_right h

theorem reaches₀.tail' {σ} {f : σ → option σ} {a b c : σ}
  (h : reaches₀ f a b) (h₂ : c ∈ f b) : reaches₁ f a c :=
h _ (trans_gen.single h₂)

/-- (co-)Induction principle for `eval`. If a property `C` holds of any point `a` evaluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfies `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many steps. -/
@[elab_as_eliminator] def eval_induction {σ}
  {f : σ → option σ} {b : σ} {C : σ → Sort*} {a : σ} (h : b ∈ eval f a)
  (H : ∀ a, b ∈ eval f a →
    (∀ a', b ∈ eval f a' → f a = some a' → C a') → C a) : C a :=
pfun.fix_induction h (λ a' ha' h', H _ ha' $ λ b' hb' e, h' _ hb' $
  roption.mem_some_iff.2 $ by rw e; refl)

theorem mem_eval {σ} {f : σ → option σ} {a b} :
  b ∈ eval f a ↔ reaches f a b ∧ f b = none :=
⟨λ h, begin
  refine eval_induction h (λ a h IH, _),
  cases e : f a with a',
  { rw roption.mem_unique h (pfun.mem_fix_iff.2 $ or.inl $
      roption.mem_some_iff.2 $ by rw e; refl),
    exact ⟨refl_trans_gen.refl, e⟩ },
  { rcases pfun.mem_fix_iff.1 h with h | ⟨_, h, h'⟩;
      rw e at h; cases roption.mem_some_iff.1 h,
    cases IH a' h' (by rwa e) with h₁ h₂,
    exact ⟨refl_trans_gen.head e h₁, h₂⟩ }
end, λ ⟨h₁, h₂⟩, begin
  refine refl_trans_gen.head_induction_on h₁ _ (λ a a' h _ IH, _),
  { refine pfun.mem_fix_iff.2 (or.inl _),
    rw h₂, apply roption.mem_some },
  { refine pfun.mem_fix_iff.2 (or.inr ⟨_, _, IH⟩),
    rw show f a = _, from h,
    apply roption.mem_some }
end⟩

theorem eval_maximal₁ {σ} {f : σ → option σ} {a b}
  (h : b ∈ eval f a) (c) : ¬ reaches₁ f b c | bc :=
let ⟨ab, b0⟩ := mem_eval.1 h, ⟨b', h', _⟩ := trans_gen.head'_iff.1 bc in
by cases b0.symm.trans h'

theorem eval_maximal {σ} {f : σ → option σ} {a b}
  (h : b ∈ eval f a) {c} : reaches f b c ↔ c = b :=
let ⟨ab, b0⟩ := mem_eval.1 h in
refl_trans_gen_iff_eq $ λ b' h', by cases b0.symm.trans h'

theorem reaches_eval {σ} {f : σ → option σ} {a b}
  (ab : reaches f a b) : eval f a = eval f b :=
roption.ext $ λ c,
 ⟨λ h, let ⟨ac, c0⟩ := mem_eval.1 h in
    mem_eval.2 ⟨(or_iff_left_of_imp $ by exact
      λ cb, (eval_maximal h).1 cb ▸ refl_trans_gen.refl).1
      (reaches_total ab ac), c0⟩,
  λ h, let ⟨bc, c0⟩ := mem_eval.1 h in mem_eval.2 ⟨ab.trans bc, c0⟩,⟩

/-- Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transition functions
`f₁ : σ₁ → option σ₁` and `f₂ : σ₂ → option σ₂`, `respects f₁ f₂ tr` means that if `tr a₁ a₂` holds
initially and `f₁` takes a step to `a₂` then `f₂` will take one or more steps before reaching a
state `b₂` satisfying `tr a₂ b₂`, and if `f₁ a₁` terminates then `f₂ a₂` also terminates.
Such a relation `tr` is also known as a refinement. -/
def respects {σ₁ σ₂}
  (f₁ : σ₁ → option σ₁) (f₂ : σ₂ → option σ₂) (tr : σ₁ → σ₂ → Prop) :=
∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (match f₁ a₁ with
  | some b₁ := ∃ b₂, tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂
  | none := f₂ a₂ = none
  end : Prop)

theorem tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : reaches₁ f₁ a₁ b₁) :
  ∃ b₂, tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂ :=
begin
  induction ab with c₁ ac c₁ d₁ ac cd IH,
  { have := H aa,
    rwa (show f₁ a₁ = _, from ac) at this },
  { rcases IH with ⟨c₂, cc, ac₂⟩,
    have := H cc,
    rw (show f₁ c₁ = _, from cd) at this,
    rcases this with ⟨d₂, dd, cd₂⟩,
    exact ⟨_, dd, ac₂.trans cd₂⟩ }
end

theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : reaches f₁ a₁ b₁) :
  ∃ b₂, tr b₁ b₂ ∧ reaches f₂ a₂ b₂ :=
begin
  rcases refl_trans_gen_iff_eq_or_trans_gen.1 ab with rfl | ab,
  { exact ⟨_, aa, refl_trans_gen.refl⟩ },
  { exact let ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab in
    ⟨b₂, bb, h.to_refl⟩ }
end

theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₂} (ab : reaches f₂ a₂ b₂) :
  ∃ c₁ c₂, reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ reaches f₁ a₁ c₁ :=
begin
  induction ab with c₂ d₂ ac cd IH,
  { exact ⟨_, _, refl_trans_gen.refl, aa, refl_trans_gen.refl⟩ },
  { rcases IH with ⟨e₁, e₂, ce, ee, ae⟩,
    rcases refl_trans_gen.cases_head ce with rfl | ⟨d', cd', de⟩,
    { have := H ee, revert this,
      cases eg : f₁ e₁ with g₁; simp only [respects, and_imp, exists_imp_distrib],
      { intro c0, cases cd.symm.trans c0 },
      { intros g₂ gg cg,
        rcases trans_gen.head'_iff.1 cg with ⟨d', cd', dg⟩,
        cases option.mem_unique cd cd',
        exact ⟨_, _, dg, gg, ae.tail eg⟩ } },
    { cases option.mem_unique cd cd',
      exact ⟨_, _, de, ee, ae⟩ } }
end

theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ b₁ a₂} (aa : tr a₁ a₂)
  (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ :=
begin
  cases mem_eval.1 ab with ab b0,
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩,
  refine ⟨_, bb, mem_eval.2 ⟨ab, _⟩⟩,
  have := H bb, rwa b0 at this
end

theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ b₂ a₂} (aa : tr a₁ a₂)
  (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ :=
begin
  cases mem_eval.1 ab with ab b0,
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩,
  cases (refl_trans_gen_iff_eq
    (by exact option.eq_none_iff_forall_not_mem.1 b0)).1 bc,
  refine ⟨_, cc, mem_eval.2 ⟨ac, _⟩⟩,
  have := H cc, cases f₁ c₁ with d₁, {refl},
  rcases this with ⟨d₂, dd, bd⟩,
  rcases trans_gen.head'_iff.1 bd with ⟨e, h, _⟩,
  cases b0.symm.trans h
end

theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) :
  (eval f₂ a₂).dom ↔ (eval f₁ a₁).dom :=
⟨λ h, let ⟨b₂, tr, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩ in h,
 λ h, let ⟨b₂, tr, h, _⟩ := tr_eval H aa ⟨h, rfl⟩ in h⟩

/-- A simpler version of `respects` when the state transition relation `tr` is a function. -/
def frespects {σ₁ σ₂} (f₂ : σ₂ → option σ₂) (tr : σ₁ → σ₂) (a₂ : σ₂) : option σ₁ → Prop
| (some b₁) := reaches₁ f₂ a₂ (tr b₁)
| none := f₂ a₂ = none

theorem frespects_eq {σ₁ σ₂} {f₂ : σ₂ → option σ₂} {tr : σ₁ → σ₂} {a₂ b₂}
  (h : f₂ a₂ = f₂ b₂) : ∀ {b₁}, frespects f₂ tr a₂ b₁ ↔ frespects f₂ tr b₂ b₁
| (some b₁) := reaches₁_eq h
| none := by unfold frespects; rw h

theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂} :
  respects f₁ f₂ (λ a b, tr a = b) ↔ ∀ ⦃a₁⦄, frespects f₂ tr (tr a₁) (f₁ a₁) :=
forall_congr $ λ a₁, by cases f₁ a₁; simp only [frespects, respects, exists_eq_left', forall_eq']

theorem tr_eval' {σ₁ σ₂}
  (f₁ : σ₁ → option σ₁) (f₂ : σ₂ → option σ₂) (tr : σ₁ → σ₂)
  (H : respects f₁ f₂ (λ a b, tr a = b))
  (a₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ :=
roption.ext $ λ b₂,
 ⟨λ h, let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h in
    (roption.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
  λ h, begin
    rcases (roption.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩,
    rcases tr_eval H rfl ab with ⟨_, rfl, h⟩,
    rwa bb at h
  end⟩

/-!
## The TM0 model

A TM0 turing machine is essentially a Post-Turing machine, adapted for type theory.

A Post-Turing machine with symbol type `Γ` and label type `Λ` is a function
`Λ → Γ → option (Λ × stmt)`, where a `stmt` can be either `move left`, `move right` or `write a`
for `a : Γ`. The machine works over a "tape", a doubly-infinite sequence of elements of `Γ`, and
an instantaneous configuration, `cfg`, is a label `q : Λ` indicating the current internal state of
the machine, and a `tape Γ` (which is essentially `ℤ →₀ Γ`). The evolution is described by the
`step` function:

* If `M q T.head = none`, then the machine halts.
* If `M q T.head = some (q', s)`, then the machine performs action `s : stmt` and then transitions
  to state `q'`.

The initial state takes a `list Γ` and produces a `tape Γ` where the head of the list is the head
of the tape and the rest of the list extends to the right, with the left side all blank. The final
state takes the entire right side of the tape right or equal to the current position of the
machine. (This is actually a `list_blank Γ`, not a `list Γ`, because we don't know, at this level
of generality, where the output ends. If equality to `default Γ` is decidable we can trim the list
to remove the infinite tail of blanks.)
-/

namespace TM0

section
parameters (Γ : Type*) [inhabited Γ] -- type of tape symbols
parameters (Λ : Type*) [inhabited Λ] -- type of "labels" or TM states

/-- A Turing machine "statement" is just a command to either move
  left or right, or write a symbol on the tape. -/
inductive stmt
| move : dir → stmt
| write : Γ → stmt

instance stmt.inhabited : inhabited stmt := ⟨stmt.write (default _)⟩

/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Λ` and a `stmt` describing what to do,
  either a move left or right, or a write command.

  Both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
@[nolint unused_arguments] -- [inhabited Λ]: this is a deliberate addition, see comment
def machine := Λ → Γ → option (Λ × stmt)

instance machine.inhabited : inhabited machine := by unfold machine; apply_instance

/-- The configuration state of a Turing machine during operation
  consists of a label (machine state), and a tape, represented in
  the form `(a, L, R)` meaning the tape looks like `L.rev ++ [a] ++ R`
  with the machine currently reading the `a`. The lists are
  automatically extended with blanks as the machine moves around. -/
structure cfg :=
(q : Λ)
(tape : tape Γ)

instance cfg.inhabited : inhabited cfg := ⟨⟨default _, default _⟩⟩

parameters {Γ Λ}
/-- Execution semantics of the Turing machine. -/
def step (M : machine) : cfg → option cfg
| ⟨q, T⟩ := (M q T.1).map (λ ⟨q', a⟩, ⟨q',
  match a with
  | stmt.move d := T.move d
  | stmt.write a := T.write a
  end⟩)

/-- The statement `reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def reaches (M : machine) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

/-- The initial configuration. -/
def init (l : list Γ) : cfg :=
⟨default Λ, tape.mk₁ l⟩

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : machine) (l : list Γ) : roption (list_blank Γ) :=
(eval (step M) (init l)).map (λ c, c.tape.right₀)

/-- The raw definition of a Turing machine does not require that
  `Γ` and `Λ` are finite, and in practice we will be interested
  in the infinite `Λ` case. We recover instead a notion of
  "effectively finite" Turing machines, which only make use of a
  finite subset of their states. We say that a set `S ⊆ Λ`
  supports a Turing machine `M` if `S` is closed under the
  transition function and contains the initial state. -/
def supports (M : machine) (S : set Λ) :=
default Λ ∈ S ∧ ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S

theorem step_supports (M : machine) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.q ∈ S → c'.q ∈ S
| ⟨q, T⟩ c' h₁ h₂ := begin
  rcases option.map_eq_some'.1 h₁ with ⟨⟨q', a⟩, h, rfl⟩,
  exact ss.2 h h₂,
end

theorem univ_supports (M : machine) : supports M set.univ :=
⟨trivial, λ q a q' s h₁ h₂, trivial⟩

end

section
variables {Γ : Type*} [inhabited Γ]
variables {Γ' : Type*} [inhabited Γ']
variables {Λ : Type*} [inhabited Λ]
variables {Λ' : Type*} [inhabited Λ']

/-- Map a TM statement across a function. This does nothing to move statements and maps the write
values. -/
def stmt.map (f : pointed_map Γ Γ') : stmt Γ → stmt Γ'
| (stmt.move d)  := stmt.move d
| (stmt.write a) := stmt.write (f a)

/-- Map a configuration across a function, given `f : Γ → Γ'` a map of the alphabets and
`g : Λ → Λ'` a map of the machine states. -/
def cfg.map (f : pointed_map Γ Γ') (g : Λ → Λ') : cfg Γ Λ → cfg Γ' Λ'
| ⟨q, T⟩ := ⟨g q, T.map f⟩

variables (M : machine Γ Λ)
  (f₁ : pointed_map Γ Γ') (f₂ : pointed_map Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ)

/-- Because the state transition function uses the alphabet and machine states in both the input
and output, to map a machine from one alphabet and machine state space to another we need functions
in both directions, essentially an `equiv` without the laws. -/
def machine.map : machine Γ' Λ'
| q l := (M (g₂ q) (f₂ l)).map (prod.map g₁ (stmt.map f₁))

theorem machine.map_step {S : set Λ}
  (f₂₁ : function.right_inverse f₁ f₂)
  (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
  ∀ c : cfg Γ Λ, c.q ∈ S →
    (step M c).map (cfg.map f₁ g₁) =
    step (M.map f₁ f₂ g₁ g₂) (cfg.map f₁ g₁ c)
| ⟨q, T⟩ h := begin
  unfold step machine.map cfg.map,
  simp only [turing.tape.map_fst, g₂₁ q h, f₂₁ _],
  rcases M q T.1 with _|⟨q', d|a⟩, {refl},
  { simp only [step, cfg.map, option.map_some', tape.map_move f₁], refl },
  { simp only [step, cfg.map, option.map_some', tape.map_write], refl }
end

theorem map_init (g₁ : pointed_map Λ Λ') (l : list Γ) :
  (init l).map f₁ g₁ = init (l.map f₁) :=
congr (congr_arg cfg.mk g₁.map_pt) (tape.map_mk₁ _ _)

theorem machine.map_respects
  (g₁ : pointed_map Λ Λ') (g₂ : Λ' → Λ)
  {S} (ss : supports M S)
  (f₂₁ : function.right_inverse f₁ f₂)
  (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
  respects (step M) (step (M.map f₁ f₂ g₁ g₂))
    (λ a b, a.q ∈ S ∧ cfg.map f₁ g₁ a = b)
| c _ ⟨cs, rfl⟩ := begin
  cases e : step M c with c'; unfold respects,
  { rw [← M.map_step f₁ f₂ g₁ g₂ f₂₁ g₂₁ _ cs, e], refl },
  { refine ⟨_, ⟨step_supports M ss e cs, rfl⟩, trans_gen.single _⟩,
    rw [← M.map_step f₁ f₂ g₁ g₂ f₂₁ g₂₁ _ cs, e], exact rfl }
end

end

end TM0

/-!
## The TM1 model

The TM1 model is a simplification and extension of TM0 (Post-Turing model) in the direction of
Wang B-machines. The machine's internal state is extended with a (finite) store `σ` of variables
that may be accessed and updated at any time.

A machine is given by a `Λ` indexed set of procedures or functions. Each function has a body which
is a `stmt`. Most of the regular commands are allowed to use the current value `a` of the local
variables and the value `T.head` on the tape to calculate what to write or how to change local
state, but the statements themselves have a fixed structure. The `stmt`s can be as follows:

* `move d q`: move left or right, and then do `q`
* `write (f : Γ → σ → Γ) q`: write `f a T.head` to the tape, then do `q`
* `load (f : Γ → σ → σ) q`: change the internal state to `f a T.head`
* `branch (f : Γ → σ → bool) qtrue qfalse`: If `f a T.head` is true, do `qtrue`, else `qfalse`
* `goto (f : Γ → σ → Λ)`: Go to label `f a T.head`
* `halt`: Transition to the halting state, which halts on the following step

Note that here most statements do not have labels; `goto` commands can only go to a new function.
Only the `goto` and `halt` statements actually take a step; the rest is done by recursion on
statements and so take 0 steps. (There is a uniform bound on many statements can be executed before
the next `goto`, so this is an `O(1)` speedup with the constant depending on the machine.)

The `halt` command has a one step stutter before actually halting so that any changes made before
the halt have a chance to be "committed", since the `eval` relation uses the final configuration
before the halt as the output, and `move` and `write` etc. take 0 steps in this model.
-/

namespace TM1

section
parameters (Γ : Type*) [inhabited Γ] -- Type of tape symbols
parameters (Λ : Type*) -- Type of function labels
parameters (σ : Type*) -- Type of variable settings

/-- The TM1 model is a simplification and extension of TM0
  (Post-Turing model) in the direction of Wang B-machines. The machine's
  internal state is extended with a (finite) store `σ` of variables
  that may be accessed and updated at any time.
  A machine is given by a `Λ` indexed set of procedures or functions.
  Each function has a body which is a `stmt`, which can either be a
  `move` or `write` command, a `branch` (if statement based on the
  current tape value), a `load` (set the variable value),
  a `goto` (call another function), or `halt`. Note that here
  most statements do not have labels; `goto` commands can only
  go to a new function. All commands have access to the variable value
  and current tape value. -/
inductive stmt
| move : dir → stmt → stmt
| write : (Γ → σ → Γ) → stmt → stmt
| load : (Γ → σ → σ) → stmt → stmt
| branch : (Γ → σ → bool) → stmt → stmt → stmt
| goto : (Γ → σ → Λ) → stmt
| halt : stmt
open stmt

instance stmt.inhabited : inhabited stmt := ⟨halt⟩

/-- The configuration of a TM1 machine is given by the currently
  evaluating statement, the variable store value, and the tape. -/
structure cfg :=
(l : option Λ)
(var : σ)
(tape : tape Γ)

instance cfg.inhabited [inhabited σ] : inhabited cfg := ⟨⟨default _, default _, default _⟩⟩

parameters {Γ Λ σ}
/-- The semantics of TM1 evaluation. -/
def step_aux : stmt → σ → tape Γ → cfg
| (move d q)       v T := step_aux q v (T.move d)
| (write a q)      v T := step_aux q v (T.write (a T.1 v))
| (load s q)       v T := step_aux q (s T.1 v) T
| (branch p q₁ q₂) v T := cond (p T.1 v) (step_aux q₁ v T) (step_aux q₂ v T)
| (goto l)         v T := ⟨some (l T.1 v), v, T⟩
| halt             v T := ⟨none, v, T⟩

/-- The state transition function. -/
def step (M : Λ → stmt) : cfg → option cfg
| ⟨none,   v, T⟩ := none
| ⟨some l, v, T⟩ := some (step_aux (M l) v T)

/-- A set `S` of labels supports the statement `q` if all the `goto`
  statements in `q` refer only to other functions in `S`. -/
def supports_stmt (S : finset Λ) : stmt → Prop
| (move d q)       := supports_stmt q
| (write a q)      := supports_stmt q
| (load s q)       := supports_stmt q
| (branch p q₁ q₂) := supports_stmt q₁ ∧ supports_stmt q₂
| (goto l)         := ∀ a v, l a v ∈ S
| halt             := true

open_locale classical
/-- The subterm closure of a statement. -/
noncomputable def stmts₁ : stmt → finset stmt
| Q@(move d q)       := insert Q (stmts₁ q)
| Q@(write a q)      := insert Q (stmts₁ q)
| Q@(load s q)       := insert Q (stmts₁ q)
| Q@(branch p q₁ q₂) := insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
| Q                  := {Q}

theorem stmts₁_self {q} : q ∈ stmts₁ q :=
by cases q; apply_rules [finset.mem_insert_self, finset.mem_singleton_self]

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ q IH _ q IH _ q IH;
    simp only [stmts₁] at h₁₂ ⊢;
    simp only [finset.mem_insert, finset.mem_union, finset.mem_singleton] at h₁₂,
  iterate 3 {
    rcases h₁₂ with rfl | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (IH h₁₂) } },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    rcases h₁₂ with rfl | h₁₂ | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (finset.mem_union_left _ $ IH₁ h₁₂) },
    { exact finset.mem_insert_of_mem (finset.mem_union_right _ $ IH₂ h₁₂) } },
  case TM1.stmt.goto : l {
    subst h₁₂, exact h₀₁ },
  case TM1.stmt.halt {
    subst h₁₂, exact h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂ with _ q IH _ q IH _ q IH;
    simp only [stmts₁, supports_stmt, finset.mem_insert, finset.mem_union,
      finset.mem_singleton] at h hs,
  iterate 3 { rcases h with rfl | h; [exact hs, exact IH h hs] },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    rcases h with rfl | h | h, exacts [hs, IH₁ h hs.1, IH₂ h hs.2] },
  case TM1.stmt.goto : l { subst h, exact hs },
  case TM1.stmt.halt { subst h, trivial }
end

/-- The set of all statements in a turing machine, plus one extra value `none` representing the
halt state. This is used in the TM1 to TM0 reduction. -/
noncomputable def stmts (M : Λ → stmt) (S : finset Λ) : finset (option stmt) :=
(S.bUnion (λ q, stmts₁ (M q))).insert_none

theorem stmts_trans {M : Λ → stmt} {S q₁ q₂}
  (h₁ : q₁ ∈ stmts₁ q₂) : some q₂ ∈ stmts M S → some q₁ ∈ stmts M S :=
by simp only [stmts, finset.mem_insert_none, finset.mem_bUnion,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

variable [inhabited Λ]

/-- A set `S` of labels supports machine `M` if all the `goto`
  statements in the functions in `S` refer only to other functions
  in `S`. -/
def supports (M : Λ → stmt) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ q ∈ S, supports_stmt S (M q)

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q :=
by simp only [stmts, finset.mem_insert_none, finset.mem_bUnion,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.l ∈ S.insert_none → c'.l ∈ S.insert_none
| ⟨some l₁, v, T⟩ c' h₁ h₂ := begin
  replace h₂ := ss.2 _ (finset.some_mem_insert_none.1 h₂),
  simp only [step, option.mem_def] at h₁, subst c',
  revert h₂, induction M l₁ with _ q IH _ q IH _ q IH generalizing v T;
    intro hs,
  iterate 3 { exact IH _ _ hs },
  case TM1.stmt.branch : p q₁' q₂' IH₁ IH₂ {
    unfold step_aux, cases p T.1 v,
    { exact IH₂ _ _ hs.2 },
    { exact IH₁ _ _ hs.1 } },
  case TM1.stmt.goto { exact finset.some_mem_insert_none.2 (hs _ _) },
  case TM1.stmt.halt { apply multiset.mem_cons_self }
end

variable [inhabited σ]

/-- The initial state, given a finite input that is placed on the tape starting at the TM head and
going to the right. -/
def init (l : list Γ) : cfg :=
⟨some (default _), default _, tape.mk₁ l⟩

/-- Evaluate a TM to completion, resulting in an output list on the tape (with an indeterminate
number of blanks on the end). -/
def eval (M : Λ → stmt) (l : list Γ) : roption (list_blank Γ) :=
(eval (step M) (init l)).map (λ c, c.tape.right₀)

end

end TM1

/-!
## TM1 emulator in TM0

To prove that TM1 computable functions are TM0 computable, we need to reduce each TM1 program to a
TM0 program. So suppose a TM1 program is given. We take the following:

* The alphabet `Γ` is the same for both TM1 and TM0
* The set of states `Λ'` is defined to be `option stmt₁ × σ`, that is, a TM1 statement or `none`
  representing halt, and the possible settings of the internal variables.
  Note that this is an infinite set, because `stmt₁` is infinite. This is okay because we assume
  that from the initial TM1 state, only finitely many other labels are reachable, and there are
  only finitely many statements that appear in all of these functions.

Even though `stmt₁` contains a statement called `halt`, we must separate it from `none`
(`some halt` steps to `none` and `none` actually halts) because there is a one step stutter in the
TM1 semantics.
-/

namespace TM1to0

section
parameters {Γ : Type*} [inhabited Γ]
parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₁` := TM1.stmt Γ Λ σ
local notation `cfg₁` := TM1.cfg Γ Λ σ
local notation `stmt₀` := TM0.stmt Γ

parameters (M : Λ → stmt₁)
include M

/-- The base machine state space is a pair of an `option stmt₁` representing the current program
to be executed, or `none` for the halt state, and a `σ` which is the local state (stored in the TM,
not the tape). Because there are an infinite number of programs, this state space is infinite, but
for a finitely supported TM1 machine and a finite type `σ`, only finitely many of these states are
reachable. -/
@[nolint unused_arguments] -- [inhabited Λ] [inhabited σ] (M : Λ → stmt₁): We need the M assumption
-- because of the inhabited instance, but we could avoid the inhabited instances on Λ and σ here.
-- But they are parameters so we cannot easily skip them for just this definition.
def Λ' := option stmt₁ × σ
instance : inhabited Λ' := ⟨(some (M (default _)), default _)⟩

open TM0.stmt

/-- The core TM1 → TM0 translation function. Here `s` is the current value on the tape, and the
`stmt₁` is the TM1 statement to translate, with local state `v : σ`. We evaluate all regular
instructions recursively until we reach either a `move` or `write` command, or a `goto`; in the
latter case we emit a dummy `write s` step and transition to the new target location. -/
def tr_aux (s : Γ) : stmt₁ → σ → Λ' × stmt₀
| (TM1.stmt.move d q)       v := ((some q, v), move d)
| (TM1.stmt.write a q)      v := ((some q, v), write (a s v))
| (TM1.stmt.load a q)       v := tr_aux q (a s v)
| (TM1.stmt.branch p q₁ q₂) v := cond (p s v) (tr_aux q₁ v) (tr_aux q₂ v)
| (TM1.stmt.goto l)         v := ((some (M (l s v)), v), write s)
| TM1.stmt.halt             v := ((none, v), write s)

local notation `cfg₀` := TM0.cfg Γ Λ'

/-- The translated TM0 machine (given the TM1 machine input). -/
def tr : TM0.machine Γ Λ'
| (none,   v) s := none
| (some q, v) s := some (tr_aux s q v)

/-- Translate configurations from TM1 to TM0. -/
def tr_cfg : cfg₁ → cfg₀
| ⟨l, v, T⟩ := ⟨(l.map M, v), T⟩

theorem tr_respects : respects (TM1.step M) (TM0.step tr)
  (λ c₁ c₂, tr_cfg c₁ = c₂) :=
fun_respects.2 $ λ ⟨l₁, v, T⟩, begin
  cases l₁ with l₁, {exact rfl},
  unfold tr_cfg TM1.step frespects option.map function.comp option.bind,
  induction M l₁ with _ q IH _ q IH _ q IH generalizing v T,
  case TM1.stmt.move  : d q IH { exact trans_gen.head rfl (IH _ _) },
  case TM1.stmt.write : a q IH { exact trans_gen.head rfl (IH _ _) },
  case TM1.stmt.load : a q IH { exact (reaches₁_eq (by refl)).2 (IH _ _) },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    unfold TM1.step_aux, cases e : p T.1 v,
    { exact (reaches₁_eq (by simp only [TM0.step, tr, tr_aux, e]; refl)).2 (IH₂ _ _) },
    { exact (reaches₁_eq (by simp only [TM0.step, tr, tr_aux, e]; refl)).2 (IH₁ _ _) } },
  iterate 2 {
    exact trans_gen.single (congr_arg some
      (congr (congr_arg TM0.cfg.mk rfl) (tape.write_self T))) }
end

theorem tr_eval (l : list Γ) : TM0.eval tr l = TM1.eval M l :=
(congr_arg _ (tr_eval' _ _ _ tr_respects ⟨some _, _, _⟩)).trans begin
  rw [roption.map_eq_map, roption.map_map, TM1.eval],
  congr' with ⟨⟩, refl
end

variables [fintype σ]
/-- Given a finite set of accessible `Λ` machine states, there is a finite set of accessible
machine states in the target (even though the type `Λ'` is infinite). -/
noncomputable def tr_stmts (S : finset Λ) : finset Λ' :=
(TM1.stmts M S).product finset.univ

open_locale classical
local attribute [simp] TM1.stmts₁_self
theorem tr_supports {S : finset Λ} (ss : TM1.supports M S) :
  TM0.supports tr (↑(tr_stmts S)) :=
⟨finset.mem_product.2 ⟨finset.some_mem_insert_none.2
  (finset.mem_bUnion.2 ⟨_, ss.1, TM1.stmts₁_self⟩),
  finset.mem_univ _⟩,
 λ q a q' s h₁ h₂, begin
  rcases q with ⟨_|q, v⟩, {cases h₁},
  cases q' with q' v', simp only [tr_stmts, finset.mem_coe,
    finset.mem_product, finset.mem_univ, and_true] at h₂ ⊢,
  cases q', {exact multiset.mem_cons_self _ _},
  simp only [tr, option.mem_def] at h₁,
  have := TM1.stmts_supports_stmt ss h₂,
  revert this, induction q generalizing v; intro hs,
  case TM1.stmt.move : d q {
    cases h₁, refine TM1.stmts_trans _ h₂,
    unfold TM1.stmts₁,
    exact finset.mem_insert_of_mem TM1.stmts₁_self },
  case TM1.stmt.write : b q {
    cases h₁, refine TM1.stmts_trans _ h₂,
    unfold TM1.stmts₁,
    exact finset.mem_insert_of_mem TM1.stmts₁_self },
  case TM1.stmt.load : b q IH {
    refine IH (TM1.stmts_trans _ h₂) _ h₁ hs,
    unfold TM1.stmts₁,
    exact finset.mem_insert_of_mem TM1.stmts₁_self },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    change cond (p a v) _ _ = ((some q', v'), s) at h₁,
    cases p a v,
    { refine IH₂ (TM1.stmts_trans _ h₂) _ h₁ hs.2,
      unfold TM1.stmts₁,
      exact finset.mem_insert_of_mem (finset.mem_union_right _ TM1.stmts₁_self) },
    { refine IH₁ (TM1.stmts_trans _ h₂) _ h₁ hs.1,
      unfold TM1.stmts₁,
      exact finset.mem_insert_of_mem (finset.mem_union_left _ TM1.stmts₁_self) } },
  case TM1.stmt.goto : l {
    cases h₁, exact finset.some_mem_insert_none.2
      (finset.mem_bUnion.2 ⟨_, hs _ _, TM1.stmts₁_self⟩) },
  case TM1.stmt.halt { cases h₁ }
end⟩

end
end TM1to0

/-!
## TM1(Γ) emulator in TM1(bool)

The most parsimonious Turing machine model that is still Turing complete is `TM0` with `Γ = bool`.
Because our construction in the previous section reducing `TM1` to `TM0` doesn't change the
alphabet, we can do the alphabet reduction on `TM1` instead of `TM0` directly.

The basic idea is to use a bijection between `Γ` and a subset of `vector bool n`, where `n` is a
fixed constant. Each tape element is represented as a block of `n` bools. Whenever the machine
wants to read a symbol from the tape, it traverses over the block, performing `n` `branch`
instructions to each any of the `2^n` results.

For the `write` instruction, we have to use a `goto` because we need to follow a different code
path depending on the local state, which is not available in the TM1 model, so instead we jump to
a label computed using the read value and the local state, which performs the writing and returns
to normal execution.

Emulation overhead is `O(1)`. If not for the above `write` behavior it would be 1-1 because we are
exploiting the 0-step behavior of regular commands to avoid taking steps, but there are
nevertheless a bounded number of `write` calls between `goto` statements because TM1 statements are
finitely long.
-/

namespace TM1to1
open TM1

section
parameters {Γ : Type*} [inhabited Γ]

theorem exists_enc_dec [fintype Γ] :
  ∃ n (enc : Γ → vector bool n) (dec : vector bool n → Γ),
    enc (default _) = vector.repeat ff n ∧ ∀ a, dec (enc a) = a :=
begin
  rcases fintype.exists_equiv_fin Γ with ⟨n, ⟨F⟩⟩,
  let G : fin n ↪ fin n → bool := ⟨λ a b, a = b,
    λ a b h, of_to_bool_true $ (congr_fun h b).trans $ to_bool_tt rfl⟩,
  let H := (F.to_embedding.trans G).trans
    (equiv.vector_equiv_fin _ _).symm.to_embedding,
  classical,
  let enc := H.set_value (default _) (vector.repeat ff n),
  exact ⟨_, enc, function.inv_fun enc,
    H.set_value_eq _ _, function.left_inverse_inv_fun enc.2⟩
end

parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₁` := stmt Γ Λ σ
local notation `cfg₁` := cfg Γ Λ σ

/-- The configuration state of the TM. -/
inductive Λ' : Type (max u_1 u_2 u_3)
| normal : Λ → Λ'
| write : Γ → stmt₁ → Λ'
instance : inhabited Λ' := ⟨Λ'.normal (default _)⟩

local notation `stmt'` := stmt bool Λ' σ
local notation `cfg'` := cfg bool Λ' σ

/-- Read a vector of length `n` from the tape. -/
def read_aux : ∀ n, (vector bool n → stmt') → stmt'
| 0     f := f vector.nil
| (i+1) f := stmt.branch (λ a s, a)
    (stmt.move dir.right $ read_aux i (λ v, f (tt ::ᵥ v)))
    (stmt.move dir.right $ read_aux i (λ v, f (ff ::ᵥ v)))

parameters {n : ℕ} (enc : Γ → vector bool n) (dec : vector bool n → Γ)

/-- A move left or right corresponds to `n` moves across the super-cell. -/
def move (d : dir) (q : stmt') : stmt' := (stmt.move d)^[n] q

/-- To read a symbol from the tape, we use `read_aux` to traverse the symbol,
then return to the original position with `n` moves to the left. -/
def read (f : Γ → stmt') : stmt' :=
read_aux n (λ v, move dir.left $ f (dec v))

/-- Write a list of bools on the tape. -/
def write : list bool → stmt' → stmt'
| []       q := q
| (a :: l) q := stmt.write (λ _ _, a) $ stmt.move dir.right $ write l q

/-- Translate a normal instruction. For the `write` command, we use a `goto` indirection so that
we can access the current value of the tape. -/
def tr_normal : stmt₁ → stmt'
| (stmt.move d q)       := move d $ tr_normal q
| (stmt.write f q)      := read $ λ a, stmt.goto $ λ _ s, Λ'.write (f a s) q
| (stmt.load f q)       := read $ λ a, stmt.load (λ _ s, f a s) $ tr_normal q
| (stmt.branch p q₁ q₂) := read $ λ a, stmt.branch (λ _ s, p a s) (tr_normal q₁) (tr_normal q₂)
| (stmt.goto l)         := read $ λ a, stmt.goto $ λ _ s, Λ'.normal (l a s)
| stmt.halt             := stmt.halt

theorem step_aux_move (d q v T) :
  step_aux (move d q) v T =
  step_aux q v ((tape.move d)^[n] T) :=
begin
  suffices : ∀ i,
    step_aux (stmt.move d^[i] q) v T =
    step_aux q v (tape.move d^[i] T), from this n,
  intro, induction i with i IH generalizing T, {refl},
  rw [iterate_succ', step_aux, IH, iterate_succ]
end

theorem supports_stmt_move {S d q} :
  supports_stmt S (move d q) = supports_stmt S q :=
suffices ∀ {i}, supports_stmt S (stmt.move d^[i] q) = _, from this,
by intro; induction i generalizing q; simp only [*, iterate]; refl

theorem supports_stmt_write {S l q} :
  supports_stmt S (write l q) = supports_stmt S q :=
by induction l with a l IH; simp only [write, supports_stmt, *]

theorem supports_stmt_read {S} : ∀ {f : Γ → stmt'},
  (∀ a, supports_stmt S (f a)) → supports_stmt S (read f) :=
suffices ∀ i (f : vector bool i → stmt'),
  (∀ v, supports_stmt S (f v)) → supports_stmt S (read_aux i f),
from λ f hf, this n _ (by intro; simp only [supports_stmt_move, hf]),
λ i f hf, begin
  induction i with i IH, {exact hf _},
  split; apply IH; intro; apply hf,
end

parameter (enc0 : enc (default _) = vector.repeat ff n)

section
parameter {enc}
include enc0

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def tr_tape' (L R : list_blank Γ) : tape bool :=
begin
  refine tape.mk'
    (L.bind (λ x, (enc x).to_list.reverse) ⟨n, _⟩)
    (R.bind (λ x, (enc x).to_list) ⟨n, _⟩);
  simp only [enc0, vector.repeat,
    list.reverse_repeat, bool.default_bool, vector.to_list_mk]
end

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def tr_tape (T : tape Γ) : tape bool := tr_tape' T.left T.right₀

theorem tr_tape_mk' (L R : list_blank Γ) : tr_tape (tape.mk' L R) = tr_tape' L R :=
by simp only [tr_tape, tape.mk'_left, tape.mk'_right₀]

end

parameters (M : Λ → stmt₁)

/-- The top level program. -/
def tr : Λ' → stmt'
| (Λ'.normal l)  := tr_normal (M l)
| (Λ'.write a q) := write (enc a).to_list $ move dir.left $ tr_normal q

/-- The machine configuration translation. -/
def tr_cfg : cfg₁ → cfg'
| ⟨l, v, T⟩ := ⟨l.map Λ'.normal, v, tr_tape T⟩

parameter {enc}
include enc0

theorem tr_tape'_move_left (L R) :
  (tape.move dir.left)^[n] (tr_tape' L R) =
  (tr_tape' L.tail (R.cons L.head)) :=
begin
  obtain ⟨a, L, rfl⟩ := L.exists_cons,
  simp only [tr_tape', list_blank.cons_bind, list_blank.head_cons, list_blank.tail_cons],
  suffices : ∀ {L' R' l₁ l₂}
    (e : vector.to_list (enc a) = list.reverse_core l₁ l₂),
    tape.move dir.left^[l₁.length]
      (tape.mk' (list_blank.append l₁ L') (list_blank.append l₂ R')) =
    tape.mk' L' (list_blank.append (vector.to_list (enc a)) R'),
  { simpa only [list.length_reverse, vector.to_list_length]
      using this (list.reverse_reverse _).symm },
  intros, induction l₁ with b l₁ IH generalizing l₂,
  { cases e, refl },
  simp only [list.length, list.cons_append, iterate_succ_apply],
  convert IH e,
  simp only [list_blank.tail_cons, list_blank.append, tape.move_left_mk', list_blank.head_cons]
end

theorem tr_tape'_move_right (L R) :
  (tape.move dir.right)^[n] (tr_tape' L R) =
  (tr_tape' (L.cons R.head) R.tail) :=
begin
  suffices : ∀ i L, (tape.move dir.right)^[i] ((tape.move dir.left)^[i] L) = L,
  { refine (eq.symm _).trans (this n _),
    simp only [tr_tape'_move_left, list_blank.cons_head_tail,
      list_blank.head_cons, list_blank.tail_cons] },
  intros, induction i with i IH, {refl},
  rw [iterate_succ_apply, iterate_succ_apply', tape.move_left_right, IH]
end

theorem step_aux_write (q v a b L R) :
  step_aux (write (enc a).to_list q) v (tr_tape' L (list_blank.cons b R)) =
  step_aux q v (tr_tape' (list_blank.cons a L) R) :=
begin
  simp only [tr_tape', list.cons_bind, list.append_assoc],
  suffices : ∀ {L' R'} (l₁ l₂ l₂' : list bool)
    (e : l₂'.length = l₂.length),
    step_aux (write l₂ q) v (tape.mk' (list_blank.append l₁ L') (list_blank.append l₂' R')) =
    step_aux q v (tape.mk' (L'.append (list.reverse_core l₂ l₁)) R'),
  { convert this [] _ _ ((enc b).2.trans (enc a).2.symm);
    rw list_blank.cons_bind; refl },
  clear a b L R, intros,
  induction l₂ with a l₂ IH generalizing l₁ l₂',
  { cases list.length_eq_zero.1 e, refl },
  cases l₂' with b l₂'; injection e with e,
  dunfold write step_aux,
  convert IH _ _ e using 1,
  simp only [list_blank.head_cons, list_blank.tail_cons,
    list_blank.append, tape.move_right_mk', tape.write_mk']
end

parameters (encdec : ∀ a, dec (enc a) = a)
include encdec

theorem step_aux_read (f v L R) :
  step_aux (read f) v (tr_tape' L R) =
  step_aux (f R.head) v (tr_tape' L R) :=
begin
  suffices : ∀ f,
    step_aux (read_aux n f) v (tr_tape' enc0 L R) =
    step_aux (f (enc R.head)) v
      (tr_tape' enc0 (L.cons R.head) R.tail),
  { rw [read, this, step_aux_move, encdec, tr_tape'_move_left enc0],
    simp only [list_blank.head_cons, list_blank.cons_head_tail, list_blank.tail_cons] },
  obtain ⟨a, R, rfl⟩ := R.exists_cons,
  simp only [list_blank.head_cons, list_blank.tail_cons,
    tr_tape', list_blank.cons_bind, list_blank.append_assoc],
  suffices : ∀ i f L' R' l₁ l₂ h,
    step_aux (read_aux i f) v
      (tape.mk' (list_blank.append l₁ L') (list_blank.append l₂ R')) =
    step_aux (f ⟨l₂, h⟩) v
      (tape.mk' (list_blank.append (l₂.reverse_core l₁) L') R'),
  { intro f, convert this n f _ _ _ _ (enc a).2; simp },
  clear f L a R, intros, subst i,
  induction l₂ with a l₂ IH generalizing l₁, {refl},
  transitivity step_aux
    (read_aux l₂.length (λ v, f (a ::ᵥ v))) v
    (tape.mk' ((L'.append l₁).cons a) (R'.append l₂)),
  { dsimp [read_aux, step_aux], simp, cases a; refl },
  rw [← list_blank.append, IH], refl
end

theorem tr_respects : respects (step M) (step tr)
  (λ c₁ c₂, tr_cfg c₁ = c₂) :=
fun_respects.2 $ λ ⟨l₁, v, T⟩, begin
  obtain ⟨L, R, rfl⟩ := T.exists_mk',
  cases l₁ with l₁, {exact rfl},
  suffices : ∀ q R, reaches (step (tr enc dec M))
    (step_aux (tr_normal dec q) v (tr_tape' enc0 L R))
    (tr_cfg enc0 (step_aux q v (tape.mk' L R))),
  { refine trans_gen.head' rfl _, rw tr_tape_mk', exact this _ R },
  clear R l₁, intros,
  induction q with _ q IH _ q IH _ q IH generalizing v L R,
  case TM1.stmt.move : d q IH {
    cases d; simp only [tr_normal, iterate, step_aux_move, step_aux,
      list_blank.head_cons, tape.move_left_mk',
      list_blank.cons_head_tail, list_blank.tail_cons,
      tr_tape'_move_left enc0, tr_tape'_move_right enc0];
      apply IH },
  case TM1.stmt.write : f q IH {
    simp only [tr_normal, step_aux_read dec enc0 encdec, step_aux],
    refine refl_trans_gen.head rfl _,
    obtain ⟨a, R, rfl⟩ := R.exists_cons,
    rw [tr, tape.mk'_head, step_aux_write, list_blank.head_cons,
      step_aux_move, tr_tape'_move_left enc0, list_blank.head_cons,
      list_blank.tail_cons, tape.write_mk'],
    apply IH },
  case TM1.stmt.load : a q IH {
    simp only [tr_normal, step_aux_read dec enc0 encdec],
    apply IH },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    simp only [tr_normal, step_aux_read dec enc0 encdec, step_aux],
    cases p R.head v; [apply IH₂, apply IH₁] },
  case TM1.stmt.goto : l {
    simp only [tr_normal, step_aux_read dec enc0 encdec, step_aux, tr_cfg, tr_tape_mk'],
    apply refl_trans_gen.refl },
  case TM1.stmt.halt {
    simp only [tr_normal, step_aux, tr_cfg, step_aux_move,
      tr_tape'_move_left enc0, tr_tape'_move_right enc0, tr_tape_mk'],
    apply refl_trans_gen.refl }
end

omit enc0 encdec
open_locale classical
parameters [fintype Γ]
/-- The set of accessible `Λ'.write` machine states. -/
noncomputable def writes : stmt₁ → finset Λ'
| (stmt.move d q)       := writes q
| (stmt.write f q)      := finset.univ.image (λ a, Λ'.write a q) ∪ writes q
| (stmt.load f q)       := writes q
| (stmt.branch p q₁ q₂) := writes q₁ ∪ writes q₂
| (stmt.goto l)         := ∅
| stmt.halt             := ∅

/-- The set of accessible machine states, assuming that the input machine is supported on `S`,
are the normal states embedded from `S`, plus all write states accessible from these states. -/
noncomputable def tr_supp (S : finset Λ) : finset Λ' :=
S.bUnion (λ l, insert (Λ'.normal l) (writes (M l)))

theorem tr_supports {S} (ss : supports M S) :
  supports tr (tr_supp S) :=
⟨finset.mem_bUnion.2 ⟨_, ss.1, finset.mem_insert_self _ _⟩,
λ q h, begin
  suffices : ∀ q, supports_stmt S q →
    (∀ q' ∈ writes q, q' ∈ tr_supp M S) →
    supports_stmt (tr_supp M S) (tr_normal dec q) ∧
    ∀ q' ∈ writes q, supports_stmt (tr_supp M S) (tr enc dec M q'),
  { rcases finset.mem_bUnion.1 h with ⟨l, hl, h⟩,
    have := this _ (ss.2 _ hl) (λ q' hq,
      finset.mem_bUnion.2 ⟨_, hl, finset.mem_insert_of_mem hq⟩),
    rcases finset.mem_insert.1 h with rfl | h,
    exacts [this.1, this.2 _ h] },
  intros q hs hw, induction q,
  case TM1.stmt.move : d q IH {
    unfold writes at hw ⊢,
    replace IH := IH hs hw, refine ⟨_, IH.2⟩,
    cases d; simp only [tr_normal, iterate, supports_stmt_move, IH] },
  case TM1.stmt.write : f q IH {
    unfold writes at hw ⊢,
    simp only [finset.mem_image, finset.mem_union, finset.mem_univ,
      exists_prop, true_and] at hw ⊢,
    replace IH := IH hs (λ q hq, hw q (or.inr hq)),
    refine ⟨supports_stmt_read _ $ λ a _ s,
      hw _ (or.inl ⟨_, rfl⟩), λ q' hq, _⟩,
    rcases hq with ⟨a, q₂, rfl⟩ | hq,
    { simp only [tr, supports_stmt_write, supports_stmt_move, IH.1] },
    { exact IH.2 _ hq } },
  case TM1.stmt.load : a q IH {
    unfold writes at hw ⊢,
    replace IH := IH hs hw,
    refine ⟨supports_stmt_read _ (λ a, IH.1), IH.2⟩ },
  case TM1.stmt.branch : p q₁ q₂ IH₁ IH₂ {
    unfold writes at hw ⊢,
    simp only [finset.mem_union] at hw ⊢,
    replace IH₁ := IH₁ hs.1 (λ q hq, hw q (or.inl hq)),
    replace IH₂ := IH₂ hs.2 (λ q hq, hw q (or.inr hq)),
    exact ⟨supports_stmt_read _ (λ a, ⟨IH₁.1, IH₂.1⟩),
      λ q, or.rec (IH₁.2 _) (IH₂.2 _)⟩ },
  case TM1.stmt.goto : l {
    refine ⟨_, λ _, false.elim⟩,
    refine supports_stmt_read _ (λ a _ s, _),
    exact finset.mem_bUnion.2 ⟨_, hs _ _, finset.mem_insert_self _ _⟩ },
  case TM1.stmt.halt {
    refine ⟨_, λ _, false.elim⟩,
    simp only [supports_stmt, supports_stmt_move, tr_normal] }
end⟩

end

end TM1to1

/-!
## TM0 emulator in TM1

To establish that TM0 and TM1 are equivalent computational models, we must also have a TM0 emulator
in TM1. The main complication here is that TM0 allows an action to depend on the value at the head
and local state, while TM1 doesn't (in order to have more programming language-like semantics).
So we use a computed `goto` to go to a state that performes the desired action and then returns to
normal execution.

One issue with this is that the `halt` instruction is supposed to halt immediately, not take a step
to a halting state. To resolve this we do a check for `halt` first, then `goto` (with an
unreachable branch).
-/

namespace TM0to1

section
parameters {Γ : Type*} [inhabited Γ]
parameters {Λ : Type*} [inhabited Λ]

/-- The machine states for a TM1 emulating a TM0 machine. States of the TM0 machine are embedded
as `normal q` states, but the actual operation is split into two parts, a jump to `act s q`
followed by the action and a jump to the next `normal` state.  -/
inductive Λ'
| normal : Λ → Λ'
| act : TM0.stmt Γ → Λ → Λ'
instance : inhabited Λ' := ⟨Λ'.normal (default _)⟩

local notation `cfg₀` := TM0.cfg Γ Λ
local notation `stmt₁` := TM1.stmt Γ Λ' unit
local notation `cfg₁` := TM1.cfg Γ Λ' unit

parameters (M : TM0.machine Γ Λ)

open TM1.stmt

/-- The program.  -/
def tr : Λ' → stmt₁
| (Λ'.normal q) :=
  branch (λ a _, (M q a).is_none) halt $
  goto (λ a _, match M q a with
  | none := default _ -- unreachable
  | some (q', s) := Λ'.act s q'
  end)
| (Λ'.act (TM0.stmt.move d) q) := move d $ goto (λ _ _, Λ'.normal q)
| (Λ'.act (TM0.stmt.write a) q) := write (λ _ _, a) $ goto (λ _ _, Λ'.normal q)

/-- The configuration translation. -/
def tr_cfg : cfg₀ → cfg₁
| ⟨q, T⟩ := ⟨cond (M q T.1).is_some (some (Λ'.normal q)) none, (), T⟩

theorem tr_respects : respects (TM0.step M) (TM1.step tr)
  (λ a b, tr_cfg a = b) :=
fun_respects.2 $ λ ⟨q, T⟩, begin
  cases e : M q T.1,
  { simp only [TM0.step, tr_cfg, e]; exact eq.refl none },
  cases val with q' s,
  simp only [frespects, TM0.step, tr_cfg, e, option.is_some, cond, option.map_some'],
  have : TM1.step (tr M) ⟨some (Λ'.act s q'), (), T⟩ =
    some ⟨some (Λ'.normal q'), (), TM0.step._match_1 T s⟩,
  { cases s with d a; refl },
  refine trans_gen.head _ (trans_gen.head' this _),
  { unfold TM1.step TM1.step_aux tr has_mem.mem,
    rw e, refl },
  cases e' : M q' _,
  { apply refl_trans_gen.single,
    unfold TM1.step TM1.step_aux tr has_mem.mem,
    rw e', refl },
  { refl }
end

end

end TM0to1

/-!
## The TM2 model

The TM2 model removes the tape entirely from the TM1 model, replacing it with an arbitrary (finite)
collection of stacks, each with elements of different types (the alphabet of stack `k : K` is
`Γ k`). The statements are:

* `push k (f : σ → Γ k) q` puts `f a` on the `k`-th stack, then does `q`.
* `pop k (f : σ → option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, and removes this element from the stack, then does `q`.
* `peek k (f : σ → option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, then does `q`.
* `load (f : σ → σ) q` reads nothing but applies `f` to the internal state, then does `q`.
* `branch (f : σ → bool) qtrue qfalse` does `qtrue` or `qfalse` according to `f a`.
* `goto (f : σ → Λ)` jumps to label `f a`.
* `halt` halts on the next step.

The configuration is a tuple `(l, var, stk)` where `l : option Λ` is the current label to run or
`none` for the halting state, `var : σ` is the (finite) internal state, and `stk : ∀ k, list (Γ k)`
is the collection of stacks. (Note that unlike the `TM0` and `TM1` models, these are not
`list_blank`s, they have definite ends that can be detected by the `pop` command.)

Given a designated stack `k` and a value `L : list (Γ k)`, the initial configuration has all the
stacks empty except the designated "input" stack; in `eval` this designated stack also functions
as the output stack.
-/

namespace TM2

section
parameters {K : Type*} [decidable_eq K] -- Index type of stacks
parameters (Γ : K → Type*) -- Type of stack elements
parameters (Λ : Type*) -- Type of function labels
parameters (σ : Type*) -- Type of variable settings

/-- The TM2 model removes the tape entirely from the TM1 model,
  replacing it with an arbitrary (finite) collection of stacks.
  The operation `push` puts an element on one of the stacks,
  and `pop` removes an element from a stack (and modifying the
  internal state based on the result). `peek` modifies the
  internal state but does not remove an element. -/
inductive stmt
| push : ∀ k, (σ → Γ k) → stmt → stmt
| peek : ∀ k, (σ → option (Γ k) → σ) → stmt → stmt
| pop : ∀ k, (σ → option (Γ k) → σ) → stmt → stmt
| load : (σ → σ) → stmt → stmt
| branch : (σ → bool) → stmt → stmt → stmt
| goto : (σ → Λ) → stmt
| halt : stmt
open stmt

instance stmt.inhabited : inhabited stmt := ⟨halt⟩

/-- A configuration in the TM2 model is a label (or `none` for the halt state), the state of
local variables, and the stacks. (Note that the stacks are not `list_blank`s, they have a definite
size.) -/
structure cfg :=
(l : option Λ)
(var : σ)
(stk : ∀ k, list (Γ k))

instance cfg.inhabited [inhabited σ] : inhabited cfg := ⟨⟨default _, default _, default _⟩⟩

parameters {Γ Λ σ K}
/-- The step function for the TM2 model. -/
@[simp] def step_aux : stmt → σ → (∀ k, list (Γ k)) → cfg
| (push k f q)     v S := step_aux q v (update S k (f v :: S k))
| (peek k f q)     v S := step_aux q (f v (S k).head') S
| (pop k f q)      v S := step_aux q (f v (S k).head') (update S k (S k).tail)
| (load a q)       v S := step_aux q (a v) S
| (branch f q₁ q₂) v S :=
  cond (f v) (step_aux q₁ v S) (step_aux q₂ v S)
| (goto f)         v S := ⟨some (f v), v, S⟩
| halt             v S := ⟨none, v, S⟩

/-- The step function for the TM2 model. -/
@[simp] def step (M : Λ → stmt) : cfg → option cfg
| ⟨none,   v, S⟩ := none
| ⟨some l, v, S⟩ := some (step_aux (M l) v S)

/-- The (reflexive) reachability relation for the TM2 model. -/
def reaches (M : Λ → stmt) : cfg → cfg → Prop :=
refl_trans_gen (λ a b, b ∈ step M a)

/-- Given a set `S` of states, `support_stmt S q` means that `q` only jumps to states in `S`. -/
def supports_stmt (S : finset Λ) : stmt → Prop
| (push k f q)     := supports_stmt q
| (peek k f q)     := supports_stmt q
| (pop k f q)      := supports_stmt q
| (load a q)       := supports_stmt q
| (branch f q₁ q₂) := supports_stmt q₁ ∧ supports_stmt q₂
| (goto l)         := ∀ v, l v ∈ S
| halt             := true

open_locale classical
/-- The set of subtree statements in a statement. -/
noncomputable def stmts₁ : stmt → finset stmt
| Q@(push k f q)     := insert Q (stmts₁ q)
| Q@(peek k f q)     := insert Q (stmts₁ q)
| Q@(pop k f q)      := insert Q (stmts₁ q)
| Q@(load a q)       := insert Q (stmts₁ q)
| Q@(branch f q₁ q₂) := insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
| Q@(goto l)         := {Q}
| Q@halt             := {Q}

theorem stmts₁_self {q} : q ∈ stmts₁ q :=
by cases q; apply_rules [finset.mem_insert_self, finset.mem_singleton_self]

theorem stmts₁_trans {q₁ q₂} :
  q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ :=
begin
  intros h₁₂ q₀ h₀₁,
  induction q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH;
    simp only [stmts₁] at h₁₂ ⊢;
    simp only [finset.mem_insert, finset.mem_singleton, finset.mem_union] at h₁₂,
  iterate 4 {
    rcases h₁₂ with rfl | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (IH h₁₂) } },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h₁₂ with rfl | h₁₂ | h₁₂,
    { unfold stmts₁ at h₀₁, exact h₀₁ },
    { exact finset.mem_insert_of_mem (finset.mem_union_left _ (IH₁ h₁₂)) },
    { exact finset.mem_insert_of_mem (finset.mem_union_right _ (IH₂ h₁₂)) } },
  case TM2.stmt.goto : l {
    subst h₁₂, exact h₀₁ },
  case TM2.stmt.halt {
    subst h₁₂, exact h₀₁ }
end

theorem stmts₁_supports_stmt_mono {S q₁ q₂}
  (h : q₁ ∈ stmts₁ q₂) (hs : supports_stmt S q₂) : supports_stmt S q₁ :=
begin
  induction q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH;
    simp only [stmts₁, supports_stmt, finset.mem_insert, finset.mem_union,
      finset.mem_singleton] at h hs,
  iterate 4 { rcases h with rfl | h; [exact hs, exact IH h hs] },
  case TM2.stmt.branch : f q₁ q₂ IH₁ IH₂ {
    rcases h with rfl | h | h, exacts [hs, IH₁ h hs.1, IH₂ h hs.2] },
  case TM2.stmt.goto : l { subst h, exact hs },
  case TM2.stmt.halt { subst h, trivial }
end

/-- The set of statements accessible from initial set `S` of labels. -/
noncomputable def stmts (M : Λ → stmt) (S : finset Λ) : finset (option stmt) :=
(S.bUnion (λ q, stmts₁ (M q))).insert_none

theorem stmts_trans {M : Λ → stmt} {S q₁ q₂}
  (h₁ : q₁ ∈ stmts₁ q₂) : some q₂ ∈ stmts M S → some q₁ ∈ stmts M S :=
by simp only [stmts, finset.mem_insert_none, finset.mem_bUnion,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h₂, ⟨_, ls, stmts₁_trans h₂ h₁⟩

variable [inhabited Λ]

/-- Given a TM2 machine `M` and a set `S` of states, `supports M S` means that all states in
`S` jump only to other states in `S`. -/
def supports (M : Λ → stmt) (S : finset Λ) :=
default Λ ∈ S ∧ ∀ q ∈ S, supports_stmt S (M q)

theorem stmts_supports_stmt {M : Λ → stmt} {S q}
  (ss : supports M S) : some q ∈ stmts M S → supports_stmt S q :=
by simp only [stmts, finset.mem_insert_none, finset.mem_bUnion,
  option.mem_def, forall_eq', exists_imp_distrib];
exact λ l ls h, stmts₁_supports_stmt_mono h (ss.2 _ ls)

theorem step_supports (M : Λ → stmt) {S}
  (ss : supports M S) : ∀ {c c' : cfg},
  c' ∈ step M c → c.l ∈ S.insert_none → c'.l ∈ S.insert_none
| ⟨some l₁, v, T⟩ c' h₁ h₂ := begin
  replace h₂ := ss.2 _ (finset.some_mem_insert_none.1 h₂),
  simp only [step, option.mem_def] at h₁, subst c',
  revert h₂, induction M l₁ with _ _ q IH _ _ q IH _ _ q IH _ q IH generalizing v T;
    intro hs,
  iterate 4 { exact IH _ _ hs },
  case TM2.stmt.branch : p q₁' q₂' IH₁ IH₂ {
    unfold step_aux, cases p v,
    { exact IH₂ _ _ hs.2 },
    { exact IH₁ _ _ hs.1 } },
  case TM2.stmt.goto { exact finset.some_mem_insert_none.2 (hs _) },
  case TM2.stmt.halt { apply multiset.mem_cons_self }
end

variable [inhabited σ]
/-- The initial state of the TM2 model. The input is provided on a designated stack. -/
def init (k) (L : list (Γ k)) : cfg :=
⟨some (default _), default _, update (λ _, []) k L⟩

/-- Evaluates a TM2 program to completion, with the output on the same stack as the input. -/
def eval (M : Λ → stmt) (k) (L : list (Γ k)) : roption (list (Γ k)) :=
(eval (step M) (init k L)).map $ λ c, c.stk k

end

end TM2

/-!
## TM2 emulator in TM1

To prove that TM2 computable functions are TM1 computable, we need to reduce each TM2 program to a
TM1 program. So suppose a TM2 program is given. This program has to maintain a whole collection of
stacks, but we have only one tape, so we must "multiplex" them all together. Pictorially, if stack
1 contains `[a, b]` and stack 2 contains `[c, d, e, f]` then the tape looks like this:

```
 bottom:  ... | _ | T | _ | _ | _ | _ | ...
 stack 1: ... | _ | b | a | _ | _ | _ | ...
 stack 2: ... | _ | f | e | d | c | _ | ...
```

where a tape element is a vertical slice through the diagram. Here the alphabet is
`Γ' := bool × ∀ k, option (Γ k)`, where:

* `bottom : bool` is marked only in one place, the initial position of the TM, and represents the
  tail of all stacks. It is never modified.
* `stk k : option (Γ k)` is the value of the `k`-th stack, if in range, otherwise `none` (which is
  the blank value). Note that the head of the stack is at the far end; this is so that push and pop
  don't have to do any shifting.

In "resting" position, the TM is sitting at the position marked `bottom`. For non-stack actions,
it operates in place, but for the stack actions `push`, `peek`, and `pop`, it must shuttle to the
end of the appropriate stack, make its changes, and then return to the bottom. So the states are:

* `normal (l : Λ)`: waiting at `bottom` to execute function `l`
* `go k (s : st_act k) (q : stmt₂)`: travelling to the right to get to the end of stack `k` in
  order to perform stack action `s`, and later continue with executing `q`
* `ret (q : stmt₂)`: travelling to the left after having performed a stack action, and executing
  `q` once we arrive

Because of the shuttling, emulation overhead is `O(n)`, where `n` is the current maximum of the
length of all stacks. Therefore a program that takes `k` steps to run in TM2 takes `O((m+k)k)`
steps to run when emulated in TM1, where `m` is the length of the input.
-/

namespace TM2to1

-- A displaced lemma proved in unnecessary generality
theorem stk_nth_val {K : Type*} {Γ : K → Type*} {L : list_blank (∀ k, option (Γ k))} {k S} (n)
  (hL : list_blank.map (proj k) L = list_blank.mk (list.map some S).reverse) :
  L.nth n k = S.reverse.nth n :=
begin
  rw [← proj_map_nth, hL, ← list.map_reverse, list_blank.nth_mk, list.inth, list.nth_map],
  cases S.reverse.nth n; refl
end

section
parameters {K : Type*} [decidable_eq K]
parameters {Γ : K → Type*}
parameters {Λ : Type*} [inhabited Λ]
parameters {σ : Type*} [inhabited σ]

local notation `stmt₂` := TM2.stmt Γ Λ σ
local notation `cfg₂` := TM2.cfg Γ Λ σ

/-- The alphabet of the TM2 simulator on TM1 is a marker for the stack bottom,
plus a vector of stack elements for each stack, or none if the stack does not extend this far. -/
@[nolint unused_arguments] -- [decidable_eq K]: Because K is a parameter, we cannot easily skip
-- the decidable_eq assumption, and this is a local definition anyway so it's not important.
def Γ' := bool × ∀ k, option (Γ k)

instance Γ'.inhabited : inhabited Γ' := ⟨⟨ff, λ _, none⟩⟩

instance Γ'.fintype [fintype K] [∀ k, fintype (Γ k)] : fintype Γ' :=
prod.fintype _ _

/-- The bottom marker is fixed throughout the calculation, so we use the `add_bottom` function
to express the program state in terms of a tape with only the stacks themselves. -/
def add_bottom (L : list_blank (∀ k, option (Γ k))) : list_blank Γ' :=
list_blank.cons (tt, L.head) (L.tail.map ⟨prod.mk ff, rfl⟩)

theorem add_bottom_map (L) : (add_bottom L).map ⟨prod.snd, rfl⟩ = L :=
begin
  simp only [add_bottom, list_blank.map_cons]; convert list_blank.cons_head_tail _,
  generalize : list_blank.tail L = L',
  refine L'.induction_on _, intro l, simp,
  rw (_ : _ ∘ _ = id), {simp},
  funext a, refl
end

theorem add_bottom_modify_nth (f : (∀ k, option (Γ k)) → (∀ k, option (Γ k))) (L n) :
  (add_bottom L).modify_nth (λ a, (a.1, f a.2)) n = add_bottom (L.modify_nth f n) :=
begin
  cases n; simp only [add_bottom,
    list_blank.head_cons, list_blank.modify_nth, list_blank.tail_cons],
  congr, symmetry, apply list_blank.map_modify_nth, intro, refl
end

theorem add_bottom_nth_snd (L n) : ((add_bottom L).nth n).2 = L.nth n :=
by conv {to_rhs, rw [← add_bottom_map L, list_blank.nth_map]}; refl

theorem add_bottom_nth_succ_fst (L n) : ((add_bottom L).nth (n+1)).1 = ff :=
by rw [list_blank.nth_succ, add_bottom, list_blank.tail_cons, list_blank.nth_map]; refl

theorem add_bottom_head_fst (L) : (add_bottom L).head.1 = tt :=
by rw [add_bottom, list_blank.head_cons]; refl

/-- A stack action is a command that interacts with the top of a stack. Our default position
is at the bottom of all the stacks, so we have to hold on to this action while going to the end
to modify the stack. -/
inductive st_act (k : K)
| push : (σ → Γ k) → st_act
| peek : (σ → option (Γ k) → σ) → st_act
| pop : (σ → option (Γ k) → σ) → st_act

instance st_act.inhabited {k} : inhabited (st_act k) := ⟨st_act.peek (λ s _, s)⟩

section
open st_act

/-- The TM2 statement corresponding to a stack action. -/
@[nolint unused_arguments] -- [inhabited Λ]: as this is a local definition it is more trouble than
-- it is worth to omit the typeclass assumption without breaking the parameters
def st_run {k : K} : st_act k → stmt₂ → stmt₂
| (push f) := TM2.stmt.push k f
| (peek f) := TM2.stmt.peek k f
| (pop f) := TM2.stmt.pop k f

/-- The effect of a stack action on the local variables, given the value of the stack. -/
def st_var {k : K} (v : σ) (l : list (Γ k)) : st_act k → σ
| (push f)  := v
| (peek f) := f v l.head'
| (pop f) := f v l.head'

/-- The effect of a stack action on the stack. -/
def st_write {k : K} (v : σ) (l : list (Γ k)) : st_act k → list (Γ k)
| (push f) := f v :: l
| (peek f) := l
| (pop f) := l.tail

/-- We have partitioned the TM2 statements into "stack actions", which require going to the end
of the stack, and all other actions, which do not. This is a modified recursor which lumps the
stack actions into one. -/
@[elab_as_eliminator] def {l} stmt_st_rec
  {C : stmt₂ → Sort l}
  (H₁ : Π k (s : st_act k) q (IH : C q), C (st_run s q))
  (H₂ : Π a q (IH : C q), C (TM2.stmt.load a q))
  (H₃ : Π p q₁ q₂ (IH₁ : C q₁) (IH₂ : C q₂), C (TM2.stmt.branch p q₁ q₂))
  (H₄ : Π l, C (TM2.stmt.goto l))
  (H₅ : C TM2.stmt.halt) : ∀ n, C n
| (TM2.stmt.push k f q)     := H₁ _ (push f) _ (stmt_st_rec q)
| (TM2.stmt.peek k f q)     := H₁ _ (peek f) _ (stmt_st_rec q)
| (TM2.stmt.pop k f q)      := H₁ _ (pop f) _ (stmt_st_rec q)
| (TM2.stmt.load a q)       := H₂ _ _ (stmt_st_rec q)
| (TM2.stmt.branch a q₁ q₂) := H₃ _ _ _ (stmt_st_rec q₁) (stmt_st_rec q₂)
| (TM2.stmt.goto l)         := H₄ _
| TM2.stmt.halt             := H₅

theorem supports_run (S : finset Λ) {k} (s : st_act k) (q) :
  TM2.supports_stmt S (st_run s q) ↔ TM2.supports_stmt S q :=
by rcases s with _|_|_; refl

end

/-- The machine states of the TM2 emulator. We can either be in a normal state when waiting for the
next TM2 action, or we can be in the "go" and "return" states to go to the top of the stack and
return to the bottom, respectively. -/
inductive Λ' : Type (max u_1 u_2 u_3 u_4)
| normal : Λ → Λ'
| go (k) : st_act k → stmt₂ → Λ'
| ret : stmt₂ → Λ'
open Λ'
instance Λ'.inhabited : inhabited Λ' := ⟨normal (default _)⟩

local notation `stmt₁` := TM1.stmt Γ' Λ' σ
local notation `cfg₁` := TM1.cfg Γ' Λ' σ

open TM1.stmt

/-- The program corresponding to state transitions at the end of a stack. Here we start out just
after the top of the stack, and should end just after the new top of the stack. -/
def tr_st_act {k} (q : stmt₁) : st_act k → stmt₁
| (st_act.push f) := write (λ a s, (a.1, update a.2 k $ some $ f s)) $ move dir.right q
| (st_act.peek f) := move dir.left $ load (λ a s, f s (a.2 k)) $ move dir.right q
| (st_act.pop f) :=
  branch (λ a _, a.1)
  ( load (λ a s, f s none) q )
  ( move dir.left $
    load (λ a s, f s (a.2 k)) $
    write (λ a s, (a.1, update a.2 k none)) q )

/-- The initial state for the TM2 emulator, given an initial TM2 state. All stacks start out empty
except for the input stack, and the stack bottom mark is set at the head. -/
def tr_init (k) (L : list (Γ k)) : list Γ' :=
let L' : list Γ' := L.reverse.map (λ a, (ff, update (λ _, none) k a)) in
(tt, L'.head.2) :: L'.tail

theorem step_run {k : K} (q v S) : ∀ s : st_act k,
  TM2.step_aux (st_run s q) v S =
  TM2.step_aux q (st_var v (S k) s) (update S k (st_write v (S k) s))
| (st_act.push f) := rfl
| (st_act.peek f) := by unfold st_write; rw function.update_eq_self; refl
| (st_act.pop f) := rfl

/-- The translation of TM2 statements to TM1 statements. regular actions have direct equivalents,
but stack actions are deferred by going to the corresponding `go` state, so that we can find the
appropriate stack top. -/
def tr_normal : stmt₂ → stmt₁
| (TM2.stmt.push k f q)     := goto (λ _ _, go k (st_act.push f) q)
| (TM2.stmt.peek k f q)     := goto (λ _ _, go k (st_act.peek f) q)
| (TM2.stmt.pop k f q)      := goto (λ _ _, go k (st_act.pop f) q)
| (TM2.stmt.load a q)       := load (λ _, a) (tr_normal q)
| (TM2.stmt.branch f q₁ q₂) := branch (λ a, f) (tr_normal q₁) (tr_normal q₂)
| (TM2.stmt.goto l)         := goto (λ a s, normal (l s))
| TM2.stmt.halt             := halt

theorem tr_normal_run {k} (s q) : tr_normal (st_run s q) = goto (λ _ _, go k s q) :=
by rcases s with _|_|_; refl

open_locale classical

/-- The set of machine states accessible from an initial TM2 statement. -/
noncomputable def tr_stmts₁ : stmt₂ → finset Λ'
| (TM2.stmt.push k f q)     := {go k (st_act.push f) q, ret q} ∪ tr_stmts₁ q
| (TM2.stmt.peek k f q)     := {go k (st_act.peek f) q, ret q} ∪ tr_stmts₁ q
| (TM2.stmt.pop k f q)      := {go k (st_act.pop f) q, ret q} ∪ tr_stmts₁ q
| (TM2.stmt.load a q)       := tr_stmts₁ q
| (TM2.stmt.branch f q₁ q₂) := tr_stmts₁ q₁ ∪ tr_stmts₁ q₂
| _                         := ∅

theorem tr_stmts₁_run {k s q} : tr_stmts₁ (st_run s q) = {go k s q, ret q} ∪ tr_stmts₁ q :=
by rcases s with _|_|_; unfold tr_stmts₁ st_run

theorem tr_respects_aux₂
  {k q v} {S : Π k, list (Γ k)} {L : list_blank (∀ k, option (Γ k))}
  (hL : ∀ k, L.map (proj k) = list_blank.mk ((S k).map some).reverse) (o) :
  let v' := st_var v (S k) o,
      Sk' := st_write v (S k) o,
      S' := update S k Sk' in
  ∃ (L' : list_blank (∀ k, option (Γ k))),
    (∀ k, L'.map (proj k) = list_blank.mk ((S' k).map some).reverse) ∧
    TM1.step_aux (tr_st_act q o) v
      ((tape.move dir.right)^[(S k).length] (tape.mk' ∅ (add_bottom L))) =
    TM1.step_aux q v'
      ((tape.move dir.right)^[(S' k).length] (tape.mk' ∅ (add_bottom L'))) :=
begin
  dsimp only, simp, cases o;
  simp only [st_write, st_var, tr_st_act, TM1.step_aux],
  case TM2to1.st_act.push : f {
    have := tape.write_move_right_n (λ a : Γ', (a.1, update a.2 k (some (f v)))),
    dsimp only at this,
    refine ⟨_, λ k', _, by rw [
      tape.move_right_n_head, list.length, tape.mk'_nth_nat, this,
      add_bottom_modify_nth (λ a, update a k (some (f v))),
      nat.add_one, iterate_succ']⟩,
    refine list_blank.ext (λ i, _),
    rw [list_blank.nth_map, list_blank.nth_modify_nth, proj, pointed_map.mk_val],
    by_cases h' : k' = k,
    { subst k', split_ifs; simp only [list.reverse_cons,
        function.update_same, list_blank.nth_mk, list.inth, list.map],
      { rw [list.nth_le_nth, list.nth_le_append_right];
        simp only [h, list.nth_le_singleton, list.length_map, list.length_reverse, nat.succ_pos',
          list.length_append, lt_add_iff_pos_right, list.length] },
      rw [← proj_map_nth, hL, list_blank.nth_mk, list.inth],
      cases decidable.lt_or_gt_of_ne h with h h,
      { rw list.nth_append, simpa only [list.length_map, list.length_reverse] using h },
      { rw [list.nth_len_le, list.nth_len_le];
        simp only [nat.add_one_le_iff, h, list.length, le_of_lt,
          list.length_reverse, list.length_append, list.length_map] } },
    { split_ifs; rw [function.update_noteq h', ← proj_map_nth, hL],
      rw function.update_noteq h' } },
  case TM2to1.st_act.peek : f {
    rw function.update_eq_self,
    use [L, hL], rw [tape.move_left_right], congr,
    cases e : S k, {refl},
    rw [list.length_cons, iterate_succ', tape.move_right_left, tape.move_right_n_head,
      tape.mk'_nth_nat, add_bottom_nth_snd, stk_nth_val _ (hL k), e,
      list.reverse_cons, ← list.length_reverse, list.nth_concat_length], refl },
  case TM2to1.st_act.pop : f {
    cases e : S k,
    { simp only [tape.mk'_head, list_blank.head_cons, tape.move_left_mk',
        list.length, tape.write_mk', list.head', iterate_zero_apply, list.tail_nil],
      rw [← e, function.update_eq_self], exact ⟨L, hL, by rw [add_bottom_head_fst, cond]⟩ },
    { refine ⟨_, λ k', _, by rw [
        list.length_cons, tape.move_right_n_head, tape.mk'_nth_nat, add_bottom_nth_succ_fst,
        cond, iterate_succ', tape.move_right_left, tape.move_right_n_head, tape.mk'_nth_nat,
        tape.write_move_right_n (λ a:Γ', (a.1, update a.2 k none)),
        add_bottom_modify_nth (λ a, update a k none),
        add_bottom_nth_snd, stk_nth_val _ (hL k), e,
        show (list.cons hd tl).reverse.nth tl.length = some hd,
        by rw [list.reverse_cons, ← list.length_reverse, list.nth_concat_length]; refl,
        list.head', list.tail]⟩,
    refine list_blank.ext (λ i, _),
    rw [list_blank.nth_map, list_blank.nth_modify_nth, proj, pointed_map.mk_val],
    by_cases h' : k' = k,
    { subst k', split_ifs; simp only [
        function.update_same, list_blank.nth_mk, list.tail, list.inth],
      { rw [list.nth_len_le], {refl}, rw [h, list.length_reverse, list.length_map] },
      rw [← proj_map_nth, hL, list_blank.nth_mk, list.inth, e, list.map, list.reverse_cons],
      cases decidable.lt_or_gt_of_ne h with h h,
      { rw list.nth_append, simpa only [list.length_map, list.length_reverse] using h },
      { rw [list.nth_len_le, list.nth_len_le];
        simp only [nat.add_one_le_iff, h, list.length, le_of_lt,
          list.length_reverse, list.length_append, list.length_map] } },
    { split_ifs; rw [function.update_noteq h', ← proj_map_nth, hL],
      rw function.update_noteq h' } } },
end

parameters (M : Λ → stmt₂)
include M

/-- The TM2 emulator machine states written as a TM1 program.
This handles the `go` and `ret` states, which shuttle to and from a stack top. -/
def tr : Λ' → stmt₁
| (normal q) := tr_normal (M q)
| (go k s q) :=
  branch (λ a s, (a.2 k).is_none) (tr_st_act (goto (λ _ _, ret q)) s)
    (move dir.right $ goto (λ _ _, go k s q))
| (ret q) :=
  branch (λ a s, a.1) (tr_normal q)
    (move dir.left $ goto (λ _ _, ret q))

local attribute [pp_using_anonymous_constructor] turing.TM1.cfg
/-- The relation between TM2 configurations and TM1 configurations of the TM2 emulator. -/
inductive tr_cfg : cfg₂ → cfg₁ → Prop
| mk {q v} {S : ∀ k, list (Γ k)} (L : list_blank (∀ k, option (Γ k))) :
  (∀ k, L.map (proj k) = list_blank.mk ((S k).map some).reverse) →
  tr_cfg ⟨q, v, S⟩ ⟨q.map normal, v, tape.mk' ∅ (add_bottom L)⟩

theorem tr_respects_aux₁ {k} (o q v) {S : list (Γ k)} {L : list_blank (∀ k, option (Γ k))}
  (hL : L.map (proj k) = list_blank.mk (S.map some).reverse) (n ≤ S.length) :
  reaches₀ (TM1.step tr)
    ⟨some (go k o q), v, (tape.mk' ∅ (add_bottom L))⟩
    ⟨some (go k o q), v, (tape.move dir.right)^[n] (tape.mk' ∅ (add_bottom L))⟩ :=
begin
  induction n with n IH, {refl},
  apply (IH (le_of_lt H)).tail,
  rw iterate_succ_apply', simp only [TM1.step, TM1.step_aux, tr,
    tape.mk'_nth_nat, tape.move_right_n_head, add_bottom_nth_snd,
    option.mem_def],
  rw [stk_nth_val _ hL, list.nth_le_nth], refl, rwa list.length_reverse
end

theorem tr_respects_aux₃ {q v} {L : list_blank (∀ k, option (Γ k))} (n) :
  reaches₀ (TM1.step tr)
    ⟨some (ret q), v, (tape.move dir.right)^[n] (tape.mk' ∅ (add_bottom L))⟩
    ⟨some (ret q), v, (tape.mk' ∅ (add_bottom L))⟩ :=
begin
  induction n with n IH, {refl},
  refine reaches₀.head _ IH,
  rw [option.mem_def, TM1.step, tr, TM1.step_aux, tape.move_right_n_head, tape.mk'_nth_nat,
    add_bottom_nth_succ_fst, TM1.step_aux, iterate_succ', tape.move_right_left], refl,
end

theorem tr_respects_aux {q v T k} {S : Π k, list (Γ k)}
  (hT : ∀ k, list_blank.map (proj k) T = list_blank.mk ((S k).map some).reverse)
  (o : st_act k)
  (IH : ∀ {v : σ} {S : Π (k : K), list (Γ k)} {T : list_blank (∀ k, option (Γ k))},
    (∀ k, list_blank.map (proj k) T = list_blank.mk ((S k).map some).reverse) →
    (∃ b, tr_cfg (TM2.step_aux q v S) b ∧
      reaches (TM1.step tr) (TM1.step_aux (tr_normal q) v (tape.mk' ∅ (add_bottom T))) b)) :
  ∃ b, tr_cfg (TM2.step_aux (st_run o q) v S) b ∧
    reaches (TM1.step tr) (TM1.step_aux (tr_normal (st_run o q))
      v (tape.mk' ∅ (add_bottom T))) b :=
begin
  simp only [tr_normal_run, step_run],
  have hgo := tr_respects_aux₁ M o q v (hT k) _ (le_refl _),
  obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ hT o,
  have hret := tr_respects_aux₃ M _,
  have := hgo.tail' rfl,
  rw [tr, TM1.step_aux, tape.move_right_n_head, tape.mk'_nth_nat, add_bottom_nth_snd,
    stk_nth_val _ (hT k), list.nth_len_le (le_of_eq (list.length_reverse _)),
    option.is_none, cond, hrun, TM1.step_aux] at this,
  obtain ⟨c, gc, rc⟩ := IH hT',
  refine ⟨c, gc, (this.to₀.trans hret c (trans_gen.head' rfl _)).to_refl⟩,
  rw [tr, TM1.step_aux, tape.mk'_head, add_bottom_head_fst],
  exact rc,
end

local attribute [simp] respects TM2.step TM2.step_aux tr_normal

theorem tr_respects : respects (TM2.step M) (TM1.step tr) tr_cfg :=
λ c₁ c₂ h, begin
  cases h with l v S L hT, clear h,
  cases l, {constructor},
  simp only [TM2.step, respects, option.map_some'],
  suffices : ∃ b, _ ∧ reaches (TM1.step (tr M)) _ _,
  from let ⟨b, c, r⟩ := this in ⟨b, c, trans_gen.head' rfl r⟩,
  rw [tr],
  revert v S L hT, refine stmt_st_rec _ _ _ _ _ (M l); intros,
  { exact tr_respects_aux M hT s @IH },
  { exact IH _ hT },
  { unfold TM2.step_aux tr_normal TM1.step_aux,
    cases p v; [exact IH₂ _ hT, exact IH₁ _ hT] },
  { exact ⟨_, ⟨_, hT⟩, refl_trans_gen.refl⟩ },
  { exact ⟨_, ⟨_, hT⟩, refl_trans_gen.refl⟩ }
end

theorem tr_cfg_init (k) (L : list (Γ k)) :
  tr_cfg (TM2.init k L) (TM1.init (tr_init k L)) :=
begin
  rw (_ : TM1.init _ = _),
  { refine ⟨list_blank.mk (L.reverse.map $ λ a, update (default _) k (some a)), λ k', _⟩,
    refine list_blank.ext (λ i, _),
    rw [list_blank.map_mk, list_blank.nth_mk, list.inth, list.map_map, (∘),
       list.nth_map, proj, pointed_map.mk_val],
    by_cases k' = k,
    { subst k', simp only [function.update_same],
      rw [list_blank.nth_mk, list.inth, ← list.map_reverse, list.nth_map] },
    { simp only [function.update_noteq h],
      rw [list_blank.nth_mk, list.inth, list.map, list.reverse_nil, list.nth],
      cases L.reverse.nth i; refl } },
  { rw [tr_init, TM1.init], dsimp only, congr; cases L.reverse; try {refl},
    simp only [list.map_map, list.tail_cons, list.map], refl }
end

theorem tr_eval_dom (k) (L : list (Γ k)) :
  (TM1.eval tr (tr_init k L)).dom ↔ (TM2.eval M k L).dom :=
tr_eval_dom tr_respects (tr_cfg_init _ _)

theorem tr_eval (k) (L : list (Γ k)) {L₁ L₂}
  (H₁ : L₁ ∈ TM1.eval tr (tr_init k L))
  (H₂ : L₂ ∈ TM2.eval M k L) :
  ∃ (S : ∀ k, list (Γ k)) (L' : list_blank (∀ k, option (Γ k))),
    add_bottom L' = L₁ ∧
    (∀ k, L'.map (proj k) = list_blank.mk ((S k).map some).reverse) ∧
    S k = L₂ :=
begin
  obtain ⟨c₁, h₁, rfl⟩ := (roption.mem_map_iff _).1 H₁,
  obtain ⟨c₂, h₂, rfl⟩ := (roption.mem_map_iff _).1 H₂,
  obtain ⟨_, ⟨q, v, S, L', hT⟩, h₃⟩ := tr_eval (tr_respects M) (tr_cfg_init M k L) h₂,
  cases roption.mem_unique h₁ h₃,
  exact ⟨S, L', by simp only [tape.mk'_right₀], hT, rfl⟩
end

/-- The support of a set of TM2 states in the TM2 emulator. -/
noncomputable def tr_supp (S : finset Λ) : finset Λ' :=
S.bUnion (λ l, insert (normal l) (tr_stmts₁ (M l)))

theorem tr_supports {S} (ss : TM2.supports M S) :
  TM1.supports tr (tr_supp S) :=
⟨finset.mem_bUnion.2 ⟨_, ss.1, finset.mem_insert.2 $ or.inl rfl⟩,
λ l' h, begin
  suffices : ∀ q (ss' : TM2.supports_stmt S q)
    (sub : ∀ x ∈ tr_stmts₁ q, x ∈ tr_supp M S),
    TM1.supports_stmt (tr_supp M S) (tr_normal q) ∧
    (∀ l' ∈ tr_stmts₁ q, TM1.supports_stmt (tr_supp M S) (tr M l')),
  { rcases finset.mem_bUnion.1 h with ⟨l, lS, h⟩,
    have := this _ (ss.2 l lS) (λ x hx,
      finset.mem_bUnion.2 ⟨_, lS, finset.mem_insert_of_mem hx⟩),
    rcases finset.mem_insert.1 h with rfl | h;
    [exact this.1, exact this.2 _ h] },
  clear h l', refine stmt_st_rec _ _ _ _ _; intros,
  { -- stack op
    rw TM2to1.supports_run at ss',
    simp only [TM2to1.tr_stmts₁_run, finset.mem_union,
      finset.mem_insert, finset.mem_singleton] at sub,
    have hgo := sub _ (or.inl $ or.inl rfl),
    have hret := sub _ (or.inl $ or.inr rfl),
    cases IH ss' (λ x hx, sub x $ or.inr hx) with IH₁ IH₂,
    refine ⟨by simp only [tr_normal_run, TM1.supports_stmt]; intros; exact hgo, λ l h, _⟩,
    rw [tr_stmts₁_run] at h,
    simp only [TM2to1.tr_stmts₁_run, finset.mem_union,
      finset.mem_insert, finset.mem_singleton] at h,
    rcases h with ⟨rfl | rfl⟩ | h,
    { unfold TM1.supports_stmt TM2to1.tr,
      rcases s with _|_|_,
      { exact ⟨λ _ _, hret, λ _ _, hgo⟩ },
      { exact ⟨λ _ _, hret, λ _ _, hgo⟩ },
      { exact ⟨⟨λ _ _, hret, λ _ _, hret⟩, λ _ _, hgo⟩ } },
    { unfold TM1.supports_stmt TM2to1.tr,
      exact ⟨IH₁, λ _ _, hret⟩ },
    { exact IH₂ _ h } },
  { -- load
    unfold TM2to1.tr_stmts₁ at ss' sub ⊢,
    exact IH ss' sub },
  { -- branch
    unfold TM2to1.tr_stmts₁ at sub,
    cases IH₁ ss'.1 (λ x hx, sub x $ finset.mem_union_left _ hx) with IH₁₁ IH₁₂,
    cases IH₂ ss'.2 (λ x hx, sub x $ finset.mem_union_right _ hx) with IH₂₁ IH₂₂,
    refine ⟨⟨IH₁₁, IH₂₁⟩, λ l h, _⟩,
    rw [tr_stmts₁] at h,
    rcases finset.mem_union.1 h with h | h;
    [exact IH₁₂ _ h, exact IH₂₂ _ h] },
  { -- goto
    rw tr_stmts₁, unfold TM2to1.tr_normal TM1.supports_stmt,
    unfold TM2.supports_stmt at ss',
    exact ⟨λ _ v, finset.mem_bUnion.2 ⟨_, ss' v, finset.mem_insert_self _ _⟩, λ _, false.elim⟩ },
  { exact ⟨trivial, λ _, false.elim⟩ } -- halt
end⟩

end

end TM2to1

end turing
