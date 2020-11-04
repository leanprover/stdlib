/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import data.list.pairwise
import logic.relation

universes u v

open nat

variables {α : Type u} {β : Type v}

namespace list

/- chain relation (conjunction of R a b ∧ R b c ∧ R c d ...) -/

mk_iff_of_inductive_prop list.chain list.chain_iff

variable {R : α → α → Prop}

theorem rel_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b::l)) : R a b :=
(chain_cons.1 p).1

theorem chain_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b::l)) : chain R b l :=
(chain_cons.1 p).2

theorem chain.imp' {S : α → α → Prop}
  (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α} (Hab : ∀ ⦃c⦄, R a c → S b c)
  {l : list α} (p : chain R a l) : chain S b l :=
by induction p with _ a c l r p IH generalizing b; constructor;
   [exact Hab r, exact IH (@HRS _)]

theorem chain.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {a : α} {l : list α} (p : chain R a l) : chain S a l :=
p.imp' H (H a)

theorem chain.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {a : α} {l : list α} : chain R a l ↔ chain S a l :=
⟨chain.imp (λ a b, (H a b).1), chain.imp (λ a b, (H a b).2)⟩

theorem chain.iff_mem {a : α} {l : list α} :
  chain R a l ↔ chain (λ x y, x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
⟨λ p, by induction p with _ a b l r p IH; constructor;
  [exact ⟨mem_cons_self _ _, mem_cons_self _ _, r⟩,
   exact IH.imp (λ a b ⟨am, bm, h⟩,
    ⟨mem_cons_of_mem _ am, mem_cons_of_mem _ bm, h⟩)],
 chain.imp (λ a b h, h.2.2)⟩

theorem chain_singleton {a b : α} : chain R a [b] ↔ R a b :=
by simp only [chain_cons, chain.nil, and_true]

theorem chain_split {a b : α} {l₁ l₂ : list α} : chain R a (l₁++b::l₂) ↔
  chain R a (l₁++[b]) ∧ chain R b l₂ :=
by induction l₁ with x l₁ IH generalizing a;
simp only [*, nil_append, cons_append, chain.nil, chain_cons, and_true, and_assoc]

theorem chain_map (f : β → α) {b : β} {l : list β} :
  chain R (f b) (map f l) ↔ chain (λ a b : β, R (f a) (f b)) b l :=
by induction l generalizing b; simp only [map, chain.nil, chain_cons, *]

theorem chain_of_chain_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {a : α} {l : list α}
  (p : chain S (f a) (map f l)) : chain R a l :=
((chain_map f).1 p).imp H

theorem chain_map_of_chain {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {a : α} {l : list α}
  (p : chain R a l) : chain S (f a) (map f l) :=
(chain_map f).2 $ p.imp H

theorem chain_of_pairwise {a : α} {l : list α} (p : pairwise R (a::l)) : chain R a l :=
begin
  cases pairwise_cons.1 p with r p', clear p,
  induction p' with b l r' p IH generalizing a, {exact chain.nil},
  simp only [chain_cons, forall_mem_cons] at r,
  exact chain_cons.2 ⟨r.1, IH r'⟩
end

theorem chain_iff_pairwise (tr : transitive R) {a : α} {l : list α} :
  chain R a l ↔ pairwise R (a::l) :=
⟨λ c, begin
  induction c with b b c l r p IH, {exact pairwise_singleton _ _},
  apply IH.cons _, simp only [mem_cons_iff, forall_eq_or_imp, r, true_and],
  show ∀ x ∈ l, R b x, from λ x m, (tr r (rel_of_pairwise_cons IH m)),
end, chain_of_pairwise⟩

theorem chain_iff_nth_le {R} : ∀ {a : α} {l : list α},
  chain R a l ↔ (∀ h : 0 < length l, R a (nth_le l 0 h)) ∧ (∀ i (h : i < length l - 1),
    R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h)))
| a [] := by simp
| a (b :: t) :=
begin
  rw [chain_cons, chain_iff_nth_le],
  split,
  { rintros ⟨R, ⟨h0, h⟩⟩,
    split,
    { intro w, exact R, },
    { intros i w,
      cases i,
      { apply h0, },
      { convert h i _ using 1,
        refl, refl,
        simp only [succ_eq_add_one, add_succ_sub_one, add_zero, length, add_lt_add_iff_right] at w,
        exact lt_pred_iff.mpr w, } } },
  { rintros ⟨h0, h⟩, split,
    { apply h0, simp, },
    { split,
      { apply h 0, },
      { intros i w, convert h (i+1) _ using 1, refl, refl,
        exact lt_pred_iff.mp w, } } },
end

theorem chain'.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {l : list α} (p : chain' R l) : chain' S l :=
by cases l; [trivial, exact p.imp H]

theorem chain'.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {l : list α} : chain' R l ↔ chain' S l :=
⟨chain'.imp (λ a b, (H a b).1), chain'.imp (λ a b, (H a b).2)⟩

theorem chain'.iff_mem : ∀ {l : list α}, chain' R l ↔ chain' (λ x y, x ∈ l ∧ y ∈ l ∧ R x y) l
| [] := iff.rfl
| (x::l) :=
  ⟨λ h, (chain.iff_mem.1 h).imp $ λ a b ⟨h₁, h₂, h₃⟩, ⟨h₁, or.inr h₂, h₃⟩,
   chain'.imp $ λ a b h, h.2.2⟩

@[simp] theorem chain'_nil : chain' R [] := trivial

@[simp] theorem chain'_singleton (a : α) : chain' R [a] := chain.nil

theorem chain'_split {a : α} : ∀ {l₁ l₂ : list α}, chain' R (l₁++a::l₂) ↔
  chain' R (l₁++[a]) ∧ chain' R (a::l₂)
| []      l₂ := (and_iff_right (chain'_singleton a)).symm
| (b::l₁) l₂ := chain_split

theorem chain'_map (f : β → α) {l : list β} :
  chain' R (map f l) ↔ chain' (λ a b : β, R (f a) (f b)) l :=
by cases l; [refl, exact chain_map _]

theorem chain'_of_chain'_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {l : list α}
  (p : chain' S (map f l)) : chain' R l :=
((chain'_map f).1 p).imp H

theorem chain'_map_of_chain' {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {l : list α}
  (p : chain' R l) : chain' S (map f l) :=
(chain'_map f).2 $ p.imp H

theorem pairwise.chain' : ∀ {l : list α}, pairwise R l → chain' R l
| [] _ := trivial
| (a::l) h := chain_of_pairwise h

theorem chain'_iff_pairwise (tr : transitive R) : ∀ {l : list α},
  chain' R l ↔ pairwise R l
| [] := (iff_true_intro pairwise.nil).symm
| (a::l) := chain_iff_pairwise tr

@[simp] theorem chain'_cons {x y l} : chain' R (x :: y :: l) ↔ R x y ∧ chain' R (y :: l) :=
chain_cons

theorem chain'.cons {x y l} (h₁ : R x y) (h₂ : chain' R (y :: l)) :
  chain' R (x :: y :: l) :=
chain'_cons.2 ⟨h₁, h₂⟩

theorem chain'.tail : ∀ {l} (h : chain' R l), chain' R l.tail
| []            _ := trivial
| [x]           _ := trivial
| (x :: y :: l) h := (chain'_cons.mp h).right

theorem chain'.rel_head {x y l} (h : chain' R (x :: y :: l)) : R x y :=
rel_of_chain_cons h

theorem chain'.rel_head' {x l} (h : chain' R (x :: l)) ⦃y⦄ (hy : y ∈ head' l) : R x y :=
by { rw ← cons_head'_tail hy at h, exact h.rel_head }

theorem chain'.cons' {x} :
  ∀ {l : list α},  chain' R l → (∀ y ∈ l.head', R x y) → chain' R (x :: l)
| [] _ _ := chain'_singleton x
| (a :: l) hl H := hl.cons $ H _ rfl

theorem chain'_cons' {x l} : chain' R (x :: l) ↔ (∀ y ∈ head' l, R x y) ∧ chain' R l :=
⟨λ h, ⟨h.rel_head', h.tail⟩, λ ⟨h₁, h₂⟩, h₂.cons' h₁⟩

theorem chain'.append : ∀ {l₁ l₂ : list α} (h₁ : chain' R l₁) (h₂ : chain' R l₂)
  (h : ∀ (x ∈ l₁.last') (y ∈ l₂.head'), R x y),
  chain' R (l₁ ++ l₂)
| [] l₂ h₁ h₂ h := h₂
| [a] l₂ h₁ h₂ h := h₂.cons' $ h _ rfl
| (a::b::l) l₂ h₁ h₂ h :=
  begin
    simp only [last'] at h,
    have : chain' R (b::l) := h₁.tail,
    exact (this.append h₂ h).cons h₁.rel_head
  end

theorem chain'_pair {x y} : chain' R [x, y] ↔ R x y :=
by simp only [chain'_singleton, chain'_cons, and_true]

theorem chain'.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : chain' R (x :: l)) :
  chain' R (y :: l) :=
hl.tail.cons' $ λ z hz, h $ hl.rel_head' hz

theorem chain'_reverse : ∀ {l}, chain' R (reverse l) ↔ chain' (flip R) l
| [] := iff.rfl
| [a] := by simp only [chain'_singleton, reverse_singleton]
| (a :: b :: l) := by rw [chain'_cons, reverse_cons, reverse_cons, append_assoc, cons_append,
    nil_append, chain'_split, ← reverse_cons, @chain'_reverse (b :: l), and_comm, chain'_pair, flip]

theorem chain'_iff_nth_le {R} : ∀ {l : list α},
  chain' R l ↔ ∀ i (h : i < length l - 1),
    R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h))
| [] := by simp
| (a :: nil) := by simp
| (a :: b :: t) :=
begin
  rw [chain'_cons, chain'_iff_nth_le],
  split,
  { rintros ⟨R, h⟩ i w,
    cases i,
    { exact R, },
    { convert h i _ using 1, refl, refl,
      simp only [succ_eq_add_one, add_succ_sub_one, add_zero, length, add_lt_add_iff_right] at w,
      simpa using w, },
   },
  { rintros h, split,
    { apply h 0, simp, },
    { intros i w, convert h (i+1) _ using 1, refl, refl,
      simp only [add_zero, length, add_succ_sub_one] at w,
      simpa using w, }
    },
end

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `chain' R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
lemma chain'.append_overlap : ∀ {l₁ l₂ l₃ : list α}
  (h₁ : chain' R (l₁ ++ l₂)) (h₂ : chain' R (l₂ ++ l₃)) (hn : l₂ ≠ []),
  chain' R (l₁ ++ l₂ ++ l₃)
| [] l₂ l₃ h₁ h₂ hn := h₂
| l₁ [] l₃ h₁ h₂ hn := (hn rfl).elim
| [a] (b::l₂) l₃ h₁ h₂ hn := by { simp at *, tauto }
| (a::b::l₁) (c::l₂) l₃ h₁ h₂ hn := begin
  simp only [cons_append, chain'_cons] at h₁ h₂ ⊢,
  simp only [← cons_append] at h₁ h₂ ⊢,
  exact ⟨h₁.1, chain'.append_overlap h₁.2 h₂ (cons_ne_nil _ _)⟩
end

/--
If `a` and `b` are related by the reflexive transitive closure of `r`,
then there is a `r`-chain starting from `a` and ending on `b`.
-/
lemma exists_chain_of_relation_refl_trans_gen {r : α → α → Prop} {a b : α} (h : relation.refl_trans_gen r a b) :
  ∃ l, chain r a l ∧ last (a :: l) (cons_ne_nil _ _) = b :=
begin
  apply relation.refl_trans_gen.head_induction_on h,
  { exact ⟨[], chain.nil, rfl⟩ },
  { intros c d e t ih,
    obtain ⟨l, hl₁, hl₂⟩ := ih,
    refine ⟨d :: l, chain.cons e hl₁, _⟩,
    rwa last_cons_cons }
end

/--
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate up the chain.
-/
lemma chain.induction {r : α → α → Prop} (p : α → Prop) {a b : α}
  (l : list α) (h : chain r a l)
  (hb : last (a :: l) (cons_ne_nil _ _) = b)
  (carries : ∀ {x y : α}, r x y → p y → p x) (final : p b) : p a :=
begin
  induction l generalizing a,
  { cases hb, exact final },
  { rw chain_cons at h,
    apply carries h.1 (l_ih h.2 hb) }
end

end list
