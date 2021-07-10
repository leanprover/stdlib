/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import data.list.basic

/-!
# zip & unzip

This file provides results about `list.zip_with`, `list.zip` and `list.unzip` (definitions are in
core Lean).
`zip_with f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : list α` and `l₂ : list β`. It
applies, until one of the lists is exhausted. For example,
`zip_with f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zip_with` applied to `prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/

universe u

open nat

namespace list
variables {α : Type u} {β γ δ : Type*}

@[simp] theorem zip_with_cons_cons (f : α → β → γ) (a : α) (b : β) (l₁ : list α) (l₂ : list β) :
  zip_with f (a :: l₁) (b :: l₂) = f a b :: zip_with f l₁ l₂ := rfl

@[simp] theorem zip_cons_cons (a : α) (b : β) (l₁ : list α) (l₂ : list β) :
  zip (a :: l₁) (b :: l₂) = (a, b) :: zip l₁ l₂ := rfl

@[simp] theorem zip_with_nil_left (f : α → β → γ) (l) : zip_with f [] l = [] := rfl

@[simp] theorem zip_with_nil_right (f : α → β → γ) (l)  : zip_with f l [] = [] :=
by cases l; refl

@[simp] lemma zip_with_eq_nil_iff {f : α → β → γ} {l l'} :
  zip_with f l l' = [] ↔ l = [] ∨ l' = [] :=
by { cases l; cases l'; simp }

@[simp] theorem zip_nil_left (l : list α) : zip ([] : list β) l = [] := rfl

@[simp] theorem zip_nil_right (l : list α) : zip l ([] : list β) = [] :=
zip_with_nil_right _ l

@[simp] theorem zip_swap : ∀ (l₁ : list α) (l₂ : list β),
  (zip l₁ l₂).map prod.swap = zip l₂ l₁
| []      l₂      := (zip_nil_right _).symm
| l₁      []      := by rw zip_nil_right; refl
| (a::l₁) (b::l₂) := by simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, prod.swap_prod_mk];
    split; refl

@[simp] theorem length_zip_with (f : α → β → γ) : ∀  (l₁ : list α) (l₂ : list β),
   length (zip_with f l₁ l₂) = min (length l₁) (length l₂)
| []      l₂      := rfl
| l₁      []      := by simp only [length, min_zero, zip_with_nil_right]
| (a::l₁) (b::l₂) := by by simp [length, zip_cons_cons, length_zip_with l₁ l₂, min_add_add_right]

@[simp] theorem length_zip : ∀ (l₁ : list α) (l₂ : list β),
   length (zip l₁ l₂) = min (length l₁) (length l₂) :=
length_zip_with _

lemma lt_length_left_of_zip_with {f : α → β → γ} {i : ℕ} {l : list α} {l' : list β}
  (h : i < (zip_with f l l').length) :
  i < l.length :=
by { rw [length_zip_with, lt_min_iff] at h, exact h.left }

lemma lt_length_right_of_zip_with {f : α → β → γ} {i : ℕ} {l : list α} {l' : list β}
  (h : i < (zip_with f l l').length) :
  i < l'.length :=
by { rw [length_zip_with, lt_min_iff] at h, exact h.right }

lemma lt_length_left_of_zip {i : ℕ} {l : list α} {l' : list β} (h : i < (zip l l').length) :
  i < l.length :=
lt_length_left_of_zip_with h

lemma lt_length_right_of_zip {i : ℕ} {l : list α} {l' : list β} (h : i < (zip l l').length) :
  i < l'.length :=
lt_length_right_of_zip_with h

theorem zip_append : ∀ {l₁ r₁ : list α} {l₂ r₂ : list β} (h : length l₁ = length l₂),
   zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂
| []      r₁ l₂      r₂ h := by simp only [eq_nil_of_length_eq_zero h.symm]; refl
| l₁      r₁ []      r₂ h := by simp only [eq_nil_of_length_eq_zero h]; refl
| (a::l₁) r₁ (b::l₂) r₂ h := by simp only [cons_append, zip_cons_cons, zip_append (succ.inj h)];
    split; refl

theorem zip_map (f : α → γ) (g : β → δ) : ∀ (l₁ : list α) (l₂ : list β),
   zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (prod.map f g)
| []      l₂      := rfl
| l₁      []      := by simp only [map, zip_nil_right]
| (a::l₁) (b::l₂) := by simp only [map, zip_cons_cons, zip_map l₁ l₂, prod.map]; split; refl

theorem zip_map_left (f : α → γ) (l₁ : list α) (l₂ : list β) :
   zip (l₁.map f) l₂ = (zip l₁ l₂).map (prod.map f id) :=
by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : list α) (l₂ : list β) :
   zip l₁ (l₂.map f) = (zip l₁ l₂).map (prod.map id f) :=
by rw [← zip_map, map_id]

@[simp] lemma zip_with_map {μ}
  (f : γ → δ → μ) (g : α → γ) (h : β → δ) (as : list α) (bs : list β) :
  zip_with f (as.map g) (bs.map h) =
  zip_with (λ a b, f (g a) (h b)) as bs :=
begin
  induction as generalizing bs,
  { simp },
  { cases bs; simp * }
end

lemma zip_with_map_left
  (f : α → β → γ) (g : δ → α) (l : list δ) (l' : list β) :
  zip_with f (l.map g) l' = zip_with (f ∘ g) l l' :=
by { convert (zip_with_map f g id l l'), exact eq.symm (list.map_id _) }

lemma zip_with_map_right
  (f : α → β → γ) (l : list α) (g : δ → β) (l' : list δ) :
  zip_with f l (l'.map g) = zip_with (λ x, f x ∘ g) l l' :=
by { convert (list.zip_with_map f id g l l'), exact eq.symm (list.map_id _) }

theorem zip_map' (f : α → β) (g : α → γ) : ∀ (l : list α),
   zip (l.map f) (l.map g) = l.map (λ a, (f a, g a))
| []     := rfl
| (a::l) := by simp only [map, zip_cons_cons, zip_map' l]; split; refl

lemma map_zip_with {δ : Type*} (f : α → β) (g : γ → δ → α) (l : list γ) (l' : list δ) :
  map f (zip_with g l l') = zip_with (λ x y, f (g x y)) l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l',
    { simp },
    { simp [hl] } }
end

theorem mem_zip {a b} : ∀ {l₁ : list α} {l₂ : list β},
   (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
| (_::l₁) (_::l₂) (or.inl rfl) := ⟨or.inl rfl, or.inl rfl⟩
| (a'::l₁) (b'::l₂) (or.inr h) := by split; simp only [mem_cons_iff, or_true, mem_zip h]

theorem map_fst_zip : ∀ (l₁ : list α) (l₂ : list β),
  l₁.length ≤ l₂.length →
  map prod.fst (zip l₁ l₂) = l₁
| [] bs _ := rfl
| (a :: as) (b :: bs) h := by { simp at h, simp! * }
| (a :: as) [] h := by { simp at h, contradiction }

theorem map_snd_zip : ∀ (l₁ : list α) (l₂ : list β),
  l₂.length ≤ l₁.length →
  map prod.snd (zip l₁ l₂) = l₂
| _ [] _ := by { rw zip_nil_right, refl }
| [] (b :: bs) h := by { simp at h, contradiction }
| (a :: as) (b :: bs) h := by { simp at h, simp! * }

@[simp] theorem unzip_nil : unzip (@nil (α × β)) = ([], []) := rfl

@[simp] theorem unzip_cons (a : α) (b : β) (l : list (α × β)) :
   unzip ((a, b) :: l) = (a :: (unzip l).1, b :: (unzip l).2) :=
by rw unzip; cases unzip l; refl

theorem unzip_eq_map : ∀ (l : list (α × β)), unzip l = (l.map prod.fst, l.map prod.snd)
| []            := rfl
| ((a, b) :: l) := by simp only [unzip_cons, map_cons, unzip_eq_map l]

theorem unzip_left (l : list (α × β)) : (unzip l).1 = l.map prod.fst :=
by simp only [unzip_eq_map]

theorem unzip_right (l : list (α × β)) : (unzip l).2 = l.map prod.snd :=
by simp only [unzip_eq_map]

theorem unzip_swap (l : list (α × β)) : unzip (l.map prod.swap) = (unzip l).swap :=
by simp only [unzip_eq_map, map_map]; split; refl

theorem zip_unzip : ∀ (l : list (α × β)), zip (unzip l).1 (unzip l).2 = l
| []            := rfl
| ((a, b) :: l) := by simp only [unzip_cons, zip_cons_cons, zip_unzip l]; split; refl

theorem unzip_zip_left : ∀ {l₁ : list α} {l₂ : list β}, length l₁ ≤ length l₂ →
  (unzip (zip l₁ l₂)).1 = l₁
| []      l₂      h := rfl
| l₁      []      h := by rw eq_nil_of_length_eq_zero (eq_zero_of_le_zero h); refl
| (a::l₁) (b::l₂) h := by simp only [zip_cons_cons, unzip_cons,
    unzip_zip_left (le_of_succ_le_succ h)]; split; refl

theorem unzip_zip_right {l₁ : list α} {l₂ : list β} (h : length l₂ ≤ length l₁) :
  (unzip (zip l₁ l₂)).2 = l₂ :=
by rw [← zip_swap, unzip_swap]; exact unzip_zip_left h

theorem unzip_zip {l₁ : list α} {l₂ : list β} (h : length l₁ = length l₂) :
  unzip (zip l₁ l₂) = (l₁, l₂) :=
by rw [← @prod.mk.eta _ _ (unzip (zip l₁ l₂)),
  unzip_zip_left (le_of_eq h), unzip_zip_right (ge_of_eq h)]

lemma zip_of_prod {l : list α} {l' : list β} {lp : list (α × β)}
  (hl : lp.map prod.fst = l) (hr : lp.map prod.snd = l') :
  lp = l.zip l' :=
by rw [←hl, ←hr, ←zip_unzip lp, ←unzip_left, ←unzip_right, zip_unzip, zip_unzip]

lemma map_prod_left_eq_zip {l : list α} (f : α → β) : l.map (λ x, (x, f x)) = l.zip (l.map f) :=
by { rw ←zip_map', congr, exact map_id _ }

lemma map_prod_right_eq_zip {l : list α} (f : α → β) : l.map (λ x, (f x, x)) = (l.map f).zip l :=
by { rw ←zip_map', congr, exact map_id _ }

lemma zip_with_comm (f : α → α → β) (comm : ∀ (x y : α), f x y = f y x)
  (l l' : list α) :
  zip_with f l l' = zip_with f l' l :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l',
    { simp },
    { simp [comm, hl] } }
end

instance (f : α → α → β) [is_symm_op α β f] : is_symm_op (list α) (list β) (zip_with f) :=
⟨zip_with_comm f is_symm_op.symm_op⟩

@[simp] theorem length_revzip (l : list α) : length (revzip l) = length l :=
by simp only [revzip, length_zip, length_reverse, min_self]

@[simp] theorem unzip_revzip (l : list α) : (revzip l).unzip = (l, l.reverse) :=
unzip_zip (length_reverse l).symm

@[simp] theorem revzip_map_fst (l : list α) : (revzip l).map prod.fst = l :=
by rw [← unzip_left, unzip_revzip]

@[simp] theorem revzip_map_snd (l : list α) : (revzip l).map prod.snd = l.reverse :=
by rw [← unzip_right, unzip_revzip]

theorem reverse_revzip (l : list α) : reverse l.revzip = revzip l.reverse :=
by rw [← zip_unzip.{u u} (revzip l).reverse, unzip_eq_map]; simp; simp [revzip]

theorem revzip_swap (l : list α) : (revzip l).map prod.swap = revzip l.reverse :=
by simp [revzip]

lemma nth_zip_with (f : α → β → γ) (l₁ : list α) (l₂ : list β) (i : ℕ) :
  (zip_with f l₁ l₂).nth i = ((l₁.nth i).map f).bind (λ g, (l₂.nth i).map g) :=
begin
  induction l₁ generalizing l₂ i,
  { simp [zip_with, (<*>)] },
  { cases l₂; simp only [zip_with, has_seq.seq, functor.map, nth, option.map_none'],
    { cases ((l₁_hd :: l₁_tl).nth i); refl },
    { cases i; simp only [option.map_some', nth, option.some_bind', *] } }
end

lemma nth_zip_with_eq_some {α β γ} (f : α → β → γ) (l₁ : list α) (l₂ : list β) (z : γ) (i : ℕ) :
  (zip_with f l₁ l₂).nth i = some z ↔ ∃ x y, l₁.nth i = some x ∧ l₂.nth i = some y ∧ f x y = z :=
begin
  induction l₁ generalizing l₂ i,
  { simp [zip_with] },
  { cases l₂; simp only [zip_with, nth, exists_false, and_false, false_and],
    cases i; simp *, },
end

lemma nth_zip_eq_some (l₁ : list α) (l₂ : list β) (z : α × β) (i : ℕ) :
  (zip l₁ l₂).nth i = some z ↔ l₁.nth i = some z.1 ∧ l₂.nth i = some z.2 :=
begin
  cases z,
  rw [zip, nth_zip_with_eq_some], split,
  { rintro ⟨x, y, h₀, h₁, h₂⟩, cc },
  { rintro ⟨h₀, h₁⟩, exact ⟨_,_,h₀,h₁,rfl⟩ }
end

@[simp] lemma nth_le_zip_with {f : α → β → γ} {l : list α} {l' : list β} {i : ℕ}
  {h : i < (zip_with f l l').length} :
  (zip_with f l l').nth_le i h =
    f (l.nth_le i (lt_length_left_of_zip_with h)) (l'.nth_le i (lt_length_right_of_zip_with h)) :=
begin
  rw [←option.some_inj, ←nth_le_nth, nth_zip_with_eq_some],
  refine ⟨l.nth_le i (lt_length_left_of_zip_with h), l'.nth_le i (lt_length_right_of_zip_with h),
          nth_le_nth _, _⟩,
  simp only [←nth_le_nth, eq_self_iff_true, and_self]
end

@[simp] lemma nth_le_zip {l : list α} {l' : list β} {i : ℕ} {h : i < (zip l l').length} :
  (zip l l').nth_le i h =
    (l.nth_le i (lt_length_left_of_zip h), l'.nth_le i (lt_length_right_of_zip h)) :=
nth_le_zip_with

lemma mem_zip_inits_tails {l : list α} {init tail : list α} :
  (init, tail) ∈ zip l.inits l.tails ↔ init ++ tail = l :=
begin
  induction l generalizing init tail;
    simp_rw [tails, inits, zip_cons_cons],
  { simp },
  { split; rw [mem_cons_iff, zip_map_left, mem_map, prod.exists],
    { rintros (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩),
      { simp },
      { simp [l_ih.mp h], }, },
    { cases init,
      { simp },
      { intro h,
        right,
        use [init_tl, tail],
        simp * at *, }, }, },
end

lemma map_uncurry_zip_eq_zip_with
  (f : α → β → γ) (l : list α) (l' : list β) :
  map (function.uncurry f) (l.zip l') = zip_with f l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp [hl] } }
end

@[simp] lemma sum_zip_with_distrib_left {γ : Type*} [semiring γ]
  (f : α → β → γ) (n : γ) (l : list α) (l' : list β) :
  (l.zip_with (λ x y, n * f x y) l').sum = n * (l.zip_with f l').sum :=
begin
  induction l with hd tl hl generalizing f n l',
  { simp },
  { cases l' with hd' tl',
    { simp, },
    { simp [hl, mul_add] } }
end

section distrib

/-! ### Operations that can be applied before or after a `zip_with` -/

variables (f : α → β → γ) (l : list α) (l' : list β) (n : ℕ)

lemma zip_with_distrib_take :
  (zip_with f l l').take n = zip_with f (l.take n) (l'.take n) :=
begin
  induction l with hd tl hl generalizing l' n,
  { simp },
  { cases l',
    { simp },
    { cases n,
      { simp },
      { simp [hl] } } }
end

lemma zip_with_distrib_drop :
  (zip_with f l l').drop n = zip_with f (l.drop n) (l'.drop n) :=
begin
  induction l with hd tl hl generalizing l' n,
  { simp },
  { cases l',
    { simp },
    { cases n,
      { simp },
      { simp [hl] } } }
end

lemma zip_with_distrib_tail :
  (zip_with f l l').tail = zip_with f l.tail l'.tail :=
by simp_rw [←drop_one, zip_with_distrib_drop]

lemma zip_with_append (f : α → β → γ) (l la : list α) (l' lb : list β) (h : l.length = l'.length) :
  zip_with f (l ++ la) (l' ++ lb) = zip_with f l l' ++ zip_with f la lb :=
begin
  induction l with hd tl hl generalizing l',
  { have : l' = [] := eq_nil_of_length_eq_zero (by simpa using h.symm),
    simp [this], },
  { cases l',
    { simpa using h },
    { simp only [add_left_inj, length] at h,
      simp [hl _ h] } }
end

lemma zip_with_distrib_reverse (h : l.length = l'.length) :
  (zip_with f l l').reverse = zip_with f l.reverse l'.reverse :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp only [add_left_inj, length] at h,
      have : tl.reverse.length = tl'.reverse.length := by simp [h],
      simp [hl _ h, zip_with_append _ _ _ _ _ this] } }
end

end distrib

end list
