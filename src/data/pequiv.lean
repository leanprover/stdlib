/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.set.lattice

/-!

# Partial Equivalences

In this file, we define partial equivalences `pequiv`, which are a bijection between a subset of `α`
and a subset of `β`. Notationally, a `pequiv` is denoted by "`≃.`" (note that the full stop is part
of the notation). The way we store these internally is with two functions `f : α → option β` and
the reverse function `g : β → option α`, with the condition that if `f a` is `option.some b`,
then `g b` is `option.some a`.

## Main results

- `pequiv.of_set`: creates a `pequiv` from a set `s`,
  which sends an element to itself if it is in `s`.
- `pequiv.single`: given two elements `a : α` and `b : β`, create a `pequiv` that sends them to
  each other, and ignores all other elements.
- `pequiv.injective_of_forall_ne_is_some`/`injective_of_forall_is_some`: If the domain of a `pequiv`
  is all of `α` (except possibly one point), its `to_fun` is injective.

## Canonical order

`pequiv` is canonically ordered by inclusion; that is, if a function `f` defined on a subset `s`
is equal to `g` on that subset, but `g` is also defined on a larger set, then `f ≤ g`. We also have
a definition of `⊥`, which is the empty `pequiv` (sends all to `none`), which in the end gives us a
`semilattice_inf_bot` instance.

## Tags

pequiv, partial equivalence

-/

universes u v w x

/-- A `pequiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β` -/
structure pequiv (α : Type u) (β : Type v) :=
(to_fun : α → option β)
(inv_fun : β → option α)
(inv : ∀ (a : α) (b : β), a ∈ inv_fun b ↔ b ∈ to_fun a)

infixr ` ≃. `:25 := pequiv

namespace pequiv
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
open function option

instance : has_coe_to_fun (α ≃. β) := ⟨_, to_fun⟩

@[simp] lemma coe_mk_apply (f₁ : α → option β) (f₂ : β → option α) (h) (x : α) :
  (pequiv.mk f₁ f₂ h : α → option β) x = f₁ x := rfl

@[ext] lemma ext : ∀ {f g : α ≃. β} (h : ∀ x, f x = g x), f = g
| ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩ h :=
have h : f₁ = g₁, from funext h,
have ∀ b, f₂ b = g₂ b,
  begin
    subst h,
    assume b,
    have hf := λ a, hf a b,
    have hg := λ a, hg a b,
    cases h : g₂ b with a,
    { simp only [h, option.not_mem_none, false_iff] at hg,
      simp only [hg, iff_false] at hf,
      rwa [option.eq_none_iff_forall_not_mem] },
    { rw [← option.mem_def, hf, ← hg, h, option.mem_def] }
  end,
by simp [*, funext_iff]

lemma ext_iff {f g : α ≃. β} : f = g ↔ ∀ x, f x = g x :=
⟨congr_fun ∘ congr_arg _, ext⟩

@[refl] protected def refl (α : Type*) : α ≃. α :=
{ to_fun := some,
  inv_fun := some,
  inv := λ _ _, eq_comm }

@[symm] protected def symm (f : α ≃. β) : β ≃. α :=
{ to_fun := f.2,
  inv_fun := f.1,
  inv := λ _ _, (f.inv _ _).symm }

lemma mem_iff_mem (f : α ≃. β) : ∀ {a : α} {b : β}, a ∈ f.symm b ↔ b ∈ f a := f.3

lemma eq_some_iff (f : α ≃. β) : ∀ {a : α} {b : β}, f.symm b = some a ↔ f a = some b := f.3

@[trans] protected def trans (f : α ≃. β) (g : β ≃. γ) : pequiv α γ :=
{ to_fun := λ a, (f a).bind g,
  inv_fun := λ a, (g.symm a).bind f.symm,
  inv := λ a b, by simp [*, and.comm, eq_some_iff f, eq_some_iff g] at * }

@[simp] lemma refl_apply (a : α) : pequiv.refl α a = some a := rfl

@[simp] lemma symm_refl : (pequiv.refl α).symm = pequiv.refl α := rfl

@[simp] lemma symm_symm (f : α ≃. β) : f.symm.symm = f := by cases f; refl

lemma symm_injective : function.injective (@pequiv.symm α β) :=
left_inverse.injective symm_symm

lemma trans_assoc (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) :
  (f.trans g).trans h = f.trans (g.trans h) :=
ext (λ _, option.bind_assoc _ _ _)

lemma mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
  c ∈ f.trans g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b := option.bind_eq_some'

lemma trans_eq_some (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
  f.trans g a = some c ↔ ∃ b, f a = some b ∧ g b = some c := option.bind_eq_some'

lemma trans_eq_none (f : α ≃. β) (g : β ≃. γ) (a : α) :
  f.trans g a = none ↔ (∀ b c, b ∉ f a ∨ c ∉ g b) :=
begin
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm],
  push_neg, tauto
end

@[simp] lemma refl_trans (f : α ≃. β) : (pequiv.refl α).trans f = f :=
by ext; dsimp [pequiv.trans]; refl

@[simp] lemma trans_refl (f : α ≃. β) : f.trans (pequiv.refl β) = f :=
by ext; dsimp [pequiv.trans]; simp

protected lemma inj (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) : a₁ = a₂ :=
by rw ← mem_iff_mem at *; cases h : f.symm b; simp * at *

/-- If the domain of a `pequiv` is `α` except a point, its forward direction is injective. -/
lemma injective_of_forall_ne_is_some (f : α ≃. β) (a₂ : α)
  (h : ∀ (a₁ : α), a₁ ≠ a₂ → is_some (f a₁)) : injective f :=
has_left_inverse.injective
  ⟨λ b, option.rec_on b a₂ (λ b', option.rec_on (f.symm b') a₂ id),
    λ x, begin
      classical,
      cases hfx : f x,
      { have : x = a₂, from not_imp_comm.1 (h x) (hfx.symm ▸ by simp), simp [this] },
      { simp only [hfx], rw [(eq_some_iff f).2 hfx], refl }
    end⟩

/-- If the domain of a `pequiv` is all of `α`, its forward direction is injective. -/
lemma injective_of_forall_is_some {f : α ≃. β}
  (h : ∀ (a : α), is_some (f a)) : injective f :=
(classical.em (nonempty α)).elim
  (λ hn, injective_of_forall_ne_is_some f (classical.choice hn)
    (λ a _, h a))
  (λ hn x, (hn ⟨x⟩).elim)

section of_set
variables (s : set α) [decidable_pred (∈ s)]

/-- Creates a `pequiv` that is the identity on `s`, and `none` outside of it. -/
def of_set (s : set α) [decidable_pred (∈ s)] : α ≃. α :=
{ to_fun := λ a, if a ∈ s then some a else none,
  inv_fun := λ a, if a ∈ s then some a else none,
  inv := λ a b, by {
    split_ifs with hb ha ha,
    { simp [eq_comm] },
    { simp [ne_of_mem_of_not_mem hb ha] },
    { simp [ne_of_mem_of_not_mem ha hb] },
    { simp } } }

lemma mem_of_set_self_iff {s : set α} [decidable_pred (∈ s)] {a : α} : a ∈ of_set s a ↔ a ∈ s :=
by dsimp [of_set]; split_ifs; simp *

lemma mem_of_set_iff {s : set α} [decidable_pred (∈ s)] {a b : α} :
  a ∈ of_set s b ↔ a = b ∧ a ∈ s :=
begin
  dsimp [of_set],
  split_ifs,
  { simp only [iff_self_and, option.mem_def, eq_comm],
    rintro rfl,
    exact h, },
  { simp only [false_iff, not_and, option.not_mem_none],
    rintro rfl,
    exact h, }
end

@[simp] lemma of_set_eq_some_iff {s : set α} {h : decidable_pred (∈ s)} {a b : α} :
  of_set s b = some a ↔ a = b ∧ a ∈ s := mem_of_set_iff

@[simp] lemma of_set_eq_some_self_iff {s : set α} {h : decidable_pred (∈ s)} {a : α} :
  of_set s a = some a ↔ a ∈ s := mem_of_set_self_iff

@[simp] lemma of_set_symm : (of_set s).symm = of_set s := rfl

@[simp] lemma of_set_univ : of_set set.univ = pequiv.refl α := rfl

@[simp] lemma of_set_eq_refl {s : set α} [decidable_pred (∈ s)] :
  of_set s = pequiv.refl α ↔ s = set.univ :=
⟨λ h, begin
  rw [set.eq_univ_iff_forall],
  intro,
  rw [← mem_of_set_self_iff, h],
  exact rfl
end, λ h, by simp only [of_set_univ.symm, h]; congr⟩

end of_set

lemma symm_trans_rev (f : α ≃. β) (g : β ≃. γ) : (f.trans g).symm = g.symm.trans f.symm := rfl

lemma trans_symm (f : α ≃. β) : f.trans f.symm = of_set {a | (f a).is_some} :=
begin
  ext,
  dsimp [pequiv.trans],
  simp only [eq_some_iff f, option.is_some_iff_exists, option.mem_def, bind_eq_some',
    of_set_eq_some_iff],
  split,
  { rintros ⟨b, hb₁, hb₂⟩,
    exact ⟨pequiv.inj _ hb₂ hb₁, b, hb₂⟩ },
  { simp {contextual := tt} }
end

lemma symm_trans (f : α ≃. β) : f.symm.trans f = of_set {b | (f.symm b).is_some} :=
symm_injective $ by simp [symm_trans_rev, trans_symm, -symm_symm]

lemma trans_symm_eq_iff_forall_is_some {f : α ≃. β} :
  f.trans f.symm = pequiv.refl α ↔ ∀ a, is_some (f a) :=
by rw [trans_symm, of_set_eq_refl, set.eq_univ_iff_forall]; refl

instance : has_bot (α ≃. β) :=
⟨{ to_fun := λ _, none,
   inv_fun := λ _, none,
   inv := by simp }⟩

@[simp] lemma bot_apply (a : α) : (⊥ : α ≃. β) a = none := rfl

@[simp] lemma symm_bot : (⊥ : α ≃. β).symm = ⊥ := rfl

@[simp] lemma trans_bot (f : α ≃. β) : f.trans (⊥ : β ≃. γ) = ⊥ :=
by ext; dsimp [pequiv.trans]; simp

@[simp] lemma bot_trans (f : β ≃. γ) : (⊥ : α ≃. β).trans f = ⊥ :=
by ext; dsimp [pequiv.trans]; simp

lemma is_some_symm_get (f : α ≃. β) {a : α} (h : is_some (f a)) :
  is_some (f.symm (option.get h)) :=
is_some_iff_exists.2 ⟨a, by rw [f.eq_some_iff, some_get]⟩

section single
variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

/-- Create a `pequiv` which sends `a` to `b` and `b` to `a`, but is otherwise `none`. -/
def single (a : α) (b : β) : α ≃. β :=
{ to_fun := λ x, if x = a then some b else none,
  inv_fun := λ x, if x = b then some a else none,
  inv := λ _ _, by simp; split_ifs; cc }

lemma mem_single (a : α) (b : β) : b ∈ single a b a := if_pos rfl

lemma mem_single_iff (a₁ a₂ : α) (b₁ b₂ : β) : b₁ ∈ single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
by dsimp [single]; split_ifs; simp [*, eq_comm]

@[simp] lemma symm_single (a : α) (b : β) : (single a b).symm = single b a := rfl

@[simp] lemma single_apply (a : α) (b : β) : single a b a = some b := if_pos rfl

lemma single_apply_of_ne {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) : single a₁ b a₂ = none := if_neg h.symm

lemma single_trans_of_mem (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c ∈ f b) :
  (single a b).trans f = single a c :=
begin
  ext,
  dsimp [single, pequiv.trans],
  split_ifs; simp * at *
end

lemma trans_single_of_mem {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b ∈ f a) :
  f.trans (single b c) = single a c :=
symm_injective $ single_trans_of_mem _ ((mem_iff_mem f).2 h)

@[simp]
lemma single_trans_single (a : α) (b : β) (c : γ) : (single a b).trans (single b c) = single a c :=
single_trans_of_mem _ (mem_single _ _)

@[simp] lemma single_subsingleton_eq_refl [subsingleton α] (a b : α) : single a b = pequiv.refl α :=
begin
  ext i j,
  dsimp [single],
  rw [if_pos (subsingleton.elim i a), subsingleton.elim i j, subsingleton.elim b j]
end

lemma trans_single_of_eq_none {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none) :
  f.trans (single b c) = ⊥ :=
begin
  ext,
  simp only [eq_none_iff_forall_not_mem, option.mem_def, f.eq_some_iff] at h,
  dsimp [pequiv.trans, single],
  simp,
  intros,
  split_ifs;
  simp * at *
end

lemma single_trans_of_eq_none (a : α) {b : β} {f : β ≃. δ} (h : f b = none) :
  (single a b).trans f = ⊥ :=
symm_injective $ trans_single_of_eq_none _ h

lemma single_trans_single_of_ne {b₁ b₂ : β} (h : b₁ ≠ b₂) (a : α) (c : γ) :
  (single a b₁).trans (single b₂ c) = ⊥ :=
single_trans_of_eq_none _ (single_apply_of_ne h.symm _)

end single

section order

instance : partial_order (α ≃. β) :=
{ le := λ f g, ∀ (a : α) (b : β), b ∈ f a → b ∈ g a,
  le_refl := λ _ _ _, id,
  le_trans := λ f g h fg gh a b, (gh a b) ∘ (fg a b),
  le_antisymm := λ f g fg gf, ext begin
    assume a,
    cases h : g a with b,
    { exact eq_none_iff_forall_not_mem.2
       (λ b hb, option.not_mem_none b $ h ▸ fg a b hb) },
    { exact gf _ _ h }
  end }

lemma le_def {f g : α ≃. β} : f ≤ g ↔ (∀ (a : α) (b : β), b ∈ f a → b ∈ g a) := iff.rfl

instance : order_bot (α ≃. β) :=
{ bot_le := λ _ _  _ h, (not_mem_none _ h).elim,
  ..pequiv.partial_order,
  ..pequiv.has_bot }

instance [decidable_eq α] [decidable_eq β] : semilattice_inf_bot (α ≃. β) :=
{ inf := λ f g,
  { to_fun := λ a, if f a = g a then f a else none,
    inv_fun := λ b, if f.symm b = g.symm b then f.symm b else none,
    inv := λ a b, begin
      have := @mem_iff_mem _ _ f a b,
      have := @mem_iff_mem _ _ g a b,
      split_ifs; finish
    end },
  inf_le_left := λ _ _ _ _, by simp; split_ifs; cc,
  inf_le_right := λ _ _ _ _, by simp; split_ifs; cc,
  le_inf := λ f g h fg gh a b, begin
    have := fg a b,
    have := gh a b,
    simp [le_def],
    split_ifs; finish
  end,
  ..pequiv.order_bot }

end order

end pequiv

namespace equiv
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Turns an `equiv` into a `pequiv` of the whole type. -/
def to_pequiv (f : α ≃ β) : α ≃. β :=
{ to_fun := some ∘ f,
  inv_fun := some ∘ f.symm,
  inv := by simp [equiv.eq_symm_apply, eq_comm] }

@[simp] lemma to_pequiv_refl : (equiv.refl α).to_pequiv = pequiv.refl α := rfl

lemma to_pequiv_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).to_pequiv =
  f.to_pequiv.trans g.to_pequiv := rfl

lemma to_pequiv_symm (f : α ≃ β) : f.symm.to_pequiv = f.to_pequiv.symm := rfl

lemma to_pequiv_apply (f : α ≃ β) (x : α) : f.to_pequiv x = some (f x) := rfl

end equiv
