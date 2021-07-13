/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import algebra.ordered_ring

/-!
# Basic operations on the natural numbers

This file contains:
- instances on the natural numbers
- some basic lemmas about natural numbers
- extra recursors:
  * `le_rec_on`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `strong_rec'`: recursion based on strong inequalities
- decidability instances on predicates about the natural numbers
-/

universes u v

/-! ### instances -/

instance : nontrivial ℕ :=
⟨⟨0, 1, nat.zero_ne_one⟩⟩

instance : comm_semiring nat :=
{ add            := nat.add,
  add_assoc      := nat.add_assoc,
  zero           := nat.zero,
  zero_add       := nat.zero_add,
  add_zero       := nat.add_zero,
  add_comm       := nat.add_comm,
  mul            := nat.mul,
  mul_assoc      := nat.mul_assoc,
  one            := nat.succ nat.zero,
  one_mul        := nat.one_mul,
  mul_one        := nat.mul_one,
  left_distrib   := nat.left_distrib,
  right_distrib  := nat.right_distrib,
  zero_mul       := nat.zero_mul,
  mul_zero       := nat.mul_zero,
  mul_comm       := nat.mul_comm,
  nsmul          := λ m n, m * n,
  nsmul_zero'    := nat.zero_mul,
  nsmul_succ'    := λ n x, by rw [nat.succ_eq_one_add, nat.right_distrib, nat.one_mul] }

instance : linear_ordered_semiring nat :=
{ add_left_cancel            := @nat.add_left_cancel,
  lt                         := nat.lt,
  add_le_add_left            := @nat.add_le_add_left,
  le_of_add_le_add_left      := @nat.le_of_add_le_add_left,
  zero_le_one                := nat.le_of_lt (nat.zero_lt_succ 0),
  mul_lt_mul_of_pos_left     := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right    := @nat.mul_lt_mul_of_pos_right,
  decidable_eq               := nat.decidable_eq,
  exists_pair_ne             := ⟨0, 1, ne_of_lt nat.zero_lt_one⟩,
  ..nat.comm_semiring, ..nat.linear_order }

-- all the fields are already included in the linear_ordered_semiring instance
instance : linear_ordered_cancel_add_comm_monoid ℕ :=
{ add_left_cancel := @nat.add_left_cancel,
  ..nat.linear_ordered_semiring }

instance : linear_ordered_comm_monoid_with_zero ℕ :=
{ mul_le_mul_left := λ a b h c, nat.mul_le_mul_left c h,
  ..nat.linear_ordered_semiring,
  ..(infer_instance : comm_monoid_with_zero ℕ)}

/-! Extra instances to short-circuit type class resolution -/
instance : add_comm_monoid nat    := by apply_instance
instance : add_monoid nat         := by apply_instance
instance : monoid nat             := by apply_instance
instance : comm_monoid nat        := by apply_instance
instance : comm_semigroup nat     := by apply_instance
instance : semigroup nat          := by apply_instance
instance : add_comm_semigroup nat := by apply_instance
instance : add_semigroup nat      := by apply_instance
instance : distrib nat            := by apply_instance
instance : semiring nat           := by apply_instance
instance : ordered_semiring nat   := by apply_instance

instance : canonically_ordered_comm_semiring ℕ :=
{ le_iff_exists_add := assume a b,
  ⟨assume h, let ⟨c, hc⟩ := nat.le.dest h in ⟨c, hc.symm⟩,
    assume ⟨c, hc⟩, hc.symm ▸ nat.le_add_right _ _⟩,
  eq_zero_or_eq_zero_of_mul_eq_zero   := assume a b, nat.eq_zero_of_mul_eq_zero,
  bot               := 0,
  bot_le            := nat.zero_le,
  .. nat.nontrivial,
  .. (infer_instance : ordered_add_comm_monoid ℕ),
  .. (infer_instance : linear_ordered_semiring ℕ),
  .. (infer_instance : comm_semiring ℕ) }

instance : canonically_linear_ordered_add_monoid ℕ :=
{ .. (infer_instance : canonically_ordered_add_monoid ℕ),
  .. nat.linear_order }

instance nat.subtype.semilattice_sup_bot (s : set ℕ) [decidable_pred (∈ s)] [h : nonempty s] :
  semilattice_sup_bot s :=
{ bot := ⟨nat.find (nonempty_subtype.1 h), nat.find_spec (nonempty_subtype.1 h)⟩,
  bot_le := λ x, nat.find_min' _ x.2,
  ..subtype.linear_order s,
  ..lattice_of_linear_order }

instance nat.has_lt_iff_add_one_le : has_lt_iff_add_one_le ℕ :=
{ lt_iff_add_one_le := λ a b, iff.rfl }

theorem nat.nsmul_eq_mul (m n : ℕ) : m • n = m * n :=
rfl

theorem nat.eq_of_mul_eq_mul_right {n m k : ℕ} (Hm : 0 < m) (H : n * m = k * m) : n = k :=
by rw [mul_comm n m, mul_comm k m] at H; exact nat.eq_of_mul_eq_mul_left Hm H

instance nat.comm_cancel_monoid_with_zero : comm_cancel_monoid_with_zero ℕ :=
{ mul_left_cancel_of_ne_zero :=
    λ _ _ _ h1 h2, nat.eq_of_mul_eq_mul_left (nat.pos_of_ne_zero h1) h2,
  mul_right_cancel_of_ne_zero :=
    λ _ _ _ h1 h2, nat.eq_of_mul_eq_mul_right (nat.pos_of_ne_zero h1) h2,
  .. (infer_instance : comm_monoid_with_zero ℕ) }

attribute [simp] nat.not_lt_zero nat.succ_ne_zero nat.succ_ne_self
  nat.zero_ne_one nat.one_ne_zero
  nat.zero_ne_bit1 nat.bit1_ne_zero
  nat.bit0_ne_one nat.one_ne_bit0
  nat.bit0_ne_bit1 nat.bit1_ne_bit0

/-!
Inject some simple facts into the type class system.
This `fact` should not be confused with the factorial function `nat.fact`!
-/
section facts

instance succ_pos'' (n : ℕ) : fact (0 < n.succ) := ⟨n.succ_pos⟩

instance pos_of_one_lt (n : ℕ) [h : fact (1 < n)] : fact (0 < n) :=
⟨lt_trans zero_lt_one h.1⟩

end facts

variables {m n k : ℕ}
namespace nat

/-!
### Recursion and `set.range`
-/

section set

open set

theorem zero_union_range_succ : {0} ∪ range succ = univ :=
by { ext n, cases n; simp }

variables {α : Type*}

theorem range_of_succ (f : ℕ → α) : {f 0} ∪ range (f ∘ succ) = range f :=
by rw [← image_singleton, range_comp, ← image_union, zero_union_range_succ, image_univ]

theorem range_rec {α : Type*} (x : α) (f : ℕ → α → α) :
  (set.range (λ n, nat.rec x f n) : set α) =
    {x} ∪ set.range (λ n, nat.rec (f 0 x) (f ∘ succ) n) :=
begin
  convert (range_of_succ _).symm,
  ext n,
  induction n with n ihn,
  { refl },
  { dsimp at ihn ⊢,
    rw ihn }
end

theorem range_cases_on {α : Type*} (x : α) (f : ℕ → α) :
  (set.range (λ n, nat.cases_on n x f) : set α) = {x} ∪ set.range f :=
(range_of_succ _).symm

end set

/-! ### The units of the natural numbers as a `monoid` and `add_monoid` -/

theorem units_eq_one (u : units ℕ) : u = 1 :=
units.ext $ nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

theorem add_units_eq_zero (u : add_units ℕ) : u = 0 :=
add_units.ext $ (nat.eq_zero_of_add_eq_zero u.val_neg).1

@[simp] protected theorem is_unit_iff {n : ℕ} : is_unit n ↔ n = 1 :=
iff.intro
  (assume ⟨u, hu⟩, match n, u, hu, nat.units_eq_one u with _, _, rfl, rfl := rfl end)
  (assume h, h.symm ▸ ⟨1, rfl⟩)

instance unique_units : unique (units ℕ) :=
{ default := 1, uniq := nat.units_eq_one }

instance unique_add_units : unique (add_units ℕ) :=
{ default := 0, uniq := nat.add_units_eq_zero }

/-! ### Equalities and inequalities involving zero and one -/

lemma one_lt_iff_ne_zero_and_ne_one : ∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
| 0     := dec_trivial
| 1     := dec_trivial
| (n+2) := dec_trivial

protected theorem mul_ne_zero {n m : ℕ} (n0 : n ≠ 0) (m0 : m ≠ 0) : n * m ≠ 0
| nm := (eq_zero_of_mul_eq_zero nm).elim n0 m0

@[simp] protected theorem mul_eq_zero {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
iff.intro eq_zero_of_mul_eq_zero (by simp [or_imp_distrib] {contextual := tt})

@[simp] protected theorem zero_eq_mul {a b : ℕ} : 0 = a * b ↔ a = 0 ∨ b = 0 :=
by rw [eq_comm, nat.mul_eq_zero]

lemma eq_zero_of_double_le {a : ℕ} (h : 2 * a ≤ a) : a = 0 :=
nat.eq_zero_of_le_zero $
  by rwa [two_mul, nat.add_le_to_le_sub, nat.sub_self] at h; refl

lemma eq_zero_of_mul_le {a b : ℕ} (hb : 2 ≤ b) (h : b * a ≤ a) : a = 0 :=
eq_zero_of_double_le $ le_trans (nat.mul_le_mul_right _ hb) h

theorem le_zero_iff {i : ℕ} : i ≤ 0 ↔ i = 0 :=
⟨nat.eq_zero_of_le_zero, assume h, h ▸ le_refl i⟩

lemma zero_max {m : ℕ} : max 0 m = m :=
max_eq_right (zero_le _)

@[simp] lemma min_eq_zero_iff {m n : ℕ} : min m n = 0 ↔ m = 0 ∨ n = 0 :=
begin
  split,
  { intro h,
    cases le_total n m with H H,
    { simpa [H] using or.inr h },
    { simpa [H] using or.inl h } },
  { rintro (rfl|rfl);
    simp }
end

@[simp] lemma max_eq_zero_iff {m n : ℕ} : max m n = 0 ↔ m = 0 ∧ n = 0 :=
begin
  split,
  { intro h,
    cases le_total n m with H H,
    { simp only [H, max_eq_left] at h,
      exact ⟨h, le_antisymm (H.trans h.le) (zero_le _)⟩ },
    { simp only [H, max_eq_right] at h,
      exact ⟨le_antisymm (H.trans h.le) (zero_le _), h⟩ } },
  { rintro ⟨rfl, rfl⟩,
    simp }
end

lemma add_eq_max_iff {n m : ℕ} :
  n + m = max n m ↔ n = 0 ∨ m = 0 :=
begin
  rw ←min_eq_zero_iff,
  cases le_total n m with H H;
  simp [H]
end

lemma add_eq_min_iff {n m : ℕ} :
  n + m = min n m ↔ n = 0 ∧ m = 0 :=
begin
  rw ←max_eq_zero_iff,
  cases le_total n m with H H;
  simp [H]
end

lemma one_le_of_lt {n m : ℕ} (h : n < m) : 1 ≤ m :=
lt_of_le_of_lt (nat.zero_le _) h

theorem eq_one_of_mul_eq_one_right {m n : ℕ} (H : m * n = 1) : m = 1 :=
eq_one_of_dvd_one ⟨n, H.symm⟩

theorem eq_one_of_mul_eq_one_left {m n : ℕ} (H : m * n = 1) : n = 1 :=
eq_one_of_mul_eq_one_right (by rwa mul_comm)

/-! ### `succ` -/

theorem eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬ a < b) : a = b :=
have h3 : a ≤ b, from le_of_lt_succ h1,
or.elim (eq_or_lt_of_not_lt h2) (λ h, h) (λ h, absurd h (not_lt_of_ge h3))

lemma eq_of_le_of_lt_succ {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
nat.le_antisymm (le_of_succ_le_succ h₂) h₁

theorem one_add (n : ℕ) : 1 + n = succ n := by simp [add_comm]

@[simp] lemma succ_pos' {n : ℕ} : 0 < succ n := succ_pos n

theorem succ_inj' {n m : ℕ} : succ n = succ m ↔ n = m :=
⟨succ.inj, congr_arg _⟩

theorem succ_injective : function.injective nat.succ := λ x y, succ.inj

lemma succ_ne_succ {n m : ℕ} : succ n ≠ succ m ↔ n ≠ m :=
succ_injective.ne_iff

@[simp] lemma succ_succ_ne_one (n : ℕ) : n.succ.succ ≠ 1 :=
succ_ne_succ.mpr n.succ_ne_zero

@[simp] lemma one_lt_succ_succ (n : ℕ) : 1 < n.succ.succ :=
succ_lt_succ $ succ_pos n

theorem succ_le_succ_iff {m n : ℕ} : succ m ≤ succ n ↔ m ≤ n :=
⟨le_of_succ_le_succ, succ_le_succ⟩

theorem max_succ_succ {m n : ℕ} :
  max (succ m) (succ n) = succ (max m n) :=
begin
  by_cases h1 : m ≤ n,
  rw [max_eq_right h1, max_eq_right (succ_le_succ h1)],
  { rw not_le at h1, have h2 := le_of_lt h1,
    rw [max_eq_left h2, max_eq_left (succ_le_succ h2)] }
end

lemma not_succ_lt_self {n : ℕ} : ¬succ n < n :=
not_lt_of_ge (nat.le_succ _)

theorem lt_succ_iff {m n : ℕ} : m < succ n ↔ m ≤ n :=
⟨le_of_lt_succ, lt_succ_of_le⟩

lemma succ_le_iff {m n : ℕ} : succ m ≤ n ↔ m < n :=
lt_iff_add_one_le.symm

-- just for linarith. Feel free to remove it if you manage to make linarith look up the instance
lemma lt_iff_add_one_le {m n : ℕ} : m < n ↔ m + 1 ≤ n :=
lt_iff_add_one_le

-- Just a restatement of `nat.lt_succ_iff` using `+1`.
lemma lt_add_one_iff {a b : ℕ} : a < b + 1 ↔ a ≤ b :=
lt_succ_iff

-- A flipped version of `lt_add_one_iff`.
lemma lt_one_add_iff {a b : ℕ} : a < 1 + b ↔ a ≤ b :=
by simp only [add_comm, lt_succ_iff]

-- This is true reflexively, by the definition of `≤` on ℕ,
-- but it's still useful to have, to convince Lean to change the syntactic type.
lemma add_one_le_iff {a b : ℕ} : a + 1 ≤ b ↔ a < b :=
iff.refl _

lemma one_add_le_iff {a b : ℕ} : 1 + a ≤ b ↔ a < b :=
by simp only [add_comm, add_one_le_iff]

theorem of_le_succ {n m : ℕ} (H : n ≤ m.succ) : n ≤ m ∨ n = m.succ :=
H.lt_or_eq_dec.imp le_of_lt_succ id

lemma succ_lt_succ_iff {m n : ℕ} : succ m < succ n ↔ m < n :=
⟨lt_of_succ_lt_succ, succ_lt_succ⟩

@[simp] lemma lt_one_iff {n : ℕ} : n < 1 ↔ n = 0 :=
lt_succ_iff.trans le_zero_iff

lemma div_le_iff_le_mul_add_pred {m n k : ℕ} (n0 : 0 < n) : m / n ≤ k ↔ m ≤ n * k + (n - 1) :=
begin
  rw [← lt_succ_iff, div_lt_iff_lt_mul _ _ n0, succ_mul, mul_comm],
  cases n, {cases n0},
  exact lt_succ_iff,
end

/-! ### `add` -/

-- Sometimes a bare `nat.add` or similar appears as a consequence of unfolding
-- during pattern matching. These lemmas package them back up as typeclass
-- mediated operations.
@[simp] theorem add_def {a b : ℕ} : nat.add a b = a + b := rfl
@[simp] theorem mul_def {a b : ℕ} : nat.mul a b = a * b := rfl

attribute [simp] nat.add_sub_cancel nat.add_sub_cancel_left
attribute [simp] nat.sub_self

lemma exists_eq_add_of_le : ∀ {m n : ℕ}, m ≤ n → ∃ k : ℕ, n = m + k
| 0 0 h := ⟨0, by simp⟩
| 0 (n+1) h := ⟨n+1, by simp⟩
| (m+1) (n+1) h :=
  let ⟨k, hk⟩ := exists_eq_add_of_le (nat.le_of_succ_le_succ h) in
  ⟨k, by simp [hk, add_comm, add_left_comm]⟩

lemma exists_eq_add_of_lt : ∀ {m n : ℕ}, m < n → ∃ k : ℕ, n = m + k + 1
| 0 0 h := false.elim $ lt_irrefl _ h
| 0 (n+1) h := ⟨n, by simp⟩
| (m+1) (n+1) h := let ⟨k, hk⟩ := exists_eq_add_of_le (nat.le_of_succ_le_succ h) in
  ⟨k, by simp [hk]⟩

theorem add_pos_left {m : ℕ} (h : 0 < m) (n : ℕ) : 0 < m + n :=
calc
  m + n > 0 + n : nat.add_lt_add_right h n
    ... = n     : nat.zero_add n
    ... ≥ 0     : zero_le n

theorem add_pos_right (m : ℕ) {n : ℕ} (h : 0 < n) : 0 < m + n :=
begin rw add_comm, exact add_pos_left h m end

theorem add_pos_iff_pos_or_pos (m n : ℕ) : 0 < m + n ↔ 0 < m ∨ 0 < n :=
iff.intro
  begin
    intro h,
    cases m with m,
    {simp [zero_add] at h, exact or.inr h},
    exact or.inl (succ_pos _)
  end
  begin
    intro h, cases h with mpos npos,
    { apply add_pos_left mpos },
    apply add_pos_right _ npos
  end

lemma add_eq_one_iff : ∀ {a b : ℕ}, a + b = 1 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
| 0     0     := dec_trivial
| 0     1     := dec_trivial
| 1     0     := dec_trivial
| 1     1     := dec_trivial
| (a+2) _     := by rw add_right_comm; exact dec_trivial
| _     (b+2) := by rw [← add_assoc]; simp only [nat.succ_inj', nat.succ_ne_zero]; simp

theorem le_add_one_iff {i j : ℕ} : i ≤ j + 1 ↔ (i ≤ j ∨ i = j + 1) :=
⟨assume h,
  match nat.eq_or_lt_of_le h with
  | or.inl h := or.inr h
  | or.inr h := or.inl $ nat.le_of_succ_le_succ h
  end,
  or.rec (assume h, le_trans h $ nat.le_add_right _ _) le_of_eq⟩

lemma add_succ_lt_add {a b c d : ℕ} (hab : a < b) (hcd : c < d) : a + c + 1 < b + d :=
begin
  rw add_assoc,
  exact add_lt_add_of_lt_of_le hab (nat.succ_le_iff.2 hcd)
end

-- TODO: generalize to some ordered add_monoids, based on #6145
lemma le_of_add_le_left {a b c : ℕ} (h : a + b ≤ c) : a ≤ c :=
by { refine le_trans _ h, simp }

lemma le_of_add_le_right {a b c : ℕ} (h : a + b ≤ c) : b ≤ c :=
by { refine le_trans _ h, simp }

/-! ### `pred` -/

@[simp]
lemma add_succ_sub_one (n m : ℕ) : (n + succ m) - 1 = n + m :=
by rw [add_succ, succ_sub_one]

@[simp]
lemma succ_add_sub_one (n m : ℕ) : (succ n + m) - 1 = n + m :=
by rw [succ_add, succ_sub_one]

lemma pred_eq_sub_one (n : ℕ) : pred n = n - 1 := rfl

theorem pred_eq_of_eq_succ {m n : ℕ} (H : m = n.succ) : m.pred = n := by simp [H]

@[simp] lemma pred_eq_succ_iff {n m : ℕ} : pred n = succ m ↔ n = m + 2 :=
by cases n; split; rintro ⟨⟩; refl

theorem pred_sub (n m : ℕ) : pred n - m = pred (n - m) :=
by rw [← sub_one, nat.sub_sub, one_add]; refl

lemma le_pred_of_lt {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
nat.sub_le_sub_right h 1

lemma le_of_pred_lt {m n : ℕ} : pred m < n → m ≤ n :=
match m with
| 0 := le_of_lt
| m+1 := id
end

/-- This ensures that `simp` succeeds on `pred (n + 1) = n`. -/
@[simp] lemma pred_one_add (n : ℕ) : pred (1 + n) = n :=
by rw [add_comm, add_one, pred_succ]

/-! ### `sub` -/

protected theorem le_sub_add (n m : ℕ) : n ≤ n - m + m :=
or.elim (le_total n m)
  (assume : n ≤ m, begin rw [sub_eq_zero_of_le this, zero_add], exact this end)
  (assume : m ≤ n, begin rw (nat.sub_add_cancel this) end)

theorem sub_add_eq_max (n m : ℕ) : n - m + m = max n m :=
eq_max (nat.le_sub_add _ _) (le_add_left _ _) $ λ k h₁ h₂,
by rw ← nat.sub_add_cancel h₂; exact
add_le_add_right (nat.sub_le_sub_right h₁ _) _

theorem add_sub_eq_max (n m : ℕ) : n + (m - n) = max n m :=
by rw [add_comm, max_comm, sub_add_eq_max]

theorem sub_add_min (n m : ℕ) : n - m + min n m = n :=
(le_total n m).elim
  (λ h, by rw [min_eq_left h, sub_eq_zero_of_le h, zero_add])
  (λ h, by rw [min_eq_right h, nat.sub_add_cancel h])

protected theorem add_sub_cancel' {n m : ℕ} (h : m ≤ n) : m + (n - m) = n :=
by rw [add_comm, nat.sub_add_cancel h]

protected theorem sub_add_sub_cancel {a b c : ℕ} (hab : b ≤ a) (hbc : c ≤ b) :
  (a - b) + (b - c) = a - c :=
by rw [←nat.add_sub_assoc hbc, ←nat.sub_add_comm hab, nat.add_sub_cancel]

protected theorem sub_eq_of_eq_add (h : k = m + n) : k - m = n :=
begin rw [h, nat.add_sub_cancel_left] end

theorem sub_cancel {a b c : ℕ} (h₁ : a ≤ b) (h₂ : a ≤ c) (w : b - a = c - a) : b = c :=
by rw [←nat.sub_add_cancel h₁, ←nat.sub_add_cancel h₂, w]

lemma sub_sub_sub_cancel_right {a b c : ℕ} (h₂ : c ≤ b) : (a - c) - (b - c) = a - b :=
by rw [nat.sub_sub, ←nat.add_sub_assoc h₂, nat.add_sub_cancel_left]

lemma add_sub_cancel_right (n m k : ℕ) : n + (m + k) - k = n + m :=
by { rw [nat.add_sub_assoc, nat.add_sub_cancel], apply k.le_add_left }

protected lemma sub_add_eq_add_sub {a b c : ℕ} (h : b ≤ a) : (a - b) + c = (a + c) - b :=
by rw [add_comm a, nat.add_sub_assoc h, add_comm]

theorem sub_min (n m : ℕ) : n - min n m = n - m :=
nat.sub_eq_of_eq_add $ by rw [add_comm, sub_add_min]

theorem sub_sub_assoc {a b c : ℕ} (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
(nat.sub_eq_iff_eq_add (le_trans (nat.sub_le _ _) h₁)).2 $
by rw [add_right_comm, add_assoc, nat.sub_add_cancel h₂, nat.sub_add_cancel h₁]

protected theorem lt_of_sub_pos (h : 0 < n - m) : m < n :=
lt_of_not_ge
  (assume : n ≤ m,
    have n - m = 0, from sub_eq_zero_of_le this,
    begin rw this at h, exact lt_irrefl _ h end)

protected theorem lt_of_sub_lt_sub_right : m - k < n - k → m < n :=
lt_imp_lt_of_le_imp_le (λ h, nat.sub_le_sub_right h _)

protected theorem lt_of_sub_lt_sub_left : m - n < m - k → k < n :=
lt_imp_lt_of_le_imp_le (nat.sub_le_sub_left _)

protected theorem sub_lt_self (h₁ : 0 < m) (h₂ : 0 < n) : m - n < m :=
calc
  m - n = succ (pred m) - succ (pred n) : by rw [succ_pred_eq_of_pos h₁, succ_pred_eq_of_pos h₂]
    ... = pred m - pred n               : by rw succ_sub_succ
    ... ≤ pred m                        : sub_le _ _
    ... < succ (pred m)                 : lt_succ_self _
    ... = m                             : succ_pred_eq_of_pos h₁

protected theorem le_sub_right_of_add_le (h : m + k ≤ n) : m ≤ n - k :=
by rw ← nat.add_sub_cancel m k; exact nat.sub_le_sub_right h k

protected theorem le_sub_left_of_add_le (h : k + m ≤ n) : m ≤ n - k :=
nat.le_sub_right_of_add_le (by rwa add_comm at h)

protected theorem lt_sub_right_of_add_lt (h : m + k < n) : m < n - k :=
lt_of_succ_le $ nat.le_sub_right_of_add_le $
by rw succ_add; exact succ_le_of_lt h

protected theorem lt_sub_left_of_add_lt (h : k + m < n) : m < n - k :=
nat.lt_sub_right_of_add_lt (by rwa add_comm at h)

protected theorem add_lt_of_lt_sub_right (h : m < n - k) : m + k < n :=
@nat.lt_of_sub_lt_sub_right _ _ k (by rwa nat.add_sub_cancel)

protected theorem add_lt_of_lt_sub_left (h : m < n - k) : k + m < n :=
by rw add_comm; exact nat.add_lt_of_lt_sub_right h

protected theorem le_add_of_sub_le_right : n - k ≤ m → n ≤ m + k :=
le_imp_le_of_lt_imp_lt nat.lt_sub_right_of_add_lt

protected theorem le_add_of_sub_le_left : n - k ≤ m → n ≤ k + m :=
le_imp_le_of_lt_imp_lt nat.lt_sub_left_of_add_lt

protected theorem lt_add_of_sub_lt_right : n - k < m → n < m + k :=
lt_imp_lt_of_le_imp_le nat.le_sub_right_of_add_le

protected theorem lt_add_of_sub_lt_left : n - k < m → n < k + m :=
lt_imp_lt_of_le_imp_le nat.le_sub_left_of_add_le

protected theorem sub_le_left_of_le_add : n ≤ k + m → n - k ≤ m :=
le_imp_le_of_lt_imp_lt nat.add_lt_of_lt_sub_left

protected theorem sub_le_right_of_le_add : n ≤ m + k → n - k ≤ m :=
le_imp_le_of_lt_imp_lt nat.add_lt_of_lt_sub_right

protected theorem sub_lt_left_iff_lt_add (H : n ≤ k) : k - n < m ↔ k < n + m :=
⟨nat.lt_add_of_sub_lt_left,
 λ h₁,
  have succ k ≤ n + m,   from succ_le_of_lt h₁,
  have succ (k - n) ≤ m, from
    calc succ (k - n) = succ k - n : by rw (succ_sub H)
          ...     ≤ n + m - n      : nat.sub_le_sub_right this n
          ...     = m              : by rw nat.add_sub_cancel_left,
  lt_of_succ_le this⟩

protected theorem le_sub_left_iff_add_le (H : m ≤ k) : n ≤ k - m ↔ m + n ≤ k :=
le_iff_le_iff_lt_iff_lt.2 (nat.sub_lt_left_iff_lt_add H)

protected theorem le_sub_right_iff_add_le (H : n ≤ k) : m ≤ k - n ↔ m + n ≤ k :=
by rw [nat.le_sub_left_iff_add_le H, add_comm]

protected theorem lt_sub_left_iff_add_lt : n < k - m ↔ m + n < k :=
⟨nat.add_lt_of_lt_sub_left, nat.lt_sub_left_of_add_lt⟩

protected theorem lt_sub_right_iff_add_lt : m < k - n ↔ m + n < k :=
by rw [nat.lt_sub_left_iff_add_lt, add_comm]

theorem sub_le_left_iff_le_add : m - n ≤ k ↔ m ≤ n + k :=
le_iff_le_iff_lt_iff_lt.2 nat.lt_sub_left_iff_add_lt

theorem sub_le_right_iff_le_add : m - k ≤ n ↔ m ≤ n + k :=
by rw [nat.sub_le_left_iff_le_add, add_comm]

protected theorem sub_lt_right_iff_lt_add (H : k ≤ m) : m - k < n ↔ m < n + k :=
by rw [nat.sub_lt_left_iff_lt_add H, add_comm]

protected theorem sub_le_sub_left_iff (H : k ≤ m) : m - n ≤ m - k ↔ k ≤ n :=
⟨λ h,
  have k + (m - k) - n ≤ m - k, by rwa nat.add_sub_cancel' H,
  nat.le_of_add_le_add_right (nat.le_add_of_sub_le_left this),
nat.sub_le_sub_left _⟩

protected theorem sub_lt_sub_right_iff (H : k ≤ m) : m - k < n - k ↔ m < n :=
lt_iff_lt_of_le_iff_le (nat.sub_le_sub_right_iff _ _ _ H)

protected theorem sub_lt_sub_left_iff (H : n ≤ m) : m - n < m - k ↔ k < n :=
lt_iff_lt_of_le_iff_le (nat.sub_le_sub_left_iff H)

protected theorem sub_le_iff : m - n ≤ k ↔ m - k ≤ n :=
nat.sub_le_left_iff_le_add.trans nat.sub_le_right_iff_le_add.symm

protected lemma sub_le_self (n m : ℕ) : n - m ≤ n :=
nat.sub_le_left_of_le_add (nat.le_add_left _ _)

protected theorem sub_lt_iff (h₁ : n ≤ m) (h₂ : k ≤ m) : m - n < k ↔ m - k < n :=
(nat.sub_lt_left_iff_lt_add h₁).trans (nat.sub_lt_right_iff_lt_add h₂).symm

lemma pred_le_iff {n m : ℕ} : pred n ≤ m ↔ n ≤ succ m :=
@nat.sub_le_right_iff_le_add n m 1

lemma lt_pred_iff {n m : ℕ} : n < pred m ↔ succ n < m :=
@nat.lt_sub_right_iff_add_lt n 1 m

lemma lt_of_lt_pred {a b : ℕ} (h : a < b - 1) : a < b :=
lt_of_succ_lt (lt_pred_iff.1 h)

lemma le_or_le_of_add_eq_add_pred {a b c d : ℕ} (h : c + d = a + b - 1) : a ≤ c ∨ b ≤ d :=
begin
  cases le_or_lt a c with h' h'; [left, right],
  { exact h', },
  { replace h' := add_lt_add_right h' d, rw h at h',
    cases b.eq_zero_or_pos with hb hb, { rw hb, exact zero_le d, },
    rw [a.add_sub_assoc hb, add_lt_add_iff_left] at h',
    exact nat.le_of_pred_lt h', },
end

/-! ### `mul` -/

lemma succ_mul_pos (m : ℕ) (hn : 0 < n) : 0 < (succ m) * n :=
mul_pos (succ_pos m) hn

theorem mul_self_le_mul_self {n m : ℕ} (h : n ≤ m) : n * n ≤ m * m :=
decidable.mul_le_mul h h (zero_le _) (zero_le _)

theorem mul_self_lt_mul_self : Π {n m : ℕ}, n < m → n * n < m * m
| 0        m h := mul_pos h h
| (succ n) m h := decidable.mul_lt_mul h (le_of_lt h) (succ_pos _) (zero_le _)

theorem mul_self_le_mul_self_iff {n m : ℕ} : n ≤ m ↔ n * n ≤ m * m :=
⟨mul_self_le_mul_self, le_imp_le_of_lt_imp_lt mul_self_lt_mul_self⟩

theorem mul_self_lt_mul_self_iff {n m : ℕ} : n < m ↔ n * n < m * m :=
le_iff_le_iff_lt_iff_lt.1 mul_self_le_mul_self_iff

theorem le_mul_self : Π (n : ℕ), n ≤ n * n
| 0     := le_refl _
| (n+1) := let t := mul_le_mul_left (n+1) (succ_pos n) in by simp at t; exact t

lemma le_mul_of_pos_left {m n : ℕ} (h : 0 < n) : m ≤ n * m :=
begin
  conv {to_lhs, rw [← one_mul(m)]},
  exact decidable.mul_le_mul_of_nonneg_right (nat.succ_le_of_lt h) dec_trivial,
end

lemma le_mul_of_pos_right {m n : ℕ} (h : 0 < n) : m ≤ m * n :=
begin
  conv {to_lhs, rw [← mul_one(m)]},
  exact decidable.mul_le_mul_of_nonneg_left (nat.succ_le_of_lt h) dec_trivial,
end

theorem two_mul_ne_two_mul_add_one {n m} : 2 * n ≠ 2 * m + 1 :=
mt (congr_arg (%2)) (by { rw [add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt]; simp })

lemma mul_eq_one_iff : ∀ {a b : ℕ}, a * b = 1 ↔ a = 1 ∧ b = 1
| 0     0     := dec_trivial
| 0     1     := dec_trivial
| 1     0     := dec_trivial
| (a+2) 0     := by simp
| 0     (b+2) := by simp
| (a+1) (b+1) := ⟨
  λ h, by simp only [add_mul, mul_add, mul_add, one_mul, mul_one,
    (add_assoc _ _ _).symm, nat.succ_inj', add_eq_zero_iff] at h; simp [h.1.2, h.2],
  λ h, by simp only [h, mul_one]⟩

protected theorem mul_left_inj {a b c : ℕ} (ha : 0 < a) : b * a = c * a ↔ b = c :=
⟨nat.eq_of_mul_eq_mul_right ha, λ e, e ▸ rfl⟩

protected theorem mul_right_inj {a b c : ℕ} (ha : 0 < a) : a * b = a * c ↔ b = c :=
⟨nat.eq_of_mul_eq_mul_left ha, λ e, e ▸ rfl⟩

lemma mul_left_injective {a : ℕ} (ha : 0 < a) : function.injective (λ x, x * a) :=
λ _ _, eq_of_mul_eq_mul_right ha

lemma mul_right_injective {a : ℕ} (ha : 0 < a) : function.injective (λ x, a * x) :=
λ _ _, eq_of_mul_eq_mul_left ha

lemma mul_ne_mul_left {a b c : ℕ} (ha : 0 < a) : b * a ≠ c * a ↔ b ≠ c :=
(mul_left_injective ha).ne_iff

lemma mul_ne_mul_right {a b c : ℕ} (ha : 0 < a) : a * b ≠ a * c ↔ b ≠ c :=
(mul_right_injective ha).ne_iff

lemma mul_right_eq_self_iff {a b : ℕ} (ha : 0 < a) : a * b = a ↔ b = 1 :=
suffices a * b = a * 1 ↔ b = 1, by rwa mul_one at this,
nat.mul_right_inj ha

lemma mul_left_eq_self_iff {a b : ℕ} (hb : 0 < b) : a * b = b ↔ a = 1 :=
by rw [mul_comm, nat.mul_right_eq_self_iff hb]

lemma lt_succ_iff_lt_or_eq {n i : ℕ} : n < i.succ ↔ (n < i ∨ n = i) :=
lt_succ_iff.trans decidable.le_iff_lt_or_eq

theorem mul_self_inj {n m : ℕ} : n * n = m * m ↔ n = m :=
le_antisymm_iff.trans (le_antisymm_iff.trans
  (and_congr mul_self_le_mul_self_iff mul_self_le_mul_self_iff)).symm

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

@[simp] lemma rec_zero {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
  (nat.rec h0 h : Π n, C n) 0 = h0 :=
rfl

@[simp] lemma rec_add_one {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
  (nat.rec h0 h : Π n, C n) (n + 1) = h n ((nat.rec h0 h : Π n, C n) n) :=
rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. -/
@[elab_as_eliminator]
def le_rec_on {C : ℕ → Sort u} {n : ℕ} : Π {m : ℕ}, n ≤ m → (Π {k}, C k → C (k+1)) → C n → C m
| 0     H next x := eq.rec_on (eq_zero_of_le_zero H) x
| (m+1) H next x := or.by_cases (of_le_succ H) (λ h : n ≤ m, next $ le_rec_on h @next x)
  (λ h : n = m + 1, eq.rec_on h x)

theorem le_rec_on_self {C : ℕ → Sort u} {n} {h : n ≤ n} {next} (x : C n) :
  (le_rec_on h next x : C n) = x :=
by cases n; unfold le_rec_on or.by_cases; rw [dif_neg n.not_succ_le_self, dif_pos rfl]

theorem le_rec_on_succ {C : ℕ → Sort u} {n m} (h1 : n ≤ m) {h2 : n ≤ m+1} {next} (x : C n) :
  (le_rec_on h2 @next x : C (m+1)) = next (le_rec_on h1 @next x : C m) :=
by conv { to_lhs, rw [le_rec_on, or.by_cases, dif_pos h1] }

theorem le_rec_on_succ' {C : ℕ → Sort u} {n} {h : n ≤ n+1} {next} (x : C n) :
  (le_rec_on h next x : C (n+1)) = next x :=
by rw [le_rec_on_succ (le_refl n), le_rec_on_self]

theorem le_rec_on_trans {C : ℕ → Sort u} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
  (le_rec_on (le_trans hnm hmk) @next x : C k) = le_rec_on hmk @next (le_rec_on hnm @next x) :=
begin
  induction hmk with k hmk ih, { rw le_rec_on_self },
  rw [le_rec_on_succ (le_trans hnm hmk), ih, le_rec_on_succ]
end

theorem le_rec_on_succ_left {C : ℕ → Sort u} {n m} (h1 : n ≤ m) (h2 : n+1 ≤ m)
  {next : Π{{k}}, C k → C (k+1)} (x : C n) :
  (le_rec_on h2 next (next x) : C m) = (le_rec_on h1 next x : C m) :=
begin
  rw [subsingleton.elim h1 (le_trans (le_succ n) h2),
      le_rec_on_trans (le_succ n) h2, le_rec_on_succ']
end

theorem le_rec_on_injective {C : ℕ → Sort u} {n m} (hnm : n ≤ m)
  (next : Π n, C n → C (n+1)) (Hnext : ∀ n, function.injective (next n)) :
  function.injective (le_rec_on hnm next) :=
begin
  induction hnm with m hnm ih, { intros x y H, rwa [le_rec_on_self, le_rec_on_self] at H },
  intros x y H, rw [le_rec_on_succ hnm, le_rec_on_succ hnm] at H, exact ih (Hnext _ H)
end

theorem le_rec_on_surjective {C : ℕ → Sort u} {n m} (hnm : n ≤ m)
  (next : Π n, C n → C (n+1)) (Hnext : ∀ n, function.surjective (next n)) :
  function.surjective (le_rec_on hnm next) :=
begin
  induction hnm with m hnm ih, { intros x, use x, rw le_rec_on_self },
  intros x, rcases Hnext _ x with ⟨w, rfl⟩, rcases ih w with ⟨x, rfl⟩, use x, rw le_rec_on_succ
end

/-- Recursion principle based on `<`. -/
@[elab_as_eliminator]
protected def strong_rec' {p : ℕ → Sort u} (H : ∀ n, (∀ m, m < n → p m) → p n) : ∀ (n : ℕ), p n
| n := H n (λ m hm, strong_rec' m)

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_eliminator]
def strong_rec_on' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m, m < n → P m) → P n) : P n :=
nat.strong_rec' h n

theorem strong_rec_on_beta' {P : ℕ → Sort*} {h} {n : ℕ} :
  (strong_rec_on' n h : P n) = h n (λ m hmn, (strong_rec_on' m h : P m)) :=
by { simp only [strong_rec_on'], rw nat.strong_rec' }

/-- Induction principle starting at a non-zero number. For maps to a `Sort*` see `le_rec_on`. -/
@[elab_as_eliminator] lemma le_induction {P : nat → Prop} {m}
  (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
  ∀ n, m ≤ n → P n :=
by apply nat.less_than_or_equal.rec h0; exact h1

/-- Decreasing induction: if `P (k+1)` implies `P k`, then `P n` implies `P m` for all `m ≤ n`.
Also works for functions to `Sort*`. -/
@[elab_as_eliminator]
def decreasing_induction {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n : ℕ} (mn : m ≤ n)
  (hP : P n) : P m :=
le_rec_on mn (λ k ih hsk, ih $ h k hsk) (λ h, h) hP

@[simp] lemma decreasing_induction_self {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {n : ℕ}
  (nn : n ≤ n) (hP : P n) : (decreasing_induction h nn hP : P n) = hP :=
by { dunfold decreasing_induction, rw [le_rec_on_self] }

lemma decreasing_induction_succ {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n : ℕ} (mn : m ≤ n)
  (msn : m ≤ n + 1) (hP : P (n+1)) :
  (decreasing_induction h msn hP : P m) = decreasing_induction h mn (h n hP) :=
by { dunfold decreasing_induction, rw [le_rec_on_succ] }

@[simp] lemma decreasing_induction_succ' {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m : ℕ}
  (msm : m ≤ m + 1) (hP : P (m+1)) : (decreasing_induction h msm hP : P m) = h m hP :=
by { dunfold decreasing_induction, rw [le_rec_on_succ'] }

lemma decreasing_induction_trans {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n k : ℕ}
  (mn : m ≤ n) (nk : n ≤ k) (hP : P k) :
  (decreasing_induction h (le_trans mn nk) hP : P m) =
  decreasing_induction h mn (decreasing_induction h nk hP) :=
by { induction nk with k nk ih, rw [decreasing_induction_self],
     rw [decreasing_induction_succ h (le_trans mn nk), ih, decreasing_induction_succ] }

lemma decreasing_induction_succ_left {P : ℕ → Sort*} (h : ∀n, P (n+1) → P n) {m n : ℕ}
  (smn : m + 1 ≤ n) (mn : m ≤ n) (hP : P n) :
  (decreasing_induction h mn hP : P m) = h m (decreasing_induction h smn hP) :=
by { rw [subsingleton.elim mn (le_trans (le_succ m) smn), decreasing_induction_trans,
         decreasing_induction_succ'] }

/-! ### `div` -/

attribute [simp] nat.div_self

protected lemma div_le_of_le_mul' {m n : ℕ} {k} (h : m ≤ k * n) : m / k ≤ n :=
(eq_zero_or_pos k).elim
  (λ k0, by rw [k0, nat.div_zero]; apply zero_le)
  (λ k0, (_root_.mul_le_mul_left k0).1 $
    calc k * (m / k)
        ≤ m % k + k * (m / k) : le_add_left _ _
    ... = m                   : mod_add_div _ _
    ... ≤ k * n               : h)

protected lemma div_le_self' (m n : ℕ) : m / n ≤ m :=
(eq_zero_or_pos n).elim
  (λ n0, by rw [n0, nat.div_zero]; apply zero_le)
  (λ n0, nat.div_le_of_le_mul' $ calc
      m = 1 * m : (one_mul _).symm
    ... ≤ n * m : mul_le_mul_right _ n0)

/-- A version of `nat.div_lt_self` using successors, rather than additional hypotheses. -/
lemma div_lt_self' (n b : ℕ) : (n+1)/(b+2) < n+1 :=
nat.div_lt_self (nat.succ_pos n) (nat.succ_lt_succ (nat.succ_pos _))

theorem le_div_iff_mul_le' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y :=
le_div_iff_mul_le x y k0

theorem div_lt_iff_lt_mul' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x / k < y ↔ x < y * k :=
lt_iff_lt_of_le_iff_le $ le_div_iff_mul_le' k0

protected theorem div_le_div_right {n m : ℕ} (h : n ≤ m) {k : ℕ} : n / k ≤ m / k :=
(nat.eq_zero_or_pos k).elim (λ k0, by simp [k0]) $ λ hk,
(le_div_iff_mul_le' hk).2 $ le_trans (nat.div_mul_le_self _ _) h

lemma lt_of_div_lt_div {m n k : ℕ} : m / k < n / k → m < n :=
lt_imp_lt_of_le_imp_le $ λ h, nat.div_le_div_right h

protected lemma div_pos {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
nat.pos_of_ne_zero (λ h, lt_irrefl a
  (calc a = a % b : by simpa [h] using (mod_add_div a b).symm
      ... < b : nat.mod_lt a hb
      ... ≤ a : hba))

protected lemma div_lt_of_lt_mul {m n k : ℕ} (h : m < n * k) : m / n < k :=
lt_of_mul_lt_mul_left
  (calc n * (m / n) ≤ m % n + n * (m / n) : nat.le_add_left _ _
    ... = m : mod_add_div _ _
    ... < n * k : h)
  (nat.zero_le n)

lemma lt_mul_of_div_lt {a b c : ℕ} (h : a / c < b) (w : 0 < c) : a < b * c :=
lt_of_not_ge $ not_le_of_gt h ∘ (nat.le_div_iff_mul_le _ _ w).2

protected lemma div_eq_zero_iff {a b : ℕ} (hb : 0 < b) : a / b = 0 ↔ a < b :=
⟨λ h, by rw [← mod_add_div a b, h, mul_zero, add_zero]; exact mod_lt _ hb,
  λ h, by rw [← nat.mul_right_inj hb, ← @add_left_cancel_iff _ _ (a % b), mod_add_div,
    mod_eq_of_lt h, mul_zero, add_zero]⟩

protected lemma div_eq_zero {a b : ℕ} (hb : a < b) : a / b = 0 :=
(nat.div_eq_zero_iff $ (zero_le a).trans_lt hb).mpr hb

lemma eq_zero_of_le_div {a b : ℕ} (hb : 2 ≤ b) (h : a ≤ a / b) : a = 0 :=
eq_zero_of_mul_le hb $
  by rw mul_comm; exact (nat.le_div_iff_mul_le' (lt_of_lt_of_le dec_trivial hb)).1 h

lemma mul_div_le_mul_div_assoc (a b c : ℕ) : a * (b / c) ≤ (a * b) / c :=
if hc0 : c = 0 then by simp [hc0]
else (nat.le_div_iff_mul_le _ _ (nat.pos_of_ne_zero hc0)).2
  (by rw [mul_assoc]; exact mul_le_mul_left _ (nat.div_mul_le_self _ _))

lemma div_mul_div_le_div (a b c : ℕ) : ((a / c) * b) / a ≤ b / c :=
if ha0 : a = 0 then by simp [ha0]
else calc a / c * b / a ≤ b * a / c / a :
    nat.div_le_div_right (by rw [mul_comm];
        exact mul_div_le_mul_div_assoc _ _ _)
  ... = b / c : by rw [nat.div_div_eq_div_mul, mul_comm b, mul_comm c,
      nat.mul_div_mul _ _ (nat.pos_of_ne_zero ha0)]

lemma eq_zero_of_le_half {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
eq_zero_of_le_div (le_refl _) h

protected theorem eq_mul_of_div_eq_right {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = b * c :=
by rw [← H2, nat.mul_div_cancel' H1]

protected theorem div_eq_iff_eq_mul_right {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) :
  a / b = c ↔ a = b * c :=
⟨nat.eq_mul_of_div_eq_right H', nat.div_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) :
  a / b = c ↔ a = c * b :=
by rw mul_comm; exact nat.div_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_left {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = c * b :=
by rw [mul_comm, nat.eq_mul_of_div_eq_right H1 H2]

protected theorem mul_div_cancel_left' {a b : ℕ} (Hd :  a ∣ b) : a * (b / a) = b :=
by rw [mul_comm,nat.div_mul_cancel Hd]

/-! ### `mod`, `dvd` -/

lemma div_add_mod (m k : ℕ) : k * (m / k) + m % k = m :=
(nat.add_comm _ _).trans (mod_add_div _ _)

lemma mod_add_div' (m k : ℕ) : m % k + (m / k) * k = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : ℕ) : (m / k) * k + m % k = m :=
by { rw mul_comm, exact div_add_mod _ _ }

protected theorem div_mod_unique {n k m d : ℕ} (h : 0 < k) :
  n / k = d ∧ n % k = m ↔ m + k * d = n ∧ m < k :=
⟨λ ⟨e₁, e₂⟩, e₁ ▸ e₂ ▸ ⟨mod_add_div _ _, mod_lt _ h⟩,
 λ ⟨h₁, h₂⟩, h₁ ▸ by rw [add_mul_div_left _ _ h, add_mul_mod_self_left];
   simp [div_eq_of_lt, mod_eq_of_lt, h₂]⟩

lemma two_mul_odd_div_two {n : ℕ} (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 :=
by conv {to_rhs, rw [← nat.mod_add_div n 2, hn, nat.add_sub_cancel_left]}

lemma div_dvd_of_dvd {a b : ℕ} (h : b ∣ a) : (a / b) ∣ a :=
⟨b, (nat.div_mul_cancel h).symm⟩

protected lemma div_div_self : ∀ {a b : ℕ}, b ∣ a → 0 < a → a / (a / b) = b
| a     0     h₁ h₂ := by rw [eq_zero_of_zero_dvd h₁, nat.div_zero, nat.div_zero]
| 0     b     h₁ h₂ := absurd h₂ dec_trivial
| (a+1) (b+1) h₁ h₂ :=
(nat.mul_left_inj (nat.div_pos (le_of_dvd (succ_pos a) h₁) (succ_pos b))).1 $
  by rw [nat.div_mul_cancel (div_dvd_of_dvd h₁), nat.mul_div_cancel' h₁]

lemma mod_mul_right_div_self (a b c : ℕ) : a % (b * c) / b = (a / b) % c :=
begin
  rcases eq_zero_or_pos b with rfl|hb, { simp },
  rcases eq_zero_or_pos c with rfl|hc, { simp },
  conv_rhs { rw ← mod_add_div a (b * c) },
  rw [mul_assoc, nat.add_mul_div_left _ _ hb, add_mul_mod_self_left,
    mod_eq_of_lt (nat.div_lt_of_lt_mul (mod_lt _ (mul_pos hb hc)))]
end

lemma mod_mul_left_div_self (a b c : ℕ) : a % (c * b) / b = (a / b) % c :=
by rw [mul_comm c, mod_mul_right_div_self]

@[simp] protected theorem dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 :=
⟨eq_one_of_dvd_one, λ e, e.symm ▸ dvd_refl _⟩

protected theorem dvd_add_left {k m n : ℕ} (h : k ∣ n) : k ∣ m + n ↔ k ∣ m :=
(nat.dvd_add_iff_left h).symm

protected theorem dvd_add_right {k m n : ℕ} (h : k ∣ m) : k ∣ m + n ↔ k ∣ n :=
(nat.dvd_add_iff_right h).symm

@[simp] protected theorem not_two_dvd_bit1 (n : ℕ) : ¬ 2 ∣ bit1 n :=
by { rw [bit1, nat.dvd_add_right two_dvd_bit0, nat.dvd_one], cc }

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_left {m n : ℕ} :
  m ∣ m + n ↔ m ∣ n :=
nat.dvd_add_right (dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_right {m n : ℕ} :
  m ∣ n + m ↔ m ∣ n :=
nat.dvd_add_left (dvd_refl m)

-- TODO: update `nat.dvd_sub` in core
lemma dvd_sub' {k m n : ℕ} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
begin
  cases le_total n m with H H,
  { exact dvd_sub H h₁ h₂ },
  { rw nat.sub_eq_zero_of_le H,
    exact dvd_zero k },
end

lemma not_dvd_of_pos_of_lt {a b : ℕ} (h1 : 0 < b) (h2 : b < a) : ¬ a ∣ b :=
begin
  rintros ⟨c, rfl⟩,
  rcases eq_zero_or_pos c with (rfl | hc),
  { exact lt_irrefl 0 h1 },
  { exact not_lt.2 (le_mul_of_pos_right hc) h2 },
end

protected theorem mul_dvd_mul_iff_left {a b c : ℕ} (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
exists_congr $ λ d, by rw [mul_assoc, nat.mul_right_inj ha]

protected theorem mul_dvd_mul_iff_right {a b c : ℕ} (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b :=
exists_congr $ λ d, by rw [mul_right_comm, nat.mul_left_inj hc]

lemma succ_div : ∀ (a b : ℕ), (a + 1) / b =
  a / b + if b ∣ a + 1 then 1 else 0
| a     0     := by simp
| 0     1     := by simp
| 0     (b+2) := have hb2 : b + 2 > 1, from dec_trivial,
  by simp [ne_of_gt hb2, div_eq_of_lt hb2]
| (a+1) (b+1) := begin
  rw [nat.div_def], conv_rhs { rw nat.div_def },
  by_cases hb_eq_a : b = a + 1,
  { simp [hb_eq_a, le_refl] },
  by_cases hb_le_a1 : b ≤ a + 1,
  { have hb_le_a : b ≤ a, from le_of_lt_succ (lt_of_le_of_ne hb_le_a1 hb_eq_a),
    have h₁ : (0 < b + 1 ∧ b + 1 ≤ a + 1 + 1),
      from ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a1⟩,
    have h₂ : (0 < b + 1 ∧ b + 1 ≤ a + 1),
      from ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a⟩,
    have dvd_iff : b + 1 ∣ a - b + 1 ↔  b + 1 ∣ a + 1 + 1,
    { rw [nat.dvd_add_iff_left (dvd_refl (b + 1)),
        ← nat.add_sub_add_right a 1 b, add_comm (_ - _), add_assoc,
        nat.sub_add_cancel (succ_le_succ hb_le_a), add_comm 1] },
    have wf : a - b < a + 1, from lt_succ_of_le (nat.sub_le_self _ _),
    rw [if_pos h₁, if_pos h₂, nat.add_sub_add_right, nat.sub_add_comm hb_le_a,
      by exact have _ := wf, succ_div (a - b),
      nat.add_sub_add_right],
    simp [dvd_iff, succ_eq_add_one, add_comm 1, add_assoc] },
  { have hba : ¬ b ≤ a,
      from not_le_of_gt (lt_trans (lt_succ_self a) (lt_of_not_ge hb_le_a1)),
    have hb_dvd_a : ¬ b + 1 ∣ a + 2,
      from λ h, hb_le_a1 (le_of_succ_le_succ (le_of_dvd (succ_pos _) h)),
    simp [hba, hb_le_a1, hb_dvd_a], }
end

lemma succ_div_of_dvd {a b : ℕ} (hba : b ∣ a + 1) :
  (a + 1) / b = a / b + 1 :=
by rw [succ_div, if_pos hba]

lemma succ_div_of_not_dvd {a b : ℕ} (hba : ¬ b ∣ a + 1) :
  (a + 1) / b = a / b :=
by rw [succ_div, if_neg hba, add_zero]

@[simp] theorem mod_mod_of_dvd (n : nat) {m k : nat} (h : m ∣ k) : n % k % m = n % m :=
begin
  conv { to_rhs, rw ←mod_add_div n k },
  rcases h with ⟨t, rfl⟩, rw [mul_assoc, add_mul_mod_self_left]
end

@[simp] theorem mod_mod (a n : ℕ) : (a % n) % n = a % n :=
(eq_zero_or_pos n).elim
  (λ n0, by simp [n0])
  (λ npos, mod_eq_of_lt (mod_lt _ npos))

/--  If `a` and `b` are equal mod `c`, `a - b` is zero mod `c`. -/
lemma sub_mod_eq_zero_of_mod_eq {a b c : ℕ} (h : a % c = b % c) : (a - b) % c = 0 :=
by rw [←nat.mod_add_div a c, ←nat.mod_add_div b c, ←h, ←nat.sub_sub, nat.add_sub_cancel_left,
       ←nat.mul_sub_left_distrib, nat.mul_mod_right]

@[simp] lemma one_mod (n : ℕ) : 1 % (n + 2) = 1 := nat.mod_eq_of_lt (add_lt_add_right n.succ_pos 1)

lemma dvd_sub_mod (k : ℕ) : n ∣ (k - (k % n)) :=
⟨k / n, nat.sub_eq_of_eq_add (nat.mod_add_div k n).symm⟩

@[simp] theorem mod_add_mod (m n k : ℕ) : (m % n + k) % n = (m + k) % n :=
by have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm;
   rwa [add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : ℕ) : (m + n % k) % k = (m + n) % k :=
by rw [add_comm, mod_add_mod, add_comm]

lemma add_mod (a b n : ℕ) : (a + b) % n = ((a % n) + (b % n)) % n :=
by rw [add_mod_mod, mod_add_mod]

theorem add_mod_eq_add_mod_right {m n k : ℕ} (i : ℕ) (H : m % n = k % n) :
  (m + i) % n = (k + i) % n :=
by rw [← mod_add_mod, ← mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℕ} (i : ℕ) (H : m % n = k % n) :
  (i + m) % n = (i + k) % n :=
by rw [add_comm, add_mod_eq_add_mod_right _ H, add_comm]

lemma add_mod_eq_ite {a b n : ℕ} :
  (a + b) % n = if n ≤ a % n + b % n then a % n + b % n - n else a % n + b % n :=
begin
  cases n, { simp },
  rw nat.add_mod,
  split_ifs with h,
  { rw [nat.mod_eq_sub_mod h, nat.mod_eq_of_lt],
    exact (nat.sub_lt_right_iff_lt_add h).mpr
        (nat.add_lt_add (a.mod_lt n.zero_lt_succ) (b.mod_lt n.zero_lt_succ)) },
  { exact nat.mod_eq_of_lt (lt_of_not_ge h) }
end

lemma mul_mod (a b n : ℕ) : (a * b) % n = ((a % n) * (b % n)) % n :=
begin
  conv_lhs {
    rw [←mod_add_div a n, ←mod_add_div' b n, right_distrib, left_distrib, left_distrib,
        mul_assoc, mul_assoc, ←left_distrib n _ _, add_mul_mod_self_left, ← mul_assoc,
        add_mul_mod_self_right] }
end

lemma dvd_div_of_mul_dvd {a b c : ℕ} (h : a * b ∣ c) : b ∣ c / a :=
if ha : a = 0 then
  by simp [ha]
else
  have ha : 0 < a, from nat.pos_of_ne_zero ha,
  have h1 : ∃ d, c = a * b * d, from h,
  let ⟨d, hd⟩ := h1 in
  have h2 : c / a = b * d, from nat.div_eq_of_eq_mul_right ha (by simpa [mul_assoc] using hd),
  show ∃ d, c / a = b * d, from ⟨d, h2⟩

lemma mul_dvd_of_dvd_div {a b c : ℕ} (hab : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
have h1 : ∃ d, b / c = a * d, from h,
have h2 : ∃ e, b = c * e, from hab,
let ⟨d, hd⟩ := h1, ⟨e, he⟩ := h2 in
have h3 : b = a * d * c, from
  nat.eq_mul_of_div_eq_left hab hd,
show ∃ d, b = c * a * d, from ⟨d, by cc⟩

lemma div_mul_div {a b c d : ℕ} (hab : b ∣ a) (hcd : d ∣ c) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
have exi1 : ∃ x, a = b * x, from hab,
have exi2 : ∃ y, c = d * y, from hcd,
if hb : b = 0 then by simp [hb]
else have 0 < b, from nat.pos_of_ne_zero hb,
if hd : d = 0 then by simp [hd]
else have 0 < d, from nat.pos_of_ne_zero hd,
begin
  cases exi1 with x hx, cases exi2 with y hy,
  rw [hx, hy, nat.mul_div_cancel_left, nat.mul_div_cancel_left],
  symmetry,
  apply nat.div_eq_of_eq_mul_left,
  apply mul_pos,
  repeat {assumption},
  cc
end

@[simp]
lemma div_div_div_eq_div : ∀ {a b c : ℕ} (dvd : b ∣ a) (dvd2 : a ∣ c), (c / (a / b)) / b = c / a
| 0 _ := by simp
| (a + 1) 0 := λ _ dvd _, by simpa using dvd
| (a + 1) (c + 1) :=
have a_split : a + 1 ≠ 0 := succ_ne_zero a,
have c_split : c + 1 ≠ 0 := succ_ne_zero c,
λ b dvd dvd2,
begin
  rcases dvd2 with ⟨k, rfl⟩,
  rcases dvd with ⟨k2, pr⟩,
  have k2_nonzero : k2 ≠ 0 := λ k2_zero, by simpa [k2_zero] using pr,
  rw [nat.mul_div_cancel_left k (nat.pos_of_ne_zero a_split), pr,
    nat.mul_div_cancel_left k2 (nat.pos_of_ne_zero c_split), nat.mul_comm ((c + 1) * k2) k,
    ←nat.mul_assoc k (c + 1) k2, nat.mul_div_cancel _ (nat.pos_of_ne_zero k2_nonzero),
    nat.mul_div_cancel _ (nat.pos_of_ne_zero c_split)],
end

lemma eq_of_dvd_of_div_eq_one {a b : ℕ} (w : a ∣ b) (h : b / a = 1) : a = b :=
by rw [←nat.div_mul_cancel w, h, one_mul]

lemma eq_zero_of_dvd_of_div_eq_zero {a b : ℕ} (w : a ∣ b) (h : b / a = 0) : b = 0 :=
by rw [←nat.div_mul_cancel w, h, zero_mul]

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
lemma eq_zero_of_dvd_of_lt {a b : ℕ} (w : a ∣ b) (h : b < a) : b = 0 :=
nat.eq_zero_of_dvd_of_div_eq_zero w
  ((nat.div_eq_zero_iff (lt_of_le_of_lt (zero_le b) h)).elim_right h)

lemma div_le_div_left {a b c : ℕ} (h₁ : c ≤ b) (h₂ : 0 < c) : a / b ≤ a / c :=
(nat.le_div_iff_mul_le _ _ h₂).2 $
  le_trans (mul_le_mul_left _ h₁) (div_mul_le_self _ _)

lemma div_eq_self {a b : ℕ} : a / b = a ↔ a = 0 ∨ b = 1 :=
begin
  split,
  { intro,
    cases b,
    { simp * at * },
    { cases b,
      { right, refl },
      { left,
        have : a / (b + 2) ≤ a / 2 := div_le_div_left (by simp) dec_trivial,
        refine eq_zero_of_le_half _,
        simp * at * } } },
  { rintros (rfl|rfl); simp }
end

lemma lt_iff_le_pred : ∀ {m n : ℕ}, 0 < n → (m < n ↔ m ≤ n - 1)
| m (n+1) _ := lt_succ_iff

lemma div_eq_sub_mod_div {m n : ℕ} : m / n = (m - m % n) / n :=
begin
  by_cases n0 : n = 0,
  { rw [n0, nat.div_zero, nat.div_zero] },
  { rw [← mod_add_div m n] { occs := occurrences.pos [2] },
    rw [nat.add_sub_cancel_left, mul_div_right _ (nat.pos_of_ne_zero n0)] }
end

lemma mul_div_le (m n : ℕ) : n * (m / n) ≤ m :=
begin
  cases nat.eq_zero_or_pos n with n0 h,
  { rw [n0, zero_mul], exact m.zero_le },
  { rw [mul_comm, ← nat.le_div_iff_mul_le' h] },
end

lemma lt_mul_div_succ (m : ℕ) {n : ℕ} (n0 : 0 < n) : m < n * ((m / n) + 1) :=
begin
  rw [mul_comm, ← nat.div_lt_iff_lt_mul' n0],
  exact lt_succ_self _
end

@[simp] lemma mod_div_self (m n : ℕ) : m % n / n = 0 :=
begin
  cases n,
  { exact (m % 0).div_zero },
  { exact nat.div_eq_zero (m.mod_lt n.succ_pos) }
end

/-- `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)` for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℕ) {n : ℕ} (hn : 0 < n) :
  (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬ n ∣ m :=
begin
  split,
  { rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩, rw [mul_lt_mul_left hn] at h1k h2k,
    rw [lt_succ_iff, ← not_lt] at h2k, exact h2k h1k },
  { intro h, rw [dvd_iff_mod_eq_zero, ← ne.def, ← pos_iff_ne_zero] at h,
    simp only [← mod_add_div m n] {single_pass := tt},
    refine ⟨m / n, lt_add_of_pos_left _ h, _⟩,
    rw [add_comm _ 1, left_distrib, mul_one], exact add_lt_add_right (mod_lt _ hn) _ }
end

/-- Two natural numbers are equal if and only if the have the same multiples. -/
lemma dvd_right_iff_eq {m n : ℕ} : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
⟨λ h, dvd_antisymm ((h _).mpr (dvd_refl _)) ((h _).mp (dvd_refl _)), λ h n, by rw h⟩

/-- Two natural numbers are equal if and only if the have the same divisors. -/
lemma dvd_left_iff_eq {m n : ℕ} : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
⟨λ h, dvd_antisymm ((h _).mp (dvd_refl _)) ((h _).mpr (dvd_refl _)), λ h n, by rw h⟩

/-- `dvd` is injective in the left argument -/
lemma dvd_left_injective : function.injective ((∣) : ℕ → ℕ → Prop) :=
λ m n h, dvd_right_iff_eq.mp $ λ a, iff_of_eq (congr_fun h a)

/-! ### `find` -/
section find

variables  {p q : ℕ → Prop} [decidable_pred p] [decidable_pred q]

lemma find_eq_iff (h : ∃ n : ℕ, p n) : nat.find h = m ↔ p m ∧ ∀ n < m, ¬ p n :=
begin
  split,
  { rintro rfl, exact ⟨nat.find_spec h, λ _, nat.find_min h⟩ },
  { rintro ⟨hm, hlt⟩,
    exact le_antisymm (nat.find_min' h hm) (not_lt.1 $ imp_not_comm.1 (hlt _) $ nat.find_spec h) }
end

@[simp] lemma find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : nat.find h < n ↔ ∃ m < n, p m :=
⟨λ h2, ⟨nat.find h, h2, nat.find_spec h⟩, λ ⟨m, hmn, hm⟩, (nat.find_min' h hm).trans_lt hmn⟩

@[simp] lemma find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : nat.find h ≤ n ↔ ∃ m ≤ n, p m :=
by simp only [exists_prop, ← lt_succ_iff, find_lt_iff]

@[simp] lemma le_find_iff (h : ∃ (n : ℕ), p n) (n : ℕ) : n ≤ nat.find h ↔ ∀ m < n, ¬ p m :=
by simp_rw [← not_lt, find_lt_iff, not_exists]

@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < nat.find h ↔ ∀ m ≤ n, ¬ p m :=
by simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]

@[simp] lemma find_eq_zero (h : ∃ n : ℕ, p n) : nat.find h = 0 ↔ p 0 :=
by simp [find_eq_iff]

@[simp] lemma find_pos (h : ∃ n : ℕ, p n) : 0 < nat.find h ↔ ¬ p 0 :=
by rw [pos_iff_ne_zero, ne, nat.find_eq_zero]

theorem find_le (h : ∀ n, q n → p n) (hp : ∃ n, p n) (hq : ∃ n, q n) :
  nat.find hp ≤ nat.find hq :=
nat.find_min' _ (h _ (nat.find_spec hq))

lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬ p 0) :
  nat.find h₁ = nat.find h₂ + 1 :=
begin
  refine (find_eq_iff _).2 ⟨nat.find_spec h₂, λ n hn, _⟩,
  cases n with n,
  exacts [h0, @nat.find_min (λ n, p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]
end

end find

/-! ### `find_greatest` -/
section find_greatest

/-- `find_greatest P b` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
protected def find_greatest (P : ℕ → Prop) [decidable_pred P] : ℕ → ℕ
| 0       := 0
| (n + 1) := if P (n + 1) then n + 1 else find_greatest n

variables {P : ℕ → Prop} [decidable_pred P]

@[simp] lemma find_greatest_zero : nat.find_greatest P 0 = 0 := rfl

@[simp] lemma find_greatest_eq : ∀{b}, P b → nat.find_greatest P b = b
| 0       h := rfl
| (n + 1) h := by simp [nat.find_greatest, h]

@[simp] lemma find_greatest_of_not {b} (h : ¬ P (b + 1)) :
  nat.find_greatest P (b + 1) = nat.find_greatest P b :=
by simp [nat.find_greatest, h]

lemma find_greatest_eq_iff {b m} :
  nat.find_greatest P b = m ↔ m ≤ b ∧ (m ≠ 0 → P m) ∧ (∀ ⦃n⦄, m < n → n ≤ b → ¬P n) :=
begin
  induction b with b ihb generalizing m,
  { rw [eq_comm, iff.comm],
    simp only [nonpos_iff_eq_zero, ne.def, and_iff_left_iff_imp, find_greatest_zero],
    rintro rfl,
    exact ⟨λ h, (h rfl).elim, λ n hlt heq, (hlt.ne heq.symm).elim⟩ },
  { by_cases hb : P (b + 1),
    { rw [find_greatest_eq hb], split,
      { rintro rfl,
        exact ⟨le_refl _, λ _, hb, λ n hlt hle, (hlt.not_le hle).elim⟩ },
      { rintros ⟨hle, h0, hm⟩,
        rcases decidable.eq_or_lt_of_le hle with rfl|hlt,
        exacts [rfl, (hm hlt (le_refl _) hb).elim] } },
    { rw [find_greatest_of_not hb, ihb],
      split,
      { rintros ⟨hle, hP, hm⟩,
        refine ⟨hle.trans b.le_succ, hP, λ n hlt hle, _⟩,
        rcases decidable.eq_or_lt_of_le hle with rfl|hlt',
        exacts [hb, hm hlt $ lt_succ_iff.1 hlt'] },
      { rintros ⟨hle, hP, hm⟩,
        refine ⟨lt_succ_iff.1 (hle.lt_of_ne _), hP, λ n hlt hle, hm hlt (hle.trans b.le_succ)⟩,
        rintro rfl,
        exact hb (hP b.succ_ne_zero) } } }
end

lemma find_greatest_eq_zero_iff {b} :
  nat.find_greatest P b = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ b → ¬P n :=
by simp [find_greatest_eq_iff]

lemma find_greatest_spec {b} (h : ∃m, m ≤ b ∧ P m) : P (nat.find_greatest P b) :=
begin
  rcases h with ⟨m, hmb, hm⟩,
  by_cases h : nat.find_greatest P b = 0,
  { cases m, { rwa h },
    exact ((find_greatest_eq_zero_iff.1 h) m.zero_lt_succ hmb hm).elim },
  { exact (find_greatest_eq_iff.1 rfl).2.1 h }
end

lemma find_greatest_le {b} : nat.find_greatest P b ≤ b :=
(find_greatest_eq_iff.1 rfl).1

lemma le_find_greatest {b m} (hmb : m ≤ b) (hm : P m) : m ≤ nat.find_greatest P b :=
le_of_not_lt $ λ hlt, (find_greatest_eq_iff.1 rfl).2.2 hlt hmb hm

lemma find_greatest_is_greatest {b k} (hk : nat.find_greatest P b < k) (hkb : k ≤ b) :
  ¬ P k :=
(find_greatest_eq_iff.1 rfl).2.2 hk hkb

lemma find_greatest_of_ne_zero {b m} (h : nat.find_greatest P b = m) (h0 : m ≠ 0) : P m :=
(find_greatest_eq_iff.1 h).2.1 h0

end find_greatest

/-! ### `bodd_div2` and `bodd` -/

@[simp] theorem bodd_div2_eq (n : ℕ) : bodd_div2 n = (bodd n, div2 n) :=
by unfold bodd div2; cases bodd_div2 n; refl

@[simp] lemma bodd_bit0 (n) : bodd (bit0 n) = ff := bodd_bit ff n
@[simp] lemma bodd_bit1 (n) : bodd (bit1 n) = tt := bodd_bit tt n

@[simp] lemma div2_bit0 (n) : div2 (bit0 n) = n := div2_bit ff n
@[simp] lemma div2_bit1 (n) : div2 (bit1 n) = n := div2_bit tt n

/-! ### `bit0` and `bit1` -/

-- There is no need to prove `bit0_eq_zero : bit0 n = 0 ↔ n = 0`
-- as this is true for any `[semiring R] [no_zero_divisors R] [char_zero R]`

-- However the lemmas `bit0_eq_bit0`, `bit1_eq_bit1`, `bit1_eq_one`, `one_eq_bit1`
-- need `[ring R] [no_zero_divisors R] [char_zero R]` in general,
-- so we prove `ℕ` specialized versions here.
@[simp] lemma bit0_eq_bit0 {m n : ℕ} : bit0 m = bit0 n ↔ m = n :=
⟨nat.bit0_inj, λ h, by subst h⟩

@[simp] lemma bit1_eq_bit1 {m n : ℕ} : bit1 m = bit1 n ↔ m = n :=
⟨nat.bit1_inj, λ h, by subst h⟩

@[simp] lemma bit1_eq_one {n : ℕ} : bit1 n = 1 ↔ n = 0 :=
⟨@nat.bit1_inj n 0, λ h, by subst h⟩
@[simp] lemma one_eq_bit1 {n : ℕ} : 1 = bit1 n ↔ n = 0 :=
⟨λ h, (@nat.bit1_inj 0 n h).symm, λ h, by subst h⟩

protected theorem bit0_le {n m : ℕ} (h : n ≤ m) : bit0 n ≤ bit0 m :=
add_le_add h h

protected theorem bit1_le {n m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m :=
succ_le_succ (add_le_add h h)

theorem bit_le : ∀ (b : bool) {n m : ℕ}, n ≤ m → bit b n ≤ bit b m
| tt n m h := nat.bit1_le h
| ff n m h := nat.bit0_le h

theorem bit_ne_zero (b) {n} (h : n ≠ 0) : bit b n ≠ 0 :=
by cases b; [exact nat.bit0_ne_zero h, exact nat.bit1_ne_zero _]

theorem bit0_le_bit : ∀ (b) {m n : ℕ}, m ≤ n → bit0 m ≤ bit b n
| tt m n h := le_of_lt $ nat.bit0_lt_bit1 h
| ff m n h := nat.bit0_le h

theorem bit_le_bit1 : ∀ (b) {m n : ℕ}, m ≤ n → bit b m ≤ bit1 n
| ff m n h := le_of_lt $ nat.bit0_lt_bit1 h
| tt m n h := nat.bit1_le h

theorem bit_lt_bit0 : ∀ (b) {n m : ℕ}, n < m → bit b n < bit0 m
| tt n m h := nat.bit1_lt_bit0 h
| ff n m h := nat.bit0_lt h

theorem bit_lt_bit (a b) {n m : ℕ} (h : n < m) : bit a n < bit b m :=
lt_of_lt_of_le (bit_lt_bit0 _ h) (bit0_le_bit _ (le_refl _))

@[simp] lemma bit0_le_bit1_iff : bit0 k ≤ bit1 n ↔ k ≤ n :=
⟨λ h, by rwa [← nat.lt_succ_iff, n.bit1_eq_succ_bit0, ← n.bit0_succ_eq,
  bit0_lt_bit0, nat.lt_succ_iff] at h, λ h, le_of_lt (nat.bit0_lt_bit1 h)⟩

@[simp] lemma bit0_lt_bit1_iff : bit0 k < bit1 n ↔ k ≤ n :=
⟨λ h, bit0_le_bit1_iff.1 (le_of_lt h), nat.bit0_lt_bit1⟩

@[simp] lemma bit1_le_bit0_iff : bit1 k ≤ bit0 n ↔ k < n :=
⟨λ h, by rwa [k.bit1_eq_succ_bit0, succ_le_iff, bit0_lt_bit0] at h,
  λ h, le_of_lt (nat.bit1_lt_bit0 h)⟩

@[simp] lemma bit1_lt_bit0_iff : bit1 k < bit0 n ↔ k < n :=
⟨λ h, bit1_le_bit0_iff.1 (le_of_lt h), nat.bit1_lt_bit0⟩

@[simp] lemma one_le_bit0_iff : 1 ≤ bit0 n ↔ 0 < n :=
by { convert bit1_le_bit0_iff, refl, }

@[simp] lemma one_lt_bit0_iff : 1 < bit0 n ↔ 1 ≤ n :=
by { convert bit1_lt_bit0_iff, refl, }

@[simp] lemma bit_le_bit_iff : ∀ {b : bool}, bit b k ≤ bit b n ↔ k ≤ n
| ff := bit0_le_bit0
| tt := bit1_le_bit1

@[simp] lemma bit_lt_bit_iff : ∀ {b : bool}, bit b k < bit b n ↔ k < n
| ff := bit0_lt_bit0
| tt := bit1_lt_bit1

@[simp] lemma bit_le_bit1_iff : ∀ {b : bool}, bit b k ≤ bit1 n ↔ k ≤ n
| ff := bit0_le_bit1_iff
| tt := bit1_le_bit1

@[simp] lemma bit0_mod_two : bit0 n % 2 = 0 := by { rw nat.mod_two_of_bodd, simp }

@[simp] lemma bit1_mod_two : bit1 n % 2 = 1 := by { rw nat.mod_two_of_bodd, simp }

lemma pos_of_bit0_pos {n : ℕ} (h : 0 < bit0 n) : 0 < n :=
by { cases n, cases h, apply succ_pos, }

/-- Define a function on `ℕ` depending on parity of the argument. -/
@[elab_as_eliminator]
def bit_cases {C : ℕ → Sort u} (H : Π b n, C (bit b n)) (n : ℕ) : C n :=
eq.rec_on n.bit_decomp (H (bodd n) (div2 n))

/-! ### decidability of predicates -/

instance decidable_ball_lt (n : nat) (P : Π k < n, Prop) :
  ∀ [H : ∀ n h, decidable (P n h)], decidable (∀ n h, P n h) :=
begin
  induction n with n IH; intro; resetI,
  { exact is_true (λ n, dec_trivial) },
  cases IH (λ k h, P k (lt_succ_of_lt h)) with h,
  { refine is_false (mt _ h), intros hn k h, apply hn },
  by_cases p : P n (lt_succ_self n),
  { exact is_true (λ k h',
     (le_of_lt_succ h').lt_or_eq_dec.elim (h _)
       (λ e, match k, e, h' with _, rfl, h := p end)) },
  { exact is_false (mt (λ hn, hn _ _) p) }
end

instance decidable_forall_fin {n : ℕ} (P : fin n → Prop)
  [H : decidable_pred P] : decidable (∀ i, P i) :=
decidable_of_iff (∀ k h, P ⟨k, h⟩) ⟨λ a ⟨k, h⟩, a k h, λ a k h, a ⟨k, h⟩⟩

instance decidable_ball_le (n : ℕ) (P : Π k ≤ n, Prop)
  [H : ∀ n h, decidable (P n h)] : decidable (∀ n h, P n h) :=
decidable_of_iff (∀ k (h : k < succ n), P k (le_of_lt_succ h))
⟨λ a k h, a k (lt_succ_of_le h), λ a k h, a k _⟩

instance decidable_lo_hi (lo hi : ℕ) (P : ℕ → Prop) [H : decidable_pred P] :
  decidable (∀x, lo ≤ x → x < hi → P x) :=
decidable_of_iff (∀ x < hi - lo, P (lo + x))
⟨λal x hl hh, by have := al (x - lo) (lt_of_not_ge $
  (not_congr (nat.sub_le_sub_right_iff _ _ _ hl)).2 $ not_le_of_gt hh);
  rwa [nat.add_sub_of_le hl] at this,
λal x h, al _ (nat.le_add_right _ _) (nat.add_lt_of_lt_sub_left h)⟩

instance decidable_lo_hi_le (lo hi : ℕ) (P : ℕ → Prop) [H : decidable_pred P] :
  decidable (∀x, lo ≤ x → x ≤ hi → P x) :=
decidable_of_iff (∀x, lo ≤ x → x < hi + 1 → P x) $
ball_congr $ λ x hl, imp_congr lt_succ_iff iff.rfl

instance decidable_exists_lt {P : ℕ → Prop} [h : decidable_pred P] :
  decidable_pred (λ n, ∃ (m : ℕ), m < n ∧ P m)
| 0 := is_false (by simp)
| (n + 1) := decidable_of_decidable_of_iff (@or.decidable _ _ (decidable_exists_lt n) (h n))
  (by simp only [lt_succ_iff_lt_or_eq, or_and_distrib_right, exists_or_distrib, exists_eq_left])

end nat
