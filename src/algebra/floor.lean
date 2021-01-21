/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import tactic.linarith
import tactic.abel
/-!
# Floor and Ceil

## Summary

We define `floor`, `ceil`, and `nat_ceil` functions on linear ordered rings.

## Main Definitions

- `floor_ring` is a linear ordered ring with floor function.
- `floor x` is the greatest integer `z` such that `z ≤ x`.
- `fract x` is the fractional part of x, that is `x - floor x`.
- `ceil x` is the smallest integer `z` such that `x ≤ z`.
- `nat_ceil x` is the smallest nonnegative integer `n` with `x ≤ n`.

## Notations

- `⌊x⌋` is `floor x`.
- `⌈x⌉` is `ceil x`.

## Tags

rounding
-/

variables {α : Type*}

open_locale classical

/--
A `floor_ring` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (x : α), z ≤ floor x ↔ (z : α) ≤ x)`.
-/
class floor_ring (α) [linear_ordered_ring α] :=
(floor : α → ℤ)
(le_floor : ∀ (z : ℤ) (x : α), z ≤ floor x ↔ (z : α) ≤ x)

instance : floor_ring ℤ := { floor := id, le_floor := λ _ _, by rw int.cast_id; refl }

variables [linear_ordered_ring α] [floor_ring α]

/-- `floor x` is the greatest integer `z` such that `z ≤ x` -/
def floor : α → ℤ := floor_ring.floor

notation `⌊` x `⌋` := floor x

theorem le_floor : ∀ {z : ℤ} {x : α}, z ≤ ⌊x⌋ ↔ (z : α) ≤ x :=
floor_ring.le_floor

theorem floor_lt {x : α} {z : ℤ} : ⌊x⌋ < z ↔ x < z :=
lt_iff_lt_of_le_iff_le le_floor

theorem floor_le (x : α) : (⌊x⌋ : α) ≤ x :=
le_floor.1 (le_refl _)

theorem floor_nonneg {x : α} : 0 ≤ ⌊x⌋ ↔ 0 ≤ x :=
by rw [le_floor]; refl

theorem lt_succ_floor (x : α) : x < ⌊x⌋.succ :=
floor_lt.1 $ int.lt_succ_self _

theorem lt_floor_add_one (x : α) : x < ⌊x⌋ + 1 :=
by simpa only [int.succ, int.cast_add, int.cast_one] using lt_succ_floor x

theorem sub_one_lt_floor (x : α) : x - 1 < ⌊x⌋ :=
sub_lt_iff_lt_add.2 (lt_floor_add_one x)

@[simp] theorem floor_coe (z : ℤ) : ⌊(z:α)⌋ = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

@[simp] theorem floor_zero : ⌊(0:α)⌋ = 0 := floor_coe 0

@[simp] theorem floor_one : ⌊(1:α)⌋ = 1 :=
by rw [← int.cast_one, floor_coe]

theorem floor_mono {a b : α} (h : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ :=
le_floor.2 (le_trans (floor_le _) h)

@[simp] theorem floor_add_int (x : α) (z : ℤ) : ⌊x + z⌋ = ⌊x⌋ + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

theorem floor_sub_int (x : α) (z : ℤ) : ⌊x - z⌋ = ⌊x⌋ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (floor_add_int _ _)

lemma abs_sub_lt_one_of_floor_eq_floor {α : Type*} [linear_ordered_comm_ring α]
  [floor_ring α] {x y : α} (h : ⌊x⌋ = ⌊y⌋) : abs (x - y) < 1 :=
begin
  have : x < ⌊x⌋ + 1         := lt_floor_add_one x,
  have : y < ⌊y⌋ + 1         :=  lt_floor_add_one y,
  have : (⌊x⌋ : α) = ⌊y⌋ := int.cast_inj.2 h,
  have : (⌊x⌋: α) ≤ x        := floor_le x,
  have : (⌊y⌋ : α) ≤ y       := floor_le y,
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
end

lemma floor_eq_iff {r : α} {z : ℤ} :
  ⌊r⌋ = z ↔ ↑z ≤ r ∧ r < (z + 1) :=
by rw [←le_floor, ←int.cast_one, ←int.cast_add, ←floor_lt,
int.lt_add_one_iff, le_antisymm_iff, and.comm]

lemma floor_ring_unique {α} [linear_ordered_ring α] (inst1 inst2 : floor_ring α) :
  @floor _ _ inst1 = @floor _ _ inst2 :=
begin
  ext v,
  suffices : (⌊v⌋ : α) ≤ v ∧ v < ⌊v⌋ + 1, by rwa [floor_eq_iff],
  exact ⟨floor_le v, lt_floor_add_one v⟩
end

lemma floor_eq_on_Ico (n : ℤ) : ∀ x ∈ (set.Ico n (n+1) : set α), floor x = n :=
λ x ⟨h₀, h₁⟩, floor_eq_iff.mpr ⟨h₀, h₁⟩

lemma floor_eq_on_Ico' (n : ℤ) : ∀ x ∈ (set.Ico n (n+1) : set α), (floor x : α) = n :=
λ x hx, by exact_mod_cast floor_eq_on_Ico n x hx

/-- The fractional part fract r of r is just r - ⌊r⌋ -/
def fract (r : α) : α := r - ⌊r⌋

-- Mathematical notation is usually {r}. Let's not even go there.

@[simp] lemma floor_add_fract (r : α) : (⌊r⌋ : α) + fract r = r := by unfold fract; simp

@[simp] lemma fract_add_floor (r : α) : fract r + ⌊r⌋ = r := sub_add_cancel _ _

theorem fract_nonneg (r : α) : 0 ≤ fract r :=
sub_nonneg.2 $ floor_le _

theorem fract_lt_one (r : α) : fract r < 1 :=
sub_lt.1 $ sub_one_lt_floor _

@[simp] lemma fract_zero : fract (0 : α) = 0 := by unfold fract; simp

@[simp] lemma fract_coe (z : ℤ) : fract (z : α) = 0 :=
by unfold fract; rw floor_coe; exact sub_self _

@[simp] lemma fract_floor (r : α) : fract (⌊r⌋ : α) = 0 := fract_coe _

@[simp] lemma floor_fract (r : α) : ⌊fract r⌋ = 0 :=
by rw floor_eq_iff; exact ⟨fract_nonneg _,
  by rw [int.cast_zero, zero_add]; exact fract_lt_one r⟩

theorem fract_eq_iff {r s : α} : fract r = s ↔ 0 ≤ s ∧ s < 1 ∧ ∃ z : ℤ, r - s = z :=
⟨λ h, by rw ←h; exact ⟨fract_nonneg _, fract_lt_one _,
  ⟨⌊r⌋, sub_sub_cancel _ _⟩⟩, begin
    intro h,
    show r - ⌊r⌋ = s, apply eq.symm,
    rw [eq_sub_iff_add_eq, add_comm, ←eq_sub_iff_add_eq],
    rcases h with ⟨hge, hlt, ⟨z, hz⟩⟩,
    rw [hz, int.cast_inj, floor_eq_iff, ←hz],
    clear hz, split; simpa [sub_eq_add_neg, add_assoc]
  end⟩

theorem fract_eq_fract {r s : α} : fract r = fract s ↔ ∃ z : ℤ, r - s = z :=
⟨λ h, ⟨⌊r⌋ - ⌊s⌋, begin
  unfold fract at h, rw [int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h],
 end⟩,
λ h, begin
  rcases h with ⟨z, hz⟩,
  rw fract_eq_iff,
  split, exact fract_nonneg _,
  split, exact fract_lt_one _,
  use z + ⌊s⌋,
  rw [eq_add_of_sub_eq hz, int.cast_add],
  unfold fract, simp [sub_eq_add_neg, add_assoc]
end⟩

@[simp] lemma fract_fract (r : α) : fract (fract r) = fract r :=
by rw fract_eq_fract; exact ⟨-⌊r⌋, by simp [sub_eq_add_neg, add_assoc, fract]⟩

theorem fract_add (r s : α) : ∃ z : ℤ, fract (r + s) - fract r - fract s = z :=
⟨⌊r⌋ + ⌊s⌋ - ⌊r + s⌋, by unfold fract; simp [sub_eq_add_neg]; abel⟩

theorem fract_mul_nat (r : α) (b : ℕ) : ∃ z : ℤ, fract r * b - fract (r * b) = z :=
begin
  induction b with c hc,
    use 0, simp,
  rcases hc with ⟨z, hz⟩,
  rw [nat.succ_eq_add_one, nat.cast_add, mul_add, mul_add, nat.cast_one, mul_one, mul_one],
  rcases fract_add (r * c) r with ⟨y, hy⟩,
  use z - y,
  rw [int.cast_sub, ←hz, ←hy],
  abel
end

/-- `ceil x` is the smallest integer `z` such that `x ≤ z` -/
def ceil (x : α) : ℤ := -⌊-x⌋

notation `⌈` x `⌉` := ceil x

theorem ceil_le {z : ℤ} {x : α} : ⌈x⌉ ≤ z ↔ x ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

theorem lt_ceil {x : α} {z : ℤ} : z < ⌈x⌉ ↔ (z:α) < x :=
lt_iff_lt_of_le_iff_le ceil_le

theorem ceil_le_floor_add_one (x : α) : ⌈x⌉ ≤ ⌊x⌋ + 1 :=
by rw [ceil_le, int.cast_add, int.cast_one]; exact le_of_lt (lt_floor_add_one x)

theorem le_ceil (x : α) : x ≤ ⌈x⌉ :=
ceil_le.1 (le_refl _)

@[simp] theorem ceil_coe (z : ℤ) : ⌈(z:α)⌉ = z :=
by rw [ceil, ← int.cast_neg, floor_coe, neg_neg]

theorem ceil_mono {a b : α} (h : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ :=
ceil_le.2 (le_trans h (le_ceil _))

@[simp] theorem ceil_add_int (x : α) (z : ℤ) : ⌈x + z⌉ = ⌈x⌉ + z :=
by rw [ceil, neg_add', floor_sub_int, neg_sub, sub_eq_neg_add]; refl

theorem ceil_sub_int (x : α) (z : ℤ) : ⌈x - z⌉ = ⌈x⌉ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (ceil_add_int _ _)

theorem ceil_lt_add_one (x : α) : (⌈x⌉ : α) < x + 1 :=
by rw [← lt_ceil, ← int.cast_one, ceil_add_int]; apply lt_add_one

lemma ceil_pos {a : α} : 0 < ⌈a⌉ ↔ 0 < a :=
⟨ λ h, have ⌊-a⌋ < 0, from neg_of_neg_pos h,
  pos_of_neg_neg $ lt_of_not_ge $ (not_iff_not_of_iff floor_nonneg).1 $ not_le_of_gt this,
 λ h, have -a < 0, from neg_neg_of_pos h,
  neg_pos_of_neg $ lt_of_not_ge $ (not_iff_not_of_iff floor_nonneg).2 $ not_le_of_gt this ⟩

@[simp] theorem ceil_zero : ⌈(0 : α)⌉ = 0 := by simp [ceil]

lemma ceil_nonneg {q : α} (hq : 0 ≤ q) : 0 ≤ ⌈q⌉ :=
if h : q > 0 then le_of_lt $ ceil_pos.2 h
else by rw [le_antisymm (le_of_not_lt h) hq, ceil_zero]; trivial

lemma ceil_eq_iff {r : α} {z : ℤ} :
  ⌈r⌉ = z ↔ ↑z-1 < r ∧ r ≤ z :=
by rw [←ceil_le, ←int.cast_one, ←int.cast_sub, ←lt_ceil,
int.sub_one_lt_iff, le_antisymm_iff, and.comm]

lemma ceil_eq_on_Ioc (n : ℤ) : ∀ x ∈ (set.Ioc (n-1) n : set α), ceil x = n :=
λ x ⟨h₀, h₁⟩, ceil_eq_iff.mpr ⟨h₀, h₁⟩

lemma ceil_eq_on_Ioc' (n : ℤ) : ∀ x ∈ (set.Ioc (n-1) n : set α), (ceil x : α) = n :=
λ x hx, by exact_mod_cast ceil_eq_on_Ioc n x hx

/--
`nat_ceil x` is the smallest nonnegative integer `n` with `x ≤ n`.
It is the same as `⌈q⌉` when `q ≥ 0`, otherwise it is `0`.
-/
def nat_ceil (a : α) : ℕ := int.to_nat (⌈a⌉)

theorem nat_ceil_le {a : α} {n : ℕ} : nat_ceil a ≤ n ↔ a ≤ n :=
by rw [nat_ceil, int.to_nat_le, ceil_le]; refl

theorem lt_nat_ceil {a : α} {n : ℕ} : n < nat_ceil a ↔ (n : α) < a :=
not_iff_not.1 $ by rw [not_lt, not_lt, nat_ceil_le]

theorem le_nat_ceil (a : α) : a ≤ nat_ceil a := nat_ceil_le.1 (le_refl _)

theorem nat_ceil_mono {a₁ a₂ : α} (h : a₁ ≤ a₂) : nat_ceil a₁ ≤ nat_ceil a₂ :=
nat_ceil_le.2 (le_trans h (le_nat_ceil _))

@[simp] theorem nat_ceil_coe (n : ℕ) : nat_ceil (n : α) = n :=
show (⌈((n : ℤ) : α)⌉).to_nat = n, by rw [ceil_coe]; refl

@[simp] theorem nat_ceil_zero : nat_ceil (0 : α) = 0 := nat_ceil_coe 0

theorem nat_ceil_add_nat {a : α} (a_nonneg : 0 ≤ a) (n : ℕ) : nat_ceil (a + n) = nat_ceil a + n :=
begin
  change int.to_nat (⌈a + (n:ℤ)⌉) = int.to_nat ⌈a⌉ + n,
  rw [ceil_add_int],
  have : 0 ≤ ⌈a⌉, by simpa using (ceil_mono a_nonneg),
  obtain ⟨_, ceil_a_eq⟩ : ∃ (n : ℕ), ⌈a⌉ = n, from int.eq_coe_of_zero_le this,
  rw ceil_a_eq,
  refl
end

theorem nat_ceil_lt_add_one {a : α} (a_nonneg : 0 ≤ a) :
  (nat_ceil a : α) < a + 1 :=
lt_nat_ceil.1 $ by rw (
  show nat_ceil (a + 1) = nat_ceil a + 1, by exact_mod_cast (nat_ceil_add_nat a_nonneg 1));
  apply nat.lt_succ_self

lemma lt_of_nat_ceil_lt {x : α} {n : ℕ} (h : nat_ceil x < n) : x < n :=
lt_of_le_of_lt (le_nat_ceil x) (by exact_mod_cast h)

lemma le_of_nat_ceil_le {x : α} {n : ℕ} (h : nat_ceil x ≤ n) : x ≤ n :=
le_trans (le_nat_ceil x) (by exact_mod_cast h)
