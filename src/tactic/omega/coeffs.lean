/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/

/-
Non-constant terms of linear constraints are represented
by storing their coefficients in integer lists.
-/

import data.list.func
import tactic.ring
import tactic.omega.misc

namespace omega
namespace coeffs

open list.func

variable {v : nat → int}


/-- `val_between v as l o` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping all
    subterms that include variables outside the range `[l,l+o)` -/
@[simp] def val_between (v : nat → int) (as : list int) (l : nat) : nat → int
| 0     := 0
| (o+1) := (val_between o) + (get (l+o) as * v (l+o))

@[simp] lemma val_between_nil {l : nat} :
  ∀ m, val_between v [] l m = 0
| 0     := by simp only [val_between]
| (m+1) :=
  by simp only [val_between_nil m, omega.coeffs.val_between,
     get_nil, zero_add, zero_mul, int.default_eq_zero]

/-- Evaluation of the nonconstant component of a normalized linear arithmetic term. -/
def val (v : nat → int) (as : list int) : int :=
val_between v as 0 as.length

@[simp] lemma val_nil : val v [] = 0 := rfl

lemma val_between_eq_of_le {as : list int} {l : nat} :
  ∀ m, as.length ≤ l + m →
  val_between v as l m = val_between v as l (as.length - l)
| 0 h1 :=
  begin rw (nat.sub_eq_zero_iff_le.elim_right _), apply h1 end
| (m+1) h1 :=
  begin
    rw le_iff_eq_or_lt at h1, cases h1,
    { rw [h1, add_comm l, nat.add_sub_cancel] },
    have h2 :  list.length as ≤ l + m,
    { rw ← nat.lt_succ_iff, apply h1 },
    simpa [ get_eq_default_of_le _ h2, zero_mul, add_zero,
      val_between ] using val_between_eq_of_le _ h2
  end

lemma val_eq_of_le {as : list int} {k : nat} :
  as.length ≤ k → val v as = val_between v as 0 k :=
begin
  intro h1, unfold val,
  rw [val_between_eq_of_le k _], refl,
  rw zero_add, exact h1
end

lemma val_between_eq_val_between
  {v w : nat → int} {as bs : list int} {l : nat} :
  ∀ {m}, (∀ x, l ≤ x → x < l + m → v x = w x) →
    (∀ x, l ≤ x → x < l + m → get x as = get x bs) →
    val_between v as l m = val_between w bs l m
| 0 h1 h2 := rfl
| (m+1) h1 h2 :=
  begin
    unfold val_between,
    have h3 : l + m < l + (m + 1),
    { rw ← add_assoc, apply lt_add_one },
    apply fun_mono_2,
    apply val_between_eq_val_between; intros x h4 h5,
    { apply h1 _ h4 (lt_trans h5 h3) },
    { apply h2 _ h4 (lt_trans h5 h3) },
    rw [h1 _ _ h3, h2 _ _ h3];
    apply nat.le_add_right
  end

open_locale list.func

lemma val_between_set {a : int} {l n : nat} :
  ∀ {m}, l ≤ n → n < l + m → val_between v ([] {n ↦ a}) l m = a * v n
| 0 h1 h2 :=
  begin exfalso, apply lt_irrefl l (lt_of_le_of_lt h1 h2) end
| (m+1) h1 h2 :=
  begin
    rw [← add_assoc, nat.lt_succ_iff, le_iff_eq_or_lt] at h2,
    cases h2; unfold val_between,
    { have h3 : val_between v ([] {l + m ↦ a}) l m = 0,
      { apply @eq.trans _ _ (val_between v [] l m),
        { apply val_between_eq_val_between,
          { intros, refl },
          { intros x h4 h5, rw [get_nil,
            get_set_eq_of_ne, get_nil],
            apply ne_of_lt h5 } },
        apply val_between_nil },
      rw h2,
      simp only [h3, zero_add, list.func.get_set] },
    { have h3 : l + m ≠ n,
      { apply ne_of_gt h2 },
      rw [@val_between_set m h1 h2, get_set_eq_of_ne _ _ h3],
      simp only [h3, get_nil, add_zero, zero_mul, int.default_eq_zero] }
  end

@[simp] lemma val_set {m : nat} {a : int} :
  val v ([] {m ↦ a}) = a * v m :=
begin
  apply val_between_set, apply zero_le,
  apply lt_of_lt_of_le (lt_add_one _),
  simp only [length_set, zero_add, le_max_right],
  apply_instance,
end

lemma val_between_neg {as : list int} {l : nat} :
  ∀ {o}, val_between v (neg as) l o = -(val_between v as l o)
| 0 := rfl
| (o+1) :=
  begin
    unfold val_between,
    rw [neg_add, neg_mul_eq_neg_mul],
    apply fun_mono_2,
    apply val_between_neg,
    apply fun_mono_2 _ rfl,
    apply get_neg
  end

@[simp] lemma val_neg {as : list int} :
   val v (neg as) = -(val v as) :=
by simpa only [val, length_neg] using val_between_neg

lemma val_between_add {is js : list int} {l : nat} :
  ∀ m, val_between v (add is js) l m =
  (val_between v is l m) + (val_between v js l m)
| 0     := rfl
| (m+1) :=
  by { simp only [val_between, val_between_add m,
      list.func.get, get_add], ring }

@[simp] lemma val_add {is js : list int} :
  val v (add is js) = (val v is) + (val v js) :=
begin
  unfold val,
  rw val_between_add, apply fun_mono_2;
  apply val_between_eq_of_le;
  rw [zero_add, length_add],
  apply le_max_left, apply le_max_right
end

lemma val_between_sub {is js : list int} {l : nat} :
  ∀ m, val_between v (sub is js) l m =
  (val_between v is l m) - (val_between v js l m)
| 0 := rfl
| (m+1) :=
  by { simp only [val_between, val_between_sub m,
      list.func.get, get_sub], ring }

@[simp] lemma val_sub {is js : list int} :
  val v (sub is js) = (val v is) - (val v js) :=
begin
  unfold val,
  rw val_between_sub,
  apply fun_mono_2;
  apply val_between_eq_of_le;
  rw [zero_add, length_sub],
  apply le_max_left,
  apply le_max_right
end

/-- `val_except k v as` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping the
    subterm that includes the `k`th variable. -/
def val_except (k : nat) (v : nat → int) (as) :=
val_between v as 0 k + val_between v as (k+1) (as.length - (k+1))

lemma val_except_eq_val_except
  {k : nat} {is js : list int} {v w : nat → int} :
  (∀ x ≠ k, v x = w x) → (∀ x ≠ k, get x is = get x js) →
  val_except k v is = val_except k w js :=
begin
  intros h1 h2, unfold val_except,
  apply fun_mono_2,
  { apply val_between_eq_val_between;
    intros x h3 h4;
    [ {apply h1}, {apply h2} ];
    apply ne_of_lt;
    rw zero_add at h4;
    apply h4 },
  { repeat { rw ← val_between_eq_of_le
      ((max is.length js.length) - (k+1)) },
    { apply val_between_eq_val_between;
      intros x h3 h4;
      [ {apply h1}, {apply h2} ];
      apply ne.symm;
      apply ne_of_lt;
      rw lt_iff_add_one_le;
      exact h3 },
    repeat { rw add_comm,
             apply le_trans _ (nat.le_sub_add _ _),
            { apply le_max_right <|> apply le_max_left } } }
end

open_locale omega

lemma val_except_update_set
  {n : nat} {as : list int} {i j : int} :
  val_except n (v⟨n ↦ i⟩) (as {n ↦ j}) = val_except n v as :=
by apply val_except_eq_val_except update_eq_of_ne (get_set_eq_of_ne _)

lemma val_between_add_val_between {as : list int} {l m : nat} :
  ∀ {n}, val_between v as l m + val_between v as (l+m) n =
  val_between v as l (m+n)
| 0 := by simp only [val_between, add_zero]
| (n+1) :=
  begin
    rw ← add_assoc,
    unfold val_between,
    rw add_assoc,
    rw ← @val_between_add_val_between n,
    ring,
  end

lemma val_except_add_eq (n : nat) {as : list int} :
  (val_except n v as) + ((get n as) * (v n)) = val v as :=
begin
  unfold val_except, unfold val,
  by_cases h1 : n + 1 ≤ as.length,
  { have h4 := @val_between_add_val_between v as 0 (n+1) (as.length - (n+1)),
    have h5 : n + 1 + (as.length - (n + 1)) = as.length,
    { rw [add_comm, nat.sub_add_cancel h1] },
    rw h5 at h4, apply eq.trans _ h4,
     simp only [val_between, zero_add], ring },
  have h2 : (list.length as - (n + 1)) = 0,
  { apply nat.sub_eq_zero_of_le
    (le_trans (not_lt.1 h1) (nat.le_add_right _ _)) },
  have h3 : val_between v as 0 (list.length as) =
            val_between v as 0 (n + 1),
  { simpa only [val] using @val_eq_of_le v as (n+1)
      (le_trans (not_lt.1 h1) (nat.le_add_right _ _)) },
  simp only [add_zero, val_between, zero_add, h2, h3]
end

@[simp] lemma val_between_map_mul {i : int} {as: list int} {l : nat} :
  ∀ {m}, val_between v (list.map ((*) i) as) l m = i * val_between v as l m
| 0     := by simp only [val_between, mul_zero, list.map]
| (m+1) :=
  begin
    unfold val_between,
    rw [@val_between_map_mul m, mul_add],
    apply fun_mono_2 rfl,
    by_cases h1 : l + m < as.length,
    { rw [get_map h1, mul_assoc] },
    rw not_lt at h1,
    rw [get_eq_default_of_le, get_eq_default_of_le];
    try {simp}; apply h1
  end

lemma forall_val_dvd_of_forall_mem_dvd {i : int} {as : list int} :
  (∀ x ∈ as, i ∣ x) → (∀ n, i ∣ get n as) | h1 n :=
by { apply forall_val_of_forall_mem _ h1,
     apply dvd_zero }

lemma dvd_val_between {i} {as: list int} {l : nat} :
  ∀ {m}, (∀ x ∈ as, i ∣ x) → (i ∣ val_between v as l m)
| 0 h1 := dvd_zero _
| (m+1) h1 :=
  begin
    unfold val_between,
    apply dvd_add,
    apply dvd_val_between h1,
    apply dvd_mul_of_dvd_left,
    by_cases h2 : get (l+m) as = 0,
    { rw h2, apply dvd_zero },
    apply h1, apply mem_get_of_ne_zero h2
  end

lemma dvd_val {as : list int} {i : int} :
  (∀ x ∈ as, i ∣ x) → (i ∣ val v as) := by apply dvd_val_between

@[simp] lemma val_between_map_div
  {as: list int} {i : int} {l : nat} (h1 : ∀ x ∈ as, i ∣ x) :
  ∀ {m}, val_between v (list.map (λ x, x / i) as) l m = (val_between v as l m) / i
| 0     := by simp only [int.zero_div, val_between, list.map]
| (m+1) :=
  begin
    unfold val_between,
    rw [@val_between_map_div m, int.add_div_of_dvd_right],
    apply fun_mono_2 rfl,
    { apply calc get (l + m) (list.map (λ (x : ℤ), x / i) as) * v (l + m)
          = ((get (l + m) as) / i) * v (l + m) :
            begin
              apply fun_mono_2 _ rfl,
              rw get_map',
              apply int.zero_div
            end
      ... =  get (l + m) as * v (l + m) / i :
            begin
              repeat {rw mul_comm _ (v (l+m))},
              rw int.mul_div_assoc,
              apply forall_val_dvd_of_forall_mem_dvd h1
            end },
    apply dvd_mul_of_dvd_left,
    apply forall_val_dvd_of_forall_mem_dvd h1,
  end

@[simp] lemma val_map_div {as : list int} {i : int} :
  (∀ x ∈ as, i ∣ x) → val v (list.map (λ x, x / i) as) = (val v as) / i :=
by {intro h1, simpa only [val, list.length_map] using val_between_map_div h1}

lemma val_between_eq_zero {is: list int} {l : nat} :
  ∀ {m}, (∀ x : int, x ∈ is → x = 0) → val_between v is l m = 0
| 0 h1 := rfl
| (m+1) h1 :=
  begin
    have h2 := @forall_val_of_forall_mem _ _ is (λ x, x = 0) rfl h1,
    simpa only [val_between, h2 (l+m), zero_mul, add_zero]
      using @val_between_eq_zero m h1,
  end

lemma val_eq_zero {is : list int} :
  (∀ x : int, x ∈ is → x = 0) → val v is = 0 :=
by apply val_between_eq_zero

end coeffs

end omega
