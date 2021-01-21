/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import data.zmod.basic

/-!
# Dihedral Groups

We define the dihedral groups `dihedral n`, with elements `r i` and `sr i` for `i : zmod n`.

For `n ≠ 0`, `dihedral n` represents the symmetry group of the regular `n`-gon. `r i` represents
the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the `n`-gon.
`dihedral 0` corresponds to the infinite dihedral group.
-/

/--
For `n ≠ 0`, `dihedral n` represents the symmetry group of the regular `n`-gon. `r i` represents
the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the `n`-gon.
`dihedral 0` corresponds to the infinite dihedral group.
-/
@[derive decidable_eq]
inductive dihedral (n : ℕ) : Type
| r : zmod n → dihedral
| sr : zmod n → dihedral

namespace dihedral

variables {n : ℕ}

/--
Multiplication of the dihedral group.
-/
private def mul : dihedral n → dihedral n → dihedral n
| (r i) (r j) := r (i + j)
| (r i) (sr j) := sr (j - i)
| (sr i) (r j) := sr (i + j)
| (sr i) (sr j) := r (j - i)

/--
The identity `1` is the rotation by `0`.
-/
private def one : dihedral n := r 0

instance : inhabited (dihedral n) := ⟨one⟩

/--
The inverse of a an element of the dihedral group.
-/
private def inv : dihedral n → dihedral n
| (r i) := r (-i)
| (sr i) := sr i

/--
The group structure on `dihedral n`.
-/
instance : group (dihedral n) :=
{ mul := mul,
  mul_assoc :=
  begin
    rintros (a | a) (b | b) (c | c);
    simp only [mul];
    ring,
  end,
  one := one,
  one_mul :=
  begin
    rintros (a | a),
    exact congr_arg r (zero_add a),
    exact congr_arg sr (sub_zero a),
  end,
  mul_one := begin
    rintros (a | a),
    exact congr_arg r (add_zero a),
    exact congr_arg sr (add_zero a),
  end,
  inv := inv,
  mul_left_inv := begin
    rintros (a | a),
    exact congr_arg r (neg_add_self a),
    exact congr_arg r (sub_self a),
  end }

@[simp] lemma r_mul_r (i j : zmod n) : r i * r j = r (i + j) := rfl
@[simp] lemma r_mul_sr (i j : zmod n) : r i * sr j = sr (j - i) := rfl
@[simp] lemma sr_mul_r (i j : zmod n) : sr i * r j = sr (i + j) := rfl
@[simp] lemma sr_mul_sr (i j : zmod n) : sr i * sr j = r (j - i) := rfl

lemma one_def : (1 : dihedral n) = r 0 := rfl

private def fintype_helper : (zmod n ⊕ zmod n) ≃ dihedral n :=
{ inv_fun := λ i, match i with
                 | (r j) := sum.inl j
                 | (sr j) := sum.inr j
                 end,
  to_fun := λ i, match i with
                 | (sum.inl j) := r j
                 | (sum.inr j) := sr j
                 end,
  left_inv := by rintro (x | x); refl,
  right_inv := by rintro (x | x); refl }

/--
If `0 < n`, then `dihedral n` is a finite group.
-/
instance [fact (0 < n)] : fintype (dihedral n) := fintype.of_equiv _ fintype_helper

instance : nontrivial (dihedral n) := ⟨⟨r 0, sr 0, dec_trivial⟩⟩

/--
If `0 < n`, then `dihedral n` has `2n` elements.
-/
lemma card [fact (0 < n)] : fintype.card (dihedral n) = 2 * n :=
begin
  rw ←fintype.card_eq.mpr ⟨fintype_helper⟩,
  change fintype.card (zmod n ⊕ zmod n) = 2 * n,
  rw [fintype.card_sum, zmod.card, two_mul]
end

@[simp] lemma r_one_pow (k : ℕ) : (r 1 : dihedral n) ^ k = r k :=
begin
  induction k with k IH,
  { refl },
  { rw [pow_succ, IH, r_mul_r],
    congr' 1,
    norm_cast,
    rw nat.one_add }
end

@[simp] lemma r_one_pow_n : (r (1 : zmod n))^n = 1 :=
begin
  cases n,
  { rw pow_zero },
  { rw [r_one_pow, one_def],
    congr' 1,
    exact zmod.cast_self _, }
end

@[simp] lemma sr_mul_self (i : zmod n) : sr i * sr i = 1 := by rw [sr_mul_sr, sub_self, one_def]

/--
If `0 < n`, then `sr i` has order 2.
-/
@[simp] lemma order_of_sr [fact (0 < n)] (i : zmod n) : order_of (sr i) = 2 :=
begin
  rw order_of_eq_prime _ _,
  { exact nat.prime_two },
  rw [pow_two, sr_mul_self],
  dec_trivial,
end

/--
If `0 < n`, then `r 1` has order `n`.
-/
@[simp] lemma order_of_r_one [hnpos : fact (0 < n)] : order_of (r 1 : dihedral n) = n :=
begin
  cases lt_or_eq_of_le (nat.le_of_dvd hnpos (order_of_dvd_of_pow_eq_one (@r_one_pow_n n))) with h h,
  { have h1 : (r 1 : dihedral n)^(order_of (r 1)) = 1,
    { exact pow_order_of_eq_one _ },
    rw r_one_pow at h1,
    injection h1 with h2,
    rw [←zmod.val_eq_zero, zmod.val_cast_nat, nat.mod_eq_of_lt h] at h2,
    exact absurd h2.symm (ne_of_lt (order_of_pos _)) },
  { exact h }
end

/--
If `0 < n`, then `i : zmod n` has order `n / gcd n i`
-/
lemma order_of_r [fact (0 < n)] (i : zmod n) : order_of (r i) = n / nat.gcd n i.val :=
begin
  conv_lhs { rw ←zmod.cast_val i },
  rw [←r_one_pow, order_of_pow, order_of_r_one]
end

end dihedral
