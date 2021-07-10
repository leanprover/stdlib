/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import data.int.modeq
import algebra.char_p.basic
import data.nat.totient
import ring_theory.ideal.operations
import tactic.fin_cases

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `zmod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

* `val_min_abs` returns the integer closest to zero in the equivalence class.

* A coercion `cast` is defined from `zmod n` into any ring.
This is a ring hom if the ring has characteristic dividing `n`

-/

namespace fin

/-!
## Ring structure on `fin n`

We define a commutative ring structure on `fin n`, but we do not register it as instance.
Afterwords, when we define `zmod n` in terms of `fin n`, we use these definitions
to register the ring structure on `zmod n` as type class instance.
-/

open nat nat.modeq int

/-- Multiplicative commutative semigroup structure on `fin (n+1)`. -/
instance (n : ℕ) : comm_semigroup (fin (n+1)) :=
{ mul_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
    (calc ((a * b) % (n+1) * c) ≡ a * b * c [MOD (n+1)] : modeq_mul (nat.mod_mod _ _) rfl
      ... ≡ a * (b * c) [MOD (n+1)] : by rw mul_assoc
      ... ≡ a * (b * c % (n+1)) [MOD (n+1)] : modeq_mul rfl (nat.mod_mod _ _).symm),
  mul_comm := λ ⟨a, _⟩ ⟨b, _⟩,
    fin.eq_of_veq (show (a * b) % (n+1) = (b * a) % (n+1), by rw mul_comm),
  ..fin.has_mul }

private lemma left_distrib_aux (n : ℕ) : ∀ a b c : fin (n+1), a * (b + c) = a * b + a * c :=
λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
(calc a * ((b + c) % (n+1)) ≡ a * (b + c) [MOD (n+1)] : modeq_mul rfl (nat.mod_mod _ _)
  ... ≡ a * b + a * c [MOD (n+1)] : by rw mul_add
  ... ≡ (a * b) % (n+1) + (a * c) % (n+1) [MOD (n+1)] :
        modeq_add (nat.mod_mod _ _).symm (nat.mod_mod _ _).symm)

/-- Commutative ring structure on `fin (n+1)`. -/
instance (n : ℕ) : comm_ring (fin (n+1)) :=
{ one_mul := fin.one_mul,
  mul_one := fin.mul_one,
  left_distrib := left_distrib_aux n,
  right_distrib := λ a b c, by rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm]; refl,
  ..fin.has_one,
  ..fin.add_comm_group n,
  ..fin.comm_semigroup n }

end fin

/-- The integers modulo `n : ℕ`. -/
def zmod : ℕ → Type
| 0     := ℤ
| (n+1) := fin (n+1)

namespace zmod

instance fintype : Π (n : ℕ) [fact (0 < n)], fintype (zmod n)
| 0     h := false.elim $ nat.not_lt_zero 0 h.1
| (n+1) _ := fin.fintype (n+1)

lemma card (n : ℕ) [fact (0 < n)] : fintype.card (zmod n) = n :=
begin
  casesI n,
  { exfalso, exact nat.not_lt_zero 0 (fact.out _) },
  { exact fintype.card_fin (n+1) }
end

instance decidable_eq : Π (n : ℕ), decidable_eq (zmod n)
| 0     := int.decidable_eq
| (n+1) := fin.decidable_eq _

instance has_repr : Π (n : ℕ), has_repr (zmod n)
| 0     := int.has_repr
| (n+1) := fin.has_repr _

instance comm_ring : Π (n : ℕ), comm_ring (zmod n)
| 0     := int.comm_ring
| (n+1) := fin.comm_ring n

instance inhabited (n : ℕ) : inhabited (zmod n) := ⟨0⟩

/-- `val a` is a natural number defined as:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

See `zmod.val_min_abs` for a variant that takes values in the integers.
-/
def val : Π {n : ℕ}, zmod n → ℕ
| 0     := int.nat_abs
| (n+1) := (coe : fin (n + 1) → ℕ)

lemma val_lt {n : ℕ} [fact (0 < n)] (a : zmod n) : a.val < n :=
begin
  casesI n,
  { exfalso, exact nat.not_lt_zero 0 (fact.out _) },
  exact fin.is_lt a
end

@[simp] lemma val_zero : ∀ {n}, (0 : zmod n).val = 0
| 0     := rfl
| (n+1) := rfl

@[simp] lemma val_one' : (1 : zmod 0).val = 1 := rfl
@[simp] lemma val_neg' {n : zmod 0} : (-n).val = n.val := by simp [val]
@[simp] lemma val_mul' {m n : zmod 0} : (m * n).val = m.val * n.val :=
by simp [val, int.nat_abs_mul]

lemma val_nat_cast {n : ℕ} (a : ℕ) : (a : zmod n).val = a % n :=
begin
  casesI n,
  { rw [nat.mod_zero, int.nat_cast_eq_coe_nat],
    exact int.nat_abs_of_nat a, },
  rw ← fin.of_nat_eq_coe,
  refl
end

instance (n : ℕ) : char_p (zmod n) n :=
{ cast_eq_zero_iff :=
  begin
    intro k,
    cases n,
    { simp only [int.nat_cast_eq_coe_nat, zero_dvd_iff, int.coe_nat_eq_zero], },
    rw [fin.eq_iff_veq],
    show (k : zmod (n+1)).val = (0 : zmod (n+1)).val ↔ _,
    rw [val_nat_cast, val_zero, nat.dvd_iff_mod_eq_zero],
  end }

@[simp] lemma nat_cast_self (n : ℕ) : (n : zmod n) = 0 :=
char_p.cast_eq_zero (zmod n) n

@[simp] lemma nat_cast_self' (n : ℕ) : (n + 1 : zmod (n + 1)) = 0 :=
by rw [← nat.cast_add_one, nat_cast_self (n + 1)]

section universal_property

variables {n : ℕ} {R : Type*}

section
variables [has_zero R] [has_one R] [has_add R] [has_neg R]

/-- Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `zmod.cast_hom` for a bundled version. -/
def cast : Π {n : ℕ}, zmod n → R
| 0     := int.cast
| (n+1) := λ i, i.val

-- see Note [coercion into rings]
@[priority 900] instance (n : ℕ) : has_coe_t (zmod n) R := ⟨cast⟩

@[simp] lemma cast_zero : ((0 : zmod n) : R) = 0 :=
by { cases n; refl }

end

/-- So-named because the coercion is `nat.cast` into `zmod`. For `nat.cast` into an arbitrary ring,
see `zmod.nat_cast_val`. -/
lemma nat_cast_zmod_val {n : ℕ} [fact (0 < n)] (a : zmod n) : (a.val : zmod n) = a :=
begin
  casesI n,
  { exfalso, exact nat.not_lt_zero 0 (fact.out _) },
  { apply fin.coe_coe_eq_self }
end

lemma nat_cast_right_inverse [fact (0 < n)] : function.right_inverse val (coe : ℕ → zmod n) :=
nat_cast_zmod_val

lemma nat_cast_zmod_surjective [fact (0 < n)] : function.surjective (coe : ℕ → zmod n) :=
nat_cast_right_inverse.surjective

/-- So-named because the outer coercion is `int.cast` into `zmod`. For `int.cast` into an arbitrary
ring, see `zmod.int_cast_cast`. -/
lemma int_cast_zmod_cast (a : zmod n) : ((a : ℤ) : zmod n) = a :=
begin
  cases n,
  { rw [int.cast_id a, int.cast_id a], },
  { rw [coe_coe, int.nat_cast_eq_coe_nat, int.cast_coe_nat, fin.coe_coe_eq_self] }
end

lemma int_cast_right_inverse : function.right_inverse (coe : zmod n → ℤ) (coe : ℤ → zmod n) :=
int_cast_zmod_cast

lemma int_cast_surjective : function.surjective (coe : ℤ → zmod n) :=
int_cast_right_inverse.surjective

@[norm_cast]
lemma cast_id : ∀ n (i : zmod n), ↑i = i
| 0     i := int.cast_id i
| (n+1) i := nat_cast_zmod_val i

@[simp]
lemma cast_id' : (coe : zmod n → zmod n) = id := funext (cast_id n)

variables (R) [ring R]

/-- The coercions are respectively `nat.cast` and `zmod.cast`. -/
@[simp] lemma nat_cast_comp_val [fact (0 < n)] :
  (coe : ℕ → R) ∘ (val : zmod n → ℕ) = coe :=
begin
  casesI n,
  { exfalso, exact nat.not_lt_zero 0 (fact.out _) },
  refl
end

/-- The coercions are respectively `int.cast`, `zmod.cast`, and `zmod.cast`. -/
@[simp] lemma int_cast_comp_cast : (coe : ℤ → R) ∘ (coe : zmod n → ℤ) = coe :=
begin
  cases n,
  { exact congr_arg ((∘) int.cast) zmod.cast_id', },
  { ext, simp }
end

variables {R}

@[simp] lemma nat_cast_val [fact (0 < n)] (i : zmod n) : (i.val : R) = i :=
congr_fun (nat_cast_comp_val R) i

@[simp] lemma int_cast_cast (i : zmod n) : ((i : ℤ) : R) = i :=
congr_fun (int_cast_comp_cast R) i

lemma coe_add_eq_ite {n : ℕ} (a b : zmod n) :
  (↑(a + b) : ℤ) = if (n : ℤ) ≤ a + b then a + b - n else a + b :=
begin
  cases n,
  { simp },
  simp only [coe_coe, fin.coe_add_eq_ite, int.nat_cast_eq_coe_nat,
             ← int.coe_nat_add, ← int.coe_nat_succ, int.coe_nat_le],
  split_ifs with h,
  { exact int.coe_nat_sub h },
  { refl }
end

section char_dvd
/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/

variables {n} {m : ℕ} [char_p R m]

@[simp] lemma cast_one (h : m ∣ n) : ((1 : zmod n) : R) = 1 :=
begin
  casesI n,
  { exact int.cast_one },
  show ((1 % (n+1) : ℕ) : R) = 1,
  cases n, { rw [nat.dvd_one] at h, substI m, apply subsingleton.elim },
  rw nat.mod_eq_of_lt,
  { exact nat.cast_one },
  exact nat.lt_of_sub_eq_succ rfl
end

lemma cast_add (h : m ∣ n) (a b : zmod n) : ((a + b : zmod n) : R) = a + b :=
begin
  casesI n,
  { apply int.cast_add },
  simp only [coe_coe],
  symmetry,
  erw [fin.coe_add, ← nat.cast_add, ← sub_eq_zero, ← nat.cast_sub (nat.mod_le _ _),
      @char_p.cast_eq_zero_iff R _ _ m],
  exact dvd_trans h (nat.dvd_sub_mod _),
end

lemma cast_mul (h : m ∣ n) (a b : zmod n) : ((a * b : zmod n) : R) = a * b :=
begin
  casesI n,
  { apply int.cast_mul },
  simp only [coe_coe],
  symmetry,
  erw [fin.coe_mul, ← nat.cast_mul, ← sub_eq_zero, ← nat.cast_sub (nat.mod_le _ _),
      @char_p.cast_eq_zero_iff R _ _ m],
  exact dvd_trans h (nat.dvd_sub_mod _),
end

/-- The canonical ring homomorphism from `zmod n` to a ring of characteristic `n`.

See also `zmod.lift` (in `data.zmod.quotient`) for a generalized version working in `add_group`s.
-/
def cast_hom (h : m ∣ n) (R : Type*) [ring R] [char_p R m] : zmod n →+* R :=
{ to_fun := coe,
  map_zero' := cast_zero,
  map_one' := cast_one h,
  map_add' := cast_add h,
  map_mul' := cast_mul h }

@[simp] lemma cast_hom_apply {h : m ∣ n} (i : zmod n) : cast_hom h R i = i := rfl

@[simp, norm_cast]
lemma cast_sub (h : m ∣ n) (a b : zmod n) : ((a - b : zmod n) : R) = a - b :=
(cast_hom h R).map_sub a b

@[simp, norm_cast]
lemma cast_neg (h : m ∣ n) (a : zmod n) : ((-a : zmod n) : R) = -a :=
(cast_hom h R).map_neg a

@[simp, norm_cast]
lemma cast_pow (h : m ∣ n) (a : zmod n) (k : ℕ) : ((a ^ k : zmod n) : R) = a ^ k :=
(cast_hom h R).map_pow a k

@[simp, norm_cast]
lemma cast_nat_cast (h : m ∣ n) (k : ℕ) : ((k : zmod n) : R) = k :=
(cast_hom h R).map_nat_cast k

@[simp, norm_cast]
lemma cast_int_cast (h : m ∣ n) (k : ℤ) : ((k : zmod n) : R) = k :=
(cast_hom h R).map_int_cast k

end char_dvd

section char_eq
/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/
variable [char_p R n]

@[simp] lemma cast_one' : ((1 : zmod n) : R) = 1 :=
cast_one (dvd_refl _)

@[simp] lemma cast_add' (a b : zmod n) : ((a + b : zmod n) : R) = a + b :=
cast_add (dvd_refl _) a b

@[simp] lemma cast_mul' (a b : zmod n) : ((a * b : zmod n) : R) = a * b :=
cast_mul (dvd_refl _) a b

@[simp] lemma cast_sub' (a b : zmod n) : ((a - b : zmod n) : R) = a - b :=
cast_sub (dvd_refl _) a b

@[simp] lemma cast_pow' (a : zmod n) (k : ℕ) : ((a ^ k : zmod n) : R) = a ^ k :=
cast_pow (dvd_refl _) a k

@[simp, norm_cast]
lemma cast_nat_cast' (k : ℕ) : ((k : zmod n) : R) = k :=
cast_nat_cast (dvd_refl _) k

@[simp, norm_cast]
lemma cast_int_cast' (k : ℤ) : ((k : zmod n) : R) = k :=
cast_int_cast (dvd_refl _) k

instance (R : Type*) [comm_ring R] [char_p R n] : algebra (zmod n) R :=
(zmod.cast_hom (dvd_refl n) R).to_algebra

variables (R)

lemma cast_hom_injective : function.injective (zmod.cast_hom (dvd_refl n) R) :=
begin
  rw ring_hom.injective_iff,
  intro x,
  obtain ⟨k, rfl⟩ := zmod.int_cast_surjective x,
  rw [ring_hom.map_int_cast, char_p.int_cast_eq_zero_iff R n,
    char_p.int_cast_eq_zero_iff (zmod n) n],
  exact id
end

lemma cast_hom_bijective [fintype R] (h : fintype.card R = n) :
  function.bijective (zmod.cast_hom (dvd_refl n) R) :=
begin
  haveI : fact (0 < n) :=
  ⟨begin
    rw [pos_iff_ne_zero],
    intro hn,
    rw hn at h,
    exact (fintype.card_eq_zero_iff.mp h).elim' 0
  end⟩,
  rw [fintype.bijective_iff_injective_and_card, zmod.card, h, eq_self_iff_true, and_true],
  apply zmod.cast_hom_injective
end

/-- The unique ring isomorphism between `zmod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
noncomputable def ring_equiv [fintype R] (h : fintype.card R = n) : zmod n ≃+* R :=
ring_equiv.of_bijective _ (zmod.cast_hom_bijective R h)

end char_eq

end universal_property

lemma int_coe_eq_int_coe_iff (a b : ℤ) (c : ℕ) :
  (a : zmod c) = (b : zmod c) ↔ a ≡ b [ZMOD c] :=
char_p.int_coe_eq_int_coe_iff (zmod c) c a b

lemma int_coe_eq_int_coe_iff' (a b : ℤ) (c : ℕ) :
  (a : zmod c) = (b : zmod c) ↔ a % c = b % c :=
zmod.int_coe_eq_int_coe_iff a b c

lemma nat_coe_eq_nat_coe_iff (a b c : ℕ) :
  (a : zmod c) = (b : zmod c) ↔ a ≡ b [MOD c] :=
begin
  convert zmod.int_coe_eq_int_coe_iff a b c,
  simp [nat.modeq.modeq_iff_dvd, int.modeq.modeq_iff_dvd],
end

lemma int_coe_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : zmod b) = 0 ↔ (b : ℤ) ∣ a :=
begin
  change (a : zmod b) = ((0 : ℤ) : zmod b) ↔ (b : ℤ) ∣ a,
  rw [zmod.int_coe_eq_int_coe_iff, int.modeq.modeq_zero_iff],
end

lemma nat_coe_zmod_eq_zero_iff_dvd (a b : ℕ) : (a : zmod b) = 0 ↔ b ∣ a :=
begin
  change (a : zmod b) = ((0 : ℕ) : zmod b) ↔ b ∣ a,
  rw [zmod.nat_coe_eq_nat_coe_iff, nat.modeq.modeq_zero_iff],
end

@[push_cast, simp]
lemma int_cast_mod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : zmod b) = (a : zmod b) :=
begin
  rw zmod.int_coe_eq_int_coe_iff,
  apply int.modeq.mod_modeq,
end

lemma ker_int_cast_add_hom (n : ℕ) :
  (int.cast_add_hom (zmod n)).ker = add_subgroup.gmultiples n :=
by { ext, rw [int.mem_gmultiples_iff, add_monoid_hom.mem_ker,
              int.coe_cast_add_hom, int_coe_zmod_eq_zero_iff_dvd] }

lemma ker_int_cast_ring_hom (n : ℕ) :
  (int.cast_ring_hom (zmod n)).ker = ideal.span ({n} : set ℤ) :=
by { ext, rw [ideal.mem_span_singleton, ring_hom.mem_ker,
              int.coe_cast_ring_hom, int_coe_zmod_eq_zero_iff_dvd] }

local attribute [semireducible] int.nonneg

@[simp] lemma nat_cast_to_nat (p : ℕ) :
  ∀ {z : ℤ} (h : 0 ≤ z), (z.to_nat : zmod p) = z
| (n : ℕ) h := by simp only [int.cast_coe_nat, int.to_nat_coe_nat]
| -[1+n]  h := false.elim h

lemma val_injective (n : ℕ) [fact (0 < n)] :
  function.injective (zmod.val : zmod n → ℕ) :=
begin
  casesI n,
  { exfalso, exact nat.not_lt_zero 0 (fact.out _) },
  assume a b h,
  ext,
  exact h
end

lemma val_one_eq_one_mod (n : ℕ) : (1 : zmod n).val = 1 % n :=
by rw [← nat.cast_one, val_nat_cast]

lemma val_one (n : ℕ) [fact (1 < n)] : (1 : zmod n).val = 1 :=
by { rw val_one_eq_one_mod, exact nat.mod_eq_of_lt (fact.out _) }

lemma val_add {n : ℕ} [fact (0 < n)] (a b : zmod n) : (a + b).val = (a.val + b.val) % n :=
begin
  casesI n,
  { exfalso, exact nat.not_lt_zero 0 (fact.out _) },
  { apply fin.val_add }
end

lemma val_mul {n : ℕ} (a b : zmod n) : (a * b).val = (a.val * b.val) % n :=
begin
  cases n,
  { rw nat.mod_zero, apply int.nat_abs_mul },
  { apply fin.val_mul }
end

instance nontrivial (n : ℕ) [fact (1 < n)] : nontrivial (zmod n) :=
⟨⟨0, 1, assume h, zero_ne_one $
   calc 0 = (0 : zmod n).val : by rw val_zero
      ... = (1 : zmod n).val : congr_arg zmod.val h
      ... = 1                : val_one n ⟩⟩

/-- The inversion on `zmod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`. -/
def inv : Π (n : ℕ), zmod n → zmod n
| 0     i := int.sign i
| (n+1) i := nat.gcd_a i.val (n+1)

instance (n : ℕ) : has_inv (zmod n) := ⟨inv n⟩

lemma inv_zero : ∀ (n : ℕ), (0 : zmod n)⁻¹ = 0
| 0     := int.sign_zero
| (n+1) := show (nat.gcd_a _ (n+1) : zmod (n+1)) = 0,
             by { rw val_zero, unfold nat.gcd_a nat.xgcd nat.xgcd_aux, refl }

lemma mul_inv_eq_gcd {n : ℕ} (a : zmod n) :
  a * a⁻¹ = nat.gcd a.val n :=
begin
  cases n,
  { calc a * a⁻¹ = a * int.sign a  : rfl
             ... = a.nat_abs   : by rw [int.mul_sign, int.nat_cast_eq_coe_nat]
             ... = a.val.gcd 0 : by rw nat.gcd_zero_right; refl },
  { set k := n.succ,
    calc a * a⁻¹ = a * a⁻¹ + k * nat.gcd_b (val a) k : by rw [nat_cast_self, zero_mul, add_zero]
             ... = ↑(↑a.val * nat.gcd_a (val a) k + k * nat.gcd_b (val a) k) :
                     by { push_cast, rw nat_cast_zmod_val, refl }
             ... = nat.gcd a.val k : (congr_arg coe (nat.gcd_eq_gcd_ab a.val k)).symm, }
end

@[simp] lemma nat_cast_mod (n : ℕ) (a : ℕ) : ((a % n : ℕ) : zmod n) = a :=
by conv {to_rhs, rw ← nat.mod_add_div a n}; simp

lemma eq_iff_modeq_nat (n : ℕ) {a b : ℕ} : (a : zmod n) = b ↔ a ≡ b [MOD n] :=
begin
  cases n,
  { simp only [nat.modeq, int.coe_nat_inj', nat.mod_zero, int.nat_cast_eq_coe_nat], },
  { rw [fin.ext_iff, nat.modeq, ← val_nat_cast, ← val_nat_cast], exact iff.rfl, }
end

lemma coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : nat.coprime x n) :
  (x * x⁻¹ : zmod n) = 1 :=
begin
  rw [nat.coprime, nat.gcd_comm, nat.gcd_rec] at h,
  rw [mul_inv_eq_gcd, val_nat_cast, h, nat.cast_one],
end

/-- `unit_of_coprime` makes an element of `units (zmod n)` given
  a natural number `x` and a proof that `x` is coprime to `n`  -/
def unit_of_coprime {n : ℕ} (x : ℕ) (h : nat.coprime x n) : units (zmod n) :=
⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩

@[simp] lemma coe_unit_of_coprime {n : ℕ} (x : ℕ) (h : nat.coprime x n) :
  (unit_of_coprime x h : zmod n) = x := rfl

lemma val_coe_unit_coprime {n : ℕ} (u : units (zmod n)) :
  nat.coprime (u : zmod n).val n :=
begin
  cases n,
  { rcases int.units_eq_one_or u with rfl|rfl; simp },
  apply nat.modeq.coprime_of_mul_modeq_one ((u⁻¹ : units (zmod (n+1))) : zmod (n+1)).val,
  have := units.ext_iff.1 (mul_right_inv u),
  rw [units.coe_one] at this,
  rw [← eq_iff_modeq_nat, nat.cast_one, ← this], clear this,
  rw [← nat_cast_zmod_val ((u * u⁻¹ : units (zmod (n+1))) : zmod (n+1))],
  rw [units.coe_mul, val_mul, nat_cast_mod],
end

@[simp] lemma inv_coe_unit {n : ℕ} (u : units (zmod n)) :
  (u : zmod n)⁻¹ = (u⁻¹ : units (zmod n)) :=
begin
  have := congr_arg (coe : ℕ → zmod n) (val_coe_unit_coprime u),
  rw [← mul_inv_eq_gcd, nat.cast_one] at this,
  let u' : units (zmod n) := ⟨u, (u : zmod n)⁻¹, this, by rwa mul_comm⟩,
  have h : u = u', { apply units.ext, refl },
  rw h,
  refl
end

lemma mul_inv_of_unit {n : ℕ} (a : zmod n) (h : is_unit a) :
  a * a⁻¹ = 1 :=
begin
  rcases h with ⟨u, rfl⟩,
  rw [inv_coe_unit, u.mul_inv],
end

lemma inv_mul_of_unit {n : ℕ} (a : zmod n) (h : is_unit a) :
  a⁻¹ * a = 1 :=
by rw [mul_comm, mul_inv_of_unit a h]

/-- Equivalence between the units of `zmod n` and
the subtype of terms `x : zmod n` for which `x.val` is comprime to `n` -/
def units_equiv_coprime {n : ℕ} [fact (0 < n)] :
  units (zmod n) ≃ {x : zmod n // nat.coprime x.val n} :=
{ to_fun := λ x, ⟨x, val_coe_unit_coprime x⟩,
  inv_fun := λ x, unit_of_coprime x.1.val x.2,
  left_inv := λ ⟨_, _, _, _⟩, units.ext (nat_cast_zmod_val _),
  right_inv := λ ⟨_, _⟩, by simp }

section totient
open_locale nat

@[simp] lemma card_units_eq_totient (n : ℕ) [fact (0 < n)] :
  fintype.card (units (zmod n)) = φ n :=
calc fintype.card (units (zmod n)) = fintype.card {x : zmod n // x.val.coprime n} :
  fintype.card_congr zmod.units_equiv_coprime
... = φ n :
begin
  apply finset.card_congr (λ (a : {x : zmod n // x.val.coprime n}) _, a.1.val),
  { intro a, simp [(a : zmod n).val_lt, a.prop.symm] {contextual := tt} },
  { intros _ _ _ _ h, rw subtype.ext_iff_val, apply val_injective, exact h, },
  { intros b hb,
    rw [finset.mem_filter, finset.mem_range] at hb,
    refine ⟨⟨b, _⟩, finset.mem_univ _, _⟩,
    { let u := unit_of_coprime b hb.2.symm,
      exact val_coe_unit_coprime u },
    { show zmod.val (b : zmod n) = b,
      rw [val_nat_cast, nat.mod_eq_of_lt hb.1], } }
end

end totient

instance subsingleton_units : subsingleton (units (zmod 2)) :=
⟨λ x y, begin
  ext1,
  cases x with x xi hx1 hx2,
  cases y with y yi hy1 hy2,
  revert hx1 hx2 hy1 hy2,
  fin_cases x; fin_cases y; simp
end⟩

lemma le_div_two_iff_lt_neg (n : ℕ) [hn : fact ((n : ℕ) % 2 = 1)]
  {x : zmod n} (hx0 : x ≠ 0) : x.val ≤ (n / 2 : ℕ) ↔ (n / 2 : ℕ) < (-x).val :=
begin
  haveI npos : fact (0 < n) := ⟨by
  { apply (nat.eq_zero_or_pos n).resolve_left,
    unfreezingI { rintro rfl },
    simpa [fact_iff] using hn, }⟩,
  have hn2 : (n : ℕ) / 2 < n := nat.div_lt_of_lt_mul
    ((lt_mul_iff_one_lt_left npos.1).2 dec_trivial),
  have hn2' : (n : ℕ) - n / 2 = n / 2 + 1,
  { conv {to_lhs, congr, rw [← nat.succ_sub_one n, nat.succ_sub npos.1]},
    rw [← nat.two_mul_odd_div_two hn.1, two_mul, ← nat.succ_add, nat.add_sub_cancel], },
  have hxn : (n : ℕ) - x.val < n,
  { rw [nat.sub_lt_iff (le_of_lt x.val_lt) (le_refl _), nat.sub_self],
    rw ← zmod.nat_cast_zmod_val x at hx0,
    exact nat.pos_of_ne_zero (λ h, by simpa [h] using hx0) },
  by conv {to_rhs, rw [← nat.succ_le_iff, nat.succ_eq_add_one, ← hn2', ← zero_add (- x),
    ← zmod.nat_cast_self, ← sub_eq_add_neg, ← zmod.nat_cast_zmod_val x,
    ← nat.cast_sub (le_of_lt x.val_lt),
    zmod.val_nat_cast, nat.mod_eq_of_lt hxn, nat.sub_le_sub_left_iff (le_of_lt x.val_lt)] }
end

lemma ne_neg_self (n : ℕ) [hn : fact ((n : ℕ) % 2 = 1)] {a : zmod n} (ha : a ≠ 0) : a ≠ -a :=
λ h, have a.val ≤ n / 2 ↔ (n : ℕ) / 2 < (-a).val := le_div_two_iff_lt_neg n ha,
by rwa [← h, ← not_lt, not_iff_self] at this

lemma neg_one_ne_one {n : ℕ} [fact (2 < n)] :
  (-1 : zmod n) ≠ 1 :=
char_p.neg_one_ne_one (zmod n) n

@[simp] lemma neg_eq_self_mod_two (a : zmod 2) : -a = a :=
by fin_cases a; ext; simp [fin.coe_neg, int.nat_mod]; norm_num

@[simp] lemma nat_abs_mod_two (a : ℤ) : (a.nat_abs : zmod 2) = a :=
begin
  cases a,
  { simp only [int.nat_abs_of_nat, int.cast_coe_nat, int.of_nat_eq_coe] },
  { simp only [neg_eq_self_mod_two, nat.cast_succ, int.nat_abs, int.cast_neg_succ_of_nat] }
end

@[simp] lemma val_eq_zero : ∀ {n : ℕ} (a : zmod n), a.val = 0 ↔ a = 0
| 0     a := int.nat_abs_eq_zero
| (n+1) a := by { rw fin.ext_iff, exact iff.rfl }

lemma val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : (a : zmod n).val = a :=
by rw [val_nat_cast, nat.mod_eq_of_lt h]

lemma neg_val' {n : ℕ} [fact (0 < n)] (a : zmod n) : (-a).val = (n - a.val) % n :=
begin
  have : ((-a).val + a.val) % n = (n - a.val + a.val) % n,
  { rw [←val_add, add_left_neg, nat.sub_add_cancel (le_of_lt a.val_lt), nat.mod_self, val_zero], },
  calc (-a).val = val (-a)    % n : by rw nat.mod_eq_of_lt ((-a).val_lt)
            ... = (n - val a) % n : nat.modeq.modeq_add_cancel_right rfl this
end

lemma neg_val {n : ℕ} [fact (0 < n)] (a : zmod n) : (-a).val = if a = 0 then 0 else n - a.val :=
begin
  rw neg_val',
  by_cases h : a = 0, { rw [if_pos h, h, val_zero, nat.sub_zero, nat.mod_self] },
  rw if_neg h,
  apply nat.mod_eq_of_lt,
  apply nat.sub_lt (fact.out (0 < n)),
  contrapose! h,
  rwa [nat.le_zero_iff, val_eq_zero] at h,
end

/-- `val_min_abs x` returns the integer in the same equivalence class as `x` that is closest to `0`,
  The result will be in the interval `(-n/2, n/2]`. -/
def val_min_abs : Π {n : ℕ}, zmod n → ℤ
| 0       x := x
| n@(_+1) x := if x.val ≤ n / 2 then x.val else (x.val : ℤ) - n

@[simp] lemma val_min_abs_def_zero (x : zmod 0) : val_min_abs x = x := rfl

lemma val_min_abs_def_pos {n : ℕ} [fact (0 < n)] (x : zmod n) :
  val_min_abs x = if x.val ≤ n / 2 then x.val else x.val - n :=
begin
  casesI n,
  { exfalso, exact nat.not_lt_zero 0 (fact.out (0 < 0)) },
  { refl }
end

@[simp] lemma coe_val_min_abs : ∀ {n : ℕ} (x : zmod n), (x.val_min_abs : zmod n) = x
| 0       x := int.cast_id x
| k@(n+1) x :=
begin
  rw val_min_abs_def_pos,
  split_ifs,
  { rw [int.cast_coe_nat, nat_cast_zmod_val] },
  { rw [int.cast_sub, int.cast_coe_nat, nat_cast_zmod_val, int.cast_coe_nat, nat_cast_self,
      sub_zero] }
end

lemma nat_abs_val_min_abs_le {n : ℕ} [fact (0 < n)] (x : zmod n) : x.val_min_abs.nat_abs ≤ n / 2 :=
begin
  rw zmod.val_min_abs_def_pos,
  split_ifs with h, { exact h },
  have : (x.val - n : ℤ) ≤ 0,
  { rw [sub_nonpos, int.coe_nat_le], exact le_of_lt x.val_lt, },
  rw [← int.coe_nat_le, int.of_nat_nat_abs_of_nonpos this, neg_sub],
  conv_lhs { congr, rw [← nat.mod_add_div n 2, int.coe_nat_add, int.coe_nat_mul,
    int.coe_nat_bit0, int.coe_nat_one] },
  suffices : ((n % 2 : ℕ) + (n / 2) : ℤ) ≤ (val x),
  { rw ← sub_nonneg at this ⊢, apply le_trans this (le_of_eq _), ring_nf, ring },
  norm_cast,
  calc (n : ℕ) % 2 + n / 2 ≤ 1 + n / 2 :
    nat.add_le_add_right (nat.le_of_lt_succ (nat.mod_lt _ dec_trivial)) _
                       ... ≤ x.val     :
    by { rw add_comm, exact nat.succ_le_of_lt (lt_of_not_ge h) }
end

@[simp] lemma val_min_abs_zero : ∀ n, (0 : zmod n).val_min_abs = 0
| 0     := by simp only [val_min_abs_def_zero]
| (n+1) := by simp only [val_min_abs_def_pos, if_true, int.coe_nat_zero, zero_le, val_zero]

@[simp] lemma val_min_abs_eq_zero {n : ℕ} (x : zmod n) :
  x.val_min_abs = 0 ↔ x = 0 :=
begin
  cases n, { simp },
  split,
  { simp only [val_min_abs_def_pos, int.coe_nat_succ],
    split_ifs with h h; assume h0,
    { apply val_injective, rwa [int.coe_nat_eq_zero] at h0, },
    { apply absurd h0, rw sub_eq_zero, apply ne_of_lt, exact_mod_cast x.val_lt } },
  { rintro rfl, rw val_min_abs_zero }
end

lemma nat_cast_nat_abs_val_min_abs {n : ℕ} [fact (0 < n)] (a : zmod n) :
  (a.val_min_abs.nat_abs : zmod n) = if a.val ≤ (n : ℕ) / 2 then a else -a :=
begin
  have : (a.val : ℤ) - n ≤ 0,
    by { erw [sub_nonpos, int.coe_nat_le], exact le_of_lt a.val_lt, },
  rw [zmod.val_min_abs_def_pos],
  split_ifs,
  { rw [int.nat_abs_of_nat, nat_cast_zmod_val] },
  { rw [← int.cast_coe_nat, int.of_nat_nat_abs_of_nonpos this, int.cast_neg, int.cast_sub],
    rw [int.cast_coe_nat, int.cast_coe_nat, nat_cast_self, sub_zero, nat_cast_zmod_val], }
end

@[simp] lemma nat_abs_val_min_abs_neg {n : ℕ} (a : zmod n) :
  (-a).val_min_abs.nat_abs = a.val_min_abs.nat_abs :=
begin
  cases n, { simp only [int.nat_abs_neg, val_min_abs_def_zero], },
  by_cases ha0 : a = 0, { rw [ha0, neg_zero] },
  by_cases haa : -a = a, { rw [haa] },
  suffices hpa : (n+1 : ℕ) - a.val ≤ (n+1) / 2 ↔ (n+1 : ℕ) / 2 < a.val,
  { rw [val_min_abs_def_pos, val_min_abs_def_pos],
    rw ← not_le at hpa,
    simp only [if_neg ha0, neg_val, hpa, int.coe_nat_sub (le_of_lt a.val_lt)],
    split_ifs,
    all_goals { rw [← int.nat_abs_neg], congr' 1, ring } },
  suffices : (((n+1 : ℕ) % 2) + 2 * ((n + 1) / 2)) - a.val ≤ (n+1) / 2 ↔ (n+1 : ℕ) / 2 < a.val,
  by rwa [nat.mod_add_div] at this,
  suffices : (n + 1) % 2 + (n + 1) / 2 ≤ val a ↔ (n + 1) / 2 < val a,
  by rw [nat.sub_le_iff, two_mul, ← add_assoc, nat.add_sub_cancel, this],
  cases (n + 1 : ℕ).mod_two_eq_zero_or_one with hn0 hn1,
  { split,
    { assume h,
      apply lt_of_le_of_ne (le_trans (nat.le_add_left _ _) h),
      contrapose! haa,
      rw [← zmod.nat_cast_zmod_val a, ← haa, neg_eq_iff_add_eq_zero, ← nat.cast_add],
      rw [char_p.cast_eq_zero_iff (zmod (n+1)) (n+1)],
      rw [← two_mul, ← zero_add (2 * _), ← hn0, nat.mod_add_div] },
    { rw [hn0, zero_add], exact le_of_lt } },
  { rw [hn1, add_comm, nat.succ_le_iff] }
end

lemma val_eq_ite_val_min_abs {n : ℕ} [fact (0 < n)] (a : zmod n) :
  (a.val : ℤ) = a.val_min_abs + if a.val ≤ n / 2 then 0 else n :=
by { rw [zmod.val_min_abs_def_pos], split_ifs; simp only [add_zero, sub_add_cancel] }

lemma prime_ne_zero (p q : ℕ) [hp : fact p.prime] [hq : fact q.prime] (hpq : p ≠ q) :
  (q : zmod p) ≠ 0 :=
by rwa [← nat.cast_zero, ne.def, eq_iff_modeq_nat, nat.modeq.modeq_zero_iff,
  ← hp.1.coprime_iff_not_dvd, nat.coprime_primes hp.1 hq.1]

end zmod

namespace zmod

variables (p : ℕ) [fact p.prime]

private lemma mul_inv_cancel_aux (a : zmod p) (h : a ≠ 0) : a * a⁻¹ = 1 :=
begin
  obtain ⟨k, rfl⟩ := nat_cast_zmod_surjective a,
  apply coe_mul_inv_eq_one,
  apply nat.coprime.symm,
  rwa [nat.prime.coprime_iff_not_dvd (fact.out p.prime), ← char_p.cast_eq_zero_iff (zmod p)]
end

/-- Field structure on `zmod p` if `p` is prime. -/
instance : field (zmod p) :=
{ mul_inv_cancel := mul_inv_cancel_aux p,
  inv_zero := inv_zero p,
  .. zmod.comm_ring p,
  .. zmod.has_inv p,
  .. zmod.nontrivial p }

end zmod

lemma ring_hom.ext_zmod {n : ℕ} {R : Type*} [semiring R] (f g : (zmod n) →+* R) : f = g :=
begin
  ext a,
  obtain ⟨k, rfl⟩ := zmod.int_cast_surjective a,
  let φ : ℤ →+* R := f.comp (int.cast_ring_hom (zmod n)),
  let ψ : ℤ →+* R := g.comp (int.cast_ring_hom (zmod n)),
  show φ k = ψ k,
  rw φ.ext_int ψ,
end

namespace zmod
variables {n : ℕ} {R : Type*}

instance subsingleton_ring_hom [semiring R] : subsingleton ((zmod n) →+* R) :=
⟨ring_hom.ext_zmod⟩

instance subsingleton_ring_equiv [semiring R] : subsingleton (zmod n ≃+* R) :=
⟨λ f g, by { rw ring_equiv.coe_ring_hom_inj_iff, apply ring_hom.ext_zmod _ _ }⟩

@[simp] lemma ring_hom_map_cast [ring R] (f : R →+* (zmod n)) (k : zmod n) :
  f k = k :=
by { cases n; simp }

lemma ring_hom_right_inverse [ring R] (f : R →+* (zmod n)) :
  function.right_inverse (coe : zmod n → R) f :=
ring_hom_map_cast f

lemma ring_hom_surjective [ring R] (f : R →+* (zmod n)) : function.surjective f :=
(ring_hom_right_inverse f).surjective

lemma ring_hom_eq_of_ker_eq [comm_ring R] (f g : R →+* (zmod n))
  (h : f.ker = g.ker) : f = g :=
begin
  have := f.lift_of_right_inverse_comp _ (zmod.ring_hom_right_inverse f) ⟨g, le_of_eq h⟩,
  rw subtype.coe_mk at this,
  rw [←this, ring_hom.ext_zmod (f.lift_of_right_inverse _ _ _) (ring_hom.id _), ring_hom.id_comp],
end

section lift

variables (n) {A : Type*} [add_group A]

/-- The map from `zmod n` induced by `f : ℤ →+ A` that maps `n` to `0`. -/
@[simps]
def lift : {f : ℤ →+ A // f n = 0} ≃ (zmod n →+ A) :=
(equiv.subtype_equiv_right $ begin
  intro f,
  rw ker_int_cast_add_hom,
  split,
  { rintro hf _ ⟨x, rfl⟩,
    simp only [f.map_gsmul, gsmul_zero, f.mem_ker, hf] },
  { intro h,
    refine h (add_subgroup.mem_gmultiples _) }
end).trans $ ((int.cast_add_hom (zmod n)).lift_of_right_inverse coe int_cast_zmod_cast)

variables (f : {f : ℤ →+ A // f n = 0})

@[simp] lemma lift_coe (x : ℤ) :
  lift n f (x : zmod n) = f x :=
add_monoid_hom.lift_of_right_inverse_comp_apply _ _ _ _ _

lemma lift_cast_add_hom (x : ℤ) :
  lift n f (int.cast_add_hom (zmod n) x) = f x :=
add_monoid_hom.lift_of_right_inverse_comp_apply _ _ _ _ _

@[simp] lemma lift_comp_coe : zmod.lift n f ∘ coe = f :=
funext $ lift_coe _ _

@[simp] lemma lift_comp_cast_add_hom :
  (zmod.lift n f).comp (int.cast_add_hom (zmod n)) = f :=
add_monoid_hom.ext $ lift_cast_add_hom _ _

end lift

end zmod
