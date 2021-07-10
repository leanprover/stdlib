/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import data.nat.cast
import data.int.basic
import tactic.localized
import tactic.apply_fun
import order.rel_iso

/-!
# The finite type with `n` elements

`fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

### Induction principles

* `fin_zero_elim` : Elimination principle for the empty set `fin 0`, generalizes `fin.elim0`.
* `fin.succ_rec` : Define `C n i` by induction on  `i : fin n` interpreted
  as `(0 : fin (n - i)).succ.succ…`. This function has two arguments: `H0 n` defines
  `0`-th element `C (n+1) 0` of an `(n+1)`-tuple, and `Hs n i` defines `(i+1)`-st element
  of `(n+1)`-tuple based on `n`, `i`, and `i`-th element of `n`-tuple.
* `fin.succ_rec_on` : same as `fin.succ_rec` but `i : fin n` is the first argument;
* `fin.induction` : Define `C i` by induction on `i : fin (n + 1)`, separating into the
  `nat`-like base cases of `C 0` and `C (i.succ)`.
* `fin.induction_on` : same as `fin.induction` but with `i : fin (n + 1)` as the first argument.

### Casts

* `cast_lt i h` : embed `i` into a `fin` where `h` proves it belongs into;
* `cast_le h` : embed `fin n` into `fin m`, `h : n ≤ m`;
* `cast eq` : embed `fin n` into `fin m`, `eq : n = m`;
* `cast_add m` : embed `fin n` into `fin (n+m)`;
* `cast_succ` : embed `fin n` into `fin (n+1)`;
* `succ_above p` : embed `fin n` into `fin (n + 1)` with a hole around `p`;
* `pred_above (p : fin n) i` : embed `i : fin (n+1)` into `fin n` by subtracting one if `p < i`;
* `cast_pred` : embed `fin (n + 2)` into `fin (n + 1)` by mapping `last (n + 1)` to `last n`;
* `sub_nat i h` : subtract `m` from `i ≥ m`, generalizes `fin.pred`;
* `add_nat m i` : add `m` on `i` on the right, generalizes `fin.succ`;
* `nat_add n i` adds `n` on `i` on the left;
* `clamp n m` : `min n m` as an element of `fin (m + 1)`;

### Operation on tuples

We interpret maps `Π i : fin n, α i` as tuples `(α 0, …, α (n-1))`.
If `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `vector`s.

We define the following operations:

* `tail` : the tail of an `n+1` tuple, i.e., its last `n` entries;
* `cons` : adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple;
* `init` : the beginning of an `n+1` tuple, i.e., its first `n` entries;
* `snoc` : adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc`
  comes from `cons` (i.e., adding an element to the left of a tuple) read in reverse order.
* `insert_nth` : insert an element to a tuple at a given position.
* `find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.

### Misc definitions

* `fin.last n` : The greatest value of `fin (n+1)`.

-/

universes u v
open fin nat function

/-- Elimination principle for the empty set `fin 0`, dependent version. -/
def fin_zero_elim {α : fin 0 → Sort u} (x : fin 0) : α x := x.elim0

lemma fact.succ.pos {n} : fact (0 < succ n) := ⟨zero_lt_succ _⟩

lemma fact.bit0.pos {n} [h : fact (0 < n)] : fact (0 < bit0 n) :=
⟨nat.zero_lt_bit0 $ ne_of_gt h.1⟩

lemma fact.bit1.pos {n} : fact (0 < bit1 n) :=
⟨nat.zero_lt_bit1 _⟩

lemma fact.pow.pos {p n : ℕ} [h : fact $ 0 < p] : fact (0 < p ^ n) :=
⟨pow_pos h.1 _⟩

localized "attribute [instance] fact.succ.pos" in fin_fact
localized "attribute [instance] fact.bit0.pos" in fin_fact
localized "attribute [instance] fact.bit1.pos" in fin_fact
localized "attribute [instance] fact.pow.pos" in fin_fact

namespace fin
variables {n m : ℕ} {a b : fin n}

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨subtype.val⟩

section coe

/-!
### coercions and constructions
-/

@[simp] protected lemma eta (a : fin n) (h : (a : ℕ) < n) : (⟨(a : ℕ), h⟩ : fin n) = a :=
by cases a; refl

@[ext]
lemma ext {a b : fin n} (h : (a : ℕ) = b) : a = b := eq_of_veq h

lemma ext_iff (a b : fin n) : a = b ↔ (a : ℕ) = b :=
iff.intro (congr_arg _) fin.eq_of_veq

lemma coe_injective {n : ℕ} : injective (coe : fin n → ℕ) := subtype.coe_injective

lemma eq_iff_veq (a b : fin n) : a = b ↔ a.1 = b.1 :=
⟨veq_of_eq, eq_of_veq⟩

lemma ne_iff_vne (a b : fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
⟨vne_of_ne, ne_of_vne⟩

@[simp] lemma mk_eq_subtype_mk (a : ℕ) (h : a < n) : mk a h = ⟨a, h⟩ := rfl

protected lemma mk.inj_iff {n a b : ℕ} {ha : a < n} {hb : b < n} :
  (⟨a, ha⟩ : fin n) = ⟨b, hb⟩ ↔ a = b :=
subtype.mk_eq_mk

lemma mk_val {m n : ℕ} (h : m < n) : (⟨m, h⟩ : fin n).val = m := rfl

lemma eq_mk_iff_coe_eq {k : ℕ} {hk : k < n} : a = ⟨k, hk⟩ ↔ (a : ℕ) = k :=
fin.eq_iff_veq a ⟨k, hk⟩

@[simp, norm_cast] lemma coe_mk {m n : ℕ} (h : m < n) : ((⟨m, h⟩ : fin n) : ℕ) = m := rfl

lemma mk_coe (i : fin n) : (⟨i, i.property⟩ : fin n) = i :=
fin.eta _ _

lemma coe_eq_val (a : fin n) : (a : ℕ) = a.val := rfl

@[simp] lemma val_eq_coe (a : fin n) : a.val = a := rfl

/-- Assume `k = l`. If two functions defined on `fin k` and `fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected lemma heq_fun_iff {α : Sort*} {k l : ℕ} (h : k = l) {f : fin k → α} {g : fin l → α} :
  f == g ↔ (∀ (i : fin k), f i = g ⟨(i : ℕ), h ▸ i.2⟩) :=
by { induction h, simp [heq_iff_eq, function.funext_iff] }

protected lemma heq_ext_iff {k l : ℕ} (h : k = l) {i : fin k} {j : fin l} :
  i == j ↔ (i : ℕ) = (j : ℕ) :=
by { induction h, simp [ext_iff] }

lemma exists_iff {p : fin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
⟨λ h, exists.elim h (λ ⟨i, hi⟩ hpi, ⟨i, hi, hpi⟩),
  λ h, exists.elim h (λ i hi, ⟨⟨i, hi.fst⟩, hi.snd⟩)⟩

lemma forall_iff {p : fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
⟨λ h i hi, h ⟨i, hi⟩, λ h ⟨i, hi⟩, h i hi⟩

end coe

section order

/-!
### order
-/

lemma is_lt (i : fin n) : (i : ℕ) < n := i.2

lemma is_le (i : fin (n + 1)) : (i : ℕ) ≤ n := le_of_lt_succ i.is_lt

lemma lt_iff_coe_lt_coe : a < b ↔ (a : ℕ) < b := iff.rfl

lemma le_iff_coe_le_coe : a ≤ b ↔ (a : ℕ) ≤ b := iff.rfl

lemma mk_lt_of_lt_coe {a : ℕ} (h : a < b) : (⟨a, h.trans b.is_lt⟩ : fin n) < b := h

lemma mk_le_of_le_coe {a : ℕ} (h : a ≤ b) : (⟨a, h.trans_lt b.is_lt⟩ : fin n) ≤ b := h

/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[norm_cast, simp] lemma coe_fin_lt {n : ℕ} {a b : fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[norm_cast, simp] lemma coe_fin_le {n : ℕ} {a b : fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
iff.rfl

instance {n : ℕ} : linear_order (fin n) :=
{ le := (≤), lt := (<),
  decidable_le := fin.decidable_le,
  decidable_lt := fin.decidable_lt,
  decidable_eq := fin.decidable_eq _,
 ..linear_order.lift (coe : fin n → ℕ) (@fin.eq_of_veq _) }

/-- The inclusion map `fin n → ℕ` is a relation embedding. -/
def coe_embedding (n) : (fin n) ↪o ℕ :=
⟨⟨coe, @fin.eq_of_veq _⟩, λ a b, iff.rfl⟩

/-- The ordering on `fin n` is a well order. -/
instance fin.lt.is_well_order (n) : is_well_order (fin n) (<) :=
(coe_embedding n).is_well_order

/-- Use the ordering on `fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `has_well_founded` instance:
```lean
def factorial {n : ℕ} : fin n → ℕ
| ⟨0, _⟩ := 1
| ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : has_well_founded (fin n) :=
⟨_, measure_wf coe⟩

@[simp] lemma coe_zero {n : ℕ} : ((0 : fin (n+1)) : ℕ) = 0 := rfl
attribute [simp] val_zero
@[simp] lemma val_zero' (n) : (0 : fin (n+1)).val = 0 := rfl
@[simp] lemma mk_zero : (⟨0, nat.succ_pos'⟩ : fin (n + 1)) = (0 : fin _) := rfl

lemma zero_le (a : fin (n + 1)) : 0 ≤ a := zero_le a.1

lemma pos_iff_ne_zero (a : fin (n+1)) : 0 < a ↔ a ≠ 0 :=
begin
  split,
  { rintros h rfl, exact lt_irrefl _ h, },
  { rintros h,
    apply (@pos_iff_ne_zero _ _ (a : ℕ)).mpr,
    cases a,
    rintro w,
    apply h,
    simp at w,
    subst w,
    refl, },
end

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩

@[simp, norm_cast] lemma coe_last (n : ℕ) : (last n : ℕ) = n := rfl

lemma last_val (n : ℕ) : (last n).val = n := rfl

theorem le_last (i : fin (n+1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

instance : bounded_lattice (fin (n + 1)) :=
{ top := last n,
  le_top := le_last,
  bot := 0,
  bot_le := zero_le,
  .. fin.linear_order, .. lattice_of_linear_order }

lemma last_pos : (0 : fin (n + 2)) < last (n + 1) :=
by simp [lt_iff_coe_lt_coe]

lemma eq_last_of_not_lt {i : fin (n+1)} (h : ¬ (i : ℕ) < n) : i = last n :=
le_antisymm (le_last i) (not_lt.1 h)

section

variables {α : Type*} [preorder α]
open set

/-- If `e` is an `order_iso` between `fin n` and `fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp] lemma coe_order_iso_apply (e : fin n ≃o fin m) (i : fin n) : (e i : ℕ) = i :=
begin
  rcases i with ⟨i, hi⟩,
  rw [subtype.coe_mk],
  induction i using nat.strong_induction_on with i h,
  refine le_antisymm (forall_lt_iff_le.1 $ λ j hj, _) (forall_lt_iff_le.1 $ λ j hj, _),
  { have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_coe hj),
    rw e.symm_apply_apply at this,
    convert this,
    simpa using h _ this (e.symm _).is_lt },
  { rwa [← h j hj (hj.trans hi), ← lt_iff_coe_lt_coe, e.lt_iff_lt] }
end

instance order_iso_subsingleton : subsingleton (fin n ≃o α) :=
⟨λ e e', by { ext i,
  rw [← e.symm.apply_eq_iff_eq, e.symm_apply_apply, ← e'.trans_apply, ext_iff,
    coe_order_iso_apply] }⟩

instance order_iso_subsingleton' : subsingleton (α ≃o fin n) :=
order_iso.symm_injective.subsingleton

instance order_iso_unique : unique (fin n ≃o fin n) := unique.mk' _

/-- Two strictly monotone functions from `fin n` are equal provided that their ranges
are equal. -/
lemma strict_mono_unique {f g : fin n → α} (hf : strict_mono f) (hg : strict_mono g)
  (h : range f = range g) : f = g :=
have (hf.order_iso f).trans (order_iso.set_congr _ _ h) = hg.order_iso g,
  from subsingleton.elim _ _,
congr_arg (function.comp (coe : range g → α)) (funext $ rel_iso.ext_iff.1 this)

/-- Two order embeddings of `fin n` are equal provided that their ranges are equal. -/
lemma order_embedding_eq {f g : fin n ↪o α} (h : range f = range g) : f = g :=
rel_embedding.ext $ funext_iff.1 $ strict_mono_unique f.strict_mono g.strict_mono h

end

/-- A function `f` on `fin n` is strictly monotone if and only if `f i < f (i+1)` for all `i`. -/
lemma strict_mono_iff_lt_succ {α : Type*} [preorder α] {f : fin n → α} :
  strict_mono f ↔ ∀ i (h : i + 1 < n), f ⟨i, lt_of_le_of_lt (nat.le_succ i) h⟩ < f ⟨i+1, h⟩ :=
begin
  split,
  { assume H i hi,
    apply H,
    exact nat.lt_succ_self _ },
  { assume H,
    have A : ∀ i j (h : i < j) (h' : j < n), f ⟨i, lt_trans h h'⟩ < f ⟨j, h'⟩,
    { assume i j h h',
      induction h with k h IH,
      { exact H _ _ },
      { exact lt_trans (IH (nat.lt_of_succ_lt h')) (H _ _) } },
    assume i j hij,
    convert A (i : ℕ) (j : ℕ) hij j.2; ext; simp only [subtype.coe_eta] }
end

end order

section add

/-!
### addition, numerals, and coercion from nat
-/

/-- convert a `ℕ` to `fin n`, provided `n` is positive -/
def of_nat' [h : fact (0 < n)] (i : ℕ) : fin n := ⟨i%n, mod_lt _ h.1⟩

lemma one_val {n : ℕ} : (1 : fin (n+1)).val = 1 % (n+1) := rfl
lemma coe_one' {n : ℕ} : ((1 : fin (n+1)) : ℕ) = 1 % (n+1) := rfl
@[simp] lemma val_one  {n : ℕ} : (1 : fin (n+2)).val = 1 := rfl
@[simp] lemma coe_one  {n : ℕ} : ((1 : fin (n+2)) : ℕ) = 1 := rfl
@[simp] lemma mk_one : (⟨1, nat.succ_lt_succ (nat.succ_pos n)⟩ : fin (n + 2)) = (1 : fin _) := rfl

instance {n : ℕ} : nontrivial (fin (n + 2)) := ⟨⟨0, 1, dec_trivial⟩⟩

section monoid

@[simp] protected lemma add_zero (k : fin (n + 1)) : k + 0 = k :=
by simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]

@[simp] protected lemma zero_add (k : fin (n + 1)) : (0 : fin (n + 1)) + k = k :=
by simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]

instance add_comm_monoid (n : ℕ) : add_comm_monoid (fin (n + 1)) :=
{ add := (+),
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc],
  zero := 0,
  zero_add := fin.zero_add,
  add_zero := fin.add_zero,
  add_comm := by simp [eq_iff_veq, add_def, add_comm] }

end monoid

lemma val_add {n : ℕ} : ∀ a b : fin n, (a + b).val = (a.val + b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma coe_add {n : ℕ} : ∀ a b : fin n, ((a + b : fin n) : ℕ) = (a + b) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma coe_add_eq_ite {n : ℕ} (a b : fin n) :
  (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b :=
by rw [fin.coe_add, nat.add_mod_eq_ite,
       nat.mod_eq_of_lt (show ↑a < n, from a.2), nat.mod_eq_of_lt (show ↑b < n, from b.2)]

lemma coe_bit0 {n : ℕ} (k : fin n) : ((bit0 k : fin n) : ℕ) = bit0 (k : ℕ) % n :=
by { cases k, refl }

lemma coe_bit1 {n : ℕ} (k : fin (n + 1)) :
  ((bit1 k : fin (n + 1)) : ℕ) = bit1 (k : ℕ) % (n + 1) :=
begin
  cases n, { cases k with k h, cases k, {show _ % _ = _, simp}, cases h with _ h, cases h },
  simp [bit1, fin.coe_bit0, fin.coe_add, fin.coe_one],
end

lemma coe_add_one_of_lt {n : ℕ} {i : fin n.succ} (h : i < last _) :
  (↑(i + 1) : ℕ) = i + 1 :=
begin
  -- First show that `((1 : fin n.succ) : ℕ) = 1`, because `n.succ` is at least 2.
  cases n,
  { cases h },
  -- Then just unfold the definitions.
  rw [fin.coe_add, fin.coe_one, nat.mod_eq_of_lt (nat.succ_lt_succ _)],
  exact h
end

@[simp] lemma last_add_one : ∀ n, last n + 1 = 0
| 0 := subsingleton.elim _ _
| (n + 1) := by { ext, rw [coe_add, coe_zero, coe_last, coe_one, nat.mod_self] }

lemma coe_add_one {n : ℕ} (i : fin (n + 1)) :
  ((i + 1 : fin (n + 1)) : ℕ) = if i = last _ then 0 else i + 1 :=
begin
  rcases (le_last i).eq_or_lt with rfl|h,
  { simp },
  { simpa [h.ne] using coe_add_one_of_lt h }
end

section bit

@[simp] lemma mk_bit0 {m n : ℕ} (h : bit0 m < n) :
  (⟨bit0 m, h⟩ : fin n) = (bit0 ⟨m, (nat.le_add_right m m).trans_lt h⟩ : fin _) :=
eq_of_veq (nat.mod_eq_of_lt h).symm

@[simp] lemma mk_bit1 {m n : ℕ} (h : bit1 m < n + 1) :
  (⟨bit1 m, h⟩ : fin (n + 1)) = (bit1 ⟨m, (nat.le_add_right m m).trans_lt
    ((m + m).lt_succ_self.trans h)⟩ : fin _) :=
begin
  ext,
  simp only [bit1, bit0] at h,
  simp only [bit1, bit0, coe_add, coe_one', coe_mk, ←nat.add_mod, nat.mod_eq_of_lt h],
end

end bit

@[simp] lemma val_two  {n : ℕ} : (2 : fin (n+3)).val = 2 := rfl
@[simp] lemma coe_two  {n : ℕ} : ((2 : fin (n+3)) : ℕ) = 2 := rfl

section of_nat_coe

@[simp]
lemma of_nat_eq_coe (n : ℕ) (a : ℕ) : (of_nat a : fin (n+1)) = a :=
begin
  induction a with a ih, { refl },
  ext, show (a+1) % (n+1) = subtype.val (a+1 : fin (n+1)),
  { rw [val_add, ← ih, of_nat],
    exact add_mod _ _ _ }
end

/-- Converting an in-range number to `fin (n + 1)` produces a result
whose value is the original number.  -/
lemma coe_val_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  ((a : fin (n + 1)).val) = a :=
begin
  rw ←of_nat_eq_coe,
  exact nat.mod_eq_of_lt h
end

/-- Converting the value of a `fin (n + 1)` to `fin (n + 1)` results
in the same value.  -/
lemma coe_val_eq_self {n : ℕ} (a : fin (n + 1)) : (a.val : fin (n + 1)) = a :=
begin
  rw fin.eq_iff_veq,
  exact coe_val_of_lt a.property
end

/-- Coercing an in-range number to `fin (n + 1)`, and converting back
to `ℕ`, results in that number. -/
lemma coe_coe_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  ((a : fin (n + 1)) : ℕ) = a :=
coe_val_of_lt h

/-- Converting a `fin (n + 1)` to `ℕ` and back results in the same
value. -/
@[simp] lemma coe_coe_eq_self {n : ℕ} (a : fin (n + 1)) : ((a : ℕ) : fin (n + 1)) = a :=
coe_val_eq_self a

lemma coe_nat_eq_last (n) : (n : fin (n + 1)) = fin.last n :=
by { rw [←fin.of_nat_eq_coe, fin.of_nat, fin.last], simp only [nat.mod_eq_of_lt n.lt_succ_self] }

lemma le_coe_last (i : fin (n + 1)) : i ≤ n :=
by { rw fin.coe_nat_eq_last, exact fin.le_last i }

end of_nat_coe

lemma add_one_pos (i : fin (n + 1)) (h : i < fin.last n) : (0 : fin (n + 1)) < i + 1 :=
begin
  cases n,
  { exact absurd h (nat.not_lt_zero _) },
  { rw [lt_iff_coe_lt_coe, coe_last, ←add_lt_add_iff_right 1] at h,
    rw [lt_iff_coe_lt_coe, coe_add, coe_zero, coe_one, nat.mod_eq_of_lt h],
    exact nat.zero_lt_succ _ }
end

lemma one_pos : (0 : fin (n + 2)) < 1 := succ_pos 0

lemma zero_ne_one : (0 : fin (n + 2)) ≠ 1 := ne_of_lt one_pos

@[simp] lemma zero_eq_one_iff : (0 : fin (n + 1)) = 1 ↔ n = 0 :=
begin
  split,
  { cases n; intro h,
    { refl },
    { have := zero_ne_one, contradiction } },
  { rintro rfl, refl }
end

@[simp] lemma one_eq_zero_iff : (1 : fin (n + 1)) = 0 ↔ n = 0 :=
by rw [eq_comm, zero_eq_one_iff]

end add

section succ

/-!
### succ and casts into larger fin types
-/

@[simp] lemma coe_succ (j : fin n) : (j.succ : ℕ) = j + 1 :=
by cases j; simp [fin.succ]

lemma succ_pos (a : fin n) : (0 : fin (n + 1)) < a.succ := by simp [lt_iff_coe_lt_coe]

/-- `fin.succ` as an `order_embedding` -/
def succ_embedding (n : ℕ) : fin n ↪o fin (n + 1) :=
order_embedding.of_strict_mono fin.succ $ λ ⟨i, hi⟩ ⟨j, hj⟩ h, succ_lt_succ h

@[simp] lemma coe_succ_embedding : ⇑(succ_embedding n) = fin.succ := rfl

@[simp] lemma succ_le_succ_iff : a.succ ≤ b.succ ↔ a ≤ b :=
(succ_embedding n).le_iff_le

@[simp] lemma succ_lt_succ_iff : a.succ < b.succ ↔ a < b :=
(succ_embedding n).lt_iff_lt

lemma succ_injective (n : ℕ) : injective (@fin.succ n) :=
(succ_embedding n).injective

@[simp] lemma succ_inj {a b : fin n} : a.succ = b.succ ↔ a = b :=
(succ_injective n).eq_iff

lemma succ_ne_zero {n} : ∀ k : fin n, fin.succ k ≠ 0
| ⟨k, hk⟩ heq := nat.succ_ne_zero k $ (ext_iff _ _).1 heq

@[simp] lemma succ_zero_eq_one : fin.succ (0 : fin (n + 1)) = 1 := rfl

@[simp] lemma succ_one_eq_two : fin.succ (1 : fin (n + 2)) = 2 := rfl

@[simp] lemma succ_mk (n i : ℕ) (h : i < n) : fin.succ ⟨i, h⟩ = ⟨i + 1, nat.succ_lt_succ h⟩ :=
rfl

lemma mk_succ_pos (i : ℕ) (h : i < n) : (0 : fin (n + 1)) < ⟨i.succ, add_lt_add_right h 1⟩ :=
by { rw [lt_iff_coe_lt_coe, coe_zero], exact nat.succ_pos i }

lemma one_lt_succ_succ (a : fin n) : (1 : fin (n + 2)) < a.succ.succ :=
begin
  cases n,
  { exact fin_zero_elim a },
  { rw [←succ_zero_eq_one, succ_lt_succ_iff], exact succ_pos a }
end

lemma succ_succ_ne_one (a : fin n) : fin.succ (fin.succ a) ≠ 1 := ne_of_gt (one_lt_succ_succ a)

/-- `cast_lt i h` embeds `i` into a `fin` where `h` proves it belongs into.  -/
def cast_lt (i : fin m) (h : i.1 < n) : fin n := ⟨i.1, h⟩

@[simp] lemma coe_cast_lt (i : fin m) (h : i.1 < n) : (cast_lt i h : ℕ) = i := rfl

@[simp] lemma cast_lt_mk (i n m : ℕ) (hn : i < n) (hm : i < m) : cast_lt ⟨i, hn⟩ hm = ⟨i, hm⟩ := rfl

/-- `cast_le h i` embeds `i` into a larger `fin` type.  -/
def cast_le (h : n ≤ m) : fin n ↪o fin m :=
order_embedding.of_strict_mono (λ a, cast_lt a (lt_of_lt_of_le a.2 h)) $ λ a b h, h

@[simp] lemma coe_cast_le (h : n ≤ m) (i : fin n) : (cast_le h i : ℕ) = i := rfl

@[simp] lemma cast_le_mk (i n m : ℕ) (hn : i < n) (h : n ≤ m) :
  cast_le h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h⟩ := rfl

@[simp] lemma cast_le_zero {n m : ℕ} (h : n.succ ≤ m.succ) :
  cast_le h 0 = 0 :=
by simp [eq_iff_veq]

@[simp] lemma range_cast_le {n k : ℕ} (h : n ≤ k) :
  set.range (cast_le h) = {i | (i : ℕ) < n} :=
set.ext (λ x, ⟨λ ⟨y, hy⟩, hy ▸ y.2, λ hx, ⟨⟨x, hx⟩, fin.ext rfl⟩⟩)

@[simp] lemma coe_of_injective_cast_le_symm {n k : ℕ} (h : n ≤ k) (i : fin k) (hi) :
  ((equiv.of_injective _ (cast_le h).injective).symm ⟨i, hi⟩ : ℕ) = i :=
begin
  rw ← coe_cast_le,
  exact congr_arg coe (equiv.apply_of_injective_symm _ _ _)
end

/-- `cast eq i` embeds `i` into a equal `fin` type. -/
def cast (eq : n = m) : fin n ≃o fin m :=
{ to_equiv := ⟨cast_le eq.le, cast_le eq.symm.le, λ a, eq_of_veq rfl, λ a, eq_of_veq rfl⟩,
  map_rel_iff' := λ a b, iff.rfl }

@[simp] lemma symm_cast (h : n = m) : (cast h).symm = cast h.symm := rfl

lemma coe_cast (h : n = m) (i : fin n) : (cast h i : ℕ) = i := rfl

@[simp] lemma cast_mk (h : n = m) (i : ℕ) (hn : i < n) :
  cast h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h.le⟩ := rfl

@[simp] lemma cast_trans {k : ℕ} (h : n = m) (h' : m = k) {i : fin n} :
  cast h' (cast h i) = cast (eq.trans h h') i := rfl

@[simp] lemma cast_refl (h : n = n := rfl) : cast h = order_iso.refl (fin n) :=
by { ext, refl }

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
lemma cast_to_equiv (h : n = m) : (cast h).to_equiv = equiv.cast (h ▸ rfl) :=
by { subst h, simp }

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
lemma cast_eq_cast (h : n = m) : (cast h : fin n → fin m) = _root_.cast (h ▸ rfl) :=
by { subst h, ext, simp }

/-- `cast_add m i` embeds `i : fin n` in `fin (n+m)`. -/
def cast_add (m) : fin n ↪o fin (n + m) := cast_le $ le_add_right n m

@[simp] lemma coe_cast_add (m : ℕ) (i : fin n) : (cast_add m i : ℕ) = i := rfl

@[simp] lemma cast_add_mk (m : ℕ) (i : ℕ) (h : i < n) :
  cast_add m ⟨i, h⟩ = ⟨i, lt_add_right i n m h⟩ := rfl

/-- `cast_succ i` embeds `i : fin n` in `fin (n+1)`. -/
def cast_succ : fin n ↪o fin (n + 1) := cast_add 1

@[simp] lemma coe_cast_succ (i : fin n) : (i.cast_succ : ℕ) = i := rfl

@[simp] lemma cast_succ_mk (n i : ℕ) (h : i < n) : cast_succ ⟨i, h⟩ = ⟨i, nat.lt.step h⟩ := rfl

lemma cast_succ_lt_succ (i : fin n) : i.cast_succ < i.succ :=
lt_iff_coe_lt_coe.2 $ by simp only [coe_cast_succ, coe_succ, nat.lt_succ_self]

lemma le_cast_succ_iff {i : fin (n + 1)} {j : fin n} : i ≤ j.cast_succ ↔ i < j.succ :=
by simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe] using nat.succ_le_succ_iff.symm

@[simp] lemma succ_last (n : ℕ) : (last n).succ = last (n.succ) := rfl

@[simp] lemma succ_eq_last_succ {n : ℕ} (i : fin n.succ) :
  i.succ = last (n + 1) ↔ i = last n :=
by rw [← succ_last, (succ_injective _).eq_iff]

@[simp] lemma cast_succ_cast_lt (i : fin (n + 1)) (h : (i : ℕ) < n) : cast_succ (cast_lt i h) = i :=
fin.eq_of_veq rfl

@[simp] lemma cast_lt_cast_succ {n : ℕ} (a : fin n) (h : (a : ℕ) < n) :
  cast_lt (cast_succ a) h = a :=
by cases a; refl

@[simp] lemma cast_succ_lt_cast_succ_iff : a.cast_succ < b.cast_succ ↔ a < b :=
(@cast_succ n).lt_iff_lt

lemma cast_succ_injective (n : ℕ) : injective (@fin.cast_succ n) :=
(cast_succ : fin n ↪o _).injective

lemma cast_succ_inj {a b : fin n} : a.cast_succ = b.cast_succ ↔ a = b :=
(cast_succ_injective n).eq_iff

lemma cast_succ_lt_last (a : fin n) : cast_succ a < last n := lt_iff_coe_lt_coe.mpr a.is_lt

@[simp] lemma cast_succ_zero : cast_succ (0 : fin (n + 1)) = 0 := rfl

@[simp] lemma cast_succ_one {n : ℕ} : fin.cast_succ (1 : fin (n + 2)) = 1 := rfl

/-- `cast_succ i` is positive when `i` is positive -/
lemma cast_succ_pos {i : fin (n + 1)} (h : 0 < i) : 0 < cast_succ i :=
by simpa [lt_iff_coe_lt_coe] using h

@[simp] lemma cast_succ_eq_zero_iff (a : fin (n + 1)) : a.cast_succ = 0 ↔ a = 0 :=
subtype.ext_iff.trans $ (subtype.ext_iff.trans $ by exact iff.rfl).symm

lemma cast_succ_ne_zero_iff (a : fin (n + 1)) : a.cast_succ ≠ 0 ↔ a ≠ 0 :=
not_iff_not.mpr $ cast_succ_eq_zero_iff a

lemma cast_succ_fin_succ (n : ℕ) (j : fin n) :
  cast_succ (fin.succ j) = fin.succ (cast_succ j) :=
by simp [fin.ext_iff]

@[norm_cast, simp] lemma coe_eq_cast_succ : (a : fin (n + 1)) = a.cast_succ :=
begin
  ext,
  exact coe_val_of_lt (nat.lt.step a.is_lt),
end

@[simp] lemma coe_succ_eq_succ : a.cast_succ + 1 = a.succ :=
begin
  cases n,
  { exact fin_zero_elim a },
  { simp [a.is_lt, eq_iff_veq, add_def, nat.mod_eq_of_lt] }
end

lemma lt_succ : a.cast_succ < a.succ :=
by { rw [cast_succ, lt_iff_coe_lt_coe, coe_cast_add, coe_succ], exact lt_add_one a.val }

@[simp] lemma range_cast_succ {n : ℕ} :
  set.range (cast_succ : fin n → fin n.succ) = {i | (i : ℕ) < n} :=
range_cast_le _

@[simp] lemma coe_of_injective_cast_succ_symm {n : ℕ} (i : fin n.succ) (hi) :
  ((equiv.of_injective cast_succ (cast_succ_injective _)).symm ⟨i, hi⟩ : ℕ) = i :=
begin
  rw ← coe_cast_succ,
  exact congr_arg coe (equiv.apply_of_injective_symm _ _ _)
end

/-- `add_nat m i` adds `m` to `i`, generalizes `fin.succ`. -/
def add_nat (m) : fin n ↪o fin (n + m) :=
order_embedding.of_strict_mono (λ i, ⟨(i : ℕ) + m, add_lt_add_right i.2 _⟩) $
  λ i j h, lt_iff_coe_lt_coe.2 $ add_lt_add_right h _

@[simp] lemma coe_add_nat (m : ℕ) (i : fin n) : (add_nat m i : ℕ) = i + m := rfl

/-- `nat_add n i` adds `n` to `i` "on the left". -/
def nat_add (n) {m} : fin m ↪o fin (n + m) :=
order_embedding.of_strict_mono (λ i, ⟨n + (i : ℕ), add_lt_add_left i.2 _⟩) $
  λ i j h, lt_iff_coe_lt_coe.2 $ add_lt_add_left h _

@[simp] lemma coe_nat_add (n : ℕ) {m : ℕ} (i : fin m) : (nat_add n i : ℕ) = n + i := rfl

lemma nat_add_zero {n : ℕ} : fin.nat_add 0 = (fin.cast (zero_add n).symm).to_rel_embedding :=
by { ext, apply zero_add }

end succ

section rec

/-!
### recursion and induction principles
-/

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple. -/
@[elab_as_eliminator] def succ_rec
  {C : Π n, fin n → Sort*}
  (H0 : Π n, C (succ n) 0)
  (Hs : Π n i, C n i → C (succ n) i.succ) : Π {n : ℕ} (i : fin n), C n i
| 0        i           := i.elim0
| (succ n) ⟨0, _⟩      := H0 _
| (succ n) ⟨succ i, h⟩ := Hs _ _ (succ_rec ⟨i, lt_of_succ_lt_succ h⟩)

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple.

A version of `fin.succ_rec` taking `i : fin n` as the first argument. -/
@[elab_as_eliminator] def succ_rec_on {n : ℕ} (i : fin n)
  {C : Π n, fin n → Sort*}
  (H0 : Π n, C (succ n) 0)
  (Hs : Π n i, C n i → C (succ n) i.succ) : C n i :=
i.succ_rec H0 Hs

@[simp] theorem succ_rec_on_zero {C : ∀ n, fin n → Sort*} {H0 Hs} (n) :
  @fin.succ_rec_on (succ n) 0 C H0 Hs = H0 n :=
rfl

@[simp] theorem succ_rec_on_succ {C : ∀ n, fin n → Sort*} {H0 Hs} {n} (i : fin n) :
  @fin.succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (fin.succ_rec_on i H0 Hs) :=
by cases i; refl

/--
Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.
-/
@[elab_as_eliminator] def induction
  {C : fin (n + 1) → Sort*}
  (h0 : C 0)
  (hs : ∀ i : fin n, C i.cast_succ → C i.succ) :
  Π (i : fin (n + 1)), C i :=
begin
  rintro ⟨i, hi⟩,
  induction i with i IH,
  { rwa [fin.mk_zero] },
  { refine hs ⟨i, lt_of_succ_lt_succ hi⟩ _,
    exact IH (lt_of_succ_lt hi) }
end

/--
Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.

A version of `fin.induction` taking `i : fin (n + 1)` as the first argument.
-/
@[elab_as_eliminator] def induction_on (i : fin (n + 1))
  {C : fin (n + 1) → Sort*}
  (h0 : C 0)
  (hs : ∀ i : fin n, C i.cast_succ → C i.succ) : C i :=
induction h0 hs i

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : fin n`. -/
@[elab_as_eliminator] def cases
  {C : fin (succ n) → Sort*} (H0 : C 0) (Hs : Π i : fin n, C (i.succ)) :
  Π (i : fin (succ n)), C i :=
induction H0 (λ i _, Hs i)

@[simp] theorem cases_zero {n} {C : fin (succ n) → Sort*} {H0 Hs} : @fin.cases n C H0 Hs 0 = H0 :=
rfl

@[simp] theorem cases_succ {n} {C : fin (succ n) → Sort*} {H0 Hs} (i : fin n) :
  @fin.cases n C H0 Hs i.succ = Hs i :=
by cases i; refl

@[simp] theorem cases_succ' {n} {C : fin (succ n) → Sort*} {H0 Hs} {i : ℕ} (h : i + 1 < n + 1) :
  @fin.cases n C H0 Hs ⟨i.succ, h⟩ = Hs ⟨i, lt_of_succ_lt_succ h⟩ :=
by cases i; refl

lemma forall_fin_succ {P : fin (n+1) → Prop} :
  (∀ i, P i) ↔ P 0 ∧ (∀ i:fin n, P i.succ) :=
⟨λ H, ⟨H 0, λ i, H _⟩, λ ⟨H0, H1⟩ i, fin.cases H0 H1 i⟩

lemma exists_fin_succ {P : fin (n+1) → Prop} :
  (∃ i, P i) ↔ P 0 ∨ (∃i:fin n, P i.succ) :=
⟨λ ⟨i, h⟩, fin.cases or.inl (λ i hi, or.inr ⟨i, hi⟩) i h,
  λ h, or.elim h (λ h, ⟨0, h⟩) $ λ⟨i, hi⟩, ⟨i.succ, hi⟩⟩

end rec

section pred

/-!
### pred
-/

@[simp] lemma coe_pred (j : fin (n+1)) (h : j ≠ 0) : (j.pred h : ℕ) = j - 1 :=
by { cases j, refl }

@[simp] lemma succ_pred : ∀(i : fin (n+1)) (h : i ≠ 0), (i.pred h).succ = i
| ⟨0,     h⟩ hi := by contradiction
| ⟨n + 1, h⟩ hi := rfl

@[simp] lemma pred_succ (i : fin n) {h : i.succ ≠ 0} : i.succ.pred h = i :=
by { cases i, refl }

@[simp] lemma pred_mk_succ (i : ℕ) (h : i < n + 1) :
  fin.pred ⟨i + 1, add_lt_add_right h 1⟩ (ne_of_vne (ne_of_gt (mk_succ_pos i h))) = ⟨i, h⟩ :=
by simp only [ext_iff, coe_pred, coe_mk, nat.add_sub_cancel]

-- This is not a simp lemma by default, because `pred_mk_succ` is nicer when it applies.
lemma pred_mk {n : ℕ} (i : ℕ) (h : i < n + 1) (w) :
  fin.pred ⟨i, h⟩ w =
  ⟨i - 1, by rwa nat.sub_lt_right_iff_lt_add (nat.pos_of_ne_zero (fin.vne_of_ne w))⟩ :=
rfl

@[simp] lemma pred_le_pred_iff {n : ℕ} {a b : fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
  a.pred ha ≤ b.pred hb ↔ a ≤ b :=
by rw [←succ_le_succ_iff, succ_pred, succ_pred]

@[simp] lemma pred_lt_pred_iff {n : ℕ} {a b : fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
  a.pred ha < b.pred hb ↔ a < b :=
by rw [←succ_lt_succ_iff, succ_pred, succ_pred]

@[simp] lemma pred_inj :
  ∀ {a b : fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
| ⟨0,   _⟩  b         ha hb := by contradiction
| ⟨i+1, _⟩  ⟨0,   _⟩  ha hb := by contradiction
| ⟨i+1, hi⟩ ⟨j+1, hj⟩ ha hb := by simp [fin.eq_iff_veq]

@[simp] lemma pred_one {n : ℕ} : fin.pred (1 : fin (n + 2)) (ne.symm (ne_of_lt one_pos)) = 0 := rfl

lemma pred_add_one (i : fin (n + 2)) (h : (i : ℕ) < n + 1) :
  pred (i + 1) (ne_of_gt (add_one_pos _ (lt_iff_coe_lt_coe.mpr h))) = cast_lt i h :=
begin
  rw [ext_iff, coe_pred, coe_cast_lt, coe_add, coe_one, mod_eq_of_lt, nat.add_sub_cancel],
  exact add_lt_add_right h 1,
end

/-- `sub_nat i h` subtracts `m` from `i`, generalizes `fin.pred`. -/
def sub_nat (m) (i : fin (n + m)) (h : m ≤ (i : ℕ)) : fin n :=
⟨(i : ℕ) - m, by { rw [nat.sub_lt_right_iff_lt_add h], exact i.is_lt }⟩

@[simp] lemma coe_sub_nat (i : fin (n + m)) (h : m ≤ i) : (i.sub_nat m h : ℕ) = i - m :=
rfl

@[simp] lemma pred_cast_succ_succ (i : fin n) :
  pred (cast_succ i.succ) (ne_of_gt (cast_succ_pos i.succ_pos)) = i.cast_succ :=
by simp [eq_iff_veq]

end pred

section add_group

open nat int

/-- Negation on `fin n` -/
instance (n : ℕ) : has_neg (fin n) :=
⟨λ a, ⟨(n - a) % n, nat.mod_lt _ (lt_of_le_of_lt (nat.zero_le _) a.2)⟩⟩

/-- Abelian group structure on `fin (n+1)`. -/
instance (n : ℕ) : add_comm_group (fin (n+1)) :=
{ add_left_neg := λ ⟨a, ha⟩, fin.ext $ trans (nat.mod_add_mod _ _ _) $
    by { rw [fin.coe_mk, fin.coe_zero, nat.sub_add_cancel, nat.mod_self], exact le_of_lt ha },
  sub_eq_add_neg := λ ⟨a, ha⟩ ⟨b, hb⟩, fin.ext $
    show (a + (n + 1 - b)) % (n + 1) = (a + (n + 1 - b) % (n + 1)) % (n + 1), by simp,
  sub := fin.sub,
  ..fin.add_comm_monoid n,
  ..fin.has_neg n.succ  }

protected lemma coe_neg (a : fin n) : ((-a : fin n) : ℕ) = (n - a) % n := rfl

protected lemma coe_sub (a b : fin n) : ((a - b : fin n) : ℕ) = (a + (n - b)) % n :=
by cases a; cases b; refl

end add_group

section succ_above

lemma succ_above_aux (p : fin (n + 1)) :
  strict_mono (λ i : fin n, if i.cast_succ < p then i.cast_succ else i.succ) :=
(cast_succ : fin n ↪o _).strict_mono.ite (succ_embedding n).strict_mono
  (λ i j hij hj, lt_trans ((cast_succ : fin n ↪o _).lt_iff_lt.2 hij) hj)
  (λ i, (cast_succ_lt_succ i).le)

/-- `succ_above p i` embeds `fin n` into `fin (n + 1)` with a hole around `p`. -/
def succ_above (p : fin (n + 1)) : fin n ↪o fin (n + 1) :=
order_embedding.of_strict_mono _ p.succ_above_aux

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `cast_succ` when the resulting `i.cast_succ < p`. -/
lemma succ_above_below (p : fin (n + 1)) (i : fin n) (h : i.cast_succ < p) :
  p.succ_above i = i.cast_succ :=
by { rw [succ_above], exact if_pos h }

@[simp] lemma succ_above_ne_zero_zero {a : fin (n + 2)} (ha : a ≠ 0) : a.succ_above 0 = 0 :=
begin
  rw fin.succ_above_below,
  { refl },
  { exact bot_lt_iff_ne_bot.mpr ha }
end

lemma succ_above_eq_zero_iff {a : fin (n + 2)} {b : fin (n + 1)} (ha : a ≠ 0) :
  a.succ_above b = 0 ↔ b = 0 :=
by simp only [←succ_above_ne_zero_zero ha, order_embedding.eq_iff_eq]

lemma succ_above_ne_zero {a : fin (n + 2)} {b : fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) :
  a.succ_above b ≠ 0 :=
mt (succ_above_eq_zero_iff ha).mp hb

/-- Embedding `fin n` into `fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp] lemma succ_above_zero : ⇑(succ_above (0 : fin (n + 1))) = fin.succ := rfl

/-- Embedding `fin n` into `fin (n + 1)` with a hole around `last n` embeds by `cast_succ`. -/
@[simp] lemma succ_above_last : succ_above (fin.last n) = cast_succ :=
by { ext, simp only [succ_above_below, cast_succ_lt_last] }

lemma succ_above_last_apply (i : fin n) : succ_above (fin.last n) i = i.cast_succ :=
by rw succ_above_last

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
lemma succ_above_above (p : fin (n + 1)) (i : fin n) (h : p ≤ i.cast_succ) :
  p.succ_above i = i.succ :=
by simp [succ_above, h.not_lt]

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
lemma succ_above_lt_ge (p : fin (n + 1)) (i : fin n) : i.cast_succ < p ∨ p ≤ i.cast_succ :=
lt_or_ge (cast_succ i) p

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
lemma succ_above_lt_gt (p : fin (n + 1)) (i : fin n) : i.cast_succ < p ∨ p < i.succ :=
or.cases_on (succ_above_lt_ge p i)
  (λ h, or.inl h) (λ h, or.inr (lt_of_le_of_lt h (cast_succ_lt_succ i)))

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp] lemma succ_above_lt_iff (p : fin (n + 1)) (i : fin n) :
  p.succ_above i < p ↔ i.cast_succ < p :=
begin
  refine iff.intro _ _,
  { intro h,
    cases succ_above_lt_ge p i with H H,
    { exact H },
    { rw succ_above_above _ _ H at h,
      exact lt_trans (cast_succ_lt_succ i) h } },
  { intro h,
    rw succ_above_below _ _ h,
    exact h }
end

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
lemma lt_succ_above_iff (p : fin (n + 1)) (i : fin n) : p < p.succ_above i ↔ p ≤ i.cast_succ :=
begin
  refine iff.intro _ _,
  { intro h,
    cases succ_above_lt_ge p i with H H,
    { rw succ_above_below _ _ H at h,
      exact le_of_lt h },
    { exact H } },
  { intro h,
    rw succ_above_above _ _ h,
    exact lt_of_le_of_lt h (cast_succ_lt_succ i) },
end

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
never results in `p` itself -/
theorem succ_above_ne (p : fin (n + 1)) (i : fin n) : p.succ_above i ≠ p :=
begin
  intro eq,
  by_cases H : i.cast_succ < p,
  { simpa [lt_irrefl, ←succ_above_below _ _ H, eq] using H },
  { simpa [←succ_above_above _ _ (le_of_not_lt H), eq] using cast_succ_lt_succ i }
end

/-- Embedding a positive `fin n` results in a positive fin (n + 1)` -/
lemma succ_above_pos (p : fin (n + 2)) (i : fin (n + 1)) (h : 0 < i) : 0 < p.succ_above i :=
begin
  by_cases H : i.cast_succ < p,
  { simpa [succ_above_below _ _ H] using cast_succ_pos h },
  { simpa [succ_above_above _ _ (le_of_not_lt H)] using succ_pos _ },
end

/-- The range of `p.succ_above` is everything except `p`. -/
lemma range_succ_above (p : fin (n + 1)) : set.range (p.succ_above) = { i | i ≠ p } :=
begin
  ext,
  simp only [set.mem_range, ne.def, set.mem_set_of_eq],
  split,
  { rintro ⟨y, rfl⟩,
    exact succ_above_ne _ _ },
  { intro h,
    cases lt_or_gt_of_ne h with H H,
    { refine ⟨x.cast_lt _, _⟩,
      { exact lt_of_lt_of_le H p.le_last },
      { rw succ_above_below,
        { simp },
        { exact H } } },
    { refine ⟨x.pred _, _⟩,
      { exact (ne_of_lt (lt_of_le_of_lt p.zero_le H)).symm },
      { rw succ_above_above,
        { simp },
        { simpa [le_iff_coe_le_coe] using nat.le_pred_of_lt H } } } }
end

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
lemma succ_above_right_injective {x : fin (n + 1)} : injective (succ_above x) :=
(succ_above x).injective

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
lemma succ_above_right_inj {x : fin (n + 1)} :
  x.succ_above a = x.succ_above b ↔ a = b :=
succ_above_right_injective.eq_iff

/-- `succ_above` is injective at the pivot -/
lemma succ_above_left_injective : injective (@succ_above n) :=
λ _ _ h, by simpa [range_succ_above] using congr_arg (λ f : fin n ↪o fin (n + 1), (set.range f)ᶜ) h

/-- `succ_above` is injective at the pivot -/
lemma succ_above_left_inj {x y : fin (n + 1)} :
  x.succ_above = y.succ_above ↔ x = y :=
succ_above_left_injective.eq_iff

@[simp] lemma zero_succ_above {n : ℕ} (i : fin n) :
  (0 : fin (n + 1)).succ_above i = i.succ :=
rfl

@[simp] lemma succ_succ_above_zero {n : ℕ} (i : fin (n + 1)) :
  (i.succ).succ_above 0 = 0 :=
succ_above_below _ _ (succ_pos _)

@[simp] lemma succ_succ_above_succ {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  (i.succ).succ_above j.succ = (i.succ_above j).succ :=
(lt_or_ge j.cast_succ i).elim
  (λ h, have h' : j.succ.cast_succ < i.succ, by simpa [lt_iff_coe_lt_coe] using h,
        by { ext, simp [succ_above_below _ _ h, succ_above_below _ _ h'] })
  (λ h, have h' : i.succ ≤ j.succ.cast_succ, by simpa [le_iff_coe_le_coe] using h,
        by { ext, simp [succ_above_above _ _ h, succ_above_above _ _ h'] })

@[simp] lemma one_succ_above_zero {n : ℕ} :
  (1 : fin (n + 2)).succ_above 0 = 0 :=
succ_succ_above_zero 0

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succ_above_zero` or `succ_succ_above_zero`. -/
@[simp] lemma succ_succ_above_one {n : ℕ} (i : fin (n + 2)) :
  (i.succ).succ_above 1 = (i.succ_above 0).succ :=
succ_succ_above_succ i 0

@[simp] lemma one_succ_above_succ {n : ℕ} (j : fin n) :
  (1 : fin (n + 2)).succ_above j.succ = j.succ.succ :=
succ_succ_above_succ 0 j

@[simp] lemma one_succ_above_one {n : ℕ} :
  (1 : fin (n + 3)).succ_above 1 = 2 :=
succ_succ_above_succ 0 0

end succ_above

section pred_above

/-- `pred_above p i` embeds `i : fin (n+1)` into `fin n` by subtracting one if `p < i`. -/
def pred_above (p : fin n) (i : fin (n+1)) : fin n :=
if h : p.cast_succ < i then
  i.pred (ne_of_lt (lt_of_le_of_lt (zero_le p.cast_succ) h)).symm
else
  i.cast_lt (lt_of_le_of_lt (le_of_not_lt h) p.2)

lemma pred_above_right_monotone (p : fin n) : monotone p.pred_above :=
λ a b H,
begin
  dsimp [pred_above],
  split_ifs with ha hb hb,
  all_goals { simp only [le_iff_coe_le_coe, coe_pred], },
  { exact pred_le_pred H, },
  { calc _ ≤ _ : nat.pred_le _
        ... ≤ _ : H, },
  { simp at ha, exact le_pred_of_lt (lt_of_le_of_lt ha hb), },
  { exact H, },
end

lemma pred_above_left_monotone (i : fin (n + 1)) : monotone (λ p, pred_above p i) :=
λ a b H,
begin
  dsimp [pred_above],
  split_ifs with ha hb hb,
  all_goals { simp only [le_iff_coe_le_coe, coe_pred] },
  { exact pred_le _, },
  { have : b < a := cast_succ_lt_cast_succ_iff.mpr (hb.trans_le (le_of_not_gt ha)),
    exact absurd H this.not_le }
end

/-- `cast_pred` embeds `i : fin (n + 2)` into `fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def cast_pred (i : fin (n + 2)) : fin (n + 1) :=
pred_above (last n) i

@[simp] lemma cast_pred_zero : cast_pred (0 : fin (n + 2)) = 0 := rfl

@[simp] lemma cast_pred_one : cast_pred (1 : fin (n + 2)) = 1 :=
by { cases n, apply subsingleton.elim, refl }

@[simp] theorem pred_above_zero {i : fin (n + 2)} (hi : i ≠ 0) :
  pred_above 0 i = i.pred hi :=
begin
  dsimp [pred_above],
  rw dif_pos,
  exact (pos_iff_ne_zero _).mpr hi,
end

@[simp] lemma cast_pred_last : cast_pred (last (n + 1)) = last n :=
by simp [eq_iff_veq, cast_pred, pred_above, cast_succ_lt_last]

@[simp] lemma cast_pred_mk (n i : ℕ) (h : i < n + 1) :
  cast_pred ⟨i, lt_succ_of_lt h⟩ = ⟨i, h⟩ :=
begin
  have : ¬cast_succ (last n) < ⟨i, lt_succ_of_lt h⟩,
    { simpa [lt_iff_coe_lt_coe] using le_of_lt_succ h },
  simp [cast_pred, pred_above, this]
end

lemma pred_above_below (p : fin (n + 1)) (i : fin (n + 2)) (h : i ≤ p.cast_succ) :
  p.pred_above i = i.cast_pred :=
begin
  have : i ≤ (last n).cast_succ := h.trans p.le_last,
  simp [pred_above, cast_pred, h.not_lt, this.not_lt]
end

@[simp] lemma pred_above_last : pred_above (fin.last n) = cast_pred := rfl

lemma pred_above_last_apply (i : fin n) : pred_above (fin.last n) i = i.cast_pred :=
by rw pred_above_last

lemma pred_above_above (p : fin n) (i : fin (n + 1)) (h : p.cast_succ < i) :
  p.pred_above i = i.pred (p.cast_succ.zero_le.trans_lt h).ne.symm :=
by simp [pred_above, h]

lemma cast_pred_monotone : monotone (@cast_pred n) :=
pred_above_right_monotone (last _)

/-- Sending `fin (n+1)` to `fin n` by subtracting one from anything above `p`
then back to `fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp] lemma succ_above_pred_above {p : fin n} {i : fin (n + 1)} (h : i ≠ p.cast_succ) :
  p.cast_succ.succ_above (p.pred_above i) = i :=
begin
  dsimp [pred_above, succ_above],
  rcases p with ⟨p, _⟩,
  rcases i with ⟨i, _⟩,
  cases lt_or_le i p with H H,
  { rw dif_neg, rw if_pos, refl, exact H, simp, apply le_of_lt H, },
  { rw dif_pos, rw if_neg,
    swap 3, -- For some reason `simp` doesn't fire fully unless we discharge the third goal.
    { exact lt_of_le_of_ne H (ne.symm h), },
    { simp, },
    { simp only [subtype.mk_eq_mk, ne.def, fin.cast_succ_mk] at h,
      simp only [pred, subtype.mk_lt_mk, not_lt],
      exact nat.le_pred_of_lt (nat.lt_of_le_and_ne H (ne.symm h)), }, },
end

/-- Sending `fin n` into `fin (n + 1)` with a gap at `p`
then back to `fin n` by subtracting one from anything above `p` is the identity. -/
@[simp] lemma pred_above_succ_above (p : fin n) (i : fin n) :
  p.pred_above (p.cast_succ.succ_above i) = i :=
begin
  dsimp [pred_above, succ_above],
  rcases p with ⟨p, _⟩,
  rcases i with ⟨i, _⟩,
  split_ifs,
  { rw dif_neg,
    { refl },
    { simp_rw [if_pos h],
      simp only [subtype.mk_lt_mk, not_lt],
      exact le_of_lt h, }, },
  { rw dif_pos,
    { refl, },
    { simp_rw [if_neg h],
      exact lt_succ_iff.mpr (not_lt.mp h), }, },
end

lemma cast_succ_pred_eq_pred_cast_succ  {a : fin (n + 1)} (ha : a ≠ 0)
  (ha' := a.cast_succ_ne_zero_iff.mpr ha) : (a.pred ha).cast_succ = a.cast_succ.pred ha' :=
by { cases a, refl }

/-- `pred` commutes with `succ_above`. -/
lemma pred_succ_above_pred {a : fin (n + 2)} {b : fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
  (hk := succ_above_ne_zero ha hb) :
  (a.pred ha).succ_above (b.pred hb) = (a.succ_above b).pred hk :=
begin
  obtain hbelow | habove := lt_or_le b.cast_succ a, -- `rwa` uses them
  { rw fin.succ_above_below,
    { rwa [cast_succ_pred_eq_pred_cast_succ , fin.pred_inj, fin.succ_above_below] },
    { rwa [cast_succ_pred_eq_pred_cast_succ , pred_lt_pred_iff] } },
  { rw fin.succ_above_above,
    have : (b.pred hb).succ = b.succ.pred (fin.succ_ne_zero _), by rw [succ_pred, pred_succ],
    { rwa [this, fin.pred_inj, fin.succ_above_above] },
    { rwa [cast_succ_pred_eq_pred_cast_succ , fin.pred_le_pred_iff] } }
end

@[simp] theorem cast_pred_cast_succ (i : fin (n + 1)) :
  cast_pred i.cast_succ = i :=
by simp [cast_pred, pred_above, le_last]

lemma cast_succ_cast_pred {i : fin (n + 2)} (h : i < last _) : cast_succ i.cast_pred = i :=
begin
  rw [cast_pred, pred_above, dif_neg],
  { simp [fin.eq_iff_veq] },
  { exact h.not_le }
end

lemma coe_cast_pred_le_self (i : fin (n + 2)) : (i.cast_pred : ℕ) ≤ i :=
begin
  rcases i.le_last.eq_or_lt with rfl|h,
  { simp },
  { rw [cast_pred, pred_above, dif_neg],
    { simp },
    { simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe, lt_succ_iff] using h } }
end

lemma coe_cast_pred_lt_iff {i : fin (n + 2)} : (i.cast_pred : ℕ) < i ↔ i = fin.last _ :=
begin
  rcases i.le_last.eq_or_lt with rfl|H,
  { simp },
  { simp only [ne_of_lt H],
    rw ←cast_succ_cast_pred H,
    simp }
end

lemma lt_last_iff_coe_cast_pred {i : fin (n + 2)} : i < fin.last _ ↔ (i.cast_pred : ℕ) = i :=
begin
  rcases i.le_last.eq_or_lt with rfl|H,
  { simp },
  { simp only [H],
    rw ←cast_succ_cast_pred H,
    simp }
end

lemma forall_iff_succ_above {p : fin (n + 1) → Prop} (i : fin (n + 1)) :
  (∀ j, p j) ↔ p i ∧ ∀ j, p (i.succ_above j) :=
⟨λ h, ⟨h _, λ j, h _⟩,
  λ h j, if hj : j = i then (hj.symm ▸ h.1) else
  begin
    cases n,
    { convert h.1 },
    { cases lt_or_gt_of_ne hj with lt gt,
      { rcases j.zero_le.eq_or_lt with rfl|H,
        { convert h.2 0, rw succ_above_below; simp [lt] },
        { have ltl : j < last _ := lt.trans_le i.le_last,
          convert h.2 j.cast_pred,
          simp [succ_above_below, cast_succ_cast_pred ltl, lt] } },
      { convert h.2 (j.pred (i.zero_le.trans_lt gt).ne.symm),
        rw succ_above_above;
        simp [le_cast_succ_iff, gt.lt] } }
  end⟩

end pred_above

/-- `min n m` as an element of `fin (m + 1)` -/
def clamp (n m : ℕ) : fin (m + 1) := of_nat $ min n m

@[simp] lemma coe_clamp (n m : ℕ) : (clamp n m : ℕ) = min n m :=
nat.mod_eq_of_lt $ nat.lt_succ_iff.mpr $ min_le_right _ _

section tuple
/-!
### Tuples

We can think of the type `Π(i : fin n), α i` as `n`-tuples of elements of possibly varying type
`α i`. A particular case is `fin n → α` of elements with all the same type. Here are some relevant
operations, first about adding or removing elements at the beginning of a tuple.
-/

/-- There is exactly one tuple of size zero. -/
example (α : fin 0 → Sort u) : unique (Π i : fin 0, α i) :=
by apply_instance

@[simp] lemma tuple0_le {α : Π i : fin 0, Type*} [Π i, preorder (α i)] (f g : Π i, α i) : f ≤ g :=
fin_zero_elim

variables {α : fin (n+1) → Type u} (x : α 0) (q : Πi, α i) (p : Π(i : fin n), α (i.succ))
  (i : fin n) (y : α i.succ) (z : α 0)

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail (q : Πi, α i) : (Π(i : fin n), α (i.succ)) := λ i, q i.succ

lemma tail_def {n : ℕ} {α : fin (n+1) → Type*} {q : Π i, α i} :
  tail (λ k : fin (n+1), q k) = (λ k : fin n, q k.succ) := rfl

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons (x : α 0) (p : Π(i : fin n), α (i.succ)) : Πi, α i :=
λ j, fin.cases x p j

@[simp] lemma tail_cons : tail (cons x p) = p :=
by simp [tail, cons]

@[simp] lemma cons_succ : cons x p i.succ = p i :=
by simp [cons]

@[simp] lemma cons_zero : cons x p 0 = x :=
by simp [cons]

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp] lemma cons_update : cons x (update p i y) = update (cons x p) i.succ y :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, simp [ne.symm (succ_ne_zero i)] },
  { let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, cons_succ],
    by_cases h' : j' = i,
    { rw h', simp },
    { have : j'.succ ≠ i.succ, by rwa [ne.def, succ_inj],
      rw [update_noteq h', update_noteq this, cons_succ] } }
end

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
lemma update_cons_zero : update (cons x p) 0 z = cons z p :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, simp },
  { simp only [h, update_noteq, ne.def, not_false_iff],
    let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, cons_succ, cons_succ] }
end

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp] lemma cons_self_tail : cons (q 0) (tail q) = q :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, simp },
  { let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, tail, cons_succ] }
end

/-- Updating the first element of a tuple does not change the tail. -/
@[simp] lemma tail_update_zero : tail (update q 0 z) = tail q :=
by { ext j, simp [tail, fin.succ_ne_zero] }

/-- Updating a nonzero element and taking the tail commute. -/
@[simp] lemma tail_update_succ :
  tail (update q i.succ y) = update (tail q) i y :=
begin
  ext j,
  by_cases h : j = i,
  { rw h, simp [tail] },
  { simp [tail, (fin.succ_injective n).ne h, h] }
end

lemma comp_cons {α : Type*} {β : Type*} (g : α → β) (y : α) (q : fin n → α) :
  g ∘ (cons y q) = cons (g y) (g ∘ q) :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, refl },
  { let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, cons_succ, comp_app, cons_succ] }
end

lemma comp_tail {α : Type*} {β : Type*} (g : α → β) (q : fin n.succ → α) :
  g ∘ (tail q) = tail (g ∘ q) :=
by { ext j, simp [tail] }

lemma le_cons [Π i, preorder (α i)] {x : α 0} {q : Π i, α i} {p : Π i : fin n, α i.succ} :
  q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
forall_fin_succ.trans $ and_congr iff.rfl $ forall_congr $ λ j, by simp [tail]

lemma cons_le [Π i, preorder (α i)] {x : α 0} {q : Π i, α i} {p : Π i : fin n, α i.succ} :
  cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
@le_cons  _ (λ i, order_dual (α i)) _ x q p

@[simp]
lemma range_cons {α : Type*} {n : ℕ} (x : α) (b : fin n → α) :
  set.range (fin.cons x b : fin n.succ → α) = insert x (set.range b) :=
begin
  ext y,
  simp only [set.mem_range, set.mem_insert_iff],
  split,
  { rintros ⟨i, rfl⟩,
    refine cases (or.inl (cons_zero _ _)) (λ i, or.inr ⟨i, _⟩) i,
    rw cons_succ },
  { rintros (rfl | ⟨i, hi⟩),
    { exact ⟨0, fin.cons_zero _ _⟩ },
    { refine ⟨i.succ, _⟩,
      rw [cons_succ, hi] } }
end

/-- `fin.append ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`.  `ho` provides control of definitional equality
for the vector length. -/
def append {α : Type*} {o : ℕ} (ho : o = m + n) (u : fin m → α) (v : fin n → α) : fin o → α :=
λ i, if h : (i : ℕ) < m
  then u ⟨i, h⟩
  else v ⟨(i : ℕ) - m, (nat.sub_lt_left_iff_lt_add (le_of_not_lt h)).2 (ho ▸ i.property)⟩

@[simp] lemma fin_append_apply_zero {α : Type*} {o : ℕ} (ho : (o + 1) = (m + 1) + n)
  (u : fin (m + 1) → α) (v : fin n → α) :
  fin.append ho u v 0 = u 0 := rfl

end tuple

section tuple_right
/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `fin (n+1)` is constructed
inductively from `fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/

variables {α : fin (n+1) → Type u} (x : α (last n)) (q : Πi, α i) (p : Π(i : fin n), α i.cast_succ)
(i : fin n) (y : α i.cast_succ) (z : α (last n))

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init (q : Πi, α i) (i : fin n) : α i.cast_succ :=
q i.cast_succ

lemma init_def {n : ℕ} {α : fin (n+1) → Type*} {q : Π i, α i} :
  init (λ k : fin (n+1), q k) = (λ k : fin n, q k.cast_succ) := rfl

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc (p : Π(i : fin n), α i.cast_succ) (x : α (last n)) (i : fin (n+1)) : α i :=
if h : i.val < n
then _root_.cast (by rw fin.cast_succ_cast_lt i h) (p (cast_lt i h))
else _root_.cast (by rw eq_last_of_not_lt h) x

@[simp] lemma init_snoc : init (snoc p x) = p :=
begin
  ext i,
  have h' := fin.cast_lt_cast_succ i i.is_lt,
  simp [init, snoc, i.is_lt, h'],
  convert cast_eq rfl (p i)
end

@[simp] lemma snoc_cast_succ : snoc p x i.cast_succ = p i :=
begin
  have : i.cast_succ.val < n := i.is_lt,
  have h' := fin.cast_lt_cast_succ i i.is_lt,
  simp [snoc, this, h'],
  convert cast_eq rfl (p i)
end

@[simp] lemma snoc_last : snoc p x (last n) = x :=
by { simp [snoc] }

/-- Updating a tuple and adding an element at the end commute. -/
@[simp] lemma snoc_update : snoc (update p i y) x = update (snoc p x) i.cast_succ y :=
begin
  ext j,
  by_cases h : j.val < n,
  { simp only [snoc, h, dif_pos],
    by_cases h' : j = cast_succ i,
    { have C1 : α i.cast_succ = α j, by rw h',
      have E1 : update (snoc p x) i.cast_succ y j = _root_.cast C1 y,
      { have : update (snoc p x) j (_root_.cast C1 y) j = _root_.cast C1 y, by simp,
        convert this,
        { exact h'.symm },
        { exact heq_of_cast_eq (congr_arg α (eq.symm h')) rfl } },
      have C2 : α i.cast_succ = α (cast_succ (cast_lt j h)),
        by rw [cast_succ_cast_lt, h'],
      have E2 : update p i y (cast_lt j h) = _root_.cast C2 y,
      { have : update p (cast_lt j h) (_root_.cast C2 y) (cast_lt j h) = _root_.cast C2 y,
          by simp,
        convert this,
        { simp [h, h'] },
        { exact heq_of_cast_eq C2 rfl } },
      rw [E1, E2],
      exact eq_rec_compose _ _ _ },
    { have : ¬(cast_lt j h = i),
        by { assume E, apply h', rw [← E, cast_succ_cast_lt] },
      simp [h', this, snoc, h] } },
  { rw eq_last_of_not_lt h,
    simp [ne.symm (ne_of_lt (cast_succ_lt_last i))] }
end

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
lemma update_snoc_last : update (snoc p x) (last n) z = snoc p z :=
begin
  ext j,
  by_cases h : j.val < n,
  { have : j ≠ last n := ne_of_lt h,
    simp [h, update_noteq, this, snoc] },
  { rw eq_last_of_not_lt h,
    simp }
end

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp] lemma snoc_init_self : snoc (init q) (q (last n)) = q :=
begin
  ext j,
  by_cases h : j.val < n,
  { have : j ≠ last n := ne_of_lt h,
    simp [h, update_noteq, this, snoc, init, cast_succ_cast_lt],
    have A : cast_succ (cast_lt j h) = j := cast_succ_cast_lt _ _,
    rw ← cast_eq rfl (q j),
    congr' 1; rw A },
  { rw eq_last_of_not_lt h,
    simp }
end

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp] lemma init_update_last : init (update q (last n) z) = init q :=
by { ext j, simp [init, ne_of_lt, cast_succ_lt_last] }

/-- Updating an element and taking the beginning commute. -/
@[simp] lemma init_update_cast_succ :
  init (update q i.cast_succ y) = update (init q) i y :=
begin
  ext j,
  by_cases h : j = i,
  { rw h, simp [init] },
  { simp [init, h] }
end

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
lemma tail_init_eq_init_tail {β : Type*} (q : fin (n+2) → β) :
  tail (init q) = init (tail q) :=
by { ext i, simp [tail, init, cast_succ_fin_succ] }

/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
lemma cons_snoc_eq_snoc_cons {β : Type*} (a : β) (q : fin n → β) (b : β) :
  @cons n.succ (λ i, β) a (snoc q b) = snoc (cons a q) b :=
begin
  ext i,
  by_cases h : i = 0,
  { rw h, refl },
  set j := pred i h with ji,
  have : i = j.succ, by rw [ji, succ_pred],
  rw [this, cons_succ],
  by_cases h' : j.val < n,
  { set k := cast_lt j h' with jk,
    have : j = k.cast_succ, by rw [jk, cast_succ_cast_lt],
    rw [this, ← cast_succ_fin_succ],
    simp },
  rw [eq_last_of_not_lt h', succ_last],
  simp
end


lemma comp_snoc {α : Type*} {β : Type*} (g : α → β) (q : fin n → α) (y : α) :
  g ∘ (snoc q y) = snoc (g ∘ q) (g y) :=
begin
  ext j,
  by_cases h : j.val < n,
  { have : j ≠ last n := ne_of_lt h,
    simp [h, this, snoc, cast_succ_cast_lt] },
  { rw eq_last_of_not_lt h,
    simp }
end

lemma comp_init {α : Type*} {β : Type*} (g : α → β) (q : fin n.succ → α) :
  g ∘ (init q) = init (g ∘ q) :=
by { ext j, simp [init] }

end tuple_right

section insert_nth

variables {α : fin (n+1) → Type u} {β : Type v}

/-- Insert an element into a tuple at a given position, auxiliary definition.
For the general definition, see `insert_nth`. -/
def insert_nth' {α : fin (n + 2) → Type u} (i : fin (n + 2)) (x : α i)
  (p : Π j : fin (n + 1), α (i.succ_above j)) (j : fin (n + 2)) : α j :=
if h : i = j
then _root_.cast (congr_arg α h) x
else if h' : j < i then _root_.cast (congr_arg α $ begin
  obtain ⟨k, hk⟩ : ∃ (k : fin (n + 1)), k.cast_succ = j,
    { refine ⟨⟨(j : ℕ), _⟩, _⟩,
      { exact lt_of_lt_of_le h' i.is_le, },
      { simp },
    },
  subst hk,
  simp [succ_above_below, h'],
end)
  (p j.cast_pred) else _root_.cast (congr_arg α $ begin
  have lt : i < j := lt_of_le_of_ne (le_of_not_lt h') h,
  have : j ≠ 0 := (ne_of_gt (lt_of_le_of_lt i.zero_le lt)),
  rw [←succ_pred j this, ←le_cast_succ_iff] at lt,
  simp [pred_above_zero this, succ_above_above _ _ lt]
end) (p (fin.pred_above 0 j))

/-- Insert an element into a tuple at a given position. For `i = 0` see `fin.cons`,
for `i = fin.last n` see `fin.snoc`. -/
def insert_nth : Π {n : ℕ} {α : fin (n + 1) → Type u} (i : fin (n + 1)) (x : α i)
  (p : Π j : fin n, α (i.succ_above j)) (j : fin (n + 1)), α j
| 0       _ _ x _ _ := _root_.cast (by congr) x
| (n + 1) _ i x p j := insert_nth' i x p j

@[simp] lemma insert_nth_apply_same (i : fin (n + 1)) (x : α i) (p : Π j, α (i.succ_above j)) :
  insert_nth i x p i = x :=
by { cases n; simp [insert_nth, insert_nth'] }

@[simp] lemma insert_nth_apply_succ_above (i : fin (n + 1)) (x : α i) (p : Π j, α (i.succ_above j))
  (j : fin n) :
  insert_nth i x p (i.succ_above j) = p j :=
begin
  cases n,
  { exact j.elim0 },
  simp only [insert_nth, insert_nth', dif_neg (succ_above_ne _ _).symm],
  cases succ_above_lt_ge i j with h h,
  { rw dif_pos,
    refine eq_of_heq ((cast_heq _ _).trans _),
    { simp [h] },
    { congr,
      simp [succ_above_below, h] } },
  { rw dif_neg,
    refine eq_of_heq ((cast_heq _ _).trans _),
    { simp [h] },
    { congr,
      simp [succ_above_above, h, succ_ne_zero] } }
end

@[simp] lemma insert_nth_comp_succ_above (i : fin (n + 1)) (x : β) (p : fin n → β) :
  insert_nth i x p ∘ i.succ_above = p :=
funext $ insert_nth_apply_succ_above i x p

lemma insert_nth_eq_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  i.insert_nth x p = q ↔ q i = x ∧ p = (λ j, q (i.succ_above j)) :=
by simp [funext_iff, forall_iff_succ_above i, eq_comm]

lemma eq_insert_nth_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  q = i.insert_nth x p ↔ q i = x ∧ p = (λ j, q (i.succ_above j)) :=
eq_comm.trans insert_nth_eq_iff

lemma insert_nth_zero (x : α 0) (p : Π j : fin n, α (succ_above 0 j)) :
  insert_nth 0 x p = cons x (λ j, _root_.cast (congr_arg α (congr_fun succ_above_zero j)) (p j)) :=
begin
  refine insert_nth_eq_iff.2 ⟨by simp, _⟩,
  ext j,
  convert (cons_succ _ _ _).symm
end

@[simp] lemma insert_nth_zero' (x : β) (p : fin n → β) :
  @insert_nth _ (λ _, β) 0 x p = cons x p :=
by simp [insert_nth_zero]

lemma insert_nth_last (x : α (last n)) (p : Π j : fin n, α ((last n).succ_above j)) :
  insert_nth (last n) x p =
    snoc (λ j, _root_.cast (congr_arg α (succ_above_last_apply j)) (p j)) x :=
begin
  refine insert_nth_eq_iff.2 ⟨by simp, _⟩,
  ext j,
  apply eq_of_heq,
  transitivity snoc (λ j, _root_.cast (congr_arg α (succ_above_last_apply j)) (p j)) x j.cast_succ,
  { rw [snoc_cast_succ], exact (cast_heq _ _).symm },
  { apply congr_arg_heq,
    rw [succ_above_last] }
end

@[simp] lemma insert_nth_last' (x : β) (p : fin n → β) :
  @insert_nth _ (λ _, β) (last n) x p = snoc p x :=
by simp [insert_nth_last]

variables [Π i, preorder (α i)]

lemma insert_nth_le_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  i.insert_nth x p ≤ q ↔ x ≤ q i ∧ p ≤ (λ j, q (i.succ_above j)) :=
by simp [pi.le_def, forall_iff_succ_above i]

lemma le_insert_nth_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  q ≤ i.insert_nth x p ↔ q i ≤ x ∧ (λ j, q (i.succ_above j)) ≤ p :=
by simp [pi.le_def, forall_iff_succ_above i]

open set

lemma insert_nth_mem_Icc {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)}
  {q₁ q₂ : Π j, α j} :
  i.insert_nth x p ∈ Icc q₁ q₂ ↔
    x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (λ j, q₁ (i.succ_above j)) (λ j, q₂ (i.succ_above j)) :=
by simp only [mem_Icc, insert_nth_le_iff, le_insert_nth_iff, and.assoc, and.left_comm]

lemma preimage_insert_nth_Icc_of_mem {i : fin (n + 1)} {x : α i} {q₁ q₂ : Π j, α j}
  (hx : x ∈ Icc (q₁ i) (q₂ i)) :
  i.insert_nth x ⁻¹' (Icc q₁ q₂) = Icc (λ j, q₁ (i.succ_above j)) (λ j, q₂ (i.succ_above j)) :=
set.ext $ λ p, by simp only [mem_preimage, insert_nth_mem_Icc, hx, true_and]

lemma preimage_insert_nth_Icc_of_not_mem {i : fin (n + 1)} {x : α i} {q₁ q₂ : Π j, α j}
  (hx : x ∉ Icc (q₁ i) (q₂ i)) :
  i.insert_nth x ⁻¹' (Icc q₁ q₂) = ∅ :=
set.ext $ λ p, by simp only [mem_preimage, insert_nth_mem_Icc, hx, false_and, mem_empty_eq]

end insert_nth

section find

/-- `find p` returns the first index `n` where `p n` is satisfied, and `none` if it is never
satisfied. -/
def find : Π {n : ℕ} (p : fin n → Prop) [decidable_pred p], option (fin n)
| 0     p _ := none
| (n+1) p _ := by resetI; exact option.cases_on
  (@find n (λ i, p (i.cast_lt (nat.lt_succ_of_lt i.2))) _)
  (if h : p (fin.last n) then some (fin.last n) else none)
  (λ i, some (i.cast_lt (nat.lt_succ_of_lt i.2)))

/-- If `find p = some i`, then `p i` holds -/
lemma find_spec : Π {n : ℕ} (p : fin n → Prop) [decidable_pred p] {i : fin n}
  (hi : i ∈ by exactI fin.find p), p i
| 0     p I i hi := option.no_confusion hi
| (n+1) p I i hi := begin
  dsimp [find] at hi,
  resetI,
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with j,
  { rw h at hi,
    dsimp at hi,
    split_ifs at hi with hl hl,
    { exact option.some_inj.1 hi ▸ hl },
    { exact option.no_confusion hi } },
  { rw h at hi,
    rw [← option.some_inj.1 hi],
    exact find_spec _ h }
end

/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
lemma is_some_find_iff : Π {n : ℕ} {p : fin n → Prop} [decidable_pred p],
  by exactI (find p).is_some ↔ ∃ i, p i
| 0     p _ := iff_of_false (λ h, bool.no_confusion h) (λ ⟨i, _⟩, fin_zero_elim i)
| (n+1) p _ := ⟨λ h, begin
  rw [option.is_some_iff_exists] at h,
  cases h with i hi,
  exactI ⟨i, find_spec _ hi⟩
end, λ ⟨⟨i, hin⟩, hi⟩,
begin
  resetI,
  dsimp [find],
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with j,
  { split_ifs with hl hl,
    { exact option.is_some_some },
    { have := (@is_some_find_iff n (λ x, p (x.cast_lt (nat.lt_succ_of_lt x.2))) _).2
        ⟨⟨i, lt_of_le_of_ne (nat.le_of_lt_succ hin)
        (λ h, by clear_aux_decl; cases h; exact hl hi)⟩, hi⟩,
      rw h at this,
      exact this } },
  { simp }
end⟩

/-- `find p` returns `none` if and only if `p i` never holds. -/
lemma find_eq_none_iff {n : ℕ} {p : fin n → Prop} [decidable_pred p] :
  find p = none ↔ ∀ i, ¬ p i :=
by rw [← not_exists, ← is_some_find_iff]; cases (find p); simp

/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
lemma find_min : Π {n : ℕ} {p : fin n → Prop} [decidable_pred p] {i : fin n}
  (hi : i ∈ by exactI fin.find p) {j : fin n} (hj : j < i), ¬ p j
| 0     p _ i hi j hj hpj := option.no_confusion hi
| (n+1) p _ i hi ⟨j, hjn⟩ hj hpj := begin
  resetI,
  dsimp [find] at hi,
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with k,
  { rw [h] at hi,
    split_ifs at hi with hl hl,
    { have := option.some_inj.1 hi,
      subst this,
      rw [find_eq_none_iff] at h,
      exact h ⟨j, hj⟩ hpj },
    { exact option.no_confusion hi } },
  { rw h at hi,
    dsimp at hi,
    have := option.some_inj.1 hi,
    subst this,
    exact find_min h (show (⟨j, lt_trans hj k.2⟩ : fin n) < k, from hj) hpj }
end

lemma find_min' {p : fin n → Prop} [decidable_pred p] {i : fin n}
  (h : i ∈ fin.find p) {j : fin n} (hj : p j) : i ≤ j :=
le_of_not_gt (λ hij, find_min h hij hj)

lemma nat_find_mem_find {p : fin n → Prop} [decidable_pred p]
  (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
  (⟨nat.find h, (nat.find_spec h).fst⟩ : fin n) ∈ find p :=
let ⟨i, hin, hi⟩ := h in
begin
  cases hf : find p with f,
  { rw [find_eq_none_iff] at hf,
    exact (hf ⟨i, hin⟩ hi).elim },
  { refine option.some_inj.2 (le_antisymm _ _),
    { exact find_min' hf (nat.find_spec h).snd },
    { exact nat.find_min' _ ⟨f.2, by convert find_spec p hf;
        exact fin.eta _ _⟩ } }
end

lemma mem_find_iff {p : fin n → Prop} [decidable_pred p] {i : fin n} :
  i ∈ fin.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
⟨λ hi, ⟨find_spec _ hi, λ _, find_min' hi⟩,
  begin
    rintros ⟨hpi, hj⟩,
    cases hfp : fin.find p,
    { rw [find_eq_none_iff] at hfp,
      exact (hfp _ hpi).elim },
    { exact option.some_inj.2 (le_antisymm (find_min' hfp hpi) (hj _ (find_spec _ hfp))) }
  end⟩

lemma find_eq_some_iff {p : fin n → Prop} [decidable_pred p] {i : fin n} :
  fin.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j :=
 mem_find_iff

lemma mem_find_of_unique {p : fin n → Prop} [decidable_pred p]
  (h : ∀ i j, p i → p j → i = j) {i : fin n} (hi : p i) : i ∈ fin.find p :=
mem_find_iff.2 ⟨hi, λ j hj, le_of_eq $ h i j hi hj⟩

end find

@[simp]
lemma coe_of_nat_eq_mod (m n : ℕ) :
  ((n : fin (succ m)) : ℕ) = n % succ m :=
by rw [← of_nat_eq_coe]; refl

@[simp] lemma coe_of_nat_eq_mod' (m n : ℕ) [I : fact (0 < m)] :
  (@fin.of_nat' _ I n : ℕ) = n % m :=
rfl

section mul

/-!
### mul
-/

lemma val_mul {n : ℕ} :  ∀ a b : fin n, (a * b).val = (a.val * b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma coe_mul {n : ℕ} :  ∀ a b : fin n, ((a * b : fin n) : ℕ) = (a * b) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] protected lemma mul_one (k : fin (n + 1)) : k * 1 = k :=
by { cases n, simp, simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)] }

@[simp] protected lemma one_mul (k : fin (n + 1)) : (1 : fin (n + 1)) * k = k :=
by { cases n, simp, simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)] }

@[simp] protected lemma mul_zero (k : fin (n + 1)) : k * 0 = 0 :=
by simp [eq_iff_veq, mul_def]

@[simp] protected lemma zero_mul (k : fin (n + 1)) : (0 : fin (n + 1)) * k = 0 :=
by simp [eq_iff_veq, mul_def]

end mul

end fin
