/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.finset.sort
import group_theory.order_of_element

/-!
# Sign of a permutation

The main definition of this file is `equiv.perm.sign`, associating a `units ℤ` sign with a
permutation.

This file also contains miscellaneous lemmas about `equiv.perm` and `equiv.swap`, building on top
of those in `data/equiv/basic` and `data/equiv/perm`.

-/

universes u v
open equiv function fintype finset
open_locale big_operators
variables {α : Type u} {β : Type v}

namespace equiv.perm

/--
`mod_swap i j` contains permutations up to swapping `i` and `j`.

We use this to partition permutations in `matrix.det_zero_of_row_eq`, such that each partition
sums up to `0`.
-/
def mod_swap [decidable_eq α] (i j : α) : setoid (perm α) :=
⟨λ σ τ, σ = τ ∨ σ = swap i j * τ,
 λ σ, or.inl (refl σ),
 λ σ τ h, or.cases_on h (λ h, or.inl h.symm) (λ h, or.inr (by rw [h, swap_mul_self_mul])),
 λ σ τ υ hστ hτυ, by cases hστ; cases hτυ; try {rw [hστ, hτυ, swap_mul_self_mul]}; finish⟩

instance {α : Type*} [fintype α] [decidable_eq α] (i j : α) : decidable_rel (mod_swap i j).r :=
λ σ τ, or.decidable

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtype_perm (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) : perm {x // p x} :=
⟨λ x, ⟨f x, (h _).1 x.2⟩, λ x, ⟨f⁻¹ x, (h (f⁻¹ x)).2 $ by simpa using x.2⟩,
  λ _, by simp only [perm.inv_apply_self, subtype.coe_eta, subtype.coe_mk],
  λ _, by simp only [perm.apply_inv_self, subtype.coe_eta, subtype.coe_mk]⟩

@[simp] lemma subtype_perm_one (p : α → Prop) (h : ∀ x, p x ↔ p ((1 : perm α) x)) :
  @subtype_perm α 1 p h = 1 :=
equiv.ext $ λ ⟨_, _⟩, rfl

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def of_subtype {p : α → Prop} [decidable_pred p] : perm (subtype p) →* perm α :=
{ to_fun := λ f,
  ⟨λ x, if h : p x then f ⟨x, h⟩ else x, λ x, if h : p x then f⁻¹ ⟨x, h⟩ else x,
  λ x, have h : ∀ h : p x, p (f ⟨x, h⟩), from λ h, (f ⟨x, h⟩).2,
    by { simp only [], split_ifs at *;
         simp only [perm.inv_apply_self, subtype.coe_eta, subtype.coe_mk, not_true, *] at * },
  λ x, have h : ∀ h : p x, p (f⁻¹ ⟨x, h⟩), from λ h, (f⁻¹ ⟨x, h⟩).2,
    by { simp only [], split_ifs at *;
         simp only [perm.apply_inv_self, subtype.coe_eta, subtype.coe_mk, not_true, *] at * }⟩,
  map_one' := begin ext, dsimp, split_ifs; refl, end,
  map_mul' := λ f g, equiv.ext $ λ x, begin
  by_cases h : p x,
  { have h₁ : p (f (g ⟨x, h⟩)), from (f (g ⟨x, h⟩)).2,
    have h₂ : p (g ⟨x, h⟩), from (g ⟨x, h⟩).2,
    simp only [h, h₂, coe_fn_mk, perm.mul_apply, dif_pos, subtype.coe_eta] },
  { simp only [h, coe_fn_mk, perm.mul_apply, dif_neg, not_false_iff] }
end }

/-- Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def disjoint (f g : perm α) := ∀ x, f x = x ∨ g x = x

@[symm] lemma disjoint.symm {f g : perm α} : disjoint f g → disjoint g f :=
by simp only [disjoint, or.comm, imp_self]

lemma disjoint_comm {f g : perm α} : disjoint f g ↔ disjoint g f :=
⟨disjoint.symm, disjoint.symm⟩

lemma disjoint.mul_comm {f g : perm α} (h : disjoint f g) : f * g = g * f :=
equiv.ext $ λ x, (h x).elim
  (λ hf, (h (g x)).elim (λ hg, by simp [mul_apply, hf, hg])
    (λ hg, by simp [mul_apply, hf, g.injective hg]))
  (λ hg, (h (f x)).elim (λ hf, by simp [mul_apply, f.injective hf, hg])
    (λ hf, by simp [mul_apply, hf, hg]))

@[simp] lemma disjoint_one_left (f : perm α) : disjoint 1 f := λ _, or.inl rfl

@[simp] lemma disjoint_one_right (f : perm α) : disjoint f 1 := λ _, or.inr rfl

lemma disjoint.mul_left {f g h : perm α} (H1 : disjoint f h) (H2 : disjoint g h) :
  disjoint (f * g) h :=
λ x, by cases H1 x; cases H2 x; simp *

lemma disjoint.mul_right {f g h : perm α} (H1 : disjoint f g) (H2 : disjoint f h) :
  disjoint f (g * h) :=
by { rw disjoint_comm, exact H1.symm.mul_left H2.symm }

lemma disjoint_prod_right {f : perm α} (l : list (perm α))
  (h : ∀ g ∈ l, disjoint f g) : disjoint f l.prod :=
begin
  induction l with g l ih,
  { exact disjoint_one_right _ },
  { rw list.prod_cons,
    exact (h _ (list.mem_cons_self _ _)).mul_right (ih (λ g hg, h g (list.mem_cons_of_mem _ hg))) }
end

lemma disjoint_prod_perm {l₁ l₂ : list (perm α)} (hl : l₁.pairwise disjoint)
  (hp : l₁ ~ l₂) : l₁.prod = l₂.prod :=
hp.prod_eq' $ hl.imp $ λ f g, disjoint.mul_comm

lemma of_subtype_subtype_perm {f : perm α} {p : α → Prop} [decidable_pred p]
  (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) :
  of_subtype (subtype_perm f h₁) = f :=
equiv.ext $ λ x, begin
  rw [of_subtype, subtype_perm],
  by_cases hx : p x,
  { simp only [hx, coe_fn_mk, dif_pos, monoid_hom.coe_mk, subtype.coe_mk]},
  { haveI := classical.prop_decidable,
    simp only [hx, not_not.mp (mt (h₂ x) hx), coe_fn_mk, dif_neg, not_false_iff,
      monoid_hom.coe_mk] }
end

lemma of_subtype_apply_of_not_mem {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) {x : α} (hx : ¬ p x) :
  of_subtype f x = x :=
dif_neg hx

lemma mem_iff_of_subtype_apply_mem {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) (x : α) :
  p x ↔ p ((of_subtype f : α → α) x) :=
if h : p x then by simpa only [of_subtype, h, coe_fn_mk, dif_pos, true_iff, monoid_hom.coe_mk]
  using (f ⟨x, h⟩).2
else by simp [h, of_subtype_apply_of_not_mem f h]

@[simp] lemma subtype_perm_of_subtype {p : α → Prop} [decidable_pred p] (f : perm (subtype p)) :
  subtype_perm (of_subtype f) (mem_iff_of_subtype_apply_mem f) = f :=
equiv.ext $ λ ⟨x, hx⟩, by { dsimp [subtype_perm, of_subtype],
  simp only [show p x, from hx, dif_pos, subtype.coe_eta] }

lemma pow_apply_eq_self_of_apply_eq_self {f : perm α} {x : α} (hfx : f x = x) :
  ∀ n : ℕ, (f ^ n) x = x
| 0     := rfl
| (n+1) := by rw [pow_succ', mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self]

lemma gpow_apply_eq_self_of_apply_eq_self {f : perm α} {x : α} (hfx : f x = x) :
  ∀ n : ℤ, (f ^ n) x = x
| (n : ℕ) := pow_apply_eq_self_of_apply_eq_self hfx n
| -[1+ n] := by rw [gpow_neg_succ_of_nat, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]

lemma pow_apply_eq_of_apply_apply_eq_self {f : perm α} {x : α} (hffx : f (f x) = x) :
  ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
| 0     := or.inl rfl
| (n+1) := (pow_apply_eq_of_apply_apply_eq_self n).elim
  (λ h, or.inr (by rw [pow_succ, mul_apply, h]))
  (λ h, or.inl (by rw [pow_succ, mul_apply, h, hffx]))

lemma gpow_apply_eq_of_apply_apply_eq_self {f : perm α} {x : α} (hffx : f (f x) = x) :
  ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
| (n : ℕ) := pow_apply_eq_of_apply_apply_eq_self hffx n
| -[1+ n] := by { rw [gpow_neg_succ_of_nat, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply,
    ← pow_succ, eq_comm, inv_eq_iff_eq, ← mul_apply, ← pow_succ', @eq_comm _ x, or.comm],
  exact pow_apply_eq_of_apply_apply_eq_self hffx _ }

variable [decidable_eq α]

/-- The `finset` of nonfixed points of a permutation. -/
def support [fintype α] (f : perm α) : finset α := univ.filter (λ x, f x ≠ x)

@[simp] lemma mem_support [fintype α] {f : perm α} {x : α} : x ∈ f.support ↔ f x ≠ x :=
by simp only [support, true_and, mem_filter, mem_univ]

/-- `f.is_swap` indicates that the permutation `f` is a transposition of two elements. -/
def is_swap (f : perm α) : Prop := ∃ x y, x ≠ y ∧ f = swap x y

lemma is_swap.of_subtype_is_swap {p : α → Prop} [decidable_pred p]
  {f : perm (subtype p)} (h : f.is_swap) : (of_subtype f).is_swap :=
let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h in
⟨x, y, by { simp only [ne.def] at hxy, exact hxy.1 },
  equiv.ext $ λ z, begin
    rw [hxy.2, of_subtype],
    simp only [swap_apply_def, coe_fn_mk, swap_inv, subtype.mk_eq_mk, monoid_hom.coe_mk],
    split_ifs;
    rw subtype.coe_mk <|> cc,
  end⟩

lemma ne_and_ne_of_swap_mul_apply_ne_self {f : perm α} {x y : α}
  (hy : (swap x (f x) * f) y ≠ y) : f y ≠ y ∧ y ≠ x :=
begin
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *,
  by_cases h : f y = x,
  { split; intro; simp only [*, if_true, eq_self_iff_true, not_true, ne.def] at * },
  { split_ifs at hy; cc }
end

lemma support_swap_mul_eq [fintype α] {f : perm α} {x : α}
  (hffx : f (f x) ≠ x) : (swap x (f x) * f).support = f.support.erase x :=
have hfx : f x ≠ x, from λ hfx, by simpa [hfx] using hffx,
finset.ext $ λ y,
⟨λ hy, have hy' : (swap x (f x) * f) y ≠ y, from mem_support.1 hy,
    mem_erase.2 ⟨λ hyx, by simp [hyx, mul_apply, *] at *,
    mem_support.2 $ λ hfy,
      by simp only [mul_apply, swap_apply_def, hfy] at hy';
      split_ifs at hy'; simp only [*, eq_self_iff_true, not_true, ne.def, apply_eq_iff_eq] at *⟩,
  λ hy, by simp only [mem_erase, mem_support, swap_apply_def, mul_apply] at *;
    intro; split_ifs at *; simp only [*, eq_self_iff_true, not_true, ne.def] at *⟩

lemma card_support_swap_mul [fintype α] {f : perm α} {x : α}
  (hx : f x ≠ x) : (swap x (f x) * f).support.card < f.support.card :=
finset.card_lt_card
  ⟨λ z hz, mem_support.2 (ne_and_ne_of_swap_mul_apply_ne_self (mem_support.1 hz)).1,
    λ h, absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

/-- Given a list `l : list α` and a permutation `f : perm α` such that the nonfixed points of `f`
  are in `l`, recursively factors `f` as a product of transpositions. -/
def swap_factors_aux : Π (l : list α) (f : perm α), (∀ {x}, f x ≠ x → x ∈ l) →
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g}
| []       := λ f h, ⟨[], equiv.ext $ λ x, by { rw [list.prod_nil],
    exact (not_not.1 (mt h (list.not_mem_nil _))).symm }, by simp⟩
| (x :: l) := λ f h,
if hfx : x = f x
then swap_factors_aux l f
  (λ y hy, list.mem_of_ne_of_mem (λ h : y = x, by simpa [h, hfx.symm] using hy) (h hy))
else let m := swap_factors_aux l (swap x (f x) * f)
      (λ y hy, have f y ≠ y ∧ y ≠ x, from ne_and_ne_of_swap_mul_apply_ne_self hy,
        list.mem_of_ne_of_mem this.2 (h this.1)) in
  ⟨swap x (f x) :: m.1,
  by rw [list.prod_cons, m.2.1, ← mul_assoc,
    mul_def (swap x (f x)), swap_swap, ← one_def, one_mul],
  λ g hg, ((list.mem_cons_iff _ _ _).1 hg).elim (λ h, ⟨x, f x, hfx, h⟩) (m.2.2 _)⟩

/-- `swap_factors` represents a permutation as a product of a list of transpositions.
The representation is non unique and depends on the linear order structure.
For types without linear order `trunc_swap_factors` can be used. -/
def swap_factors [fintype α] [linear_order α] (f : perm α) :
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
swap_factors_aux ((@univ α _).sort (≤)) f (λ _ _, (mem_sort _).2 (mem_univ _))

/-- This computably represents the fact that any permutation can be represented as the product of
  a list of transpositions. -/
def trunc_swap_factors [fintype α] (f : perm α) :
  trunc {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
quotient.rec_on_subsingleton (@univ α _).1
  (λ l h, trunc.mk (swap_factors_aux l f h))
  (show ∀ x, f x ≠ x → x ∈ (@univ α _).1, from λ _ _, mem_univ _)

/-- An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_eliminator] lemma swap_induction_on [fintype α] {P : perm α → Prop} (f : perm α) :
  P 1 → (∀ f x y, x ≠ y → P f → P (swap x y * f)) → P f :=
begin
  cases (trunc_swap_factors f).out with l hl,
  induction l with g l ih generalizing f,
  { simp only [hl.left.symm, list.prod_nil, forall_true_iff] {contextual := tt} },
  { assume h1 hmul_swap,
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩,
    rw [← hl.1, list.prod_cons, hxy.2],
    exact hmul_swap _ _ _ hxy.1
      (ih _ ⟨rfl, λ v hv, hl.2 _ (list.mem_cons_of_mem _ hv)⟩ h1 hmul_swap) }
end

/-- Like `swap_induction_on`, but with the composition on the right of `f`.

An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_eliminator] lemma swap_induction_on' [fintype α] {P : perm α → Prop} (f : perm α) :
  P 1 → (∀ f x y, x ≠ y → P f → P (f * swap x y)) → P f :=
λ h1 IH, inv_inv f ▸ swap_induction_on f⁻¹ h1 (λ f, IH f⁻¹)

lemma is_conj_swap {w x y z : α} (hwx : w ≠ x) (hyz : y ≠ z) : is_conj (swap w x) (swap y z) :=
have h : ∀ {y z : α}, y ≠ z → w ≠ z →
    (swap w y * swap x z) * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
  λ y z hyz hwz, by rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc (swap w y),
    mul_assoc (swap w y), ← mul_assoc _ (swap x z), swap_mul_swap_mul_swap hwx hwz,
    ← mul_assoc, swap_mul_swap_mul_swap hwz.symm hyz.symm],
if hwz : w = z
then have hwy : w ≠ y, by cc,
  ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
else ⟨swap w y * swap x z, h hyz hwz⟩

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
def fin_pairs_lt (n : ℕ) : finset (Σ a : fin n, fin n) :=
(univ : finset (fin n)).sigma (λ a, (range a).attach_fin
  (λ m hm, (mem_range.1 hm).trans a.2))

lemma mem_fin_pairs_lt {n : ℕ} {a : Σ a : fin n, fin n} :
  a ∈ fin_pairs_lt n ↔ a.2 < a.1 :=
by simp only [fin_pairs_lt, fin.lt_iff_coe_lt_coe, true_and, mem_attach_fin, mem_range, mem_univ,
  mem_sigma]

/-- `sign_aux σ` is the sign of a permutation on `fin n`, defined as the parity of the number of
  pairs `(x₁, x₂)` such that `x₂ < x₁` but `σ x₁ ≤ σ x₂` -/
def sign_aux {n : ℕ} (a : perm (fin n)) : units ℤ :=
∏ x in fin_pairs_lt n, if a x.1 ≤ a x.2 then -1 else 1

@[simp] lemma sign_aux_one (n : ℕ) : sign_aux (1 : perm (fin n)) = 1 :=
begin
  unfold sign_aux,
  conv { to_rhs, rw ← @finset.prod_const_one _ (units ℤ)
    (fin_pairs_lt n) },
  exact finset.prod_congr rfl (λ a ha, if_neg (mem_fin_pairs_lt.1 ha).not_le)
end

/-- `sign_bij_aux f ⟨a, b⟩` returns the pair consisting of `f a` and `f b` in decreasing order. -/
def sign_bij_aux {n : ℕ} (f : perm (fin n)) (a : Σ a : fin n, fin n) :
  Σ a : fin n, fin n :=
if hxa : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩

lemma sign_bij_aux_inj {n : ℕ} {f : perm (fin n)} : ∀ a b : Σ a : fin n, fin n,
   a ∈ fin_pairs_lt n → b ∈ fin_pairs_lt n →
   sign_bij_aux f a = sign_bij_aux f b → a = b :=
λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h, begin
  unfold sign_bij_aux at h,
  rw mem_fin_pairs_lt at *,
  have : ¬b₁ < b₂ := hb.le.not_lt,
  split_ifs at h;
  simp only [*, (equiv.injective f).eq_iff, eq_self_iff_true, and_self, heq_iff_eq] at *,
end

lemma sign_bij_aux_surj {n : ℕ} {f : perm (fin n)} : ∀ a ∈ fin_pairs_lt n,
  ∃ b ∈ fin_pairs_lt n, a = sign_bij_aux f b :=
λ ⟨a₁, a₂⟩ ha,
if hxa : f⁻¹ a₂ < f⁻¹ a₁
then ⟨⟨f⁻¹ a₁, f⁻¹ a₂⟩, mem_fin_pairs_lt.2 hxa,
  by { dsimp [sign_bij_aux],
    rw [apply_inv_self, apply_inv_self, dif_pos (mem_fin_pairs_lt.1 ha)] }⟩
else ⟨⟨f⁻¹ a₂, f⁻¹ a₁⟩, mem_fin_pairs_lt.2 $ (le_of_not_gt hxa).lt_of_ne $ λ h,
    by simpa [mem_fin_pairs_lt, (f⁻¹).injective h, lt_irrefl] using ha,
  by { dsimp [sign_bij_aux],
    rw [apply_inv_self, apply_inv_self, dif_neg (mem_fin_pairs_lt.1 ha).le.not_lt] }⟩

lemma sign_bij_aux_mem {n : ℕ} {f : perm (fin n)} : ∀ a : Σ a : fin n, fin n,
  a ∈ fin_pairs_lt n → sign_bij_aux f a ∈ fin_pairs_lt n :=
λ ⟨a₁, a₂⟩ ha, begin
  unfold sign_bij_aux,
  split_ifs with h,
  { exact mem_fin_pairs_lt.2 h },
  { exact mem_fin_pairs_lt.2
    ((le_of_not_gt h).lt_of_ne (λ h, (mem_fin_pairs_lt.1 ha).ne (f.injective h.symm))) }
end

@[simp] lemma sign_aux_inv {n : ℕ} (f : perm (fin n)) : sign_aux f⁻¹ = sign_aux f :=
prod_bij (λ a ha, sign_bij_aux f⁻¹ a)
  sign_bij_aux_mem
  (λ ⟨a, b⟩ hab, if h : f⁻¹ b < f⁻¹ a
    then by rw [sign_bij_aux, dif_pos h, if_neg h.not_le, apply_inv_self,
      apply_inv_self, if_neg (mem_fin_pairs_lt.1 hab).not_le]
    else by rw [sign_bij_aux, if_pos (le_of_not_gt h), dif_neg h, apply_inv_self,
      apply_inv_self, if_pos (mem_fin_pairs_lt.1 hab).le])
  sign_bij_aux_inj
  sign_bij_aux_surj

lemma sign_aux_mul {n : ℕ} (f g : perm (fin n)) :
  sign_aux (f * g) = sign_aux f * sign_aux g :=
begin
  rw ← sign_aux_inv g,
  unfold sign_aux,
  rw ← prod_mul_distrib,
  refine prod_bij (λ a ha, sign_bij_aux g a) sign_bij_aux_mem _ sign_bij_aux_inj sign_bij_aux_surj,
  rintros ⟨a, b⟩ hab,
  rw [sign_bij_aux, mul_apply, mul_apply],
  rw mem_fin_pairs_lt at hab,
  by_cases h : g b < g a,
  { rw dif_pos h,
    simp only [not_le_of_gt hab, mul_one, perm.inv_apply_self, if_false] },
  { rw [dif_neg h, inv_apply_self, inv_apply_self, if_pos hab.le],
    by_cases h₁ : f (g b) ≤ f (g a),
    { have : f (g b) ≠ f (g a),
      { rw [ne.def, f.injective.eq_iff, g.injective.eq_iff],
        exact ne_of_lt hab },
      rw [if_pos h₁, if_neg (h₁.lt_of_ne this).not_le],
      refl },
    { rw [if_neg h₁, if_pos (lt_of_not_ge h₁).le],
      refl } }
end

-- TODO: slow
private lemma sign_aux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
  sign_aux (swap (⟨0, lt_of_lt_of_le dec_trivial hn⟩ : fin n)
  ⟨1, lt_of_lt_of_le dec_trivial hn⟩) = -1 :=
let zero : fin n := ⟨0, lt_of_lt_of_le dec_trivial hn⟩ in
let one : fin n := ⟨1, lt_of_lt_of_le dec_trivial hn⟩ in
have hzo : zero < one := dec_trivial,
show _ = ∏ x : Σ a : fin n, fin n in {(⟨one, zero⟩ : Σ a : fin n, fin n)},
  if (equiv.swap zero one) x.1 ≤ swap zero one x.2 then (-1 : units ℤ) else 1,
begin
  refine eq.symm (prod_subset (λ ⟨x₁, x₂⟩, by simp [mem_fin_pairs_lt, hzo] {contextual := tt})
    (λ a ha₁ ha₂, _)),
  rcases a with ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩,
  replace ha₁ : a₂ < a₁ := mem_fin_pairs_lt.1 ha₁,
  simp only [swap_apply_def],
  have : ¬ 1 ≤ a₂ → a₂ = 0, from λ h, nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge h)),
  have : a₁ ≤ 1 → a₁ = 0 ∨ a₁ = 1, from nat.cases_on a₁ (λ _, or.inl rfl)
    (λ a₁, nat.cases_on a₁ (λ _, or.inr rfl) (λ _ h, absurd h dec_trivial)),
  split_ifs;
  simp only [*, not_le.symm, iff.intro fin.veq_of_eq fin.eq_of_veq, nat.le_zero_iff,
    eq_self_iff_true, not_true, fin.le_def, one, nat.zero_le, and_self, heq_iff_eq, mem_singleton,
    forall_prop_of_true, or_self, le_refl] at *,
end

lemma sign_aux_swap : ∀ {n : ℕ} {x y : fin n} (hxy : x ≠ y),
  sign_aux (swap x y) = -1
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ x y hxy,
have h2n : 2 ≤ n + 2 := dec_trivial,
by { rw [← is_conj_iff_eq, ← sign_aux_swap_zero_one h2n],
  exact (monoid_hom.mk' sign_aux sign_aux_mul).map_is_conj (is_conj_swap hxy dec_trivial) }

/-- When the list `l : list α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 l f` recursively calculates the sign of `f`. -/
def sign_aux2 : list α → perm α → units ℤ
| []     f := 1
| (x::l) f := if x = f x then sign_aux2 l f else -sign_aux2 l (swap x (f x) * f)

lemma sign_aux_eq_sign_aux2 {n : ℕ} : ∀ (l : list α) (f : perm α) (e : α ≃ fin n)
  (h : ∀ x, f x ≠ x → x ∈ l), sign_aux ((e.symm.trans f).trans e) = sign_aux2 l f
| []     f e h := have f = 1, from equiv.ext $
  λ y, not_not.1 (mt (h y) (list.not_mem_nil _)),
by rw [this, one_def, equiv.trans_refl, equiv.symm_trans, ← one_def,
  sign_aux_one, sign_aux2]
| (x::l) f e h := begin
  rw sign_aux2,
  by_cases hfx : x = f x,
  { rw if_pos hfx,
    exact sign_aux_eq_sign_aux2 l f _ (λ y (hy : f y ≠ y), list.mem_of_ne_of_mem
      (λ h : y = x, by simpa [h, hfx.symm] using hy) (h y hy) ) },
  { have hy : ∀ y : α, (swap x (f x) * f) y ≠ y → y ∈ l, from λ y hy,
      have f y ≠ y ∧ y ≠ x, from ne_and_ne_of_swap_mul_apply_ne_self hy,
      list.mem_of_ne_of_mem this.2 (h _ this.1),
    have : (e.symm.trans (swap x (f x) * f)).trans e =
      (swap (e x) (e (f x))) * (e.symm.trans f).trans e,
      by ext; simp [← equiv.symm_trans_swap_trans, mul_def],
    have hefx : e x ≠ e (f x), from mt e.injective.eq_iff.1 hfx,
    rw [if_neg hfx, ← sign_aux_eq_sign_aux2 _ _ e hy, this, sign_aux_mul, sign_aux_swap hefx],
    simp only [units.neg_neg, one_mul, units.neg_mul]}
end

/-- When the multiset `s : multiset α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 f _` recursively calculates the sign of `f`. -/
def sign_aux3 [fintype α] (f : perm α) {s : multiset α} : (∀ x, x ∈ s) → units ℤ :=
quotient.hrec_on s (λ l h, sign_aux2 l f)
  (trunc.induction_on (equiv_fin α)
    (λ e l₁ l₂ h, function.hfunext
      (show (∀ x, x ∈ l₁) = ∀ x, x ∈ l₂, by simp only [h.mem_iff])
      (λ h₁ h₂ _, by rw [← sign_aux_eq_sign_aux2 _ _ e (λ _ _, h₁ _),
        ← sign_aux_eq_sign_aux2 _ _ e (λ _ _, h₂ _)])))

lemma sign_aux3_mul_and_swap [fintype α] (f g : perm α) (s : multiset α) (hs : ∀ x, x ∈ s) :
  sign_aux3 (f * g) hs = sign_aux3 f hs * sign_aux3 g hs ∧ ∀ x y, x ≠ y →
  sign_aux3 (swap x y) hs = -1 :=
let ⟨l, hl⟩ := quotient.exists_rep s in
let ⟨e, _⟩ := (equiv_fin α).exists_rep in
begin
  clear _let_match _let_match,
  subst hl,
  show sign_aux2 l (f * g) = sign_aux2 l f * sign_aux2 l g ∧
    ∀ x y, x ≠ y → sign_aux2 l (swap x y) = -1,
  have hfg : (e.symm.trans (f * g)).trans e = (e.symm.trans f).trans e * (e.symm.trans g).trans e,
    from equiv.ext (λ h, by simp [mul_apply]),
  split,
  { rw [← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _), ← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _),
      ← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _), hfg, sign_aux_mul] },
  { assume x y hxy,
    have hexy : e x ≠ e y, from mt e.injective.eq_iff.1 hxy,
    rw [← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _), symm_trans_swap_trans, sign_aux_swap hexy] }
end

/-- `sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`perm α` to the group with two elements.-/
def sign [fintype α] : perm α →* units ℤ := monoid_hom.mk'
(λ f, sign_aux3 f mem_univ) (λ f g, (sign_aux3_mul_and_swap f g _ mem_univ).1)

section sign

variable [fintype α]

@[simp] lemma sign_mul (f g : perm α) : sign (f * g) = sign f * sign g :=
monoid_hom.map_mul sign f g

@[simp] lemma sign_trans (f g : perm α) : sign (f.trans g) = sign g * sign f :=
by rw [←mul_def, sign_mul]

@[simp] lemma sign_one : (sign (1 : perm α)) = 1 :=
monoid_hom.map_one sign

@[simp] lemma sign_refl : sign (equiv.refl α) = 1 :=
monoid_hom.map_one sign

@[simp] lemma sign_inv (f : perm α) : sign f⁻¹ = sign f :=
by rw [monoid_hom.map_inv sign f, int.units_inv_eq_self]

@[simp] lemma sign_symm (e : perm α) : sign e.symm = sign e :=
sign_inv e

lemma sign_swap {x y : α} (h : x ≠ y) : sign (swap x y) = -1 :=
(sign_aux3_mul_and_swap 1 1 _ mem_univ).2 x y h

@[simp] lemma sign_swap' {x y : α} :
  (swap x y).sign = if x = y then 1 else -1 :=
if H : x = y then by simp [H, swap_self] else
by simp [sign_swap H, H]

lemma is_swap.sign_eq {f : perm α} (h : f.is_swap) : sign f = -1 :=
let ⟨x, y, hxy⟩ := h in hxy.2.symm ▸ sign_swap hxy.1

lemma sign_aux3_symm_trans_trans [decidable_eq β] [fintype β] (f : perm α)
  (e : α ≃ β) {s : multiset α} {t : multiset β} (hs : ∀ x, x ∈ s) (ht : ∀ x, x ∈ t) :
  sign_aux3 ((e.symm.trans f).trans e) ht = sign_aux3 f hs :=
quotient.induction_on₂ t s
  (λ l₁ l₂ h₁ h₂, show sign_aux2 _ _ = sign_aux2 _ _,
    from let n := (equiv_fin β).out in
    by { rw [← sign_aux_eq_sign_aux2 _ _ n (λ _ _, h₁ _),
        ← sign_aux_eq_sign_aux2 _ _ (e.trans n) (λ _ _, h₂ _)],
      exact congr_arg sign_aux
        (equiv.ext (λ x, by simp only [equiv.coe_trans, apply_eq_iff_eq, symm_trans_apply])) })
  ht hs

@[simp] lemma sign_symm_trans_trans [decidable_eq β] [fintype β] (f : perm α) (e : α ≃ β) :
  sign ((e.symm.trans f).trans e) = sign f :=
sign_aux3_symm_trans_trans f e mem_univ mem_univ

@[simp] lemma sign_trans_trans_symm [decidable_eq β] [fintype β] (f : perm β) (e : α ≃ β) :
  sign ((e.trans f).trans e.symm) = sign f :=
sign_symm_trans_trans f e.symm

lemma sign_prod_list_swap {l : list (perm α)}
  (hl : ∀ g ∈ l, is_swap g) : sign l.prod = (-1) ^ l.length :=
have h₁ : l.map sign = list.repeat (-1) l.length :=
  list.eq_repeat.2 ⟨by simp, λ u hu,
  let ⟨g, hg⟩ := list.mem_map.1 hu in
  hg.2 ▸ (hl _ hg.1).sign_eq⟩,
by rw [← list.prod_repeat, ← h₁, list.prod_hom _ (@sign α _ _)]

lemma sign_surjective (hα : 1 < fintype.card α) : function.surjective (sign : perm α → units ℤ) :=
λ a, (int.units_eq_one_or a).elim
  (λ h, ⟨1, by simp [h]⟩)
  (λ h, let ⟨x⟩ := fintype.card_pos_iff.1 (lt_trans zero_lt_one hα) in
    let ⟨y, hxy⟩ := fintype.exists_ne_of_one_lt_card hα x in
    ⟨swap y x, by rw [sign_swap hxy, h]⟩ )

lemma eq_sign_of_surjective_hom {s : perm α →* units ℤ} (hs : surjective s) : s = sign :=
have ∀ {f}, is_swap f → s f = -1 :=
  λ f ⟨x, y, hxy, hxy'⟩, hxy'.symm ▸ by_contradiction (λ h,
    have ∀ f, is_swap f → s f = 1 := λ f ⟨a, b, hab, hab'⟩,
      by { rw [← is_conj_iff_eq, ← or.resolve_right (int.units_eq_one_or _) h, hab'],
        exact (monoid_hom.of s).map_is_conj (is_conj_swap hab hxy) },
  let ⟨g, hg⟩ := hs (-1) in
  let ⟨l, hl⟩ := (trunc_swap_factors g).out in
  have ∀ a ∈ l.map s, a = (1 : units ℤ) := λ a ha,
    let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸ this _ (hl.2 _ hg.1),
  have s l.prod = 1,
    by rw [← l.prod_hom s, list.eq_repeat'.2 this, list.prod_repeat, one_pow],
  by { rw [hl.1, hg] at this,
    exact absurd this dec_trivial }),
monoid_hom.ext $ λ f,
let ⟨l, hl₁, hl₂⟩ := (trunc_swap_factors f).out in
have hsl : ∀ a ∈ l.map s, a = (-1 : units ℤ) := λ a ha,
  let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸  this (hl₂ _ hg.1),
by rw [← hl₁, ← l.prod_hom s, list.eq_repeat'.2 hsl, list.length_map,
     list.prod_repeat, sign_prod_list_swap hl₂]

lemma sign_subtype_perm (f : perm α) {p : α → Prop} [decidable_pred p]
  (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) : sign (subtype_perm f h₁) = sign f :=
let l := (trunc_swap_factors (subtype_perm f h₁)).out in
have hl' : ∀ g' ∈ l.1.map of_subtype, is_swap g' :=
  λ g' hg',
  let ⟨g, hg⟩ := list.mem_map.1 hg' in
  hg.2 ▸ (l.2.2 _ hg.1).of_subtype_is_swap,
have hl'₂ : (l.1.map of_subtype).prod = f,
  by rw [l.1.prod_hom of_subtype, l.2.1, of_subtype_subtype_perm _ h₂],
by { conv { congr, rw ← l.2.1, skip, rw ← hl'₂ },
  rw [sign_prod_list_swap l.2.2, sign_prod_list_swap hl', list.length_map] }

@[simp] lemma sign_of_subtype {p : α → Prop} [decidable_pred p]
  (f : perm (subtype p)) : sign (of_subtype f) = sign f :=
have ∀ x, of_subtype f x ≠ x → p x, from λ x, not_imp_comm.1 (of_subtype_apply_of_not_mem f),
by conv {to_rhs, rw [← subtype_perm_of_subtype f, sign_subtype_perm _ _ this]}

lemma sign_eq_sign_of_equiv [decidable_eq β] [fintype β] (f : perm α) (g : perm β)
  (e : α ≃ β) (h : ∀ x, e (f x) = g (e x)) : sign f = sign g :=
have hg : g = (e.symm.trans f).trans e, from equiv.ext $ by simp [h],
by rw [hg, sign_symm_trans_trans]

lemma sign_bij [decidable_eq β] [fintype β]
  {f : perm α} {g : perm β} (i : Π x : α, f x ≠ x → β)
  (h : ∀ x hx hx', i (f x) hx' = g (i x hx))
  (hi : ∀ x₁ x₂ hx₁ hx₂, i x₁ hx₁ = i x₂ hx₂ → x₁ = x₂)
  (hg : ∀ y, g y ≠ y → ∃ x hx, i x hx = y) :
  sign f = sign g :=
calc sign f = sign (@subtype_perm _ f (λ x, f x ≠ x) (by simp)) :
  (sign_subtype_perm _ _ (λ _, id)).symm
... = sign (@subtype_perm _ g (λ x, g x ≠ x) (by simp)) :
  sign_eq_sign_of_equiv _ _
    (equiv.of_bijective (λ x : {x // f x ≠ x},
        (⟨i x.1 x.2, have f (f x) ≠ f x, from mt (λ h, f.injective h) x.2,
          by { rw [← h _ x.2 this], exact mt (hi _ _ this x.2) x.2 }⟩ : {y // g y ≠ y}))
        ⟨λ ⟨x, hx⟩ ⟨y, hy⟩ h, subtype.eq (hi _ _ _ _ (subtype.mk.inj h)),
          λ ⟨y, hy⟩, let ⟨x, hfx, hx⟩ := hg y hy in ⟨⟨x, hfx⟩, subtype.eq hx⟩⟩)
      (λ ⟨x, _⟩, subtype.eq (h x _ _))
... = sign g : sign_subtype_perm _ _ (λ _, id)

@[simp] lemma support_swap {x y : α} (hxy : x ≠ y) : (swap x y).support = {x, y} :=
finset.ext $ λ a, by { simp only [swap_apply_def, mem_insert, ne.def, mem_support, mem_singleton],
  split_ifs; cc }

lemma card_support_swap {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
show (swap x y).support.card = finset.card ⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩,
from congr_arg card $ by simp [support_swap hxy, *, finset.ext_iff]

/-- If we apply `prod_extend_right a (σ a)` for all `a : α` in turn,
we get `prod_congr_right σ`. -/
lemma prod_prod_extend_right {α : Type*} [decidable_eq α] (σ : α → perm β)
  {l : list α} (hl : l.nodup) (mem_l : ∀ a, a ∈ l) :
  (l.map (λ a, prod_extend_right a (σ a))).prod = prod_congr_right σ :=
begin
  ext ⟨a, b⟩ : 1,
  -- We'll use induction on the list of elements,
  -- but we have to keep track of whether we already passed `a` in the list.
  suffices : (a ∈ l ∧ (l.map (λ a, prod_extend_right a (σ a))).prod (a, b) = (a, σ a b)) ∨
             (a ∉ l ∧ (l.map (λ a, prod_extend_right a (σ a))).prod (a, b) = (a, b)),
  { obtain ⟨_, prod_eq⟩ := or.resolve_right this (not_and.mpr (λ h _, h (mem_l a))),
    rw [prod_eq, prod_congr_right_apply] },
  clear mem_l,

  induction l with a' l ih,
  { refine or.inr ⟨list.not_mem_nil _, _⟩,
    rw [list.map_nil, list.prod_nil, one_apply] },

  rw [list.map_cons, list.prod_cons, mul_apply],
  rcases ih (list.nodup_cons.mp hl).2 with ⟨mem_l, prod_eq⟩ | ⟨not_mem_l, prod_eq⟩; rw prod_eq,
  { refine or.inl ⟨list.mem_cons_of_mem _ mem_l, _⟩,
    rw prod_extend_right_apply_ne _ (λ (h : a = a'), (list.nodup_cons.mp hl).1 (h ▸ mem_l)) },
  by_cases ha' : a = a',
  { rw ← ha' at *,
    refine or.inl ⟨l.mem_cons_self a, _⟩,
    rw prod_extend_right_apply_eq },
  { refine or.inr ⟨λ h, not_or ha' not_mem_l ((list.mem_cons_iff _ _ _).mp h), _⟩,
    rw prod_extend_right_apply_ne _ ha' },
end

section congr

variables [decidable_eq β] [fintype β]

@[simp] lemma sign_prod_extend_right (a : α) (σ : perm β) :
  (prod_extend_right a σ).sign = σ.sign :=
sign_bij (λ (ab : α × β) _, ab.snd)
  (λ ⟨a', b⟩ hab hab', by simp [eq_of_prod_extend_right_ne hab])
  (λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h,
    by simpa [eq_of_prod_extend_right_ne hab₁, eq_of_prod_extend_right_ne hab₂] using h)
  (λ y hy, ⟨(a, y), by simpa, by simp⟩)

lemma sign_prod_congr_right (σ : α → perm β) :
  sign (prod_congr_right σ) = ∏ k, (σ k).sign :=
begin
  obtain ⟨l, hl, mem_l⟩ := fintype.exists_univ_list α,
  have l_to_finset : l.to_finset = finset.univ,
  { apply eq_top_iff.mpr,
    intros b _,
    exact list.mem_to_finset.mpr (mem_l b) },
  rw [← prod_prod_extend_right σ hl mem_l, sign.map_list_prod,
      list.map_map, ← l_to_finset, list.prod_to_finset _ hl],
  simp_rw ← λ a, sign_prod_extend_right a (σ a)
end

lemma sign_prod_congr_left (σ : α → perm β) :
  sign (prod_congr_left σ) = ∏ k, (σ k).sign :=
begin
  refine (sign_eq_sign_of_equiv _ _ (prod_comm β α) _).trans (sign_prod_congr_right σ),
  rintro ⟨b, α⟩,
  refl
end

@[simp] lemma sign_perm_congr (e : α ≃ β) (p : perm α) :
  (e.perm_congr p).sign = p.sign :=
sign_eq_sign_of_equiv _ _ e.symm (by simp)

@[simp] lemma sign_sum_congr (σa : perm α) (σb : perm β) :
  (sum_congr σa σb).sign = σa.sign * σb.sign :=
begin
  suffices : (sum_congr σa (1 : perm β)).sign = σa.sign ∧
             (sum_congr (1 : perm α) σb).sign = σb.sign,
  { rw [←this.1, ←this.2, ←sign_mul, sum_congr_mul, one_mul, mul_one], },
  split,
  { apply σa.swap_induction_on _ (λ σa' a₁ a₂ ha ih, _),
    { simp },
    { rw [←one_mul (1 : perm β), ←sum_congr_mul, sign_mul, sign_mul, ih, sum_congr_swap_one,
          sign_swap ha, sign_swap (sum.injective_inl.ne_iff.mpr ha)], }, },
  { apply σb.swap_induction_on _ (λ σb' b₁ b₂ hb ih, _),
    { simp },
    { rw [←one_mul (1 : perm α), ←sum_congr_mul, sign_mul, sign_mul, ih, sum_congr_one_swap,
          sign_swap hb, sign_swap (sum.injective_inr.ne_iff.mpr hb)], }, }
end

end congr

end sign

end equiv.perm
