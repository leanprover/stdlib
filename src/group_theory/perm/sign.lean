/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.fintype.basic
import algebra.big_operators

universes u v
open equiv function fintype finset
variables {α : Type u} {β : Type v}

namespace equiv.perm

def subtype_perm (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) : perm {x // p x} :=
⟨λ x, ⟨f x, (h _).1 x.2⟩, λ x, ⟨f⁻¹ x, (h (f⁻¹ x)).2 $ by simpa using x.2⟩,
  λ _, by simp, λ _, by simp⟩

@[simp] lemma subtype_perm_one (p : α → Prop) (h : ∀ x, p x ↔ p ((1 : perm α) x)) : @subtype_perm α 1 p h = 1 :=
equiv.ext $ λ ⟨_, _⟩, rfl

def of_subtype {p : α → Prop} [decidable_pred p] (f : perm (subtype p)) : perm α :=
⟨λ x, if h : p x then f ⟨x, h⟩ else x, λ x, if h : p x then f⁻¹ ⟨x, h⟩ else x,
  λ x, have h : ∀ h : p x, p (f ⟨x, h⟩), from λ h, (f ⟨x, h⟩).2,
    by simp; split_ifs at *; simp * at *,
  λ x, have h : ∀ h : p x, p (f⁻¹ ⟨x, h⟩), from λ h, (f⁻¹ ⟨x, h⟩).2,
    by simp; split_ifs at *; simp * at *⟩

instance of_subtype.is_group_hom {p : α → Prop} [decidable_pred p] : is_group_hom (@of_subtype α p _) :=
{ map_mul := λ f g, equiv.ext $ λ x, begin
  rw [of_subtype, of_subtype, of_subtype],
  by_cases h : p x,
  { have h₁ : p (f (g ⟨x, h⟩)), from (f (g ⟨x, h⟩)).2,
    have h₂ : p (g ⟨x, h⟩), from (g ⟨x, h⟩).2,
    simp [h, h₁, h₂] },
  { simp [h] }
end }

@[simp] lemma of_subtype_one (p : α → Prop) [decidable_pred p] : @of_subtype α p _ 1 = 1 :=
is_group_hom.map_one of_subtype

lemma eq_inv_iff_eq {f : perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
by conv {to_lhs, rw [← injective.eq_iff f.injective, apply_inv_self]}

lemma inv_eq_iff_eq {f : perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
by rw [eq_comm, eq_inv_iff_eq, eq_comm]

/-- Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def disjoint (f g : perm α) := ∀ x, f x = x ∨ g x = x

@[symm] lemma disjoint.symm {f g : perm α} : disjoint f g → disjoint g f :=
by simp [disjoint, or.comm]

lemma disjoint_comm {f g : perm α} : disjoint f g ↔ disjoint g f :=
⟨disjoint.symm, disjoint.symm⟩

lemma disjoint_mul_comm {f g : perm α} (h : disjoint f g) : f * g = g * f :=
equiv.ext $ λ x, (h x).elim
  (λ hf, (h (g x)).elim (λ hg, by simp [mul_apply, hf, hg])
    (λ hg, by simp [mul_apply, hf, g.injective hg]))
  (λ hg, (h (f x)).elim (λ hf, by simp [mul_apply, f.injective hf, hg])
    (λ hf, by simp [mul_apply, hf, hg]))

@[simp] lemma disjoint_one_left (f : perm α) : disjoint 1 f := λ _, or.inl rfl

@[simp] lemma disjoint_one_right (f : perm α) : disjoint f 1 := λ _, or.inr rfl

lemma disjoint_mul_left {f g h : perm α} (H1 : disjoint f h) (H2 : disjoint g h) :
  disjoint (f * g) h :=
λ x, by cases H1 x; cases H2 x; simp *

lemma disjoint_mul_right {f g h : perm α} (H1 : disjoint f g) (H2 : disjoint f h) :
  disjoint f (g * h) :=
by rw disjoint_comm; exact disjoint_mul_left H1.symm H2.symm

lemma disjoint_prod_right {f : perm α} (l : list (perm α))
  (h : ∀ g ∈ l, disjoint f g) : disjoint f l.prod :=
begin
  induction l with g l ih,
  { exact disjoint_one_right _ },
  { rw list.prod_cons;
    exact disjoint_mul_right (h _ (list.mem_cons_self _ _))
      (ih (λ g hg, h g (list.mem_cons_of_mem _ hg))) }
end

lemma disjoint_prod_perm {l₁ l₂ : list (perm α)} (hl : l₁.pairwise disjoint)
  (hp : l₁ ~ l₂) : l₁.prod = l₂.prod :=
hp.prod_eq' $ hl.imp $ λ f g, disjoint_mul_comm

lemma of_subtype_subtype_perm {f : perm α} {p : α → Prop} [decidable_pred p] (h₁ : ∀ x, p x ↔ p (f x))
  (h₂ : ∀ x, f x ≠ x → p x) : of_subtype (subtype_perm f h₁) = f :=
equiv.ext $ λ x, begin
  rw [of_subtype, subtype_perm],
  by_cases hx : p x,
  { simp [hx] },
  { haveI := classical.prop_decidable,
    simp [hx, not_not.1 (mt (h₂ x) hx)] }
end

lemma of_subtype_apply_of_not_mem {p : α → Prop} [decidable_pred p] (f : perm (subtype p)) {x : α} (hx : ¬ p x) :
  of_subtype f x = x := dif_neg hx

lemma mem_iff_of_subtype_apply_mem {p : α → Prop} [decidable_pred p] (f : perm (subtype p)) (x : α) :
  p x ↔ p ((of_subtype f : α → α) x) :=
if h : p x then by dsimp [of_subtype]; simpa [h] using (f ⟨x, h⟩).2
else by simp [h, of_subtype_apply_of_not_mem f h]

@[simp] lemma subtype_perm_of_subtype {p : α → Prop} [decidable_pred p] (f : perm (subtype p)) :
  subtype_perm (of_subtype f) (mem_iff_of_subtype_apply_mem f) = f :=
equiv.ext $ λ ⟨x, hx⟩, by dsimp [subtype_perm, of_subtype]; simp [show p x, from hx]

lemma pow_apply_eq_self_of_apply_eq_self {f : perm α} {x : α} (hfx : f x = x) :
  ∀ n : ℕ, (f ^ n) x = x
| 0     := rfl
| (n+1) := by rw [pow_succ', mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self]

lemma gpow_apply_eq_self_of_apply_eq_self {f : perm α} {x : α} (hfx : f x = x) :
  ∀ n : ℤ, (f ^ n) x = x
| (n : ℕ) := pow_apply_eq_self_of_apply_eq_self hfx n
| -[1+ n] := by rw [gpow_neg_succ, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]

lemma pow_apply_eq_of_apply_apply_eq_self {f : perm α} {x : α} (hffx : f (f x) = x) :
  ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
| 0     := or.inl rfl
| (n+1) := (pow_apply_eq_of_apply_apply_eq_self n).elim
  (λ h, or.inr (by rw [pow_succ, mul_apply, h]))
  (λ h, or.inl (by rw [pow_succ, mul_apply, h, hffx]))

lemma gpow_apply_eq_of_apply_apply_eq_self {f : perm α} {x : α} (hffx : f (f x) = x) :
  ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
| (n : ℕ) := pow_apply_eq_of_apply_apply_eq_self hffx n
| -[1+ n] :=
  by rw [gpow_neg_succ, inv_eq_iff_eq, ← injective.eq_iff f.injective, ← mul_apply, ← pow_succ,
    eq_comm, inv_eq_iff_eq, ← mul_apply, ← pow_succ', @eq_comm _ x, or.comm];
  exact pow_apply_eq_of_apply_apply_eq_self hffx _

variable [decidable_eq α]

def support [fintype α] (f : perm α) := univ.filter (λ x, f x ≠ x)

@[simp] lemma mem_support [fintype α] {f : perm α} {x : α} : x ∈ f.support ↔ f x ≠ x :=
by simp [support]

def is_swap (f : perm α) := ∃ x y, x ≠ y ∧ f = swap x y

lemma swap_mul_eq_mul_swap (f : perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
equiv.ext $ λ z, begin
  simp [mul_apply, swap_apply_def],
  split_ifs;
  simp [*, eq_inv_iff_eq] at * <|> cc
end

lemma mul_swap_eq_swap_mul (f : perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f :=
by rw [swap_mul_eq_mul_swap, inv_apply_self, inv_apply_self]

/-- Multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
lemma swap_mul_self_mul (i j : α) (σ : perm α) : equiv.swap i j * (equiv.swap i j * σ) = σ :=
by rw [←mul_assoc (swap i j) (swap i j) σ, equiv.swap_mul_self, one_mul]

lemma swap_mul_eq_iff {i j : α} {σ : perm α} : swap i j * σ = σ ↔ i = j :=
⟨(assume h, have swap_id : swap i j = 1 := mul_right_cancel (trans h (one_mul σ).symm),
  by {rw [←swap_apply_right i j, swap_id], refl}),
(assume h, by erw [h, swap_self, one_mul])⟩

lemma is_swap_of_subtype {p : α → Prop} [decidable_pred p]
  {f : perm (subtype p)} (h : is_swap f) : is_swap (of_subtype f) :=
let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h in
⟨x, y, by simp at hxy; tauto,
  equiv.ext $ λ z, begin
    rw [hxy.2, of_subtype],
    simp [swap_apply_def],
    split_ifs;
    cc <|> simp * at *
  end⟩

lemma ne_and_ne_of_swap_mul_apply_ne_self {f : perm α} {x y : α}
  (hy : (swap x (f x) * f) y ≠ y) : f y ≠ y ∧ y ≠ x :=
begin
  simp only [swap_apply_def, mul_apply, injective.eq_iff f.injective] at *,
  by_cases h : f y = x,
  { split; intro; simp * at * },
  { split_ifs at hy; cc }
end

lemma support_swap_mul_eq [fintype α] {f : perm α} {x : α}
  (hffx : f (f x) ≠ x) : (swap x (f x) * f).support = f.support.erase x :=
have hfx : f x ≠ x, from λ hfx, by simpa [hfx] using hffx,
finset.ext.2 $ λ y,
⟨λ hy, have hy' : (swap x (f x) * f) y ≠ y, from mem_support.1 hy,
    mem_erase.2 ⟨λ hyx, by simp [hyx, mul_apply, *] at *,
    mem_support.2 $ λ hfy,
      by simp only [mul_apply, swap_apply_def, hfy] at hy';
      split_ifs at hy'; simp * at *⟩,
  λ hy, by simp only [mem_erase, mem_support, swap_apply_def, mul_apply] at *;
    intro; split_ifs at *; simp * at *⟩

lemma card_support_swap_mul [fintype α] {f : perm α} {x : α}
  (hx : f x ≠ x) : (swap x (f x) * f).support.card < f.support.card :=
finset.card_lt_card
  ⟨λ z hz, mem_support.2 (ne_and_ne_of_swap_mul_apply_ne_self (mem_support.1 hz)).1,
    λ h, absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

def swap_factors_aux : Π (l : list α) (f : perm α), (∀ {x}, f x ≠ x → x ∈ l) →
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g}
| []       := λ f h, ⟨[], equiv.ext $ λ x, by rw [list.prod_nil];
    exact eq.symm (not_not.1 (mt h (list.not_mem_nil _))), by simp⟩
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
For types without linear order `trunc_swap_factors` can be used -/
def swap_factors [fintype α] [decidable_linear_order α] (f : perm α) :
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
swap_factors_aux ((@univ α _).sort (≤)) f (λ _ _, (mem_sort _).2 (mem_univ _))

def trunc_swap_factors [fintype α] (f : perm α) :
  trunc {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
quotient.rec_on_subsingleton (@univ α _).1
(λ l h, trunc.mk (swap_factors_aux l f h))
(show ∀ x, f x ≠ x → x ∈ (@univ α _).1, from λ _ _, mem_univ _)

@[elab_as_eliminator] lemma swap_induction_on [fintype α] {P : perm α → Prop} (f : perm α) :
  P 1 → (∀ f x y, x ≠ y → P f → P (swap x y * f)) → P f :=
begin
  cases trunc.out (trunc_swap_factors f) with l hl,
  induction l with g l ih generalizing f,
  { simp [hl.1.symm] {contextual := tt} },
  { assume h1 hmul_swap,
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩,
    rw [← hl.1, list.prod_cons, hxy.2],
    exact hmul_swap _ _ _ hxy.1 (ih _ ⟨rfl, λ v hv, hl.2 _ (list.mem_cons_of_mem _ hv)⟩ h1 hmul_swap) }
end

lemma swap_mul_swap_mul_swap {x y z : α} (hwz: x ≠ y) (hxz : x ≠ z) :
  swap y z * swap x y * swap y z = swap z x :=
equiv.ext $ λ n, by simp only [swap_apply_def, mul_apply]; split_ifs; cc

lemma is_conj_swap {w x y z : α} (hwx : w ≠ x) (hyz : y ≠ z) : is_conj (swap w x) (swap y z) :=
have h : ∀ {y z : α}, y ≠ z → w ≠ z →
    (swap w y * swap x z) * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
  λ y z hyz hwz, by rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc (swap w y),
    mul_assoc (swap w y),  ← mul_assoc _ (swap x z), swap_mul_swap_mul_swap hwx hwz,
    ← mul_assoc, swap_mul_swap_mul_swap hwz.symm hyz.symm],
if hwz : w = z
then have hwy : w ≠ y, by cc,
  ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
else ⟨swap w y * swap x z, h hyz hwz⟩

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
def fin_pairs_lt (n : ℕ) : finset (Σ a : fin n, fin n) :=
(univ : finset (fin n)).sigma (λ a, (range a.1).attach_fin
  (λ m hm, lt_trans (mem_range.1 hm) a.2))

lemma mem_fin_pairs_lt {n : ℕ} {a : Σ a : fin n, fin n} :
  a ∈ fin_pairs_lt n ↔ a.2 < a.1 :=
by simp [fin_pairs_lt, fin.lt_def]

def sign_aux {n : ℕ} (a : perm (fin n)) : units ℤ :=
(fin_pairs_lt n).prod (λ x, if a x.1 ≤ a x.2 then -1 else 1)

@[simp] lemma sign_aux_one (n : ℕ) : sign_aux (1 : perm (fin n)) = 1 :=
begin
  unfold sign_aux,
  conv { to_rhs, rw ← @finset.prod_const_one _ (units ℤ)
    (fin_pairs_lt n) },
  exact finset.prod_congr rfl (λ a ha, if_neg
    (not_le_of_gt (mem_fin_pairs_lt.1 ha)))
end

def sign_bij_aux {n : ℕ} (f : perm (fin n)) (a : Σ a : fin n, fin n) :
  Σ a : fin n, fin n :=
if hxa : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩

lemma sign_bij_aux_inj {n : ℕ} {f : perm (fin n)} : ∀ a b : Σ a : fin n, fin n,
   a ∈ fin_pairs_lt n → b ∈ fin_pairs_lt n →
   sign_bij_aux f a = sign_bij_aux f b → a = b :=
λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h, begin
  unfold sign_bij_aux at h,
  rw mem_fin_pairs_lt at *,
  have : ¬b₁ < b₂ := not_lt_of_ge (le_of_lt hb),
  split_ifs at h;
  simp [*, injective.eq_iff f.injective, sigma.mk.inj_eq] at *
end

lemma sign_bij_aux_surj {n : ℕ} {f : perm (fin n)} : ∀ a ∈ fin_pairs_lt n,
  ∃ b ∈ fin_pairs_lt n, a = sign_bij_aux f b :=
λ ⟨a₁, a₂⟩ ha,
if hxa : f⁻¹ a₂ < f⁻¹ a₁
then ⟨⟨f⁻¹ a₁, f⁻¹ a₂⟩, mem_fin_pairs_lt.2 hxa,
  by dsimp [sign_bij_aux];
    rw [apply_inv_self, apply_inv_self, dif_pos (mem_fin_pairs_lt.1 ha)]⟩
else ⟨⟨f⁻¹ a₂, f⁻¹ a₁⟩, mem_fin_pairs_lt.2 $ lt_of_le_of_ne
  (le_of_not_gt hxa) $ λ h,
    by simpa [mem_fin_pairs_lt, (f⁻¹).injective h, lt_irrefl] using ha,
  by dsimp [sign_bij_aux];
    rw [apply_inv_self, apply_inv_self,
      dif_neg (not_lt_of_ge (le_of_lt (mem_fin_pairs_lt.1 ha)))]⟩

lemma sign_bij_aux_mem {n : ℕ} {f : perm (fin n)}: ∀ a : Σ a : fin n, fin n,
  a ∈ fin_pairs_lt n → sign_bij_aux f a ∈ fin_pairs_lt n :=
λ ⟨a₁, a₂⟩ ha, begin
  unfold sign_bij_aux,
  split_ifs with h,
  { exact mem_fin_pairs_lt.2 h },
  { exact mem_fin_pairs_lt.2
    (lt_of_le_of_ne (le_of_not_gt h)
      (λ h, ne_of_lt (mem_fin_pairs_lt.1 ha) (f.injective h.symm))) }
end

@[simp] lemma sign_aux_inv {n : ℕ} (f : perm (fin n)) : sign_aux f⁻¹ = sign_aux f :=
prod_bij (λ a ha, sign_bij_aux f⁻¹ a)
sign_bij_aux_mem
(λ ⟨a, b⟩ hab, if h : f⁻¹ b < f⁻¹ a
  then by rw [sign_bij_aux, dif_pos h, if_neg (not_le_of_gt h), apply_inv_self,
    apply_inv_self, if_neg (not_le_of_gt $ mem_fin_pairs_lt.1 hab)]
  else by rw [sign_bij_aux, if_pos (le_of_not_gt h), dif_neg h, apply_inv_self,
    apply_inv_self, if_pos (le_of_lt $ mem_fin_pairs_lt.1 hab)])
sign_bij_aux_inj
sign_bij_aux_surj

lemma sign_aux_mul {n : ℕ} (f g : perm (fin n)) :
  sign_aux (f * g) = sign_aux f * sign_aux g :=
begin
  rw ← sign_aux_inv g,
  unfold sign_aux,
  rw  ← prod_mul_distrib,
  refine prod_bij (λ a ha, sign_bij_aux g a) sign_bij_aux_mem _
    sign_bij_aux_inj sign_bij_aux_surj,
  rintros ⟨a, b⟩ hab,
  rw [sign_bij_aux, mul_apply, mul_apply],
  rw mem_fin_pairs_lt at hab,
  by_cases h : g b < g a,
  { rw dif_pos h,
    simp [not_le_of_gt hab]; congr },
  { rw [dif_neg h, inv_apply_self, inv_apply_self, if_pos (le_of_lt hab)],
    by_cases h₁ : f (g b) ≤ f (g a),
    { have : f (g b) ≠ f (g a),
      { rw [ne.def, injective.eq_iff f.injective,
          injective.eq_iff g.injective];
        exact ne_of_lt hab },
      rw [if_pos h₁, if_neg (not_le_of_gt  (lt_of_le_of_ne h₁ this))],
      refl },
    { rw [if_neg h₁, if_pos (le_of_lt (lt_of_not_ge h₁))],
      refl } }
end

instance sign_aux.is_group_hom {n : ℕ} : is_group_hom (@sign_aux n) := { map_mul := sign_aux_mul }

private lemma sign_aux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
  sign_aux (swap (⟨0, lt_of_lt_of_le dec_trivial hn⟩ : fin n)
  ⟨1, lt_of_lt_of_le dec_trivial hn⟩) = -1 :=
let zero : fin n := ⟨0, lt_of_lt_of_le dec_trivial hn⟩ in
let one : fin n := ⟨1, lt_of_lt_of_le dec_trivial hn⟩ in
have hzo : zero < one := dec_trivial,
show _ = ({(⟨one, zero⟩ : Σ a : fin n, fin n)} : finset _).prod
  (λ x : Σ a : fin n, fin n, if (equiv.swap zero one) x.1
  ≤ swap zero one x.2 then (-1 : units ℤ) else 1),
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
  simp [*, lt_irrefl, -not_lt, not_le.symm, -not_le, le_refl, fin.lt_def, fin.le_def, nat.zero_le,
    zero, one, iff.intro fin.veq_of_eq fin.eq_of_veq, nat.le_zero_iff] at *,
end

lemma sign_aux_swap : ∀ {n : ℕ} {x y : fin n} (hxy : x ≠ y),
  sign_aux (swap x y) = -1
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ x y hxy,
have h2n : 2 ≤ n + 2 := dec_trivial,
by rw [← is_conj_iff_eq, ← sign_aux_swap_zero_one h2n];
  exact (monoid_hom.of sign_aux).map_is_conj (is_conj_swap hxy dec_trivial)

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
  { have hy : ∀ y : α, (swap x (f x) * f) y ≠ y → y ∈ l,
      from λ y hy, have f y ≠ y ∧ y ≠ x, from ne_and_ne_of_swap_mul_apply_ne_self hy,
      list.mem_of_ne_of_mem this.2 (h _ this.1),
    have : (e.symm.trans (swap x (f x) * f)).trans e =
      (swap (e x) (e (f x))) * (e.symm.trans f).trans e,
      by ext; simp [← equiv.symm_trans_swap_trans, mul_def],
    have hefx : e x ≠ e (f x), from mt (injective.eq_iff e.injective).1 hfx,
    rw [if_neg hfx, ← sign_aux_eq_sign_aux2 _ _ e hy, this, sign_aux_mul, sign_aux_swap hefx],
    simp }
end

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
let ⟨e, _⟩ := trunc.exists_rep (equiv_fin α) in
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
    have hexy : e x ≠ e y, from mt (injective.eq_iff e.injective).1 hxy,
    rw [← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _), equiv.symm_trans_swap_trans, sign_aux_swap hexy] }
end

/-- `sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`perm α` to the group with two elements.-/
def sign [fintype α] (f : perm α) := sign_aux3 f mem_univ

instance sign.is_group_hom [fintype α] : is_group_hom (@sign α _ _) :=
{ map_mul := λ f g, (sign_aux3_mul_and_swap f g _ mem_univ).1 }

section sign

variable [fintype α]

@[simp] lemma sign_mul (f g : perm α) : sign (f * g) = sign f * sign g :=
is_mul_hom.map_mul sign _ _

@[simp] lemma sign_one : (sign (1 : perm α)) = 1 :=
is_group_hom.map_one sign

@[simp] lemma sign_refl : sign (equiv.refl α) = 1 :=
show sign 1 = 1, by exact is_group_hom.map_one sign

@[simp] lemma sign_inv (f : perm α) : sign f⁻¹ = sign f :=
by rw [is_group_hom.map_inv sign, int.units_inv_eq_self]; apply_instance

lemma sign_swap {x y : α} (h : x ≠ y) : sign (swap x y) = -1 :=
(sign_aux3_mul_and_swap 1 1 _ mem_univ).2 x y h

@[simp] lemma sign_swap' {x y : α} :
  (swap x y).sign = if x = y then 1 else -1 :=
if H : x = y then by simp [H, swap_self] else
by simp [sign_swap H, H]

lemma sign_eq_of_is_swap {f : perm α} (h : is_swap f) : sign f = -1 :=
let ⟨x, y, hxy⟩ := h in hxy.2.symm ▸ sign_swap hxy.1

lemma sign_aux3_symm_trans_trans [decidable_eq β] [fintype β] (f : perm α)
  (e : α ≃ β) {s : multiset α} {t : multiset β} (hs : ∀ x, x ∈ s) (ht : ∀ x, x ∈ t) :
  sign_aux3 ((e.symm.trans f).trans e) ht = sign_aux3 f hs :=
quotient.induction_on₂ t s
  (λ l₁ l₂ h₁ h₂, show sign_aux2 _ _ = sign_aux2 _ _,
    from let n := trunc.out (equiv_fin β) in
    by rw [← sign_aux_eq_sign_aux2 _ _ n (λ _ _, h₁ _),
        ← sign_aux_eq_sign_aux2 _ _ (e.trans n) (λ _ _, h₂ _)];
      exact congr_arg sign_aux (equiv.ext (λ x, by simp)))
  ht hs

lemma sign_symm_trans_trans [decidable_eq β] [fintype β] (f : perm α)
  (e : α ≃ β) : sign ((e.symm.trans f).trans e) = sign f :=
sign_aux3_symm_trans_trans f e mem_univ mem_univ

lemma sign_prod_list_swap {l : list (perm α)}
  (hl : ∀ g ∈ l, is_swap g) : sign l.prod = -1 ^ l.length :=
have h₁ : l.map sign = list.repeat (-1) l.length :=
  list.eq_repeat.2 ⟨by simp, λ u hu,
  let ⟨g, hg⟩ := list.mem_map.1 hu in
  hg.2 ▸ sign_eq_of_is_swap (hl _ hg.1)⟩,
by rw [← list.prod_repeat, ← h₁, list.prod_hom _ (@sign α _ _)]

lemma sign_surjective (hα : 1 < fintype.card α) : function.surjective (sign : perm α → units ℤ) :=
λ a, (int.units_eq_one_or a).elim
  (λ h, ⟨1, by simp [h]⟩)
  (λ h, let ⟨x⟩ := fintype.card_pos_iff.1 (lt_trans zero_lt_one hα) in
    let ⟨y, hxy⟩ := fintype.exists_ne_of_one_lt_card hα x in
    ⟨swap y x, by rw [sign_swap hxy, h]⟩ )

lemma eq_sign_of_surjective_hom {s : perm α → units ℤ}
  [is_group_hom s] (hs : surjective s) : s = sign :=
have ∀ {f}, is_swap f → s f = -1 :=
  λ f ⟨x, y, hxy, hxy'⟩, hxy'.symm ▸ by_contradiction (λ h,
    have ∀ f, is_swap f → s f = 1 := λ f ⟨a, b, hab, hab'⟩,
      by rw [← is_conj_iff_eq, ← or.resolve_right (int.units_eq_one_or _) h, hab'];
        exact (monoid_hom.of s).map_is_conj (is_conj_swap hab hxy),
  let ⟨g, hg⟩ := hs (-1) in
  let ⟨l, hl⟩ := trunc.out (trunc_swap_factors g) in
  have ∀ a ∈ l.map s, a = (1 : units ℤ) := λ a ha,
    let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸ this _ (hl.2 _ hg.1),
  have s l.prod = 1,
    by rw [← l.prod_hom s, list.eq_repeat'.2 this, list.prod_repeat, one_pow],
  by rw [hl.1, hg] at this;
    exact absurd this dec_trivial),
funext $ λ f,
let ⟨l, hl₁, hl₂⟩ := trunc.out (trunc_swap_factors f) in
have hsl : ∀ a ∈ l.map s, a = (-1 : units ℤ) := λ a ha,
  let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸  this (hl₂ _ hg.1),
by rw [← hl₁, ← l.prod_hom s, list.eq_repeat'.2 hsl, list.length_map,
     list.prod_repeat, sign_prod_list_swap hl₂]

lemma sign_subtype_perm (f : perm α) {p : α → Prop} [decidable_pred p]
  (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) : sign (subtype_perm f h₁) = sign f :=
let l := trunc.out (trunc_swap_factors (subtype_perm f h₁)) in
have hl' : ∀ g' ∈ l.1.map of_subtype, is_swap g' :=
  λ g' hg',
  let ⟨g, hg⟩ := list.mem_map.1 hg' in
  hg.2 ▸ is_swap_of_subtype (l.2.2 _ hg.1),
have hl'₂ : (l.1.map of_subtype).prod = f,
  by rw [l.1.prod_hom of_subtype, l.2.1, of_subtype_subtype_perm _ h₂],
by conv {congr, rw ← l.2.1, skip, rw ← hl'₂};
  rw [sign_prod_list_swap l.2.2, sign_prod_list_swap hl', list.length_map]

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
  eq.symm (sign_subtype_perm _ _ (λ _, id))
... = sign (@subtype_perm _ g (λ x, g x ≠ x) (by simp)) :
  sign_eq_sign_of_equiv _ _
    (equiv.of_bijective
      (show function.bijective (λ x : {x // f x ≠ x},
        (⟨i x.1 x.2, have f (f x) ≠ f x, from mt (λ h, f.injective h) x.2,
          by rw [← h _ x.2 this]; exact mt (hi _ _ this x.2) x.2⟩ : {y // g y ≠ y})),
        from ⟨λ ⟨x, hx⟩ ⟨y, hy⟩ h, subtype.eq (hi _ _ _ _ (subtype.mk.inj h)),
          λ ⟨y, hy⟩, let ⟨x, hfx, hx⟩ := hg y hy in ⟨⟨x, hfx⟩, subtype.eq hx⟩⟩))
      (λ ⟨x, _⟩, subtype.eq (h x _ _))
... = sign g : sign_subtype_perm _ _ (λ _, id)

def is_cycle (f : perm β) := ∃ x, f x ≠ x ∧ ∀ y, f y ≠ y → ∃ i : ℤ, (f ^ i) x = y

lemma is_cycle_swap {x y : α} (hxy : x ≠ y) : is_cycle (swap x y) :=
⟨y, by rwa swap_apply_right,
  λ a (ha : ite (a = x) y (ite (a = y) x a) ≠ a),
    if hya : y = a then ⟨0, hya⟩
    else ⟨1, by rw [gpow_one, swap_apply_def]; split_ifs at *; cc⟩⟩

lemma is_cycle_inv {f : perm β} (hf : is_cycle f) : is_cycle (f⁻¹) :=
let ⟨x, hx⟩ := hf in
⟨x, by simp [eq_inv_iff_eq, inv_eq_iff_eq, *] at *; cc,
  λ y hy, let ⟨i, hi⟩ := hx.2 y (by simp [eq_inv_iff_eq, inv_eq_iff_eq, *] at *; cc) in
    ⟨-i, by rwa [gpow_neg, inv_gpow, inv_inv]⟩⟩

lemma exists_gpow_eq_of_is_cycle {f : perm β} (hf : is_cycle f) {x y : β}
  (hx : f x ≠ x) (hy : f y ≠ y) : ∃ i : ℤ, (f ^ i) x = y :=
let ⟨g, hg⟩ := hf in
let ⟨a, ha⟩ := hg.2 x hx in
let ⟨b, hb⟩ := hg.2 y hy in
⟨b - a, by rw [← ha, ← mul_apply, ← gpow_add, sub_add_cancel, hb]⟩

lemma is_cycle_swap_mul_aux₁ : ∀ (n : ℕ) {b x : α} {f : perm α}
  (hb : (swap x (f x) * f) b ≠ b) (h : (f ^ n) (f x) = b),
  ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
| 0         := λ b x f hb h, ⟨0, h⟩
| (n+1 : ℕ) := λ b x f hb h,
  if hfbx : f x = b then ⟨0, hfbx⟩
  else
    have f b ≠ b ∧ b ≠ x, from ne_and_ne_of_swap_mul_apply_ne_self hb,
    have hb' : (swap x (f x) * f) (f⁻¹ b) ≠ f⁻¹ b,
      by rw [mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (ne.symm hfbx),
          ne.def, ← injective.eq_iff f.injective, apply_inv_self];
        exact this.1,
    let ⟨i, hi⟩ := is_cycle_swap_mul_aux₁ n hb'
      (f.injective $
        by rw [apply_inv_self];
        rwa [pow_succ, mul_apply] at h) in
    ⟨i + 1, by rw [add_comm, gpow_add, mul_apply, hi, gpow_one, mul_apply, apply_inv_self,
        swap_apply_of_ne_of_ne (ne_and_ne_of_swap_mul_apply_ne_self hb).2 (ne.symm hfbx)]⟩

lemma is_cycle_swap_mul_aux₂ : ∀ (n : ℤ) {b x : α} {f : perm α}
  (hb : (swap x (f x) * f) b ≠ b) (h : (f ^ n) (f x) = b),
  ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
| (n : ℕ) := λ b x f, is_cycle_swap_mul_aux₁ n
| -[1+ n] := λ b x f hb h,
  if hfbx : f⁻¹ x = b then ⟨-1, by rwa [gpow_neg, gpow_one, mul_inv_rev, mul_apply, swap_inv, swap_apply_right]⟩
  else if hfbx' : f x = b then ⟨0, hfbx'⟩
  else
  have f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb,
  have hb : (swap x (f⁻¹ x) * f⁻¹) (f⁻¹ b) ≠ f⁻¹ b,
    by rw [mul_apply, swap_apply_def];
      split_ifs;
      simp [inv_eq_iff_eq, eq_inv_iff_eq] at *; cc,
  let ⟨i, hi⟩ := is_cycle_swap_mul_aux₁ n hb
    (show (f⁻¹ ^ n) (f⁻¹ x) = f⁻¹ b, by
      rw [← gpow_coe_nat, ← h, ← mul_apply, ← mul_apply, ← mul_apply, gpow_neg_succ, ← inv_pow, pow_succ', mul_assoc,
        mul_assoc, inv_mul_self, mul_one, gpow_coe_nat, ← pow_succ', ← pow_succ]) in
  have h : (swap x (f⁻¹ x) * f⁻¹) (f x) = f⁻¹ x, by rw [mul_apply, inv_apply_self, swap_apply_left],
  ⟨-i, by rw [← add_sub_cancel i 1, neg_sub, sub_eq_add_neg, gpow_add, gpow_one, gpow_neg, ← inv_gpow,
      mul_inv_rev, swap_inv, mul_swap_eq_swap_mul, inv_apply_self, swap_comm _ x, gpow_add, gpow_one,
      mul_apply, mul_apply (_ ^ i), h, hi, mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (ne.symm hfbx')]⟩

lemma eq_swap_of_is_cycle_of_apply_apply_eq_self {f : perm α} (hf : is_cycle f) {x : α}
  (hfx : f x ≠ x) (hffx : f (f x) = x) : f = swap x (f x) :=
equiv.ext $ λ y,
let ⟨z, hz⟩ := hf in
let ⟨i, hi⟩ := hz.2 x hfx in
if hyx : y = x then by simp [hyx]
else if hfyx : y = f x then by simp [hfyx, hffx]
else begin
  rw [swap_apply_of_ne_of_ne hyx hfyx],
  refine by_contradiction (λ hy, _),
  cases hz.2 y hy with j hj,
  rw [← sub_add_cancel j i, gpow_add, mul_apply, hi] at hj,
  cases gpow_apply_eq_of_apply_apply_eq_self hffx (j - i) with hji hji,
  { rw [← hj, hji] at hyx, cc },
  { rw [← hj, hji] at hfyx, cc }
end

lemma is_cycle_swap_mul {f : perm α} (hf : is_cycle f) {x : α}
  (hx : f x ≠ x) (hffx : f (f x) ≠ x) : is_cycle (swap x (f x) * f) :=
⟨f x, by simp only [swap_apply_def, mul_apply];
        split_ifs; simp [injective.eq_iff f.injective] at *; cc,
  λ y hy,
  let ⟨i, hi⟩ := exists_gpow_eq_of_is_cycle hf hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1 in
  have hi : (f ^ (i - 1)) (f x) = y, from
    calc (f ^ (i - 1)) (f x) = (f ^ (i - 1) * f ^ (1 : ℤ)) x : by rw [gpow_one, mul_apply]
    ... =  y : by rwa [← gpow_add, sub_add_cancel],
  is_cycle_swap_mul_aux₂ (i - 1) hy hi⟩

@[simp] lemma support_swap [fintype α] {x y : α} (hxy : x ≠ y) : (swap x y).support = {x, y} :=
finset.ext.2 $ λ a, by simp [swap_apply_def]; split_ifs; cc

lemma card_support_swap [fintype α] {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
show (swap x y).support.card = finset.card ⟨x::y::0, by simp [hxy]⟩,
from congr_arg card $ by rw [support_swap hxy]; simp [*, finset.ext]; cc

lemma sign_cycle [fintype α] : ∀ {f : perm α} (hf : is_cycle f),
  sign f = -(-1 ^ f.support.card)
| f := λ hf,
let ⟨x, hx⟩ := hf in
calc sign f = sign (swap x (f x) * (swap x (f x) * f)) :
  by rw [← mul_assoc, mul_def, mul_def, swap_swap, trans_refl]
... = -(-1 ^ f.support.card) :
  if h1 : f (f x) = x
  then
    have h : swap x (f x) * f = 1,
      begin
        rw eq_swap_of_is_cycle_of_apply_apply_eq_self hf hx.1 h1,
        simp [mul_def, one_def]
      end,
    by rw [sign_mul, sign_swap hx.1.symm, h, sign_one, eq_swap_of_is_cycle_of_apply_apply_eq_self hf hx.1 h1,
        card_support_swap hx.1.symm]; refl
  else
    have h : card (support (swap x (f x) * f)) + 1 = card (support f),
      by rw [← insert_erase (mem_support.2 hx.1), support_swap_mul_eq h1,
        card_insert_of_not_mem (not_mem_erase _ _)],
    have wf : card (support (swap x (f x) * f)) < card (support f),
      from card_support_swap_mul hx.1,
    by rw [sign_mul, sign_swap hx.1.symm, sign_cycle (is_cycle_swap_mul hf hx.1 h1), ← h];
      simp [pow_add]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ f, f.support.card)⟩]}

end sign

end equiv.perm
