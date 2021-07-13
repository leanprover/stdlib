/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
import data.finset.sort
import data.fintype.basic
import group_theory.perm.basic

/-!
# Support of a permutation

## Main definitions

In the following, `f g : equiv.perm α`.

* `equiv.perm.disjoint`: two permutations `f` and `g` are `disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `disjoint` iff their `support` are disjoint.
* `equiv.perm.is_swap`: `f = swap x y` for `x ≠ y`.
* `equiv.perm.support`: the elements `x : α` that are not fixed by `f`.

-/

open equiv finset

namespace equiv.perm

variables {α : Type*}
section disjoint

/-- Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def disjoint (f g : perm α) := ∀ x, f x = x ∨ g x = x

variables {f g h : perm α}

@[symm] lemma disjoint.symm : disjoint f g → disjoint g f :=
by simp only [disjoint, or.comm, imp_self]

lemma disjoint.symmetric : symmetric (@disjoint α) :=
λ _ _, disjoint.symm

lemma disjoint_comm : disjoint f g ↔ disjoint g f :=
⟨disjoint.symm, disjoint.symm⟩

lemma disjoint.commute (h : disjoint f g) : commute f g :=
equiv.ext $ λ x, (h x).elim
  (λ hf, (h (g x)).elim (λ hg, by simp [mul_apply, hf, hg])
    (λ hg, by simp [mul_apply, hf, g.injective hg]))
  (λ hg, (h (f x)).elim (λ hf, by simp [mul_apply, f.injective hf, hg])
    (λ hf, by simp [mul_apply, hf, hg]))

@[simp] lemma disjoint_one_left (f : perm α) : disjoint 1 f := λ _, or.inl rfl

@[simp] lemma disjoint_one_right (f : perm α) : disjoint f 1 := λ _, or.inr rfl

lemma disjoint_iff_eq_or_eq : disjoint f g ↔ ∀ (x : α), f x = x ∨ g x = x := iff.rfl

@[simp] lemma disjoint_refl_iff : disjoint f f ↔ f = 1 :=
begin
  refine ⟨λ h, _, λ h, h.symm ▸ disjoint_one_left 1⟩,
  ext x,
  cases h x with hx hx;
  simp [hx]
end

lemma disjoint.inv_left (h : disjoint f g) : disjoint f⁻¹ g :=
begin
  intro x,
  rw [inv_eq_iff_eq, eq_comm],
  exact h x
end

lemma disjoint.inv_right (h : disjoint f g) : disjoint f g⁻¹ :=
h.symm.inv_left.symm

@[simp] lemma disjoint_inv_left_iff : disjoint f⁻¹ g ↔  disjoint f g :=
begin
  refine ⟨λ h, _, disjoint.inv_left⟩,
  convert h.inv_left,
  exact (inv_inv _).symm
end

@[simp] lemma disjoint_inv_right_iff : disjoint f g⁻¹ ↔ disjoint f g :=
by rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]

lemma disjoint.mul_left (H1 : disjoint f h) (H2 : disjoint g h) :
  disjoint (f * g) h :=
λ x, by cases H1 x; cases H2 x; simp *

lemma disjoint.mul_right (H1 : disjoint f g) (H2 : disjoint f h) :
  disjoint f (g * h) :=
by { rw disjoint_comm, exact H1.symm.mul_left H2.symm }

lemma disjoint_prod_right (l : list (perm α))
  (h : ∀ g ∈ l, disjoint f g) : disjoint f l.prod :=
begin
  induction l with g l ih,
  { exact disjoint_one_right _ },
  { rw list.prod_cons,
    exact (h _ (list.mem_cons_self _ _)).mul_right (ih (λ g hg, h g (list.mem_cons_of_mem _ hg))) }
end

lemma disjoint_prod_perm {l₁ l₂ : list (perm α)} (hl : l₁.pairwise disjoint)
  (hp : l₁ ~ l₂) : l₁.prod = l₂.prod :=
hp.prod_eq' $ hl.imp $ λ f g, disjoint.commute

lemma nodup_of_pairwise_disjoint {l : list (perm α)} (h1 : (1 : perm α) ∉ l)
  (h2 : l.pairwise disjoint) : l.nodup :=
begin
  refine list.pairwise.imp_of_mem _ h2,
  rintros σ - h_mem - h_disjoint rfl,
  suffices : σ = 1,
  { rw this at h_mem,
    exact h1 h_mem },
  exact ext (λ a, (or_self _).mp (h_disjoint a)),
end

lemma pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) :
  ∀ n : ℕ, (f ^ n) x = x
| 0     := rfl
| (n+1) := by rw [pow_succ', mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self]

lemma gpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) :
  ∀ n : ℤ, (f ^ n) x = x
| (n : ℕ) := pow_apply_eq_self_of_apply_eq_self hfx n
| -[1+ n] := by rw [gpow_neg_succ_of_nat, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]

lemma pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
  ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
| 0     := or.inl rfl
| (n+1) := (pow_apply_eq_of_apply_apply_eq_self n).elim
  (λ h, or.inr (by rw [pow_succ, mul_apply, h]))
  (λ h, or.inl (by rw [pow_succ, mul_apply, h, hffx]))

lemma gpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
  ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
| (n : ℕ) := pow_apply_eq_of_apply_apply_eq_self hffx n
| -[1+ n] := by { rw [gpow_neg_succ_of_nat, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply,
    ← pow_succ, eq_comm, inv_eq_iff_eq, ← mul_apply, ← pow_succ', @eq_comm _ x, or.comm],
  exact pow_apply_eq_of_apply_apply_eq_self hffx _ }

lemma disjoint.mul_apply_eq_iff {σ τ : perm α} (hστ : disjoint σ τ) {a : α} :
  (σ * τ) a = a ↔ σ a = a ∧ τ a = a :=
begin
  refine ⟨λ h, _, λ h, by rw [mul_apply, h.2, h.1]⟩,
  cases hστ a with hσ hτ,
  { exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩ },
  { exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩ },
end

lemma disjoint.mul_eq_one_iff {σ τ : perm α} (hστ : disjoint σ τ) :
  σ * τ = 1 ↔ σ = 1 ∧ τ = 1 :=
by simp_rw [ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and_distrib]

lemma disjoint.gpow_disjoint_gpow {σ τ : perm α} (hστ : disjoint σ τ) (m n : ℤ) :
  disjoint (σ ^ m) (τ ^ n) :=
λ x, or.imp (λ h, gpow_apply_eq_self_of_apply_eq_self h m)
  (λ h, gpow_apply_eq_self_of_apply_eq_self h n) (hστ x)

lemma disjoint.pow_disjoint_pow {σ τ : perm α} (hστ : disjoint σ τ) (m n : ℕ) :
  disjoint (σ ^ m) (τ ^ n) :=
hστ.gpow_disjoint_gpow m n

end disjoint

section is_swap

variable [decidable_eq α]

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

end is_swap

section support

variables [decidable_eq α] [fintype α] {f g : perm α}

/-- The `finset` of nonfixed points of a permutation. -/
def support (f : perm α) : finset α := univ.filter (λ x, f x ≠ x)

@[simp] lemma mem_support {x : α} : x ∈ f.support ↔ f x ≠ x :=
by rw [support, mem_filter, and_iff_right (mem_univ x)]

lemma not_mem_support {x : α} : x ∉ f.support ↔ f x = x := by simp

@[simp] lemma support_eq_empty_iff {σ : perm α} : σ.support = ∅ ↔ σ = 1 :=
by simp_rw [finset.ext_iff, mem_support, finset.not_mem_empty, iff_false, not_not,
  equiv.perm.ext_iff, one_apply]

@[simp] lemma support_one : (1 : perm α).support = ∅ :=
by rw support_eq_empty_iff

@[simp] lemma support_refl : support (equiv.refl α) = ∅ := support_one

lemma support_congr (h : f.support ⊆ g.support)
  (h' : ∀ x ∈ g.support, f x = g x) : f = g :=
begin
  ext x,
  by_cases hx : x ∈ g.support,
  { exact h' x hx },
  { rw [not_mem_support.mp hx, ←not_mem_support],
    exact λ H, hx (h H) }
end

lemma support_mul_le (f g : perm α) :
  (f * g).support ≤ f.support ⊔ g.support :=
λ x, begin
  rw [sup_eq_union, mem_union, mem_support, mem_support,
    mem_support, mul_apply, ←not_and_distrib, not_imp_not],
  rintro ⟨hf, hg⟩,
  rw [hg, hf]
end

lemma exists_mem_support_of_mem_support_prod {l : list (perm α)} {x : α}
  (hx : x ∈ l.prod.support) :
  ∃ f : perm α, f ∈ l ∧ x ∈ f.support :=
begin
  contrapose! hx,
  simp_rw [mem_support, not_not] at hx ⊢,
  induction l with f l ih generalizing hx,
  { refl },
  { rw [list.prod_cons, mul_apply, ih (λ g hg, hx g (or.inr hg)), hx f (or.inl rfl)] },
end

lemma support_pow_le (σ : perm α) (n : ℕ) :
  (σ ^ n).support ≤ σ.support :=
λ x h1, mem_support.mpr (λ h2, mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n))

@[simp] lemma support_inv (σ : perm α) : support (σ⁻¹) = σ.support :=
by simp_rw [finset.ext_iff, mem_support, not_iff_not,
  (inv_eq_iff_eq).trans eq_comm, iff_self, imp_true_iff]

@[simp]
lemma apply_mem_support {x : α} :
  f x ∈ f.support ↔ x ∈ f.support :=
by rw [mem_support, mem_support, ne.def, ne.def, not_iff_not, apply_eq_iff_eq]

@[simp]
lemma pow_apply_mem_support {n : ℕ} {x : α} :
  (f ^ n) x ∈ f.support ↔ x ∈ f.support :=
begin
  induction n with n ih,
  { refl },
  rw [pow_succ, perm.mul_apply, apply_mem_support, ih]
end

@[simp]
lemma gpow_apply_mem_support {n : ℤ} {x : α} :
  (f ^ n) x ∈ f.support ↔ x ∈ f.support :=
begin
  cases n,
  { rw [int.of_nat_eq_coe, gpow_coe_nat, pow_apply_mem_support] },
  { rw [gpow_neg_succ_of_nat, ← support_inv, ← inv_pow, pow_apply_mem_support] }
end

lemma pow_eq_on_of_mem_support (h : ∀ (x ∈ f.support ∩ g.support), f x = g x)
  (k : ℕ) : ∀ (x ∈ f.support ∩ g.support), (f ^ k) x = (g ^ k) x :=
begin
  induction k with k hk,
  { simp },
  { intros x hx,
    rw [pow_succ', mul_apply, pow_succ', mul_apply, h _ hx, hk],
    rwa [mem_inter, apply_mem_support, ←h _ hx, apply_mem_support, ←mem_inter] }
end

lemma disjoint_iff_disjoint_support :
  disjoint f g ↔ _root_.disjoint f.support g.support :=
by simp [disjoint_iff_eq_or_eq, disjoint_iff, finset.ext_iff, not_and_distrib]

lemma disjoint.disjoint_support (h : disjoint f g) :
  _root_.disjoint f.support g.support :=
disjoint_iff_disjoint_support.1 h

lemma disjoint.support_mul (h : disjoint f g) :
  (f * g).support = f.support ∪ g.support :=
begin
  refine le_antisymm (support_mul_le _ _) (λ a, _),
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ←not_and_distrib, not_imp_not],
  exact (h a).elim (λ hf h, ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩)
    (λ hg h, ⟨(congr_arg f hg).symm.trans h, hg⟩),
end

lemma support_prod_of_pairwise_disjoint (l : list (perm α)) (h : l.pairwise disjoint) :
  l.prod.support = (l.map support).foldr (⊔) ⊥ :=
begin
  induction l with hd tl hl,
  { simp },
  { rw [list.pairwise_cons] at h,
    have : disjoint hd tl.prod := disjoint_prod_right _ h.left,
    simp [this.support_mul, hl h.right] }
end

lemma support_prod_le (l : list (perm α)) :
  l.prod.support ≤ (l.map support).foldr (⊔) ⊥ :=
begin
  induction l with hd tl hl,
  { simp },
  { rw [list.prod_cons, list.map_cons, list.foldr_cons],
    refine (support_mul_le hd tl.prod).trans _,
    exact sup_le_sup (le_refl _) hl }
end

lemma support_gpow_le (σ : perm α) (n : ℤ) :
  (σ ^ n).support ≤ σ.support :=
λ x h1, mem_support.mpr (λ h2, mem_support.mp h1 (gpow_apply_eq_self_of_apply_eq_self h2 n))

@[simp] lemma support_swap {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} :=
begin
  ext z,
  by_cases hx : z = x;
  by_cases hy : z = y,
  any_goals { simpa [hx, hy] using h.symm },
  { simp [swap_apply_of_ne_of_ne, hx, hy] }
end

lemma support_swap_iff (x y : α) :
  support (swap x y) = {x, y} ↔ x ≠ y :=
begin
  refine ⟨λ h H, _, support_swap⟩,
  subst H,
  simp only [swap_self, support_refl, insert_singleton_self_eq] at h,
  have : x ∈ ∅,
    { rw h,
      exact mem_singleton.mpr rfl },
  simpa
end

lemma support_swap_mul_swap {x y z : α} (h : list.nodup [x, y, z]) :
  support (swap x y * swap y z) = {x, y, z} :=
begin
  simp only [list.not_mem_nil, and_true, list.mem_cons_iff, not_false_iff, list.nodup_cons,
             list.mem_singleton, and_self, list.nodup_nil] at h,
  push_neg at h,
  apply le_antisymm,
  { convert support_mul_le _ _,
    rw [support_swap h.left.left, support_swap h.right],
    ext,
    simp [or.comm, or.left_comm] },
  { intro,
    simp only [mem_insert, mem_singleton],
    rintro (rfl | rfl | rfl | _);
    simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right, h.left.right.symm,
          h.right.symm] }
end

lemma support_swap_mul_ge_support_diff (f : perm α) (x y : α) :
  f.support \ {x, y} ≤ (swap x y * f).support :=
begin
  intro,
  simp only [and_imp, perm.coe_mul, function.comp_app, ne.def, mem_support, mem_insert, mem_sdiff,
             mem_singleton],
  push_neg,
  rintro ha ⟨hx, hy⟩ H,
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H,
  exact ha H
end

lemma support_swap_mul_eq (f : perm α) (x : α) (h : f (f x) ≠ x) :
  (swap x (f x) * f).support = f.support \ {x} :=
begin
  by_cases hx : f x = x,
  { simp [hx, sdiff_singleton_eq_erase, not_mem_support.mpr hx, erase_eq_of_not_mem] },
  ext z,
  by_cases hzx : z = x,
  { simp [hzx] },
  by_cases hzf : z = f x,
  { simp [hzf, hx, h, swap_apply_of_ne_of_ne], },
  by_cases hzfx : f z = x,
  { simp [ne.symm hzx, hzx, ne.symm hzf, hzfx] },
  { simp [ne.symm hzx, hzx, ne.symm hzf, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne] }
end

lemma mem_support_swap_mul_imp_mem_support_ne {x y : α}
  (hy : y ∈ support (swap x (f x) * f)) : y ∈ support f ∧ y ≠ x :=
begin
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *,
  by_cases h : f y = x,
  { split; intro; simp only [*, if_true, eq_self_iff_true, not_true, ne.def] at * },
  { split_ifs at hy; cc }
end

lemma disjoint.mem_imp (h : disjoint f g) {x : α} (hx : x ∈ f.support) :
  x ∉ g.support :=
λ H, h.disjoint_support (mem_inter_of_mem hx H)

lemma eq_on_support_mem_disjoint {l : list (perm α)} (h : f ∈ l) (hl : l.pairwise disjoint) :
  ∀ (x ∈ f.support), f x = l.prod x :=
begin
  induction l with hd tl IH,
  { simpa using h },
  { intros x hx,
    rw list.pairwise_cons at hl,
    rw list.mem_cons_iff at h,
    rcases h with rfl|h,
    { rw [list.prod_cons, mul_apply, not_mem_support.mp
          ((disjoint_prod_right tl hl.left).mem_imp hx)] },
    { rw [list.prod_cons, mul_apply, ←IH h hl.right _ hx, eq_comm, ←not_mem_support],
      refine (hl.left _ h).symm.mem_imp _,
      simpa using hx } }
end

lemma disjoint.mono {x y : perm α} (h : disjoint f g)
  (hf : x.support ≤ f.support) (hg : y.support ≤ g.support) :
  disjoint x y :=
begin
  rw disjoint_iff_disjoint_support at h ⊢,
  intros a ha,
  exact h (mem_inter_of_mem (hf (mem_of_mem_inter_left ha)) (hg (mem_of_mem_inter_right ha)))
end

lemma support_le_prod_of_mem {l : list (perm α)} (h : f ∈ l) (hl : l.pairwise disjoint) :
  f.support ≤ l.prod.support :=
begin
  intros x hx,
  rwa [mem_support, ←eq_on_support_mem_disjoint h hl _ hx, ←mem_support],
end

section extend_domain
variables {β : Type*} [decidable_eq β] [fintype β] {p : β → Prop} [decidable_pred p]

@[simp]
lemma support_extend_domain (f : α ≃ subtype p) {g : perm α} :
  support (g.extend_domain f) = g.support.map f.as_embedding :=
begin
  ext b,
  simp only [exists_prop, function.embedding.coe_fn_mk, to_embedding_apply, mem_map, ne.def,
    function.embedding.trans_apply, mem_support],
  by_cases pb : p b,
  { rw [extend_domain_apply_subtype _ _ pb],
    split,
    { rintro h,
      refine ⟨f.symm ⟨b, pb⟩, _, by simp⟩,
      contrapose! h,
      simp [h] },
    { rintro ⟨a, ha, hb⟩,
      contrapose! ha,
      obtain rfl : a = f.symm ⟨b, pb⟩,
      { rw eq_symm_apply,
        exact subtype.coe_injective hb },
      rw eq_symm_apply,
      exact subtype.coe_injective ha } },
  { rw [extend_domain_apply_not_subtype _ _ pb],
    simp only [not_exists, false_iff, not_and, eq_self_iff_true, not_true],
    rintros a ha rfl,
    exact pb (subtype.prop _) }
end

lemma card_support_extend_domain (f : α ≃ subtype p) {g : perm α} :
  (g.extend_domain f).support.card = g.support.card :=
by simp

end extend_domain

section card

@[simp]
lemma card_support_eq_zero {f : perm α} :
  f.support.card = 0 ↔ f = 1 :=
by rw [finset.card_eq_zero, support_eq_empty_iff]

lemma one_lt_card_support_of_ne_one {f : perm α} (h : f ≠ 1) :
  1 < f.support.card :=
begin
  simp_rw [one_lt_card_iff, mem_support, ←not_or_distrib],
  contrapose! h,
  ext a,
  specialize h (f a) a,
  rwa [apply_eq_iff_eq, or_self, or_self] at h,
end

lemma card_support_ne_one (f : perm α) : f.support.card ≠ 1 :=
begin
  by_cases h : f = 1,
  { exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one },
  { exact ne_of_gt (one_lt_card_support_of_ne_one h) },
end

@[simp] lemma card_support_le_one {f : perm α} : f.support.card ≤ 1 ↔ f = 1 :=
by rw [le_iff_lt_or_eq, nat.lt_succ_iff, nat.le_zero_iff, card_support_eq_zero,
  or_iff_not_imp_right, imp_iff_right f.card_support_ne_one]

lemma two_le_card_support_of_ne_one {f : perm α} (h : f ≠ 1) :
  2 ≤ f.support.card :=
one_lt_card_support_of_ne_one h

lemma card_support_swap_mul {f : perm α} {x : α}
  (hx : f x ≠ x) : (swap x (f x) * f).support.card < f.support.card :=
finset.card_lt_card
  ⟨λ z hz, (mem_support_swap_mul_imp_mem_support_ne hz).left,
    λ h, absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

lemma card_support_swap {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
show (swap x y).support.card = finset.card ⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩,
from congr_arg card $ by simp [support_swap hxy, *, finset.ext_iff]

@[simp]
lemma card_support_eq_two {f : perm α} : f.support.card = 2 ↔ is_swap f :=
begin
  split; intro h,
  { obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h,
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht,
    rw mem_singleton at hmem,
    refine ⟨x, y, hmem, _⟩,
    ext a,
    have key : ∀ b, f b ≠ b ↔ _ := λ b, by rw [←mem_support, ←hins, mem_insert, mem_singleton],
    by_cases ha : f a = a,
    { have ha' := not_or_distrib.mp (mt (key a).mpr (not_not.mpr ha)),
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2] },
    { have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha),
      obtain rfl | rfl := ((key a).mp ha),
      { rw [or.resolve_left ha' ha, swap_apply_left] },
      { rw [or.resolve_right ha' ha, swap_apply_right] } } },
  { obtain ⟨x, y, hxy, rfl⟩ := h,
    exact card_support_swap hxy }
end

lemma disjoint.card_support_mul (h : disjoint f g) :
  (f * g).support.card = f.support.card + g.support.card :=
begin
  rw ←finset.card_disjoint_union,
  { congr,
    ext,
    simp [h.support_mul] },
  { simpa using h.disjoint_support }
end

lemma card_support_prod_list_of_pairwise_disjoint {l : list (perm α)}
  (h : l.pairwise disjoint) :
  l.prod.support.card = (l.map (finset.card ∘ support)).sum :=
begin
  induction l with a t ih,
  { exact card_support_eq_zero.mpr rfl, },
  { obtain ⟨ha, ht⟩ := list.pairwise_cons.1 h,
    rw [list.prod_cons, list.map_cons, list.sum_cons, ←ih ht],
    exact (disjoint_prod_right _ ha).card_support_mul }
end

end card

end support

end equiv.perm
