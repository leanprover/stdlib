/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.algebra.basic

/-!
# Multiplication and division of submodules of an algebra.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and aet `A` be an `R`-algebra.

* `1 : submodule R A`       : the R-submodule R of the R-algebra A
* `has_mul (submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `has_div (submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `submodule R A` is a semiring, and also an algebra over `set A`.

## Tags

multiplication of submodules, division of subodules, submodule semiring
-/

universes u v

open algebra set

namespace submodule

variables {R : Type u} [comm_semiring R]

section ring

variables {A : Type v} [semiring A] [algebra R A]
variables (S T : set A) {M N P Q : submodule R A} {m n : A}

/-- `1 : submodule R A` is the submodule R of A. -/
instance : has_one (submodule R A) :=
⟨submodule.map (of_id R A).to_linear_map (⊤ : submodule R R)⟩

theorem one_eq_map_top :
  (1 : submodule R A) = submodule.map (of_id R A).to_linear_map (⊤ : submodule R R) := rfl

theorem one_eq_span : (1 : submodule R A) = R ∙ 1 :=
begin
  apply submodule.ext,
  intro a,
  erw [mem_map, mem_span_singleton],
  apply exists_congr,
  intro r,
  simpa [smul_def],
end

theorem one_le : (1 : submodule R A) ≤ P ↔ (1 : A) ∈ P :=
by simpa only [one_eq_span, span_le, set.singleton_subset_iff]

/-- Multiplication of sub-R-modules of an R-algebra A. The submodule `M * N` is the
smallest R-submodule of `A` containing the elements `m * n` for `m ∈ M` and `n ∈ N`. -/
instance : has_mul (submodule R A) :=
⟨λ M N, ⨆ s : M, N.map $ algebra.lmul R A s.1⟩

theorem mul_mem_mul (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
(le_supr _ ⟨m, hm⟩ : _ ≤ M * N) ⟨n, hn, rfl⟩

theorem mul_le : M * N ≤ P ↔ ∀ (m ∈ M) (n ∈ N), m * n ∈ P :=
⟨λ H m hm n hn, H $ mul_mem_mul hm hn,
λ H, supr_le $ λ ⟨m, hm⟩, map_le_iff_le_comap.2 $ λ n hn, H m hm n hn⟩

@[elab_as_eliminator] protected theorem mul_induction_on
  {C : A → Prop} {r : A} (hr : r ∈ M * N)
  (hm : ∀ (m ∈ M) (n ∈ N), C (m * n))
  (h0 : C 0) (ha : ∀ x y, C x → C y → C (x + y))
  (hs : ∀ (r : R) x, C x → C (r • x)) : C r :=
(@mul_le _ _ _ _ _ _ _ ⟨C, h0, ha, hs⟩).2 hm hr

variables R
theorem span_mul_span : span R S * span R T = span R (S * T) :=
begin
  apply le_antisymm,
  { rw mul_le, intros a ha b hb,
    apply span_induction ha,
    work_on_goal 0 { intros, apply span_induction hb,
      work_on_goal 0 { intros, exact subset_span ⟨_, _, ‹_›, ‹_›, rfl⟩ } },
    all_goals { intros, simp only [mul_zero, zero_mul, zero_mem,
        left_distrib, right_distrib, mul_smul_comm, smul_mul_assoc],
      try {apply add_mem _ _ _}, try {apply smul_mem _ (_ : R) _} }, assumption',
      repeat { apply_instance }, },
  { rw span_le, rintros _ ⟨a, b, ha, hb, rfl⟩,
    exact mul_mem_mul (subset_span ha) (subset_span hb) }
end
variables {R}

variables (M N P Q)
protected theorem mul_assoc : (M * N) * P = M * (N * P) :=
le_antisymm (mul_le.2 $ λ mn hmn p hp,
  suffices M * N ≤ (M * (N * P)).comap (algebra.lmul_right R p), from this hmn,
  mul_le.2 $ λ m hm n hn, show m * n * p ∈ M * (N * P), from
  (mul_assoc m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
(mul_le.2 $ λ m hm np hnp,
  suffices N * P ≤ (M * N * P).comap (algebra.lmul_left R m), from this hnp,
  mul_le.2 $ λ n hn p hp, show m * (n * p) ∈ M * N * P, from
  mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)

@[simp] theorem mul_bot : M * ⊥ = ⊥ :=
eq_bot_iff.2 $ mul_le.2 $ λ m hm n hn, by rw [submodule.mem_bot] at hn ⊢; rw [hn, mul_zero]

@[simp] theorem bot_mul : ⊥ * M = ⊥ :=
eq_bot_iff.2 $ mul_le.2 $ λ m hm n hn, by rw [submodule.mem_bot] at hm ⊢; rw [hm, zero_mul]

@[simp] protected theorem one_mul : (1 : submodule R A) * M = M :=
by { conv_lhs { rw [one_eq_span, ← span_eq M] }, erw [span_mul_span, one_mul, span_eq] }

@[simp] protected theorem mul_one : M * 1 = M :=
by { conv_lhs { rw [one_eq_span, ← span_eq M] }, erw [span_mul_span, mul_one, span_eq] }

variables {M N P Q}

@[mono] theorem mul_le_mul (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q :=
mul_le.2 $ λ m hm n hn, mul_mem_mul (hmp hm) (hnq hn)

theorem mul_le_mul_left (h : M ≤ N) : M * P ≤ N * P :=
mul_le_mul h (le_refl P)

theorem mul_le_mul_right (h : N ≤ P) : M * N ≤ M * P :=
mul_le_mul (le_refl M) h

variables (M N P)
theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P :=
le_antisymm (mul_le.2 $ λ m hm np hnp, let ⟨n, hn, p, hp, hnp⟩ := mem_sup.1 hnp in
  mem_sup.2 ⟨_, mul_mem_mul hm hn, _, mul_mem_mul hm hp, hnp ▸ (mul_add m n p).symm⟩)
(sup_le (mul_le_mul_right le_sup_left) (mul_le_mul_right le_sup_right))

theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P :=
le_antisymm (mul_le.2 $ λ mn hmn p hp, let ⟨m, hm, n, hn, hmn⟩ := mem_sup.1 hmn in
  mem_sup.2 ⟨_, mul_mem_mul hm hp, _, mul_mem_mul hn hp, hmn ▸ (add_mul m n p).symm⟩)
(sup_le (mul_le_mul_left le_sup_left) (mul_le_mul_left le_sup_right))

lemma mul_subset_mul : (↑M : set A) * (↑N : set A) ⊆ (↑(M * N) : set A) :=
by { rintros _ ⟨i, j, hi, hj, rfl⟩, exact mul_mem_mul hi hj }

lemma map_mul {A'} [semiring A'] [algebra R A'] (f : A →ₐ[R] A') :
  map f.to_linear_map (M * N) = map f.to_linear_map M * map f.to_linear_map N :=
calc map f.to_linear_map (M * N)
    = ⨆ (i : M), (N.map (lmul R A i)).map f.to_linear_map : map_supr _ _
... = map f.to_linear_map M * map f.to_linear_map N  :
  begin
    apply congr_arg Sup,
    ext S,
    split; rintros ⟨y, hy⟩,
    { use [f y, mem_map.mpr ⟨y.1, y.2, rfl⟩],
      refine trans _ hy,
      ext,
      simp },
    { obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2,
      use [y', hy'],
      refine trans _ hy,
      rw f.to_linear_map_apply at fy_eq,
      ext,
      simp [fy_eq] }
end

section decidable_eq

open_locale classical

lemma mem_span_mul_finite_of_mem_span_mul {S : set A} {S' : set A} {x : A}
  (hx : x ∈ span R (S * S')) :
  ∃ (T T' : finset A), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span R (T * T' : set A) :=
begin
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx,
  obtain ⟨T, T', hS, hS', h⟩ := finset.subset_mul h,
  use [T, T', hS, hS'],
  have h' : (U : set A) ⊆ T * T', { assumption_mod_cast, },
  have h'' := span_mono h' hU,
  assumption,
end

end decidable_eq

lemma mem_span_mul_finite_of_mem_mul {P Q : submodule R A} {x : A} (hx : x ∈ P * Q) :
  ∃ (T T' : finset A), (T : set A) ⊆ P ∧ (T' : set A) ⊆ Q ∧ x ∈ span R (T * T' : set A) :=
submodule.mem_span_mul_finite_of_mem_span_mul
  (by rwa [← submodule.span_eq P, ← submodule.span_eq Q, submodule.span_mul_span] at hx)

variables {M N P}

/-- Sub-R-modules of an R-algebra form a semiring. -/
instance : semiring (submodule R A) :=
{ one_mul       := submodule.one_mul,
  mul_one       := submodule.mul_one,
  mul_assoc     := submodule.mul_assoc,
  zero_mul      := bot_mul,
  mul_zero      := mul_bot,
  left_distrib  := mul_sup,
  right_distrib := sup_mul,
  ..submodule.add_comm_monoid_submodule,
  ..submodule.has_one,
  ..submodule.has_mul }

variables (M)

lemma pow_subset_pow {n : ℕ} : (↑M : set A)^n ⊆ ↑(M^n : submodule R A) :=
begin
  induction n with n ih,
  { erw [pow_zero, pow_zero, set.singleton_subset_iff], rw [mem_coe, ← one_le], exact le_refl _ },
  { rw [pow_succ, pow_succ],
    refine set.subset.trans (set.mul_subset_mul (subset.refl _) ih) _,
    apply mul_subset_mul }
end

/-- `span` is a semiring homomorphism (recall multiplication is pointwise multiplication of subsets
on either side). -/
def span.ring_hom : set_semiring A →+* submodule R A :=
{ to_fun := submodule.span R,
  map_zero' := span_empty,
  map_one' := le_antisymm (span_le.2 $ singleton_subset_iff.2 ⟨1, ⟨⟩, (algebra_map R A).map_one⟩)
    (map_le_iff_le_comap.2 $ λ r _, mem_span_singleton.2 ⟨r, (algebra_map_eq_smul_one r).symm⟩),
  map_add' := span_union,
  map_mul' := λ s t, by erw [span_mul_span, ← image_mul_prod] }

end ring

section comm_ring

variables {A : Type v} [comm_semiring A] [algebra R A]
variables {M N : submodule R A} {m n : A}

theorem mul_mem_mul_rev (hm : m ∈ M) (hn : n ∈ N) : n * m ∈ M * N :=
mul_comm m n ▸ mul_mem_mul hm hn

variables (M N)
protected theorem mul_comm : M * N = N * M :=
le_antisymm (mul_le.2 $ λ r hrm s hsn, mul_mem_mul_rev hsn hrm)
(mul_le.2 $ λ r hrn s hsm, mul_mem_mul_rev hsm hrn)

/-- Sub-R-modules of an R-algebra A form a semiring. -/
instance : comm_semiring (submodule R A) :=
{ mul_comm := submodule.mul_comm,
  .. submodule.semiring }

variables (R A)

/-- R-submodules of the R-algebra A are a module over `set A`. -/
instance semimodule_set : semimodule (set_semiring A) (submodule R A) :=
{ smul := λ s P, span R s * P,
  smul_add := λ _ _ _, mul_add _ _ _,
  add_smul := λ s t P, show span R (s ⊔ t) * P = _, by { erw [span_union, right_distrib] },
  mul_smul := λ s t P, show _ = _ * (_ * _),
    by { rw [← mul_assoc, span_mul_span, ← image_mul_prod] },
  one_smul := λ P, show span R {(1 : A)} * P = _,
    by { conv_lhs {erw ← span_eq P}, erw [span_mul_span, one_mul, span_eq] },
  zero_smul := λ P, show span R ∅ * P = ⊥, by erw [span_empty, bot_mul],
  smul_zero := λ _, mul_bot _ }


variables {R A}

lemma smul_def {s : set_semiring A} {P : submodule R A} : s • P = span R s * P := rfl

lemma smul_le_smul {s t : set_semiring A} {M N : submodule R A} (h₁ : s.down ≤ t.down)
  (h₂ : M ≤ N) : s • M ≤ t • N :=
mul_le_mul (span_mono h₁) h₂

lemma smul_singleton (a : A) (M : submodule R A) :
  ({a} : set A).up • M = M.map (lmul_left _ a) :=
begin
  conv_lhs {rw ← span_eq M},
  change span _ _ * span _ _ = _,
  rw [span_mul_span],
  apply le_antisymm,
  { rw span_le,
    rintros _ ⟨b, m, hb, hm, rfl⟩,
    rw [mem_coe, mem_map, set.mem_singleton_iff.mp hb],
    exact ⟨m, hm, rfl⟩ },
  { rintros _ ⟨m, hm, rfl⟩, exact subset_span ⟨a, m, set.mem_singleton a, hm, rfl⟩ }
end

section quotient

/-- The elements of `I / J` are the `x` such that `x • J ⊆ I`.

In fact, we define `x ∈ I / J` to be `∀ y ∈ J, x * y ∈ I` (see `mem_div_iff_forall_mul_mem`),
which is equivalent to `x • J ⊆ I` (see `mem_div_iff_smul_subset`), but nicer to use in proofs.

This is the general form of the ideal quotient, traditionally written $I : J$.
-/
instance : has_div (submodule R A) :=
⟨ λ I J, {
  carrier   := { x | ∀ y ∈ J, x * y ∈ I },
  zero_mem' := λ y hy, by { rw zero_mul, apply submodule.zero_mem },
  add_mem'  := λ a b ha hb y hy, by { rw add_mul, exact submodule.add_mem _ (ha _ hy) (hb _ hy) },
  smul_mem' := λ r x hx y hy, by { rw algebra.smul_mul_assoc,
    exact submodule.smul_mem _ _ (hx _ hy) } } ⟩

lemma mem_div_iff_forall_mul_mem {x : A} {I J : submodule R A} :
  x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I :=
iff.refl _

lemma mem_div_iff_smul_subset {x : A} {I J : submodule R A} : x ∈ I / J ↔ x • (J : set A) ⊆ I :=
⟨ λ h y ⟨y', hy', xy'_eq_y⟩, by { rw ← xy'_eq_y, apply h, assumption },
  λ h y hy, h (set.smul_mem_smul_set hy) ⟩

lemma le_div_iff {I J K : submodule R A} : I ≤ J / K ↔ ∀ (x ∈ I) (z ∈ K), x * z ∈ J := iff.refl _

lemma le_div_iff_mul_le {I J K : submodule R A} : I ≤ J / K ↔ I * K ≤ J :=
by rw [le_div_iff, mul_le]

@[simp] lemma one_le_one_div {I : submodule R A} :
  1 ≤ 1 / I ↔ I ≤ 1 :=
begin
  split, all_goals {intro hI},
  {rwa [le_div_iff_mul_le, one_mul] at hI},
  {rwa [le_div_iff_mul_le, one_mul]},
end

lemma le_self_mul_one_div {I : submodule R A} (hI : I ≤ 1) :
  I ≤ I * (1 / I) :=
begin
  rw [← mul_one I] {occs := occurrences.pos [1]},
  apply mul_le_mul_right (one_le_one_div.mpr hI),
end

lemma mul_one_div_le_one {I : submodule R A} : I * (1 / I) ≤ 1 :=
begin
  rw submodule.mul_le,
  intros m hm n hn,
  rw [submodule.mem_div_iff_forall_mul_mem] at hn,
  rw mul_comm,
  exact hn m hm,
end

@[simp] lemma map_div {B : Type*} [comm_ring B] [algebra R B]
  (I J : submodule R A) (h : A ≃ₐ[R] B) :
  (I / J).map h.to_linear_map = I.map h.to_linear_map / J.map h.to_linear_map :=
begin
  ext x,
  simp only [mem_map, mem_div_iff_forall_mul_mem],
  split,
  { rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
    exact ⟨x * y, hx _ hy, h.map_mul x y⟩ },
  { rintro hx,
    refine ⟨h.symm x, λ z hz, _, h.apply_symm_apply x⟩,
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩,
    convert xz_mem,
    apply h.injective,
    erw [h.map_mul, h.apply_symm_apply, hxz] }
end

end quotient

end comm_ring

end submodule
