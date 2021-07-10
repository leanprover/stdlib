/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
-/
import order.filter.filter_product
import analysis.specific_limits

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/

open filter filter.germ
open_locale topological_space classical

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
@[derive [linear_ordered_field, inhabited]]
def hyperreal : Type := germ (hyperfilter ℕ : filter ℕ) ℝ

namespace hyperreal

notation `ℝ*` := hyperreal

noncomputable instance : has_coe_t ℝ ℝ* := ⟨λ x, (↑x : germ _ _)⟩

@[simp, norm_cast]
lemma coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
germ.const_inj

@[simp, norm_cast] lemma coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 := coe_eq_coe
@[simp, norm_cast] lemma coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 := coe_eq_coe

@[simp, norm_cast] lemma coe_one : ↑(1 : ℝ) = (1 : ℝ*) := rfl
@[simp, norm_cast] lemma coe_zero : ↑(0 : ℝ) = (0 : ℝ*) := rfl
@[simp, norm_cast] lemma coe_inv (x : ℝ) : ↑(x⁻¹) = (x⁻¹ : ℝ*) := rfl
@[simp, norm_cast] lemma coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) := rfl
@[simp, norm_cast] lemma coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) := rfl
@[simp, norm_cast] lemma coe_bit0 (x : ℝ) : ↑(bit0 x) = (bit0 x : ℝ*) := rfl
@[simp, norm_cast] lemma coe_bit1 (x : ℝ) : ↑(bit1 x) = (bit1 x : ℝ*) := rfl
@[simp, norm_cast] lemma coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) := rfl
@[simp, norm_cast] lemma coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) := rfl
@[simp, norm_cast] lemma coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) := rfl

@[simp, norm_cast] lemma coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y := germ.const_lt
@[simp, norm_cast] lemma coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
coe_lt_coe
@[simp, norm_cast] lemma coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y := germ.const_le_iff
@[simp, norm_cast] lemma coe_abs (x : ℝ) : ((abs x : ℝ) : ℝ*) = abs x := germ.const_abs _
@[simp, norm_cast] lemma coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max x y := germ.const_max _ _
@[simp, norm_cast] lemma coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min x y := germ.const_min _ _

/-- Construct a hyperreal number from a sequence of real numbers. -/
noncomputable def of_seq (f : ℕ → ℝ) : ℝ* := (↑f : germ (hyperfilter ℕ : filter ℕ) ℝ)

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* := of_seq $ λ n, n⁻¹

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* := of_seq coe

localized "notation `ε` := hyperreal.epsilon" in hyperreal
localized "notation `ω` := hyperreal.omega" in hyperreal

lemma epsilon_eq_inv_omega : ε = ω⁻¹ := rfl

lemma inv_epsilon_eq_omega : ε⁻¹ = ω := @inv_inv' _ _ ω

lemma epsilon_pos : 0 < ε :=
suffices ∀ᶠ i in hyperfilter ℕ, (0 : ℝ) < (i : ℕ)⁻¹, by rwa lt_def,
have h0' : {n : ℕ | ¬ 0 < n} = {0} :=
by simp only [not_lt, (set.set_of_eq_eq_singleton).symm]; ext; exact nat.le_zero_iff,
begin
  simp only [inv_pos, nat.cast_pos],
  exact mem_hyperfilter_of_finite_compl (by convert set.finite_singleton _),
end

lemma epsilon_ne_zero : ε ≠ 0 := ne_of_gt epsilon_pos

lemma omega_pos : 0 < ω := by rw ←inv_epsilon_eq_omega; exact inv_pos.2 epsilon_pos

lemma omega_ne_zero : ω ≠ 0 := ne_of_gt omega_pos

theorem epsilon_mul_omega : ε * ω = 1 := @inv_mul_cancel _ _ ω omega_ne_zero

lemma lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : tendsto f at_top (𝓝 0)) :
  ∀ {r : ℝ}, 0 < r → of_seq f < (r : ℝ*) :=
begin
  simp only [metric.tendsto_at_top, dist_zero_right, norm, lt_def] at hf ⊢,
  intros r hr, cases hf r hr with N hf',
  have hs : {i : ℕ | f i < r}ᶜ ⊆ {i : ℕ | i ≤ N} :=
    λ i hi1, le_of_lt (by simp only [lt_iff_not_ge];
    exact λ hi2, hi1 (lt_of_le_of_lt (le_abs_self _) (hf' i hi2)) : i < N),
  exact mem_hyperfilter_of_finite_compl
    ((set.finite_le_nat N).subset hs)
end

lemma neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : tendsto f at_top (𝓝 0)) :
  ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < of_seq f :=
λ r hr, have hg : _ := hf.neg,
neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

lemma gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : tendsto f at_top (𝓝 0)) :
  ∀ {r : ℝ}, r < 0 → (r : ℝ*) < of_seq f :=
λ r hr, by rw [←neg_neg r, coe_neg];
exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)

lemma epsilon_lt_pos (x : ℝ) : 0 < x → ε < x :=
lt_of_tendsto_zero_of_pos tendsto_inverse_at_top_nhds_0_nat

/-- Standard part predicate -/
def is_st (x : ℝ*) (r : ℝ) := ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r + δ

/-- Standard part function: like a "round" to ℝ instead of ℤ -/
noncomputable def st : ℝ* → ℝ :=
λ x, if h : ∃ r, is_st x r then classical.some h else 0

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def infinitesimal (x : ℝ*) := is_st x 0

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def infinite_pos (x : ℝ*) := ∀ r : ℝ, ↑r < x

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def infinite_neg (x : ℝ*) := ∀ r : ℝ, x < r

/-- A hyperreal number is infinite if it is infinite positive or infinite negative -/
def infinite (x : ℝ*) := infinite_pos x ∨ infinite_neg x

/-!
### Some facts about `st`
-/

private lemma is_st_unique' (x : ℝ*) (r s : ℝ) (hr : is_st x r) (hs : is_st x s) (hrs : r < s) :
  false :=
have hrs' : _ := half_pos $ sub_pos_of_lt hrs,
have hr' : _ := (hr _ hrs').2,
have hs' : _ := (hs _ hrs').1,
have h : s - ((s - r) / 2) = r + (s - r) / 2 := by linarith,
begin
  norm_cast at *,
  rw h at hs',
  exact not_lt_of_lt hs' hr'
end

theorem is_st_unique {x : ℝ*} {r s : ℝ} (hr : is_st x r) (hs : is_st x s) : r = s :=
begin
  rcases lt_trichotomy r s with h | h | h,
  { exact false.elim (is_st_unique' x r s hr hs h) },
  { exact h },
  { exact false.elim (is_st_unique' x s r hs hr h) }
end

theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, is_st x r) → ¬ infinite x :=
λ he hi, Exists.dcases_on he $ λ r hr, hi.elim
   (λ hip, not_lt_of_lt (hr 2 zero_lt_two).2 (hip $ r + 2))
   (λ hin, not_lt_of_lt (hr 2 zero_lt_two).1 (hin $ r - 2))

theorem is_st_Sup {x : ℝ*} (hni : ¬ infinite x) : is_st x (Sup {y : ℝ | (y : ℝ*) < x}) :=
let S : set ℝ := {y : ℝ | (y : ℝ*) < x} in
let R : _ := Sup S in
have hnile : _ := not_forall.mp (not_or_distrib.mp hni).1,
have hnige : _ := not_forall.mp (not_or_distrib.mp hni).2,
Exists.dcases_on hnile $ Exists.dcases_on hnige $ λ r₁ hr₁ r₂ hr₂,
have HR₁ : ∃ y : ℝ, y ∈ S :=
  ⟨r₁ - 1, lt_of_lt_of_le (coe_lt_coe.2 $ sub_one_lt _) (not_lt.mp hr₁) ⟩,
have HR₂ : ∃ z : ℝ, ∀ y ∈ S, y ≤ z :=
  ⟨ r₂, λ y hy, le_of_lt (coe_lt_coe.1 (lt_of_lt_of_le hy (not_lt.mp hr₂))) ⟩,
λ δ hδ,
  ⟨ lt_of_not_ge' $ λ c,
      have hc : ∀ y ∈ S, y ≤ R - δ := λ y hy, coe_le_coe.1 $ le_of_lt $ lt_of_lt_of_le hy c,
      not_lt_of_le ((real.Sup_le _ HR₁ HR₂).mpr hc) $ sub_lt_self R hδ,
    lt_of_not_ge' $ λ c,
      have hc : ↑(R + δ / 2) < x :=
        lt_of_lt_of_le (add_lt_add_left (coe_lt_coe.2 (half_lt_self hδ)) R) c,
      not_lt_of_le (real.le_Sup _ HR₂ hc) $ (lt_add_iff_pos_right _).mpr $ half_pos hδ⟩

theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬ infinite x) : ∃ r : ℝ, is_st x r :=
⟨Sup {y : ℝ | (y : ℝ*) < x}, is_st_Sup hni⟩

theorem st_eq_Sup {x : ℝ*} : st x = Sup {y : ℝ | (y : ℝ*) < x} :=
begin
unfold st, split_ifs,
{ exact is_st_unique (classical.some_spec h) (is_st_Sup (not_infinite_of_exists_st h)) },
{ cases not_imp_comm.mp exists_st_of_not_infinite h with H H,
  { rw (set.ext (λ i, ⟨λ hi, set.mem_univ i, λ hi, H i⟩) : {y : ℝ | (y : ℝ*) < x} = set.univ),
    exact (real.Sup_univ).symm },
  { rw (set.ext (λ i, ⟨λ hi, false.elim (not_lt_of_lt (H i) hi),
    λ hi, false.elim (set.not_mem_empty i hi)⟩) : {y : ℝ | (y : ℝ*) < x} = ∅),
    exact (real.Sup_empty).symm } }
end

theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, is_st x r) ↔ ¬ infinite x :=
⟨ not_infinite_of_exists_st, exists_st_of_not_infinite ⟩

theorem infinite_iff_not_exists_st {x : ℝ*} : infinite x ↔ ¬ ∃ r : ℝ, is_st x r :=
iff_not_comm.mp exists_st_iff_not_infinite

theorem st_infinite {x : ℝ*} (hi : infinite x) : st x = 0 :=
begin
  unfold st, split_ifs,
  { exact false.elim ((infinite_iff_not_exists_st.mp hi) h) },
  { refl }
end

lemma st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : st x = r :=
begin
  unfold st, split_ifs,
  { exact is_st_unique (classical.some_spec h) hxr },
  { exact false.elim (h ⟨r, hxr⟩) }
end

lemma is_st_st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : is_st x (st x) :=
by rwa [st_of_is_st hxr]

lemma is_st_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, is_st x r) : is_st x (st x) :=
Exists.dcases_on hx (λ r, is_st_st_of_is_st)

lemma is_st_st {x : ℝ*} (hx : st x ≠ 0) : is_st x (st x) :=
begin
  unfold st, split_ifs,
  { exact classical.some_spec h },
  { exact false.elim (hx (by unfold st; split_ifs; refl)) }
end

lemma is_st_st' {x : ℝ*} (hx : ¬ infinite x) : is_st x (st x) :=
is_st_st_of_exists_st $ exists_st_of_not_infinite hx

lemma is_st_refl_real (r : ℝ) : is_st r r :=
λ δ hδ, ⟨ sub_lt_self _ (coe_lt_coe.2 hδ), (lt_add_of_pos_right _ (coe_lt_coe.2 hδ)) ⟩

lemma st_id_real (r : ℝ) : st r = r := st_of_is_st (is_st_refl_real r)

lemma eq_of_is_st_real {r s : ℝ} : is_st r s → r = s := is_st_unique (is_st_refl_real r)

lemma is_st_real_iff_eq {r s : ℝ} : is_st r s ↔ r = s :=
⟨eq_of_is_st_real, λ hrs, by rw [hrs]; exact is_st_refl_real s⟩

lemma is_st_symm_real {r s : ℝ} : is_st r s ↔ is_st s r :=
by rw [is_st_real_iff_eq, is_st_real_iff_eq, eq_comm]

lemma is_st_trans_real {r s t : ℝ} : is_st r s → is_st s t → is_st r t :=
by rw [is_st_real_iff_eq, is_st_real_iff_eq, is_st_real_iff_eq]; exact eq.trans

lemma is_st_inj_real {r₁ r₂ s : ℝ} (h1 : is_st r₁ s) (h2 : is_st r₂ s) : r₁ = r₂ :=
eq.trans (eq_of_is_st_real h1) (eq_of_is_st_real h2).symm

lemma is_st_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} :
  is_st x r ↔ ∀ (δ : ℝ), 0 < δ → abs (x - r) < δ :=
by simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, is_st, and_comm, add_comm]

lemma is_st_add {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x + y) (r + s) :=
λ hxr hys d hd,
have hxr' : _ := hxr (d / 2) (half_pos hd),
have hys' : _ := hys (d / 2) (half_pos hd),
⟨by convert add_lt_add hxr'.1 hys'.1 using 1; norm_cast; linarith,
 by convert add_lt_add hxr'.2 hys'.2 using 1; norm_cast; linarith⟩

lemma is_st_neg {x : ℝ*} {r : ℝ} (hxr : is_st x r) : is_st (-x) (-r) :=
λ d hd, show -(r : ℝ*) - d < -x ∧ -x < -r + d, by cases (hxr d hd); split; linarith

lemma is_st_sub {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x - y) (r - s) :=
λ hxr hys, by rw [sub_eq_add_neg, sub_eq_add_neg]; exact is_st_add hxr (is_st_neg hys)

/- (st x < st y) → (x < y) → (x ≤ y) → (st x ≤ st y) -/

lemma lt_of_is_st_lt {x y : ℝ*} {r s : ℝ} (hxr : is_st x r) (hys : is_st y s) :
  r < s → x < y :=
λ hrs, have hrs' : 0 < (s - r) / 2 := half_pos (sub_pos.mpr hrs),
have hxr' : _ := (hxr _ hrs').2, have hys' : _ := (hys _ hrs').1,
have H1 : r + ((s - r) / 2) = (r + s) / 2 := by linarith,
have H2 : s - ((s - r) / 2) = (r + s) / 2 := by linarith,
begin
  norm_cast at *,
  rw H1 at hxr',
  rw H2 at hys',
  exact lt_trans hxr' hys'
end

lemma is_st_le_of_le {x y : ℝ*} {r s : ℝ} (hrx : is_st x r) (hsy : is_st y s) :
  x ≤ y → r ≤ s := by rw [←not_lt, ←not_lt, not_imp_not]; exact lt_of_is_st_lt hsy hrx

lemma st_le_of_le {x y : ℝ*} (hix : ¬ infinite x) (hiy : ¬ infinite y) :
  x ≤ y → st x ≤ st y :=
have hx' : _ := is_st_st' hix, have hy' : _ := is_st_st' hiy,
is_st_le_of_le hx' hy'

lemma lt_of_st_lt {x y : ℝ*} (hix : ¬ infinite x) (hiy : ¬ infinite y) :
  st x < st y → x < y :=
have hx' : _ := is_st_st' hix, have hy' : _ := is_st_st' hiy,
lt_of_is_st_lt hx' hy'

/-!
### Basic lemmas about infinite
-/

lemma infinite_pos_def {x : ℝ*} : infinite_pos x ↔ ∀ r : ℝ, ↑r < x := by rw iff_eq_eq; refl

lemma infinite_neg_def {x : ℝ*} : infinite_neg x ↔ ∀ r : ℝ, x < r := by rw iff_eq_eq; refl

lemma ne_zero_of_infinite {x : ℝ*} : infinite x → x ≠ 0 :=
λ hI h0, or.cases_on hI
  (λ hip, lt_irrefl (0 : ℝ*) ((by rwa ←h0 : infinite_pos 0) 0))
  (λ hin, lt_irrefl (0 : ℝ*) ((by rwa ←h0 : infinite_neg 0) 0))

lemma not_infinite_zero : ¬ infinite 0 := λ hI, ne_zero_of_infinite hI rfl

lemma pos_of_infinite_pos {x : ℝ*} : infinite_pos x → 0 < x := λ hip, hip 0

lemma neg_of_infinite_neg {x : ℝ*} : infinite_neg x → x < 0 := λ hin, hin 0

lemma not_infinite_pos_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬ infinite_pos x :=
λ hn hp, not_lt_of_lt (hn 1) (hp 1)

lemma not_infinite_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬ infinite_neg x :=
imp_not_comm.mp not_infinite_pos_of_infinite_neg

lemma infinite_neg_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → infinite_neg (-x) :=
λ hp r, neg_lt.mp (hp (-r))

lemma infinite_pos_neg_of_infinite_neg {x : ℝ*} : infinite_neg x → infinite_pos (-x) :=
λ hp r, lt_neg.mp (hp (-r))

lemma infinite_pos_iff_infinite_neg_neg {x : ℝ*} : infinite_pos x ↔ infinite_neg (-x) :=
⟨ infinite_neg_neg_of_infinite_pos, λ hin, neg_neg x ▸ infinite_pos_neg_of_infinite_neg hin ⟩

lemma infinite_neg_iff_infinite_pos_neg {x : ℝ*} : infinite_neg x ↔ infinite_pos (-x) :=
⟨ infinite_pos_neg_of_infinite_neg, λ hin, neg_neg x ▸ infinite_neg_neg_of_infinite_pos hin ⟩

lemma infinite_iff_infinite_neg {x : ℝ*} : infinite x ↔ infinite (-x) :=
⟨ λ hi, or.cases_on hi
  (λ hip, or.inr (infinite_neg_neg_of_infinite_pos hip))
  (λ hin, or.inl (infinite_pos_neg_of_infinite_neg hin)),
 λ hi, or.cases_on hi
  (λ hipn, or.inr (infinite_neg_iff_infinite_pos_neg.mpr hipn))
  (λ hinp, or.inl (infinite_pos_iff_infinite_neg_neg.mpr hinp))⟩

lemma not_infinite_of_infinitesimal {x : ℝ*} : infinitesimal x → ¬ infinite x :=
λ hi hI, have hi' : _ := (hi 2 zero_lt_two), or.dcases_on hI
  (λ hip, have hip' : _ := hip 2, not_lt_of_lt hip' (by convert hi'.2; exact (zero_add 2).symm))
  (λ hin, have hin' : _ := hin (-2), not_lt_of_lt hin' (by convert hi'.1; exact (zero_sub 2).symm))

lemma not_infinitesimal_of_infinite {x : ℝ*} : infinite x → ¬ infinitesimal x :=
imp_not_comm.mp not_infinite_of_infinitesimal

lemma not_infinitesimal_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬ infinitesimal x :=
λ hp, not_infinitesimal_of_infinite (or.inl hp)

lemma not_infinitesimal_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬ infinitesimal x :=
λ hn, not_infinitesimal_of_infinite (or.inr hn)

lemma infinite_pos_iff_infinite_and_pos {x : ℝ*} : infinite_pos x ↔ (infinite x ∧ 0 < x) :=
⟨ λ hip, ⟨or.inl hip, hip 0⟩,
  λ ⟨hi, hp⟩, hi.cases_on (λ hip, hip) (λ hin, false.elim (not_lt_of_lt hp (hin 0))) ⟩

lemma infinite_neg_iff_infinite_and_neg {x : ℝ*} : infinite_neg x ↔ (infinite x ∧ x < 0) :=
⟨ λ hip, ⟨or.inr hip, hip 0⟩,
  λ ⟨hi, hp⟩, hi.cases_on (λ hin, false.elim (not_lt_of_lt hp (hin 0))) (λ hip, hip) ⟩

lemma infinite_pos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : infinite_pos x ↔ infinite x :=
by rw [infinite_pos_iff_infinite_and_pos]; exact ⟨λ hI, hI.1, λ hI, ⟨hI, hp⟩⟩

lemma infinite_pos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : infinite_pos x ↔ infinite x :=
or.cases_on (lt_or_eq_of_le hp) (infinite_pos_iff_infinite_of_pos)
  (λ h, by rw h.symm; exact
  ⟨λ hIP, false.elim (not_infinite_zero (or.inl hIP)), λ hI, false.elim (not_infinite_zero hI)⟩)

lemma infinite_neg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : infinite_neg x ↔ infinite x :=
by rw [infinite_neg_iff_infinite_and_neg]; exact ⟨λ hI, hI.1, λ hI, ⟨hI, hn⟩⟩

lemma infinite_pos_abs_iff_infinite_abs {x : ℝ*} : infinite_pos (abs x) ↔ infinite (abs x) :=
infinite_pos_iff_infinite_of_nonneg (abs_nonneg _)

lemma infinite_iff_infinite_pos_abs {x : ℝ*} : infinite x ↔ infinite_pos (abs x) :=
⟨ λ hi d, or.cases_on hi
   (λ hip, by rw [abs_of_pos (hip 0)]; exact hip d)
   (λ hin, by rw [abs_of_neg (hin 0)]; exact lt_neg.mp (hin (-d))),
  λ hipa, by { rcases (lt_trichotomy x 0) with h | h | h,
    { exact or.inr (infinite_neg_iff_infinite_pos_neg.mpr (by rwa abs_of_neg h at hipa)) },
    { exact false.elim (ne_zero_of_infinite (or.inl (by rw [h]; rwa [h, abs_zero] at hipa)) h) },
    { exact or.inl (by rwa abs_of_pos h at hipa) } } ⟩

lemma infinite_iff_infinite_abs {x : ℝ*} : infinite x ↔ infinite (abs x) :=
by rw [←infinite_pos_iff_infinite_of_nonneg (abs_nonneg _), infinite_iff_infinite_pos_abs]

lemma infinite_iff_abs_lt_abs {x : ℝ*} : infinite x ↔ ∀ r : ℝ, (abs r : ℝ*) < abs x :=
⟨ λ hI r, (coe_abs r) ▸ infinite_iff_infinite_pos_abs.mp hI (abs r),
  λ hR, or.cases_on (max_choice x (-x))
  (λ h, or.inl $ λ r, lt_of_le_of_lt (le_abs_self _) (h ▸ (hR r)))
  (λ h, or.inr $ λ r, neg_lt_neg_iff.mp $ lt_of_le_of_lt (neg_le_abs_self _) (h ▸ (hR r)))⟩

lemma infinite_pos_add_not_infinite_neg {x y : ℝ*} :
  infinite_pos x → ¬ infinite_neg y → infinite_pos (x + y) :=
begin
  intros hip hnin r,
  cases not_forall.mp hnin with r₂ hr₂,
  convert add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1,
  simp
end

lemma not_infinite_neg_add_infinite_pos {x y : ℝ*} :
  ¬ infinite_neg x → infinite_pos y → infinite_pos (x + y) :=
λ hx hy, by rw [add_comm]; exact infinite_pos_add_not_infinite_neg hy hx

lemma infinite_neg_add_not_infinite_pos {x y : ℝ*} :
  infinite_neg x → ¬ infinite_pos y → infinite_neg (x + y) :=
by rw [@infinite_neg_iff_infinite_pos_neg x, @infinite_pos_iff_infinite_neg_neg y,
       @infinite_neg_iff_infinite_pos_neg (x + y), neg_add];
exact infinite_pos_add_not_infinite_neg

lemma not_infinite_pos_add_infinite_neg {x y : ℝ*} :
  ¬ infinite_pos x → infinite_neg y → infinite_neg (x + y) :=
λ hx hy, by rw [add_comm]; exact infinite_neg_add_not_infinite_pos hy hx

lemma infinite_pos_add_infinite_pos {x y : ℝ*} :
  infinite_pos x → infinite_pos y → infinite_pos (x + y) :=
λ hx hy, infinite_pos_add_not_infinite_neg hx (not_infinite_neg_of_infinite_pos hy)

lemma infinite_neg_add_infinite_neg {x y : ℝ*} :
  infinite_neg x → infinite_neg y → infinite_neg (x + y) :=
λ hx hy, infinite_neg_add_not_infinite_pos hx (not_infinite_pos_of_infinite_neg hy)

lemma infinite_pos_add_not_infinite {x y : ℝ*} :
  infinite_pos x → ¬ infinite y → infinite_pos (x + y) :=
λ hx hy, infinite_pos_add_not_infinite_neg hx (not_or_distrib.mp hy).2

lemma infinite_neg_add_not_infinite {x y : ℝ*} :
  infinite_neg x → ¬ infinite y → infinite_neg (x + y) :=
λ hx hy, infinite_neg_add_not_infinite_pos hx (not_or_distrib.mp hy).1

theorem infinite_pos_of_tendsto_top {f : ℕ → ℝ} (hf : tendsto f at_top at_top) :
  infinite_pos (of_seq f) :=
λ r, have hf' : _ := tendsto_at_top_at_top.mp hf,
Exists.cases_on (hf' (r + 1)) $ λ i hi,
  have hi' : ∀ (a : ℕ), f a < (r + 1) → a < i :=
    λ a, by rw [←not_le, ←not_le]; exact not_imp_not.mpr (hi a),
  have hS : {a : ℕ | r < f a}ᶜ ⊆ {a : ℕ | a ≤ i} :=
    by simp only [set.compl_set_of, not_lt];
    exact λ a har, le_of_lt (hi' a (lt_of_le_of_lt har (lt_add_one _))),
  germ.coe_lt.2 $ mem_hyperfilter_of_finite_compl $
  (set.finite_le_nat _).subset hS

theorem infinite_neg_of_tendsto_bot {f : ℕ → ℝ} (hf : tendsto f at_top at_bot) :
  infinite_neg (of_seq f) :=
λ r, have hf' : _ := tendsto_at_top_at_bot.mp hf,
Exists.cases_on (hf' (r - 1)) $ λ i hi,
  have hi' : ∀ (a : ℕ), r - 1 < f a → a < i :=
    λ a, by rw [←not_le, ←not_le]; exact not_imp_not.mpr (hi a),
  have hS : {a : ℕ | f a < r}ᶜ ⊆ {a : ℕ | a ≤ i} :=
    by simp only [set.compl_set_of, not_lt];
    exact λ a har, le_of_lt (hi' a (lt_of_lt_of_le (sub_one_lt _) har)),
  germ.coe_lt.2 $ mem_hyperfilter_of_finite_compl $
  (set.finite_le_nat _).subset hS

lemma not_infinite_neg {x : ℝ*} : ¬ infinite x → ¬ infinite (-x) :=
not_imp_not.mpr infinite_iff_infinite_neg.mpr

lemma not_infinite_add {x y : ℝ*} (hx : ¬ infinite x) (hy : ¬ infinite y) :
  ¬ infinite (x + y) :=
have hx' : _ := exists_st_of_not_infinite hx, have hy' : _ := exists_st_of_not_infinite hy,
Exists.cases_on hx' $ Exists.cases_on hy' $
λ r hr s hs, not_infinite_of_exists_st $ ⟨s + r, is_st_add hs hr⟩

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬ infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
⟨ λ hni,
Exists.dcases_on (not_forall.mp (not_or_distrib.mp hni).1) $
Exists.dcases_on (not_forall.mp (not_or_distrib.mp hni).2) $ λ r hr s hs,
by rw [not_lt] at hr hs; exact ⟨r - 1, s + 1,
  ⟨ lt_of_lt_of_le (by rw sub_eq_add_neg; norm_num) hr,
    lt_of_le_of_lt hs (by norm_num)⟩ ⟩,
λ hrs, Exists.dcases_on hrs $ λ r hr, Exists.dcases_on hr $ λ s hs,
  not_or_distrib.mpr ⟨not_forall.mpr ⟨s, lt_asymm (hs.2)⟩, not_forall.mpr ⟨r, lt_asymm (hs.1) ⟩⟩⟩

theorem not_infinite_real (r : ℝ) : ¬ infinite r := by rw not_infinite_iff_exist_lt_gt; exact
⟨ r - 1, r + 1, coe_lt_coe.2 $ sub_one_lt r, coe_lt_coe.2 $ lt_add_one r⟩

theorem not_real_of_infinite {x : ℝ*} : infinite x → ∀ r : ℝ, x ≠ r :=
λ hi r hr,  not_infinite_real r $ @eq.subst _ infinite _ _ hr hi

/-!
### Facts about `st` that require some infinite machinery
-/

private lemma is_st_mul' {x y : ℝ*} {r s : ℝ} (hxr : is_st x r) (hys : is_st y s) (hs : s ≠ 0) :
  is_st (x * y) (r * s) :=
have hxr' : _ := is_st_iff_abs_sub_lt_delta.mp hxr,
have hys' : _ := is_st_iff_abs_sub_lt_delta.mp hys,
have h : _ := not_infinite_iff_exist_lt_gt.mp $ not_imp_not.mpr infinite_iff_infinite_abs.mpr $
not_infinite_of_exists_st ⟨r, hxr⟩,
Exists.cases_on h $ λ u h', Exists.cases_on h' $ λ t ⟨hu, ht⟩,
is_st_iff_abs_sub_lt_delta.mpr $ λ d hd,
   calc abs (x * y - r * s)
      = abs (x * (y - s) + (x - r) * s) :
        by rw [mul_sub, sub_mul, add_sub, sub_add_cancel]
  ... ≤ abs (x * (y - s)) + abs ((x - r) * s) : abs_add _ _
  ... ≤ abs x * abs (y - s) + abs (x - r) * abs s : by simp only [abs_mul]
  ... ≤ abs x * ((d / t) / 2 : ℝ) + ((d / abs s) / 2 : ℝ) * abs s : add_le_add
        (mul_le_mul_of_nonneg_left (le_of_lt $ hys' _ $ half_pos $ div_pos hd $
          coe_pos.1 $ lt_of_le_of_lt (abs_nonneg x) ht) $ abs_nonneg _)
        (mul_le_mul_of_nonneg_right (le_of_lt $ hxr' _ $ half_pos $ div_pos hd $
          abs_pos.2 hs) $ abs_nonneg _)
  ... = (d / 2 * (abs x / t) + d / 2 : ℝ*) : by
      { push_cast [-filter.germ.const_div], -- TODO: Why wasn't `hyperreal.coe_div` used?
        have : (abs s : ℝ*) ≠ 0, by simpa,
        have : (2 : ℝ*) ≠ 0 := two_ne_zero,
        field_simp [*, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm] }
  ... < (d / 2 * 1 + d / 2 : ℝ*) :
        add_lt_add_right (mul_lt_mul_of_pos_left
        ((div_lt_one $ lt_of_le_of_lt (abs_nonneg x) ht).mpr ht) $
        half_pos $ coe_pos.2 hd) _
  ... = (d : ℝ*) : by rw [mul_one, add_halves]

lemma is_st_mul {x y : ℝ*} {r s : ℝ} (hxr : is_st x r) (hys : is_st y s) :
  is_st (x * y) (r * s) :=
have h : _ := not_infinite_iff_exist_lt_gt.mp $
  not_imp_not.mpr infinite_iff_infinite_abs.mpr $ not_infinite_of_exists_st ⟨r, hxr⟩,
Exists.cases_on h $ λ u h', Exists.cases_on h' $ λ t ⟨hu, ht⟩,
begin
  by_cases hs : s = 0,
  { apply is_st_iff_abs_sub_lt_delta.mpr, intros d hd,
    have hys' : _ := is_st_iff_abs_sub_lt_delta.mp hys (d / t)
      (div_pos hd (coe_pos.1 (lt_of_le_of_lt (abs_nonneg x) ht))),
    rw [hs, coe_zero, sub_zero] at hys',
    rw [hs, mul_zero, coe_zero, sub_zero, abs_mul, mul_comm,
        ←div_mul_cancel (d : ℝ*) (ne_of_gt (lt_of_le_of_lt (abs_nonneg x) ht)),
        ←coe_div],
    exact mul_lt_mul'' hys' ht (abs_nonneg _) (abs_nonneg _) },
  exact is_st_mul' hxr hys hs,
end

--AN INFINITE LEMMA THAT REQUIRES SOME MORE ST MACHINERY
lemma not_infinite_mul {x y : ℝ*} (hx : ¬ infinite x) (hy : ¬ infinite y) :
  ¬ infinite (x * y) :=
have hx' : _ := exists_st_of_not_infinite hx, have hy' : _ := exists_st_of_not_infinite hy,
Exists.cases_on hx' $ Exists.cases_on hy' $ λ r hr s hs, not_infinite_of_exists_st $
⟨s * r, is_st_mul hs hr⟩
---

lemma st_add {x y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) : st (x + y) = st x + st y :=
have hx' : _ := is_st_st' hx,
have hy' : _ := is_st_st' hy,
have hxy : _ := is_st_st' (not_infinite_add hx hy),
have hxy' : _ := is_st_add hx' hy',
is_st_unique hxy hxy'

lemma st_neg (x : ℝ*) : st (-x) = - st x :=
if h : infinite x
then by rw [st_infinite h, st_infinite (infinite_iff_infinite_neg.mp h), neg_zero]
else is_st_unique (is_st_st' (not_infinite_neg h)) (is_st_neg (is_st_st' h))

lemma st_mul {x y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) : st (x * y) = (st x) * (st y) :=
have hx' : _ := is_st_st' hx,
have hy' : _ := is_st_st' hy,
have hxy : _ := is_st_st' (not_infinite_mul hx hy),
have hxy' : _ := is_st_mul hx' hy',
is_st_unique hxy hxy'

/-!
### Basic lemmas about infinitesimal
-/

theorem infinitesimal_def {x : ℝ*} :
  infinitesimal x ↔ (∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r) :=
⟨ λ hi r hr, by { convert (hi r hr); simp },
  λ hi d hd, by { convert (hi d hd); simp } ⟩

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
λ hi r hr, ((infinitesimal_def.mp hi) r hr).2

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x :=
λ hi r hr, ((infinitesimal_def.mp hi) r hr).1

theorem gt_of_neg_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r < 0 → ↑r < x :=
λ hi r hr, by convert ((infinitesimal_def.mp hi) (-r) (neg_pos.mpr hr)).1;
exact (neg_neg ↑r).symm

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} :
  infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → abs x < abs r :=
⟨ λ hi r hr, abs_lt.mpr (by rw ←coe_abs;
  exact infinitesimal_def.mp hi (abs r) (abs_pos.2 hr)),
  λ hR, infinitesimal_def.mpr $ λ r hr, abs_lt.mp $
  (abs_of_pos $ coe_pos.2 hr) ▸ hR r $ ne_of_gt hr ⟩

lemma infinitesimal_zero : infinitesimal 0 := is_st_refl_real 0

lemma zero_of_infinitesimal_real {r : ℝ} : infinitesimal r → r = 0 := eq_of_is_st_real

lemma zero_iff_infinitesimal_real {r : ℝ} : infinitesimal r ↔ r = 0 :=
⟨zero_of_infinitesimal_real, λ hr, by rw hr; exact infinitesimal_zero⟩

lemma infinitesimal_add {x y : ℝ*} (hx : infinitesimal x) (hy : infinitesimal y) :
  infinitesimal (x + y) :=
by simpa only [add_zero] using is_st_add hx hy

lemma infinitesimal_neg {x : ℝ*} (hx : infinitesimal x) : infinitesimal (-x) :=
by simpa only [neg_zero] using is_st_neg hx

lemma infinitesimal_neg_iff {x : ℝ*} : infinitesimal x ↔ infinitesimal (-x) :=
⟨infinitesimal_neg, λ h, (neg_neg x) ▸ @infinitesimal_neg (-x) h⟩

lemma infinitesimal_mul {x y : ℝ*} (hx : infinitesimal x) (hy : infinitesimal y) :
  infinitesimal (x * y) :=
by simpa only [mul_zero] using is_st_mul hx hy

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} :
  tendsto f at_top (𝓝 0) → infinitesimal (of_seq f) :=
λ hf d hd, by rw [sub_eq_add_neg, ←coe_neg, ←coe_add, ←coe_add, zero_add, zero_add];
exact ⟨neg_lt_of_tendsto_zero_of_pos hf hd, lt_of_tendsto_zero_of_pos hf hd⟩

theorem infinitesimal_epsilon : infinitesimal ε :=
infinitesimal_of_tendsto_zero tendsto_inverse_at_top_nhds_0_nat

lemma not_real_of_infinitesimal_ne_zero (x : ℝ*) :
  infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
λ hi hx r hr, hx $ hr.trans $ coe_eq_zero.2 $
is_st_unique (hr.symm ▸ is_st_refl_real r : is_st x r) hi

theorem infinitesimal_sub_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : infinitesimal (x - r) :=
show is_st (x - r) 0,
by { rw [sub_eq_add_neg, ← add_neg_self r], exact is_st_add hxr (is_st_refl_real (-r)) }

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬infinite x) : infinitesimal (x - st x) :=
infinitesimal_sub_is_st $ is_st_st' hx

lemma infinite_pos_iff_infinitesimal_inv_pos {x : ℝ*} :
  infinite_pos x ↔ (infinitesimal x⁻¹ ∧ 0 < x⁻¹) :=
⟨ λ hip, ⟨ infinitesimal_def.mpr $ λ r hr,
  ⟨ lt_trans (coe_lt_coe.2 (neg_neg_of_pos hr)) (inv_pos.2 (hip 0)),
    (inv_lt (coe_lt_coe.2 hr) (hip 0)).mp (by convert hip r⁻¹) ⟩,
  inv_pos.2 $ hip 0 ⟩,
  λ ⟨hi, hp⟩ r, @classical.by_cases (r = 0) (↑r < x) (λ h, eq.substr h (inv_pos.mp hp)) $
  λ h, lt_of_le_of_lt (coe_le_coe.2 (le_abs_self r))
  ((inv_lt_inv (inv_pos.mp hp) (coe_lt_coe.2 (abs_pos.2 h))).mp
  ((infinitesimal_def.mp hi) ((abs r)⁻¹) (inv_pos.2 (abs_pos.2 h))).2) ⟩

lemma infinite_neg_iff_infinitesimal_inv_neg {x : ℝ*} :
  infinite_neg x ↔ (infinitesimal x⁻¹ ∧ x⁻¹ < 0) :=
⟨ λ hin, have hin' : _ := infinite_pos_iff_infinitesimal_inv_pos.mp
  (infinite_pos_neg_of_infinite_neg hin),
  by rwa [infinitesimal_neg_iff, ←neg_pos, neg_inv],
  λ hin, by rwa [←neg_pos, infinitesimal_neg_iff, neg_inv,
    ←infinite_pos_iff_infinitesimal_inv_pos, ←infinite_neg_iff_infinite_pos_neg] at hin ⟩

theorem infinitesimal_inv_of_infinite {x : ℝ*} : infinite x → infinitesimal x⁻¹ :=
λ hi, or.cases_on hi
 (λ hip, (infinite_pos_iff_infinitesimal_inv_pos.mp hip).1)
 (λ hin, (infinite_neg_iff_infinitesimal_inv_neg.mp hin).1)

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : infinitesimal x⁻¹ ) :
  infinite x :=
begin
  cases (lt_or_gt_of_ne h0) with hn hp,
  { exact or.inr (infinite_neg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩) },
  { exact or.inl (infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩) }
end

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : infinite x ↔ infinitesimal x⁻¹ :=
⟨ infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0 ⟩

lemma infinitesimal_pos_iff_infinite_pos_inv {x : ℝ*} :
  infinite_pos x⁻¹ ↔ (infinitesimal x ∧ 0 < x) :=
by convert infinite_pos_iff_infinitesimal_inv_pos; simp only [inv_inv']

lemma infinitesimal_neg_iff_infinite_neg_inv {x : ℝ*} :
  infinite_neg x⁻¹ ↔ (infinitesimal x ∧ x < 0) :=
by convert infinite_neg_iff_infinitesimal_inv_neg; simp only [inv_inv']

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : infinitesimal x ↔ infinite x⁻¹ :=
by convert (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm; simp only [inv_inv']

/-!
### `st` stuff that requires infinitesimal machinery
-/

theorem is_st_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : tendsto f at_top (𝓝 r)) :
  is_st (of_seq f) r :=
have hg : tendsto (λ n, f n - r) at_top (𝓝 0) :=
  (sub_self r) ▸ (hf.sub tendsto_const_nhds),
by rw [←(zero_add r), ←(sub_add_cancel f (λ n, r))];
exact is_st_add (infinitesimal_of_tendsto_zero hg) (is_st_refl_real r)

lemma is_st_inv {x : ℝ*} {r : ℝ} (hi : ¬ infinitesimal x) : is_st x r → is_st x⁻¹ r⁻¹ :=
λ hxr, have h : x ≠ 0 := (λ h, hi (h.symm ▸ infinitesimal_zero)),
have H : _ := exists_st_of_not_infinite $ not_imp_not.mpr (infinitesimal_iff_infinite_inv h).mpr hi,
Exists.cases_on H $ λ s hs,
have H' : is_st 1 (r * s) := mul_inv_cancel h ▸ is_st_mul hxr hs,
have H'' : s = r⁻¹ := one_div r ▸ eq_one_div_of_mul_eq_one (eq_of_is_st_real H').symm,
H'' ▸ hs

lemma st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ :=
begin
  by_cases h0 : x = 0,
  rw [h0, inv_zero, ←coe_zero, st_id_real, inv_zero],
  by_cases h1 : infinitesimal x,
  rw [st_infinite ((infinitesimal_iff_infinite_inv h0).mp h1), st_of_is_st h1, inv_zero],
  by_cases h2 : infinite x,
  rw [st_of_is_st (infinitesimal_inv_of_infinite h2), st_infinite h2, inv_zero],
  exact st_of_is_st (is_st_inv h1 (is_st_st' h2)),
end

/-!
### Infinite stuff that requires infinitesimal machinery
-/

lemma infinite_pos_omega : infinite_pos ω :=
infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

lemma infinite_omega : infinite ω :=
(infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

lemma infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos {x y : ℝ*} :
  infinite_pos x → ¬ infinitesimal y → 0 < y → infinite_pos (x * y) :=
λ hx hy₁ hy₂ r, have hy₁' : _ := not_forall.mp (by rw infinitesimal_def at hy₁; exact hy₁),
Exists.dcases_on hy₁' $ λ r₁ hy₁'',
have hyr : _ := by rw [not_imp, ←abs_lt, not_lt, abs_of_pos hy₂] at hy₁''; exact hy₁'',
by rw [←div_mul_cancel r (ne_of_gt hyr.1), coe_mul];
exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))

lemma infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos {x y : ℝ*} :
  ¬ infinitesimal x → 0 < x → infinite_pos y → infinite_pos (x * y) :=
λ hx hp hy, by rw mul_comm; exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hy hx hp

lemma infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg {x y : ℝ*} :
  infinite_neg x → ¬ infinitesimal y → y < 0 → infinite_pos (x * y) :=
by rw [infinite_neg_iff_infinite_pos_neg, ←neg_pos, ←neg_mul_neg, infinitesimal_neg_iff];
exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

lemma infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg {x y : ℝ*} :
  ¬ infinitesimal x → x < 0 → infinite_neg y → infinite_pos (x * y) :=
λ hx hp hy, by rw mul_comm; exact infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hy hx hp

lemma infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg {x y : ℝ*} :
  infinite_pos x → ¬ infinitesimal y → y < 0 → infinite_neg (x * y) :=
by rw [infinite_neg_iff_infinite_pos_neg, ←neg_pos, neg_mul_eq_mul_neg, infinitesimal_neg_iff];
exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

lemma infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos {x y : ℝ*} :
  ¬ infinitesimal x → x < 0 → infinite_pos y → infinite_neg (x * y) :=
λ hx hp hy, by rw mul_comm; exact infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hy hx hp

lemma infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos {x y : ℝ*} :
  infinite_neg x → ¬ infinitesimal y → 0 < y → infinite_neg (x * y) :=
by rw [infinite_neg_iff_infinite_pos_neg, infinite_neg_iff_infinite_pos_neg, neg_mul_eq_neg_mul];
exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

lemma infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg {x y : ℝ*} :
  ¬ infinitesimal x → 0 < x → infinite_neg y → infinite_neg (x * y) :=
λ hx hp hy, by rw mul_comm; exact infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hy hx hp

lemma infinite_pos_mul_infinite_pos {x y : ℝ*} :
  infinite_pos x → infinite_pos y → infinite_pos (x * y) :=
λ hx hy, infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

lemma infinite_neg_mul_infinite_neg {x y : ℝ*} :
  infinite_neg x → infinite_neg y → infinite_pos (x * y) :=
λ hx hy, infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg
hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

lemma infinite_pos_mul_infinite_neg {x y : ℝ*} :
  infinite_pos x → infinite_neg y → infinite_neg (x * y) :=
λ hx hy, infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg
hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

lemma infinite_neg_mul_infinite_pos {x y : ℝ*} :
  infinite_neg x → infinite_pos y → infinite_neg (x * y) :=
λ hx hy, infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos
hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

lemma infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} :
  infinite x → ¬ infinitesimal y → infinite (x * y) :=
λ hx hy, have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne (λ H0, hy (eq.substr H0 (is_st_refl_real 0))),
or.dcases_on hx
  (or.dcases_on h0
    (λ H0 Hx, or.inr (infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hx hy H0))
    (λ H0 Hx, or.inl (infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hx hy H0)))
  (or.dcases_on h0
    (λ H0 Hx, or.inl (infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hx hy H0))
    (λ H0 Hx, or.inr (infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hx hy H0)))

lemma infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} :
  ¬ infinitesimal x → infinite y → infinite (x * y) :=
λ hx hy, by rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

lemma infinite_mul_infinite {x y : ℝ*} : infinite x → infinite y → infinite (x * y) :=
λ hx hy, infinite_mul_of_infinite_not_infinitesimal hx (not_infinitesimal_of_infinite hy)

end hyperreal
