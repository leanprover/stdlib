/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import data.set.intervals.basic
/-!

# Upper / lower bounds

In this file we define:

* `upper_bounds`, `lower_bounds` : the set of upper bounds (resp., lower bounds) of a set;
* `bdd_above s`, `bdd_below s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `is_least s a`, `is_greatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `is_lub s a`, `is_glb s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.

We also prove various lemmas about monotonicity, behaviour under `∪`, `∩`, `insert`, and provide
formulas for `∅`, `univ`, and intervals.
-/
open set

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section
variables [preorder α] [preorder β] {s t : set α} {a b : α}

/-!
### Definitions
-/

/-- The set of upper bounds of a set. -/
def upper_bounds (s : set α) : set α := { x | ∀ ⦃a⦄, a ∈ s →  a ≤ x }
/-- The set of lower bounds of a set. -/
def lower_bounds (s : set α) : set α := { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }

/-- A set is bounded above if there exists an upper bound. -/
def bdd_above (s : set α) := (upper_bounds s).nonempty
/-- A set is bounded below if there exists a lower bound. -/
def bdd_below (s : set α) := (lower_bounds s).nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
def is_least (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ lower_bounds s
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists -/
def is_greatest (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ upper_bounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def is_lub (s : set α) : α → Prop := is_least (upper_bounds s)
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def is_glb (s : set α) : α → Prop := is_greatest (lower_bounds s)

lemma mem_upper_bounds : a ∈ upper_bounds s ↔ ∀ x ∈ s, x ≤ a := iff.rfl

lemma mem_lower_bounds : a ∈ lower_bounds s ↔ ∀ x ∈ s, a ≤ x := iff.rfl

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bdd_above_iff`. -/
lemma not_bdd_above_iff' : ¬bdd_above s ↔ ∀ x, ∃ y ∈ s, ¬(y ≤ x) :=
by simp [bdd_above, upper_bounds, set.nonempty]

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bdd_below_iff`. -/
lemma not_bdd_below_iff' : ¬bdd_below s ↔ ∀ x, ∃ y ∈ s, ¬(x ≤ y) :=
@not_bdd_above_iff' (order_dual α) _ _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bdd_above_iff'`. -/
lemma not_bdd_above_iff {α : Type*} [linear_order α] {s : set α} :
  ¬bdd_above s ↔ ∀ x, ∃ y ∈ s, x < y :=
by simp only [not_bdd_above_iff', not_le]

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bdd_below_iff'`. -/
lemma not_bdd_below_iff {α : Type*} [linear_order α] {s : set α} :
  ¬bdd_below s ↔ ∀ x, ∃ y ∈ s, y < x :=
@not_bdd_above_iff (order_dual α) _ _

/-!
### Monotonicity
-/

lemma upper_bounds_mono_set ⦃s t : set α⦄ (hst : s ⊆ t) :
  upper_bounds t ⊆ upper_bounds s :=
λ b hb x h, hb $ hst h

lemma lower_bounds_mono_set ⦃s t : set α⦄ (hst : s ⊆ t) :
  lower_bounds t ⊆ lower_bounds s :=
λ b hb x h, hb $ hst h

lemma upper_bounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ upper_bounds s → b ∈ upper_bounds s :=
λ ha x h, le_trans (ha h) hab

lemma lower_bounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : b ∈ lower_bounds s → a ∈ lower_bounds s :=
λ hb x h, le_trans hab (hb h)

lemma upper_bounds_mono ⦃s t : set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
  a ∈ upper_bounds t → b ∈ upper_bounds s :=
λ ha, upper_bounds_mono_set hst $ upper_bounds_mono_mem hab ha

lemma lower_bounds_mono ⦃s t : set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
  b ∈ lower_bounds t → a ∈ lower_bounds s :=
λ hb, lower_bounds_mono_set hst $ lower_bounds_mono_mem hab hb

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
lemma bdd_above.mono ⦃s t : set α⦄ (h : s ⊆ t) : bdd_above t → bdd_above s :=
nonempty.mono $ upper_bounds_mono_set h

/-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/
lemma bdd_below.mono ⦃s t : set α⦄ (h : s ⊆ t) : bdd_below t → bdd_below s :=
nonempty.mono $ lower_bounds_mono_set h

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
lemma is_lub.of_subset_of_superset {s t p : set α} (hs : is_lub s a) (hp : is_lub p a)
  (hst : s ⊆ t) (htp : t ⊆ p) : is_lub t a :=
⟨upper_bounds_mono_set htp hp.1, lower_bounds_mono_set (upper_bounds_mono_set hst) hs.2⟩

/-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower bound for any
set `t`, `s ⊆ t ⊆ p`. -/
lemma is_glb.of_subset_of_superset {s t p : set α} (hs : is_glb s a) (hp : is_glb p a)
  (hst : s ⊆ t) (htp : t ⊆ p) : is_glb t a :=
@is_lub.of_subset_of_superset (order_dual α) _ a s t p hs hp hst htp

lemma is_least.mono (ha : is_least s a) (hb : is_least t b) (hst : s ⊆ t) : b ≤ a :=
hb.2 (hst ha.1)

lemma is_greatest.mono (ha : is_greatest s a) (hb : is_greatest t b) (hst : s ⊆ t) : a ≤ b :=
hb.2 (hst ha.1)

lemma is_lub.mono (ha : is_lub s a) (hb : is_lub t b) (hst : s ⊆ t) : a ≤ b :=
hb.mono ha $ upper_bounds_mono_set hst

lemma is_glb.mono (ha : is_glb s a) (hb : is_glb t b) (hst : s ⊆ t) : b ≤ a :=
hb.mono ha $ lower_bounds_mono_set hst

/-!
### Conversions
-/

lemma is_least.is_glb (h : is_least s a) : is_glb s a := ⟨h.2, λ b hb, hb h.1⟩

lemma is_greatest.is_lub (h : is_greatest s a) : is_lub s a := ⟨h.2, λ b hb, hb h.1⟩

lemma is_lub.upper_bounds_eq (h : is_lub s a) : upper_bounds s = Ici a :=
set.ext $ λ b, ⟨λ hb, h.2 hb, λ hb, upper_bounds_mono_mem hb h.1⟩

lemma is_glb.lower_bounds_eq (h : is_glb s a) : lower_bounds s = Iic a :=
@is_lub.upper_bounds_eq (order_dual α) _ _ _ h

lemma is_least.lower_bounds_eq (h : is_least s a) : lower_bounds s = Iic a :=
h.is_glb.lower_bounds_eq

lemma is_greatest.upper_bounds_eq (h : is_greatest s a) : upper_bounds s = Ici a :=
h.is_lub.upper_bounds_eq

lemma is_lub_le_iff (h : is_lub s a) : a ≤ b ↔ b ∈ upper_bounds s :=
by { rw h.upper_bounds_eq, refl }

lemma le_is_glb_iff (h : is_glb s a) : b ≤ a ↔ b ∈ lower_bounds s :=
by { rw h.lower_bounds_eq, refl }

/-- If `s` has a least upper bound, then it is bounded above. -/
lemma is_lub.bdd_above (h : is_lub s a) : bdd_above s := ⟨a, h.1⟩

/-- If `s` has a greatest lower bound, then it is bounded below. -/
lemma is_glb.bdd_below (h : is_glb s a) : bdd_below s := ⟨a, h.1⟩

/-- If `s` has a greatest element, then it is bounded above. -/
lemma is_greatest.bdd_above (h : is_greatest s a) : bdd_above s := ⟨a, h.2⟩

/-- If `s` has a least element, then it is bounded below. -/
lemma is_least.bdd_below (h : is_least s a) : bdd_below s := ⟨a, h.2⟩

lemma is_least.nonempty (h : is_least s a) : s.nonempty := ⟨a, h.1⟩

lemma is_greatest.nonempty (h : is_greatest s a) : s.nonempty := ⟨a, h.1⟩

/-!
### Union and intersection
-/

@[simp] lemma upper_bounds_union : upper_bounds (s ∪ t) = upper_bounds s ∩ upper_bounds t :=
subset.antisymm
  (λ b hb, ⟨λ x hx, hb (or.inl hx), λ x hx, hb (or.inr hx)⟩)
  (λ b hb x hx, hx.elim (λ hs, hb.1 hs) (λ ht, hb.2 ht))

@[simp] lemma lower_bounds_union : lower_bounds (s ∪ t) = lower_bounds s ∩ lower_bounds t :=
@upper_bounds_union (order_dual α) _ s t

lemma union_upper_bounds_subset_upper_bounds_inter :
  upper_bounds s ∪ upper_bounds t ⊆ upper_bounds (s ∩ t) :=
union_subset
  (upper_bounds_mono_set $ inter_subset_left _ _)
  (upper_bounds_mono_set $ inter_subset_right _ _)

lemma union_lower_bounds_subset_lower_bounds_inter :
  lower_bounds s ∪ lower_bounds t ⊆ lower_bounds (s ∩ t) :=
@union_upper_bounds_subset_upper_bounds_inter (order_dual α) _ s t

lemma is_least_union_iff {a : α} {s t : set α} :
  is_least (s ∪ t) a ↔ (is_least s a ∧ a ∈ lower_bounds t ∨ a ∈ lower_bounds s ∧ is_least t a) :=
by simp [is_least, lower_bounds_union, or_and_distrib_right, and_comm (a ∈ t), and_assoc]

lemma is_greatest_union_iff :
  is_greatest (s ∪ t) a ↔ (is_greatest s a ∧ a ∈ upper_bounds t ∨
    a ∈ upper_bounds s ∧ is_greatest t a) :=
@is_least_union_iff (order_dual α) _ a s t

/-- If `s` is bounded, then so is `s ∩ t` -/
lemma bdd_above.inter_of_left (h : bdd_above s) : bdd_above (s ∩ t) :=
h.mono $ inter_subset_left s t

/-- If `t` is bounded, then so is `s ∩ t` -/
lemma bdd_above.inter_of_right (h : bdd_above t) : bdd_above (s ∩ t) :=
h.mono $ inter_subset_right s t

/-- If `s` is bounded, then so is `s ∩ t` -/
lemma bdd_below.inter_of_left (h : bdd_below s) : bdd_below (s ∩ t) :=
h.mono $ inter_subset_left s t

/-- If `t` is bounded, then so is `s ∩ t` -/
lemma bdd_below.inter_of_right (h : bdd_below t) : bdd_below (s ∩ t) :=
h.mono $ inter_subset_right s t

/-- If `s` and `t` are bounded above sets in a `semilattice_sup`, then so is `s ∪ t`. -/
lemma bdd_above.union [semilattice_sup γ] {s t : set γ} :
  bdd_above s → bdd_above t → bdd_above (s ∪ t) :=
begin
  rintros ⟨bs, hs⟩ ⟨bt, ht⟩,
  use bs ⊔ bt,
  rw upper_bounds_union,
  exact ⟨upper_bounds_mono_mem le_sup_left hs,
    upper_bounds_mono_mem le_sup_right ht⟩
end

/-- The union of two sets is bounded above if and only if each of the sets is. -/
lemma bdd_above_union [semilattice_sup γ] {s t : set γ} :
  bdd_above (s ∪ t) ↔ bdd_above s ∧ bdd_above t :=
⟨λ h, ⟨h.mono $ subset_union_left s t, h.mono $ subset_union_right s t⟩,
  λ h, h.1.union h.2⟩

lemma bdd_below.union [semilattice_inf γ] {s t : set γ} :
  bdd_below s → bdd_below t → bdd_below (s ∪ t) :=
@bdd_above.union (order_dual γ) _ s t

/--The union of two sets is bounded above if and only if each of the sets is.-/
lemma bdd_below_union [semilattice_inf γ] {s t : set γ} :
  bdd_below (s ∪ t) ↔ bdd_below s ∧ bdd_below t :=
@bdd_above_union (order_dual γ) _ s t

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
lemma is_lub.union [semilattice_sup γ] {a b : γ} {s t : set γ}
  (hs : is_lub s a) (ht : is_lub t b) :
  is_lub (s ∪ t) (a ⊔ b) :=
⟨assume c h, h.cases_on (λ h, le_sup_left_of_le $ hs.left h) (λ h, le_sup_right_of_le $ ht.left h),
  assume c hc, sup_le
    (hs.right $ assume d hd, hc $ or.inl hd) (ht.right $ assume d hd, hc $ or.inr hd)⟩

/-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/
lemma is_glb.union [semilattice_inf γ] {a₁ a₂ : γ} {s t : set γ}
  (hs : is_glb s a₁) (ht : is_glb t a₂) :
  is_glb (s ∪ t) (a₁ ⊓ a₂) :=
@is_lub.union (order_dual γ) _ _ _ _ _ hs ht

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
lemma is_least.union [linear_order γ] {a b : γ} {s t : set γ}
  (ha : is_least s a) (hb : is_least t b) : is_least (s ∪ t) (min a b) :=
⟨by cases (le_total a b) with h h; simp [h, ha.1, hb.1],
  (ha.is_glb.union hb.is_glb).1⟩

/-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/
lemma is_greatest.union [linear_order γ] {a b : γ} {s t : set γ}
  (ha : is_greatest s a) (hb : is_greatest t b) : is_greatest (s ∪ t) (max a b) :=
⟨by cases (le_total a b) with h h; simp [h, ha.1, hb.1],
  (ha.is_lub.union hb.is_lub).1⟩

/-!
### Specific sets

#### Unbounded intervals
-/

lemma is_least_Ici : is_least (Ici a) a := ⟨left_mem_Ici, λ x, id⟩

lemma is_greatest_Iic : is_greatest (Iic a) a := ⟨right_mem_Iic, λ x, id⟩

lemma is_lub_Iic : is_lub (Iic a) a := is_greatest_Iic.is_lub

lemma is_glb_Ici : is_glb (Ici a) a := is_least_Ici.is_glb

lemma upper_bounds_Iic : upper_bounds (Iic a) = Ici a := is_lub_Iic.upper_bounds_eq

lemma lower_bounds_Ici : lower_bounds (Ici a) = Iic a := is_glb_Ici.lower_bounds_eq

lemma bdd_above_Iic : bdd_above (Iic a) := is_lub_Iic.bdd_above

lemma bdd_below_Ici : bdd_below (Ici a) := is_glb_Ici.bdd_below

lemma bdd_above_Iio : bdd_above (Iio a) := ⟨a, λ x hx, le_of_lt hx⟩

lemma bdd_below_Ioi : bdd_below (Ioi a) := ⟨a, λ x hx, le_of_lt hx⟩

section

variables [linear_order γ] [densely_ordered γ]

lemma is_lub_Iio {a : γ} : is_lub (Iio a) a :=
⟨λ x hx, le_of_lt hx, λ y hy, le_of_forall_ge_of_dense hy⟩

lemma is_glb_Ioi {a : γ} : is_glb (Ioi a) a := @is_lub_Iio (order_dual γ) _ _ a

lemma upper_bounds_Iio {a : γ} : upper_bounds (Iio a) = Ici a := is_lub_Iio.upper_bounds_eq

lemma lower_bounds_Ioi {a : γ} : lower_bounds (Ioi a) = Iic a := is_glb_Ioi.lower_bounds_eq

end

/-!
#### Singleton
-/

lemma is_greatest_singleton : is_greatest {a} a :=
⟨mem_singleton a, λ x hx, le_of_eq $ eq_of_mem_singleton hx⟩

lemma is_least_singleton : is_least {a} a :=
@is_greatest_singleton (order_dual α) _ a

lemma is_lub_singleton : is_lub {a} a := is_greatest_singleton.is_lub

lemma is_glb_singleton : is_glb {a} a := is_least_singleton.is_glb

lemma bdd_above_singleton : bdd_above ({a} : set α) := is_lub_singleton.bdd_above

lemma bdd_below_singleton : bdd_below ({a} : set α) := is_glb_singleton.bdd_below

@[simp] lemma upper_bounds_singleton : upper_bounds {a} = Ici a := is_lub_singleton.upper_bounds_eq

@[simp] lemma lower_bounds_singleton : lower_bounds {a} = Iic a := is_glb_singleton.lower_bounds_eq

/-!
#### Bounded intervals
-/

lemma bdd_above_Icc : bdd_above (Icc a b) := ⟨b, λ _, and.right⟩

lemma bdd_below_Icc : bdd_below (Icc a b) := ⟨a, λ _, and.left⟩

lemma bdd_above_Ico : bdd_above (Ico a b) := bdd_above_Icc.mono Ico_subset_Icc_self

lemma bdd_below_Ico : bdd_below (Ico a b) := bdd_below_Icc.mono Ico_subset_Icc_self

lemma bdd_above_Ioc : bdd_above (Ioc a b) := bdd_above_Icc.mono Ioc_subset_Icc_self

lemma bdd_below_Ioc : bdd_below (Ioc a b) := bdd_below_Icc.mono Ioc_subset_Icc_self

lemma bdd_above_Ioo : bdd_above (Ioo a b) := bdd_above_Icc.mono Ioo_subset_Icc_self

lemma bdd_below_Ioo : bdd_below (Ioo a b) := bdd_below_Icc.mono Ioo_subset_Icc_self

lemma is_greatest_Icc (h : a ≤ b) : is_greatest (Icc a b) b :=
⟨right_mem_Icc.2 h, λ x, and.right⟩

lemma is_lub_Icc (h : a ≤ b) : is_lub (Icc a b) b := (is_greatest_Icc h).is_lub

lemma upper_bounds_Icc (h : a ≤ b) : upper_bounds (Icc a b) = Ici b :=
(is_lub_Icc h).upper_bounds_eq

lemma is_least_Icc (h : a ≤ b) : is_least (Icc a b) a :=
⟨left_mem_Icc.2 h, λ x, and.left⟩

lemma is_glb_Icc (h : a ≤ b) : is_glb (Icc a b) a := (is_least_Icc h).is_glb

lemma lower_bounds_Icc (h : a ≤ b) : lower_bounds (Icc a b) = Iic a :=
(is_glb_Icc h).lower_bounds_eq

lemma is_greatest_Ioc (h : a < b) : is_greatest (Ioc a b) b :=
⟨right_mem_Ioc.2 h, λ x, and.right⟩

lemma is_lub_Ioc (h : a < b) : is_lub (Ioc a b) b :=
(is_greatest_Ioc h).is_lub

lemma upper_bounds_Ioc (h : a < b) : upper_bounds (Ioc a b) = Ici b :=
(is_lub_Ioc h).upper_bounds_eq

lemma is_least_Ico (h : a < b) : is_least (Ico a b) a :=
⟨left_mem_Ico.2 h, λ x, and.left⟩

lemma is_glb_Ico (h : a < b) : is_glb (Ico a b) a :=
(is_least_Ico h).is_glb

lemma lower_bounds_Ico (h : a < b) : lower_bounds (Ico a b) = Iic a :=
(is_glb_Ico h).lower_bounds_eq

section

variables [linear_order γ] [densely_ordered γ]

lemma is_glb_Ioo {a b : γ} (hab : a < b) : is_glb (Ioo a b) a :=
begin
  refine ⟨λx hx, le_of_lt hx.1, λy hy, le_of_not_lt $ λ h, _⟩,
  have : a < min b y, by { rw lt_min_iff, exact ⟨hab, h⟩ },
  rcases exists_between this with ⟨z, az, zy⟩,
  rw lt_min_iff at zy,
  exact lt_irrefl _ (lt_of_le_of_lt (hy ⟨az, zy.1⟩) zy.2)
end

lemma lower_bounds_Ioo {a b : γ} (hab : a < b) : lower_bounds (Ioo a b) = Iic a :=
(is_glb_Ioo hab).lower_bounds_eq

lemma is_glb_Ioc {a b : γ} (hab : a < b) : is_glb (Ioc a b) a :=
(is_glb_Ioo hab).of_subset_of_superset (is_glb_Icc $ le_of_lt hab)
  Ioo_subset_Ioc_self Ioc_subset_Icc_self

lemma lower_bound_Ioc {a b : γ} (hab : a < b) : lower_bounds (Ioc a b) = Iic a :=
(is_glb_Ioc hab).lower_bounds_eq

lemma is_lub_Ioo {a b : γ} (hab : a < b) : is_lub (Ioo a b) b :=
by simpa only [dual_Ioo] using @is_glb_Ioo (order_dual γ) _ _ b a hab

lemma upper_bounds_Ioo {a b : γ} (hab : a < b) : upper_bounds (Ioo a b) = Ici b :=
(is_lub_Ioo hab).upper_bounds_eq

lemma is_lub_Ico {a b : γ} (hab : a < b) : is_lub (Ico a b) b :=
by simpa only [dual_Ioc] using @is_glb_Ioc (order_dual γ) _ _ b a hab

lemma upper_bounds_Ico {a b : γ} (hab : a < b) : upper_bounds (Ico a b) = Ici b :=
(is_lub_Ico hab).upper_bounds_eq

end

lemma bdd_below_iff_subset_Ici : bdd_below s ↔ ∃ a, s ⊆ Ici a := iff.rfl

lemma bdd_above_iff_subset_Iic : bdd_above s ↔ ∃ a, s ⊆ Iic a := iff.rfl

lemma bdd_below_bdd_above_iff_subset_Icc : bdd_below s ∧ bdd_above s ↔ ∃ a b, s ⊆ Icc a b :=
by simp only [Ici_inter_Iic.symm, subset_inter_iff, bdd_below_iff_subset_Ici,
  bdd_above_iff_subset_Iic, exists_and_distrib_left, exists_and_distrib_right]

/-!
### Univ
-/

lemma order_top.upper_bounds_univ [order_top γ] : upper_bounds (univ : set γ) = {⊤} :=
set.ext $ λ b, iff.trans ⟨λ hb, top_unique $ hb trivial, λ hb x hx, hb.symm ▸ le_top⟩
  mem_singleton_iff.symm

lemma is_greatest_univ [order_top γ] : is_greatest (univ : set γ) ⊤ :=
by simp only [is_greatest, order_top.upper_bounds_univ, mem_univ, mem_singleton, true_and]

lemma is_lub_univ [order_top γ] : is_lub (univ : set γ) ⊤ :=
is_greatest_univ.is_lub

lemma order_bot.lower_bounds_univ [order_bot γ] : lower_bounds (univ : set γ) = {⊥} :=
@order_top.upper_bounds_univ (order_dual γ) _

lemma is_least_univ [order_bot γ] : is_least (univ : set γ) ⊥ :=
@is_greatest_univ (order_dual γ) _

lemma is_glb_univ [order_bot γ] : is_glb (univ : set γ) ⊥ :=
is_least_univ.is_glb

lemma no_top_order.upper_bounds_univ [no_top_order α] : upper_bounds (univ : set α) = ∅ :=
eq_empty_of_subset_empty $ λ b hb, let ⟨x, hx⟩ := no_top b in
not_le_of_lt hx (hb trivial)

lemma no_bot_order.lower_bounds_univ [no_bot_order α] : lower_bounds (univ : set α) = ∅ :=
@no_top_order.upper_bounds_univ (order_dual α) _ _

/-!
### Empty set
-/

@[simp] lemma upper_bounds_empty : upper_bounds (∅ : set α) = univ :=
by simp only [upper_bounds, eq_univ_iff_forall, mem_set_of_eq, ball_empty_iff, forall_true_iff]

@[simp] lemma lower_bounds_empty : lower_bounds (∅ : set α) = univ :=
@upper_bounds_empty (order_dual α) _

@[simp] lemma bdd_above_empty [nonempty α] : bdd_above (∅ : set α) :=
by simp only [bdd_above, upper_bounds_empty, univ_nonempty]

@[simp] lemma bdd_below_empty [nonempty α] : bdd_below (∅ : set α) :=
by simp only [bdd_below, lower_bounds_empty, univ_nonempty]

lemma is_glb_empty [order_top γ] : is_glb ∅ (⊤:γ) :=
by simp only [is_glb, lower_bounds_empty, is_greatest_univ]

lemma is_lub_empty [order_bot γ] : is_lub ∅ (⊥:γ) :=
@is_glb_empty (order_dual γ) _

lemma is_lub.nonempty [no_bot_order α] (hs : is_lub s a) : s.nonempty :=
let ⟨a', ha'⟩ := no_bot a in
ne_empty_iff_nonempty.1 $ assume h,
have a ≤ a', from hs.right $ by simp only [h, upper_bounds_empty],
not_le_of_lt ha' this

lemma is_glb.nonempty [no_top_order α] (hs : is_glb s a) : s.nonempty :=
@is_lub.nonempty (order_dual α) _ _ _ _ hs

lemma nonempty_of_not_bdd_above [ha : nonempty α] (h : ¬bdd_above s) : s.nonempty :=
nonempty.elim ha $ λ x, (not_bdd_above_iff'.1 h x).imp $ λ a ha, ha.fst

lemma nonempty_of_not_bdd_below [ha : nonempty α] (h : ¬bdd_below s) : s.nonempty :=
@nonempty_of_not_bdd_above (order_dual α) _ _ _ h

/-!
### insert
-/

/-- Adding a point to a set preserves its boundedness above. -/
@[simp] lemma bdd_above_insert [semilattice_sup γ] (a : γ) {s : set γ} :
  bdd_above (insert a s) ↔ bdd_above s :=
by simp only [insert_eq, bdd_above_union, bdd_above_singleton, true_and]

lemma bdd_above.insert [semilattice_sup γ] (a : γ) {s : set γ} (hs : bdd_above s) :
  bdd_above (insert a s) :=
(bdd_above_insert a).2 hs

/--Adding a point to a set preserves its boundedness below.-/
@[simp] lemma bdd_below_insert [semilattice_inf γ] (a : γ) {s : set γ} :
  bdd_below (insert a s) ↔ bdd_below s :=
by simp only [insert_eq, bdd_below_union, bdd_below_singleton, true_and]

lemma bdd_below.insert [semilattice_inf γ] (a : γ) {s : set γ} (hs : bdd_below s) :
  bdd_below (insert a s) :=
(bdd_below_insert a).2 hs

lemma is_lub.insert [semilattice_sup γ] (a) {b} {s : set γ} (hs : is_lub s b) :
  is_lub (insert a s) (a ⊔ b) :=
by { rw insert_eq, exact is_lub_singleton.union hs }

lemma is_glb.insert [semilattice_inf γ] (a) {b} {s : set γ} (hs : is_glb s b) :
  is_glb (insert a s) (a ⊓ b) :=
by { rw insert_eq, exact is_glb_singleton.union hs }

lemma is_greatest.insert [linear_order γ] (a) {b} {s : set γ} (hs : is_greatest s b) :
  is_greatest (insert a s) (max a b) :=
by { rw insert_eq, exact is_greatest_singleton.union hs }

lemma is_least.insert [linear_order γ] (a) {b} {s : set γ} (hs : is_least s b) :
  is_least (insert a s) (min a b) :=
by { rw insert_eq, exact is_least_singleton.union hs }

@[simp] lemma upper_bounds_insert (a : α) (s : set α) :
  upper_bounds (insert a s) = Ici a ∩ upper_bounds s :=
by rw [insert_eq, upper_bounds_union, upper_bounds_singleton]

@[simp] lemma lower_bounds_insert (a : α) (s : set α) :
  lower_bounds (insert a s) = Iic a ∩ lower_bounds s :=
by rw [insert_eq, lower_bounds_union, lower_bounds_singleton]

/-- When there is a global maximum, every set is bounded above. -/
@[simp] protected lemma order_top.bdd_above [order_top γ] (s : set γ) : bdd_above s :=
⟨⊤, assume a ha, order_top.le_top a⟩

/-- When there is a global minimum, every set is bounded below. -/
@[simp] protected lemma order_bot.bdd_below [order_bot γ] (s : set γ) : bdd_below s :=
⟨⊥, assume a ha, order_bot.bot_le a⟩

/-!
### Pair
-/

lemma is_lub_pair [semilattice_sup γ] {a b : γ} : is_lub {a, b} (a ⊔ b) :=
is_lub_singleton.insert _

lemma is_glb_pair [semilattice_inf γ] {a b : γ} : is_glb {a, b} (a ⊓ b) :=
is_glb_singleton.insert _

lemma is_least_pair [linear_order γ] {a b : γ} : is_least {a, b} (min a b) :=
is_least_singleton.insert _

lemma is_greatest_pair [linear_order γ] {a b : γ} : is_greatest {a, b} (max a b) :=
is_greatest_singleton.insert _

end

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/

section preorder
variables [preorder α] {s : set α} {a b : α}

lemma lower_bounds_le_upper_bounds (ha : a ∈ lower_bounds s) (hb : b ∈ upper_bounds s) :
  s.nonempty → a ≤ b
| ⟨c, hc⟩ := le_trans (ha hc) (hb hc)

lemma is_glb_le_is_lub (ha : is_glb s a) (hb : is_lub s b) (hs : s.nonempty) : a ≤ b :=
lower_bounds_le_upper_bounds ha.1 hb.1 hs

lemma is_lub_lt_iff (ha : is_lub s a) : a < b ↔ ∃ c ∈ upper_bounds s, c < b :=
⟨λ hb, ⟨a, ha.1, hb⟩, λ ⟨c, hcs, hcb⟩, lt_of_le_of_lt (ha.2 hcs) hcb⟩

lemma lt_is_glb_iff (ha : is_glb s a) : b < a ↔ ∃ c ∈ lower_bounds s, b < c :=
@is_lub_lt_iff (order_dual α) _ s _ _ ha

end preorder

section partial_order
variables [partial_order α] {s : set α} {a b : α}

lemma is_least.unique (Ha : is_least s a) (Hb : is_least s b) : a = b :=
le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

lemma is_least.is_least_iff_eq (Ha : is_least s a) : is_least s b ↔ a = b :=
iff.intro Ha.unique (assume h, h ▸ Ha)

lemma is_greatest.unique (Ha : is_greatest s a) (Hb : is_greatest s b) : a = b :=
le_antisymm (Hb.right Ha.left) (Ha.right Hb.left)

lemma is_greatest.is_greatest_iff_eq (Ha : is_greatest s a) : is_greatest s b ↔ a = b :=
iff.intro Ha.unique (assume h, h ▸ Ha)

lemma is_lub.unique (Ha : is_lub s a) (Hb : is_lub s b) : a = b :=
Ha.unique Hb

lemma is_glb.unique (Ha : is_glb s a) (Hb : is_glb s b) : a = b :=
Ha.unique Hb

end partial_order

section linear_order
variables [linear_order α] {s : set α} {a b : α}

lemma lt_is_lub_iff (h : is_lub s a) : b < a ↔ ∃ c ∈ s, b < c :=
by simp only [← not_le, is_lub_le_iff h, mem_upper_bounds, not_forall]

lemma is_glb_lt_iff (h : is_glb s a) : a < b ↔ ∃ c ∈ s, c < b :=
@lt_is_lub_iff (order_dual α) _ _ _ _ h

lemma is_lub.exists_between (h : is_lub s a) (hb : b < a) :
  ∃ c ∈ s, b < c ∧ c ≤ a :=
let ⟨c, hcs, hbc⟩ := (lt_is_lub_iff h).1 hb in ⟨c, hcs, hbc, h.1 hcs⟩

lemma is_lub.exists_between' (h : is_lub s a) (h' : a ∉ s) (hb : b < a) :
  ∃ c ∈ s, b < c ∧ c < a :=
let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
in ⟨c, hcs, hbc, hca.lt_of_ne $ λ hac, h' $ hac ▸ hcs⟩

lemma is_glb.exists_between (h : is_glb s a) (hb : a < b) :
  ∃ c ∈ s, a ≤ c ∧ c < b :=
let ⟨c, hcs, hbc⟩ := (is_glb_lt_iff h).1 hb in ⟨c, hcs, h.1 hcs, hbc⟩

lemma is_glb.exists_between' (h : is_glb s a) (h' : a ∉ s) (hb : a < b) :
  ∃ c ∈ s, a < c ∧ c < b :=
let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
in ⟨c, hcs, hac.lt_of_ne $ λ hac, h' $ hac.symm ▸ hcs, hcb⟩

end linear_order

/-!
### Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

section linear_ordered_add_comm_group

variables [linear_ordered_add_comm_group α] {s : set α} {a ε : α}

lemma is_glb.exists_between_self_add (h : is_glb s a) (hε : 0 < ε) :
  ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
h.exists_between $ lt_add_of_pos_right _ hε

lemma is_glb.exists_between_self_add' (h : is_glb s a) (h₂ : a ∉ s) (hε : 0 < ε) :
  ∃ b ∈ s, a < b ∧ b < a + ε :=
h.exists_between' h₂ $ lt_add_of_pos_right _ hε

lemma is_lub.exists_between_sub_self  (h : is_lub s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
h.exists_between $ sub_lt_self _ hε

lemma is_lub.exists_between_sub_self' (h : is_lub s a) (h₂ : a ∉ s) (hε : 0 < ε) :
  ∃ b ∈ s, a - ε < b ∧ b < a :=
h.exists_between' h₂ $ sub_lt_self _ hε

end linear_ordered_add_comm_group

/-!
### Images of upper/lower bounds under monotone functions
-/

namespace monotone

variables [preorder α] [preorder β] {f : α → β} (Hf : monotone f) {a : α} {s : set α}

lemma mem_upper_bounds_image (Ha : a ∈ upper_bounds s) :
  f a ∈ upper_bounds (f '' s) :=
ball_image_of_ball (assume x H, Hf (Ha ‹x ∈ s›))

lemma mem_lower_bounds_image (Ha : a ∈ lower_bounds s) :
  f a ∈ lower_bounds (f '' s) :=
ball_image_of_ball (assume x H, Hf (Ha ‹x ∈ s›))

/-- The image under a monotone function of a set which is bounded above is bounded above. -/
lemma map_bdd_above (hf : monotone f) : bdd_above s → bdd_above (f '' s)
| ⟨C, hC⟩ := ⟨f C, hf.mem_upper_bounds_image hC⟩

/-- The image under a monotone function of a set which is bounded below is bounded below. -/
lemma map_bdd_below (hf : monotone f) : bdd_below s → bdd_below (f '' s)
| ⟨C, hC⟩ := ⟨f C, hf.mem_lower_bounds_image hC⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
lemma map_is_least (Ha : is_least s a) : is_least (f '' s) (f a) :=
⟨mem_image_of_mem _ Ha.1, Hf.mem_lower_bounds_image Ha.2⟩

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
lemma map_is_greatest (Ha : is_greatest s a) : is_greatest (f '' s) (f a) :=
⟨mem_image_of_mem _ Ha.1, Hf.mem_upper_bounds_image Ha.2⟩

lemma is_lub_image_le (Ha : is_lub s a) {b : β} (Hb : is_lub (f '' s) b) :
  b ≤ f a :=
Hb.2 (Hf.mem_upper_bounds_image Ha.1)

lemma le_is_glb_image (Ha : is_glb s a) {b : β} (Hb : is_glb (f '' s) b) :
  f a ≤ b :=
Hb.2 (Hf.mem_lower_bounds_image Ha.1)

end monotone

lemma is_glb.of_image [preorder α] [preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
  {s : set α} {x : α} (hx : is_glb (f '' s) (f x)) :
  is_glb s x :=
⟨λ y hy, hf.1 $ hx.1 $ mem_image_of_mem _ hy,
  λ y hy, hf.1 $ hx.2 $ monotone.mem_lower_bounds_image (λ x y, hf.2) hy⟩

lemma is_lub.of_image [preorder α] [preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
  {s : set α} {x : α} (hx : is_lub (f '' s) (f x)) :
  is_lub s x :=
@is_glb.of_image (order_dual α) (order_dual β) _ _ f (λ x y, hf) _ _ hx
