/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import algebra.module.pi

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `list ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : holor α ds₁` and `x₂ : holor α ds₂` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/

universes u

open list

open_locale big_operators

/-- `holor_index ds` is the type of valid index tuples to identify an entry of a holor of dimensions `ds` -/
def holor_index (ds : list ℕ) : Type := { is : list ℕ // forall₂ (<) is ds}

namespace holor_index
variables {ds₁ ds₂ ds₃ : list ℕ}

def take : Π {ds₁ : list ℕ}, holor_index (ds₁ ++ ds₂) → holor_index ds₁
| ds is := ⟨ list.take (length ds) is.1, forall₂_take_append is.1 ds ds₂ is.2 ⟩

def drop : Π {ds₁ : list ℕ}, holor_index (ds₁ ++ ds₂) → holor_index ds₂
| ds is := ⟨ list.drop (length ds) is.1, forall₂_drop_append is.1 ds ds₂ is.2 ⟩

lemma cast_type (is : list ℕ) (eq : ds₁ = ds₂) (h : forall₂ (<) is ds₁) :
  (cast (congr_arg holor_index eq) ⟨is, h⟩).val = is :=
by subst eq; refl

def assoc_right :
  holor_index (ds₁ ++ ds₂ ++ ds₃) → holor_index (ds₁ ++ (ds₂ ++ ds₃)) :=
cast (congr_arg holor_index (append_assoc ds₁ ds₂ ds₃))

def assoc_left :
  holor_index (ds₁ ++ (ds₂ ++ ds₃)) → holor_index (ds₁ ++ ds₂ ++ ds₃) :=
cast (congr_arg holor_index (append_assoc ds₁ ds₂ ds₃).symm)

lemma take_take :
  ∀ t : holor_index (ds₁ ++ ds₂ ++ ds₃),
  t.assoc_right.take = t.take.take
| ⟨ is , h ⟩ := subtype.eq (by simp [assoc_right,take, cast_type, list.take_take, nat.le_add_right, min_eq_left])

lemma drop_take :
  ∀ t : holor_index (ds₁ ++ ds₂ ++ ds₃),
  t.assoc_right.drop.take = t.take.drop
| ⟨ is , h ⟩ := subtype.eq (by simp [assoc_right, take, drop, cast_type, list.drop_take])

lemma drop_drop :
  ∀ t : holor_index (ds₁ ++ ds₂ ++ ds₃),
  t.assoc_right.drop.drop = t.drop
| ⟨ is , h ⟩ := subtype.eq (by simp [add_comm, assoc_right, drop, cast_type, list.drop_drop])

end holor_index

/-- Holor (indexed collections of tensor coefficients) -/
def holor (α : Type u) (ds:list ℕ) := holor_index ds → α

namespace holor

variables {α : Type} {d : ℕ} {ds : list ℕ} {ds₁ : list ℕ} {ds₂ : list ℕ} {ds₃ : list ℕ}

instance [inhabited α] : inhabited (holor α ds) := ⟨λ t, default α⟩
instance [has_zero α] : has_zero (holor α ds) := ⟨λ t, 0⟩
instance [has_add α] : has_add (holor α ds) := ⟨λ x y t, x t + y t⟩
instance [has_neg α] : has_neg (holor α ds) :=  ⟨λ a t, - a t⟩

instance [add_semigroup α] : add_semigroup (holor α ds) := by pi_instance

instance [add_comm_semigroup α] : add_comm_semigroup (holor α ds) := by pi_instance

instance [add_monoid α] : add_monoid (holor α ds) := by pi_instance

instance [add_comm_monoid α] : add_comm_monoid (holor α ds) := by pi_instance

instance [add_group α] : add_group (holor α ds) := by pi_instance

instance [add_comm_group α] : add_comm_group (holor α ds) := by pi_instance

/- scalar product -/

instance [has_mul α] : has_scalar α (holor α ds) :=
  ⟨λ a x, λ t, a * x t⟩

instance [semiring α] : semimodule α (holor α ds) := pi.semimodule _ _ _

/-- The tensor product of two holors. -/
def mul [s : has_mul α] (x : holor α ds₁) (y : holor α ds₂) : holor α (ds₁ ++ ds₂) :=
  λ t, x (t.take) * y (t.drop)

local infix ` ⊗ ` : 70 := mul

lemma cast_type (eq : ds₁ = ds₂) (a : holor α ds₁) :
  cast (congr_arg (holor α) eq) a = (λ t, a (cast (congr_arg holor_index eq.symm) t)) :=
by subst eq; refl

def assoc_right :
  holor α (ds₁ ++ ds₂ ++ ds₃) → holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
cast (congr_arg (holor α) (append_assoc ds₁ ds₂ ds₃))

def assoc_left :
  holor α (ds₁ ++ (ds₂ ++ ds₃)) → holor α (ds₁ ++ ds₂ ++ ds₃) :=
cast (congr_arg (holor α) (append_assoc ds₁ ds₂ ds₃).symm)

lemma mul_assoc0 [semigroup α] (x : holor α ds₁) (y : holor α ds₂) (z : holor α ds₃) :
  x ⊗ y ⊗ z = (x ⊗ (y ⊗ z)).assoc_left :=
funext (assume t : holor_index (ds₁ ++ ds₂ ++ ds₃),
begin
  rw assoc_left,
  unfold mul,
  rw mul_assoc,
  rw [←holor_index.take_take, ←holor_index.drop_take, ←holor_index.drop_drop],
  rw cast_type,
  refl,
  rw append_assoc
end)

lemma mul_assoc [semigroup α] (x : holor α ds₁) (y : holor α ds₂) (z : holor α ds₃) :
  mul (mul x y) z == (mul x (mul y z)) :=
by simp [cast_heq, mul_assoc0, assoc_left].

lemma mul_left_distrib [distrib α] (x : holor α ds₁) (y : holor α ds₂) (z : holor α ds₂) :
  x ⊗ (y + z) = x ⊗ y + x ⊗ z :=
funext (λt, left_distrib (x (holor_index.take t)) (y (holor_index.drop t)) (z (holor_index.drop t)))

lemma mul_right_distrib [distrib α] (x : holor α ds₁) (y : holor α ds₁) (z : holor α ds₂) :
  (x + y) ⊗ z = x ⊗ z + y ⊗ z :=
funext (λt, right_distrib (x (holor_index.take t)) (y (holor_index.take t)) (z (holor_index.drop t)))

@[simp] lemma zero_mul {α : Type} [ring α] (x : holor α ds₂) :
  (0 : holor α ds₁) ⊗ x = 0 :=
funext (λ t, zero_mul (x (holor_index.drop t)))

@[simp] lemma mul_zero {α : Type} [ring α] (x : holor α ds₁) :
  x ⊗ (0 :holor α ds₂) = 0 :=
funext (λ t, mul_zero (x (holor_index.take t)))

lemma mul_scalar_mul [monoid α] (x : holor α []) (y : holor α ds) :
  x ⊗ y = x ⟨[], forall₂.nil⟩ • y :=
by simp [mul, has_scalar.smul, holor_index.take, holor_index.drop]

/- holor slices -/

/-- A slice is a subholor consisting of all entries with initial index i. -/
def slice (x : holor α (d :: ds)) (i : ℕ) (h : i < d) : holor α ds :=
  (λ is : holor_index ds, x ⟨ i :: is.1, forall₂.cons h is.2⟩)

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
def unit_vec [monoid α] [add_monoid α] (d : ℕ) (j : ℕ) : holor α [d] :=
  λ ti, if ti.1 = [j] then 1 else 0

lemma holor_index_cons_decomp (p: holor_index (d :: ds) → Prop) :
  Π (t : holor_index (d :: ds)),
    (∀ i is, Π h : t.1 = i :: is, p ⟨ i :: is, begin rw [←h], exact t.2 end ⟩ ) → p t
| ⟨[], hforall₂⟩        hp := absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
| ⟨(i :: is), hforall₂⟩ hp := hp i is rfl

/-- Two holors are equal if all their slices are equal. -/
lemma slice_eq (x : holor α (d :: ds)) (y : holor α (d :: ds))
  (h : slice x = slice y) : x = y :=
funext $ λ t : holor_index (d :: ds), holor_index_cons_decomp (λ t, x t = y t) t $ λ i is hiis,
have hiisdds: forall₂ (<) (i :: is) (d :: ds), begin rw [←hiis], exact t.2 end,
have hid:     i<d,                             from (forall₂_cons.1 hiisdds).1,
have hisds:   forall₂ (<) is ds,               from (forall₂_cons.1 hiisdds).2,
calc
  x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩  : congr_arg (λ t, x t) (subtype.eq rfl)
              ... = slice y i hid ⟨is, hisds⟩  : by rw h
              ... = y ⟨i :: is, _⟩             : congr_arg (λ t, y t) (subtype.eq rfl)

lemma slice_unit_vec_mul [ring α] {i : ℕ} {j : ℕ}
  (hid : i < d) (x : holor α ds) :
  slice (unit_vec d j ⊗ x) i hid = if i=j then x else 0 :=
funext $ λ t : holor_index ds, if h : i = j
  then by simp [slice, mul, holor_index.take, unit_vec, holor_index.drop, h]
  else by simp [slice, mul, holor_index.take, unit_vec, holor_index.drop, h]; refl

lemma slice_add [has_add α] (i : ℕ) (hid : i < d)  (x : holor α (d :: ds)) (y : holor α (d :: ds)) :
  slice x i hid + slice y i hid = slice (x + y) i hid := funext (λ t, by simp [slice,(+)])

lemma slice_zero [has_zero α] (i : ℕ) (hid : i < d)  :
  slice (0 : holor α (d :: ds)) i hid = 0 := funext (λ t, by simp [slice]; refl)

lemma slice_sum [add_comm_monoid α] {β : Type}
  (i : ℕ) (hid : i < d) (s : finset β) (f : β → holor α (d :: ds)) :
  ∑ x in s, slice (f x) i hid = slice (∑ x in s, f x) i hid :=
begin
  letI := classical.dec_eq β,
  refine finset.induction_on s _ _,
  { simp [slice_zero] },
  { intros _ _ h_not_in ih,
    rw [finset.sum_insert h_not_in, ih, slice_add, finset.sum_insert h_not_in] }
end

/-- The original holor can be recovered from its slices by multiplying with unit vectors and summing up. -/
@[simp] lemma sum_unit_vec_mul_slice [ring α] (x : holor α (d :: ds)) :
  ∑ i in (finset.range d).attach,
    unit_vec d i ⊗ slice x i (nat.succ_le_of_lt (finset.mem_range.1 i.prop)) = x :=
begin
  apply slice_eq _ _ _,
  ext i hid,
  rw [←slice_sum],
  simp only [slice_unit_vec_mul hid],
  rw finset.sum_eq_single (subtype.mk i $ finset.mem_range.2 hid),
  { simp },
  { assume (b : {x // x ∈ finset.range d}) (hb : b ∈ (finset.range d).attach) (hbi : b ≠ ⟨i, _⟩),
    have hbi' : i ≠ b,
    { simpa only [ne.def, subtype.ext_iff, subtype.coe_mk] using hbi.symm },
    simp [hbi'] },
  { assume hid' : subtype.mk i _ ∉ finset.attach (finset.range d),
    exfalso,
    exact absurd (finset.mem_attach _ _) hid'
  }
end

/- CP rank -/

/-- `cprank_max1 x` means `x` has CP rank at most 1, that is,
  it is the tensor product of 1-dimensional holors. -/
inductive cprank_max1 [has_mul α]: Π {ds}, holor α ds → Prop
| nil (x : holor α []) :
    cprank_max1 x
| cons {d} {ds} (x : holor α [d]) (y : holor α ds) :
    cprank_max1 y → cprank_max1 (x ⊗ y)

/-- `cprank_max N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
inductive cprank_max [has_mul α] [add_monoid α] : ℕ → Π {ds}, holor α ds → Prop
| zero {ds} :
    cprank_max 0 (0 : holor α ds)
| succ n {ds} (x : holor α ds) (y : holor α ds) :
    cprank_max1 x → cprank_max n y →  cprank_max (n+1) (x + y)

lemma cprank_max_nil [monoid α] [add_monoid α] (x : holor α nil) : cprank_max 1 x :=
  have h : _, from cprank_max.succ 0 x 0 (cprank_max1.nil x) (cprank_max.zero),
  by rwa [add_zero x, zero_add] at h

lemma cprank_max_1 [monoid α] [add_monoid α] {x : holor α ds}
  (h : cprank_max1 x) : cprank_max 1 x :=
have h' : _, from cprank_max.succ 0 x 0 h cprank_max.zero,
by rwa [zero_add, add_zero] at h'

lemma cprank_max_add [monoid α] [add_monoid α]:
  ∀ {m : ℕ} {n : ℕ} {x : holor α ds} {y : holor α ds},
  cprank_max m x → cprank_max n y → cprank_max (m + n) (x + y)
| 0     n x y (cprank_max.zero) hy := by simp [hy]
| (m+1) n _ y (cprank_max.succ k x₁ x₂ hx₁ hx₂) hy :=
begin
  simp only [add_comm, add_assoc],
  apply cprank_max.succ,
  { assumption },
  { exact cprank_max_add hx₂ hy }
end

lemma cprank_max_mul [ring α] :
  ∀ (n : ℕ) (x : holor α [d]) (y : holor α ds), cprank_max n y → cprank_max n (x ⊗ y)
| 0 x _ (cprank_max.zero) := by simp [mul_zero x, cprank_max.zero]
| (n+1) x _ (cprank_max.succ k y₁ y₂ hy₁ hy₂) :=
begin
  rw mul_left_distrib,
  rw nat.add_comm,
  apply cprank_max_add,
  { exact cprank_max_1 (cprank_max1.cons _ _ hy₁) },
  { exact cprank_max_mul k x y₂ hy₂ }
end

lemma cprank_max_sum [ring α] {β} {n : ℕ} (s : finset β) (f : β → holor α ds) :
  (∀ x ∈ s, cprank_max n (f x)) → cprank_max (s.card * n) (∑ x in s, f x) :=
by letI := classical.dec_eq β;
exact finset.induction_on s
  (by simp [cprank_max.zero])
  (begin
    assume x s (h_x_notin_s : x ∉ s) ih h_cprank,
    simp only [finset.sum_insert h_x_notin_s,finset.card_insert_of_not_mem h_x_notin_s],
    rw nat.right_distrib,
    simp only [nat.one_mul, nat.add_comm],
    have ih' : cprank_max (finset.card s * n) (∑ x in s, f x),
    {
      apply ih,
      assume (x : β) (h_x_in_s: x ∈ s),
      simp only [h_cprank, finset.mem_insert_of_mem, h_x_in_s]
    },
    exact (cprank_max_add (h_cprank x (finset.mem_insert_self x s)) ih')
  end)


lemma cprank_max_upper_bound [ring α] : Π {ds}, ∀ x : holor α ds, cprank_max ds.prod x
| [] x := cprank_max_nil x
| (d :: ds) x :=
have h_summands : Π (i : {x // x ∈ finset.range d}),
  cprank_max ds.prod (unit_vec d i.1 ⊗ slice x i.1 (mem_range.1 i.2)),
  from λ i, cprank_max_mul _ _ _ (cprank_max_upper_bound (slice x i.1 (mem_range.1 i.2))),
have h_dds_prod : (list.cons d ds).prod = finset.card (finset.range d) * prod ds,
  by simp [finset.card_range],
have cprank_max (finset.card (finset.attach (finset.range d)) * prod ds)
  (∑ i in finset.attach (finset.range d), unit_vec d (i.val)⊗slice x (i.val) (mem_range.1 i.2)),
  from cprank_max_sum (finset.range d).attach _ (λ i _, h_summands i),
have h_cprank_max_sum : cprank_max (finset.card (finset.range d) * prod ds)
  (∑ i in finset.attach (finset.range d), unit_vec d (i.val)⊗slice x (i.val) (mem_range.1 i.2)),
  by rwa [finset.card_attach] at this,
begin
  rw [←sum_unit_vec_mul_slice x],
  rw [h_dds_prod],
  exact h_cprank_max_sum,
end

/-- The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1. -/
noncomputable def cprank [ring α] (x : holor α ds) : nat :=
@nat.find (λ n, cprank_max n x) (classical.dec_pred _) ⟨ds.prod, cprank_max_upper_bound x⟩

lemma cprank_upper_bound [ring α] :
  Π {ds}, ∀ x : holor α ds, cprank x ≤ ds.prod :=
λ ds (x : holor α ds),
  by letI := classical.dec_pred (λ (n : ℕ), cprank_max n x);
  exact nat.find_min'
    ⟨ds.prod, show (λ n, cprank_max n x) ds.prod, from cprank_max_upper_bound x⟩
    (cprank_max_upper_bound x)

end holor
