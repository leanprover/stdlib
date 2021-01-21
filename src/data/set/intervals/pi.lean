/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import data.set.lattice

/-!
# Intervals in `pi`-space

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/

variables {ι : Type*} {α : ι → Type*}

namespace set

section pi_preorder

variables [Π i, preorder (α i)] (x y : Π i, α i)

@[simp] lemma pi_univ_Ici : pi univ (λ i, Ici (x i)) = Ici x :=
ext $ λ y, by simp [pi.le_def]

@[simp] lemma pi_univ_Iic : pi univ (λ i, Iic (x i)) = Iic x :=
ext $ λ y, by simp [pi.le_def]

@[simp] lemma pi_univ_Icc : pi univ (λ i, Icc (x i) (y i)) = Icc x y :=
ext $ λ y, by simp [pi.le_def, forall_and_distrib]

section nonempty

variable [nonempty ι]

lemma pi_univ_Ioi_subset : pi univ (λ i, Ioi (x i)) ⊆ Ioi x :=
λ z hz, ⟨λ i, le_of_lt $ hz i trivial,
  λ h, nonempty.elim ‹nonempty ι› $ λ i, (h i).not_lt (hz i trivial)⟩

lemma pi_univ_Iio_subset : pi univ (λ i, Iio (x i)) ⊆ Iio x :=
@pi_univ_Ioi_subset ι (λ i, order_dual (α i)) _ x _

lemma pi_univ_Ioo_subset : pi univ (λ i, Ioo (x i) (y i)) ⊆ Ioo x y :=
λ x hx, ⟨pi_univ_Ioi_subset _ $ λ i hi, (hx i hi).1, pi_univ_Iio_subset _ $ λ i hi, (hx i hi).2⟩

lemma pi_univ_Ioc_subset : pi univ (λ i, Ioc (x i) (y i)) ⊆ Ioc x y :=
λ x hx, ⟨pi_univ_Ioi_subset _ $ λ i hi, (hx i hi).1, λ i, (hx i trivial).2⟩

lemma pi_univ_Ico_subset : pi univ (λ i, Ico (x i) (y i)) ⊆ Ico x y :=
λ x hx, ⟨λ i, (hx i trivial).1, pi_univ_Iio_subset _ $ λ i hi, (hx i hi).2⟩

end nonempty

variable [decidable_eq ι]

open function (update)

lemma pi_univ_Ioc_update_left {x y : Π i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ ≤ m) :
  pi univ (λ i, Ioc (update x i₀ m i) (y i)) = {z | m < z i₀} ∩ pi univ (λ i, Ioc (x i) (y i)) :=
begin
  have : Ioc m (y i₀) = Ioi m ∩ Ioc (x i₀) (y i₀),
    by rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, ← inter_assoc,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)],
  simp_rw [univ_pi_update i₀ _ _ (λ i z, Ioc z (y i)), ← pi_inter_compl ({i₀} : set ι),
    singleton_pi', ← inter_assoc, this],
  refl
end

lemma pi_univ_Ioc_update_right {x y : Π i, α i} {i₀ : ι} {m : α i₀} (hm : m ≤ y i₀) :
  pi univ (λ i, Ioc (x i) (update y i₀ m i)) = {z | z i₀ ≤ m} ∩ pi univ (λ i, Ioc (x i) (y i)) :=
begin
  have : Ioc (x i₀) m = Iic m ∩ Ioc (x i₀) (y i₀),
    by rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_left_comm,
      inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)],
  simp_rw [univ_pi_update i₀ y m (λ i z, Ioc (x i) z), ← pi_inter_compl ({i₀} : set ι),
    singleton_pi', ← inter_assoc, this],
  refl
end

lemma disjoint_pi_univ_Ioc_update_left_right {x y : Π i, α i} {i₀ : ι} {m : α i₀} :
  disjoint (pi univ (λ i, Ioc (x i) (update y i₀ m i)))
    (pi univ (λ i, Ioc (update x i₀ m i) (y i))) :=
begin
  rintro z ⟨h₁, h₂⟩,
  refine (h₁ i₀ (mem_univ _)).2.not_lt _,
  simpa only [function.update_same] using (h₂ i₀ (mem_univ _)).1
end

end pi_preorder

variables [decidable_eq ι] [Π i, linear_order (α i)]

open function (update)

lemma pi_univ_Ioc_update_union (x y : Π i, α i) (i₀ : ι) (m : α i₀) (hm : m ∈ Icc (x i₀) (y i₀)) :
  pi univ (λ i, Ioc (x i) (update y i₀ m i)) ∪ pi univ (λ i, Ioc (update x i₀ m i) (y i)) =
    pi univ (λ i, Ioc (x i) (y i)) :=
by simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2,
  ← union_inter_distrib_right, ← set_of_or, le_or_lt, set_of_true, univ_inter]

/-- If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open intervals `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference between a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered by the union
of the faces of `[x, y]`. -/
lemma Icc_diff_pi_univ_Ioo_subset (x y x' y' : Π i, α i) :
  Icc x y \ pi univ (λ i, Ioo (x' i) (y' i)) ⊆
    (⋃ i : ι, Icc x (update y i (x' i))) ∪ ⋃ i : ι, Icc (update x i (y' i)) y :=
begin
  rintros a ⟨⟨hxa, hay⟩, ha'⟩,
  simpa [le_update_iff, update_le_iff, hxa, hay, hxa _, hay _, ← exists_or_distrib,
    not_and_distrib] using ha'
end

/-- If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed box
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is covered by the union
of the faces of `[x, y]` adjacent to `x`. -/
lemma Icc_diff_pi_univ_Ioc_subset (x y z : Π i, α i) :
  Icc x z \ pi univ (λ i, Ioc (y i) (z i)) ⊆ ⋃ i : ι, Icc x (update z i (y i)) :=
begin
  rintros a ⟨⟨hax, haz⟩, hay⟩,
  simpa [not_and_distrib, hax, le_update_iff, haz _] using hay
end

end set
