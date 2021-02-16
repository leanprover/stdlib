/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import data.set.intervals.basic

/-!
# Intervals in `with_top α` and `with_bot α`

In this file we prove various lemmas about `set.image`s and `set.preimage`s of intervals under
`coe : α → with_top α` and `coe : α → with_bot α`.
-/

open set

variables {α : Type*}

/-! ### `with_top` -/

namespace with_top

variables [partial_order α] {a b : α}

@[simp] lemma range_coe : range (coe : α → with_top α) = Iio ⊤ :=
begin
  ext x,
  rw [mem_Iio, lt_top_iff_ne_top, mem_range, ← none_eq_top, option.ne_none_iff_exists],
  exact exists_congr (λ _, eq_comm)
end

@[simp] lemma preimage_coe_Ioi : (coe : α → with_top α) ⁻¹' (Ioi a) = Ioi a := ext $ λ x, coe_lt_coe

@[simp] lemma preimage_coe_Ici : (coe : α → with_top α) ⁻¹' (Ici a) = Ici a := ext $ λ x, coe_le_coe

@[simp] lemma preimage_coe_Iio : (coe : α → with_top α) ⁻¹' (Iio a) = Iio a := ext $ λ x, coe_lt_coe

@[simp] lemma preimage_coe_Iic : (coe : α → with_top α) ⁻¹' (Iic a) = Iic a := ext $ λ x, coe_le_coe

@[simp] lemma preimage_coe_Icc : (coe : α → with_top α) ⁻¹' (Icc a b) = Icc a b :=
by simp [← Ici_inter_Iic]

@[simp] lemma preimage_coe_Ico : (coe : α → with_top α) ⁻¹' (Ico a b) = Ico a b :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_coe_Ioc : (coe : α → with_top α) ⁻¹' (Ioc a b) = Ioc a b :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_coe_Ioo : (coe : α → with_top α) ⁻¹' (Ioo a b) = Ioo a b :=
by simp [← Ioi_inter_Iio]

@[simp] lemma preimage_coe_top : (coe : α → with_top α) ⁻¹' {⊤} = (∅ : set α) :=
eq_empty_of_subset_empty $ λ a, coe_ne_top

@[simp] lemma preimage_coe_Iio_top : (coe : α → with_top α) ⁻¹' (Iio ⊤) = univ :=
by rw [← range_coe, preimage_range]

@[simp] lemma preimage_coe_Ico_top : (coe : α → with_top α) ⁻¹' (Ico a ⊤) = Ici a :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_coe_Ioo_top : (coe : α → with_top α) ⁻¹' (Ioo a ⊤) = Ioi a :=
by simp [← Ioi_inter_Iio]

@[simp] lemma image_coe_Ioi : (coe : α → with_top α) '' (Ioi a) = Ioo a ⊤ :=
by rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe, Ioi_inter_Iio]

@[simp] lemma image_coe_Ici : (coe : α → with_top α) '' (Ici a) = Ico a ⊤ :=
by rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe, Ici_inter_Iio]

@[simp] lemma image_coe_Iio : (coe : α → with_top α) '' (Iio a) = Iio a :=
by rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

@[simp] lemma image_coe_Iic : (coe : α → with_top α) '' (Iic a) = Iic a :=
by rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (Iic_subset_Iio.2 $ coe_lt_top a)]

@[simp] lemma image_coe_Icc : (coe : α → with_top α) '' (Icc a b) = Icc a b :=
by rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Icc_subset_Iic_self $ Iic_subset_Iio.2 $ coe_lt_top b)]

@[simp] lemma image_coe_Ico : (coe : α → with_top α) '' (Ico a b) = Ico a b :=
by rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Ico_subset_Iio_self $ Iio_subset_Iio le_top)]

@[simp] lemma image_coe_Ioc : (coe : α → with_top α) '' (Ioc a b) = Ioc a b :=
by rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Ioc_subset_Iic_self $ Iic_subset_Iio.2 $ coe_lt_top b)]

@[simp] lemma image_coe_Ioo : (coe : α → with_top α) '' (Ioo a b) = Ioo a b :=
by rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Ioo_subset_Iio_self $ Iio_subset_Iio le_top)]

end with_top

/-! ### `with_bot` -/

namespace with_bot

variables [partial_order α] {a b : α}

@[simp] lemma range_coe : range (coe : α → with_bot α) = Ioi ⊥ :=
@with_top.range_coe (order_dual α) _

@[simp] lemma preimage_coe_Ioi : (coe : α → with_bot α) ⁻¹' (Ioi a) = Ioi a := ext $ λ x, coe_lt_coe

@[simp] lemma preimage_coe_Ici : (coe : α → with_bot α) ⁻¹' (Ici a) = Ici a := ext $ λ x, coe_le_coe

@[simp] lemma preimage_coe_Iio : (coe : α → with_bot α) ⁻¹' (Iio a) = Iio a := ext $ λ x, coe_lt_coe

@[simp] lemma preimage_coe_Iic : (coe : α → with_bot α) ⁻¹' (Iic a) = Iic a := ext $ λ x, coe_le_coe

@[simp] lemma preimage_coe_Icc : (coe : α → with_bot α) ⁻¹' (Icc a b) = Icc a b :=
by simp [← Ici_inter_Iic]

@[simp] lemma preimage_coe_Ico : (coe : α → with_bot α) ⁻¹' (Ico a b) = Ico a b :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_coe_Ioc : (coe : α → with_bot α) ⁻¹' (Ioc a b) = Ioc a b :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_coe_Ioo : (coe : α → with_bot α) ⁻¹' (Ioo a b) = Ioo a b :=
by simp [← Ioi_inter_Iio]

@[simp] lemma preimage_coe_bot : (coe : α → with_bot α) ⁻¹' {⊥} = (∅ : set α) :=
@with_top.preimage_coe_top (order_dual α) _

@[simp] lemma preimage_coe_Ioi_bot : (coe : α → with_bot α) ⁻¹' (Ioi ⊥) = univ :=
by rw [← range_coe, preimage_range]

@[simp] lemma preimage_coe_Ioc_bot : (coe : α → with_bot α) ⁻¹' (Ioc ⊥ a) = Iic a :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_coe_Ioo_bot : (coe : α → with_bot α) ⁻¹' (Ioo ⊥ a) = Iio a :=
by simp [← Ioi_inter_Iio]

@[simp] lemma image_coe_Iio : (coe : α → with_bot α) '' (Iio a) = Ioo ⊥ a :=
by rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iio]

@[simp] lemma image_coe_Iic : (coe : α → with_bot α) '' (Iic a) = Ioc ⊥ a :=
by rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iic]

@[simp] lemma image_coe_Ioi : (coe : α → with_bot α) '' (Ioi a) = Ioi a :=
by rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (Ioi_subset_Ioi bot_le)]

@[simp] lemma image_coe_Ici : (coe : α → with_bot α) '' (Ici a) = Ici a :=
by rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (Ici_subset_Ioi.2 $ bot_lt_coe a)]

@[simp] lemma image_coe_Icc : (coe : α → with_bot α) '' (Icc a b) = Icc a b :=
by rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Icc_subset_Ici_self $ Ici_subset_Ioi.2 $ bot_lt_coe a)]

@[simp] lemma image_coe_Ioc : (coe : α → with_bot α) '' (Ioc a b) = Ioc a b :=
by rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Ioc_subset_Ioi_self $ Ioi_subset_Ioi bot_le)]

@[simp] lemma image_coe_Ico : (coe : α → with_bot α) '' (Ico a b) = Ico a b :=
by rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Ico_subset_Ici_self $ Ici_subset_Ioi.2 $ bot_lt_coe a)]

@[simp] lemma image_coe_Ioo : (coe : α → with_bot α) '' (Ioo a b) = Ioo a b :=
by rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
  inter_eq_self_of_subset_left (subset.trans Ioo_subset_Ioi_self $ Ioi_subset_Ioi bot_le)]

end with_bot
