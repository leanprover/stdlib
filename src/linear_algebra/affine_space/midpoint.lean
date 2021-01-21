/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import linear_algebra.affine_space.affine_equiv

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `add_monoid_hom.of_map_midpoint`: construct an `add_monoid_hom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `point_reflection_midpoint_left`, `point_reflection_midpoint_right`:
  `equiv.point_reflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, add_monoid_hom
-/

open affine_map affine_equiv

section

variables (R : Type*) {V V' P P' : Type*} [ring R] [invertible (2:R)]
  [add_comm_group V] [semimodule R V] [add_torsor V P]
  [add_comm_group V'] [semimodule R V'] [add_torsor V' P']

include V

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
def midpoint (x y : P) : P := line_map x y (⅟2:R)

variables {R} {x y z : P}
include V'

@[simp] lemma affine_map.map_midpoint (f : P →ᵃ[R] P') (a b : P) :
  f (midpoint R a b) = midpoint R (f a) (f b) :=
f.apply_line_map a b _

@[simp] lemma affine_equiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) :
  f (midpoint R a b) = midpoint R (f a) (f b) :=
f.apply_line_map a b _

omit V'

@[simp] lemma affine_equiv.point_reflection_midpoint_left (x y : P) :
  point_reflection R (midpoint R x y) x = y :=
by rw [midpoint, point_reflection_apply, line_map_apply, vadd_vsub,
  vadd_assoc, ← add_smul, ← two_mul, mul_inv_of_self, one_smul, vsub_vadd]

lemma midpoint_comm (x y : P) : midpoint R x y = midpoint R y x :=
by rw [midpoint, ← line_map_apply_one_sub, one_sub_inv_of_two, midpoint]

@[simp] lemma affine_equiv.point_reflection_midpoint_right (x y : P) :
  point_reflection R (midpoint R x y) y = x :=
by rw [midpoint_comm, affine_equiv.point_reflection_midpoint_left]

lemma midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) :
  midpoint R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) :=
line_map_vsub_line_map _ _ _ _ _

lemma midpoint_vadd_midpoint (v v' : V) (p p' : P) :
  midpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p') :=
line_map_vadd_line_map _ _ _ _ _

lemma midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ point_reflection R z x = y :=
eq_comm.trans ((injective_point_reflection_left_of_module R x).eq_iff'
  (affine_equiv.point_reflection_midpoint_left x y)).symm

@[simp] lemma midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = (⅟2:R) • (p₂ -ᵥ p₁) :=
line_map_vsub_left _ _ _

@[simp] lemma midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = (⅟2:R) • (p₁ -ᵥ p₂) :=
by rw [midpoint_comm, midpoint_vsub_left]

@[simp] lemma left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = (⅟2:R) • (p₁ -ᵥ p₂) :=
left_vsub_line_map _ _ _

@[simp] lemma right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = (⅟2:R) • (p₂ -ᵥ p₁) :=
by rw [midpoint_comm, left_vsub_midpoint]

@[simp] lemma midpoint_sub_left (v₁ v₂ : V) : midpoint R v₁ v₂ - v₁ = (⅟2:R) • (v₂ - v₁) :=
midpoint_vsub_left v₁ v₂

@[simp] lemma midpoint_sub_right (v₁ v₂ : V) : midpoint R v₁ v₂ - v₂ = (⅟2:R) • (v₁ - v₂) :=
midpoint_vsub_right v₁ v₂

@[simp] lemma left_sub_midpoint (v₁ v₂ : V) : v₁ - midpoint R v₁ v₂ = (⅟2:R) • (v₁ - v₂) :=
left_vsub_midpoint v₁ v₂

@[simp] lemma right_sub_midpoint (v₁ v₂ : V) : v₂ - midpoint R v₁ v₂ = (⅟2:R) • (v₂ - v₁) :=
right_vsub_midpoint v₁ v₂

variable (R)

lemma midpoint_eq_midpoint_iff_vsub_eq_vsub {x x' y y' : P} :
  midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y :=
by rw [← @vsub_eq_zero_iff_eq V, midpoint_vsub_midpoint, midpoint_eq_iff, point_reflection_apply,
  vsub_eq_sub, zero_sub, vadd_eq_add, add_zero, neg_eq_iff_neg_eq, neg_vsub_eq_vsub_rev, eq_comm]

lemma midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ equiv.point_reflection z x = y :=
midpoint_eq_iff

/-- `midpoint` does not depend on the ring `R`. -/
lemma midpoint_unique (R' : Type*) [ring R'] [invertible (2:R')] [semimodule R' V] (x y : P) :
  midpoint R x y = midpoint R' x y :=
(midpoint_eq_iff' R).2 $ (midpoint_eq_iff' R').1 rfl

@[simp] lemma midpoint_self (x : P) : midpoint R x x = x :=
line_map_same_apply _ _

@[simp] lemma midpoint_add_self (x y : V) : midpoint R x y + midpoint R x y = x + y :=
calc midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x : by rw midpoint_comm
... = x + y : by rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_comm, midpoint_self]

lemma midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y :=
(midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 $ by simp [sub_add_eq_sub_sub_swap]

end

lemma line_map_inv_two {R : Type*} {V P : Type*} [division_ring R] [char_zero R]
  [add_comm_group V] [semimodule R V] [add_torsor V P] (a b : P) :
  line_map a b (2⁻¹:R) = midpoint R a b :=
rfl

lemma line_map_one_half {R : Type*} {V P : Type*} [division_ring R] [char_zero R]
  [add_comm_group V] [semimodule R V] [add_torsor V P] (a b : P) :
  line_map a b (1/2:R) = midpoint R a b :=
by rw [one_div, line_map_inv_two]

lemma homothety_inv_of_two {R : Type*} {V P : Type*} [comm_ring R] [invertible (2:R)]
  [add_comm_group V] [semimodule R V] [add_torsor V P] (a b : P) :
  homothety a (⅟2:R) b = midpoint R a b :=
rfl

lemma homothety_inv_two {k : Type*} {V P : Type*} [field k] [char_zero k]
  [add_comm_group V] [semimodule k V] [add_torsor V P] (a b : P) :
  homothety a (2⁻¹:k) b = midpoint k a b :=
rfl

lemma homothety_one_half {k : Type*} {V P : Type*} [field k] [char_zero k]
  [add_comm_group V] [semimodule k V] [add_torsor V P] (a b : P) :
  homothety a (1/2:k) b = midpoint k a b :=
by rw [one_div, homothety_inv_two]

@[simp] lemma pi_midpoint_apply {k ι : Type*} {V : Π i : ι, Type*} {P : Π i : ι, Type*} [field k]
  [invertible (2:k)] [Π i, add_comm_group (V i)] [Π i, semimodule k (V i)]
  [Π i, add_torsor (V i) (P i)] (f g : Π i, P i) (i : ι) :
  midpoint k f g i = midpoint k (f i) (g i) := rfl

namespace add_monoid_hom

variables (R R' : Type*) {E F : Type*}
  [ring R] [invertible (2:R)] [add_comm_group E] [semimodule R E]
  [ring R'] [invertible (2:R')] [add_comm_group F] [semimodule R' F]

/-- A map `f : E → F` sending zero to zero and midpoints to midpoints is an `add_monoid_hom`. -/
def of_map_midpoint (f : E → F) (h0 : f 0 = 0)
  (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
  E →+ F :=
{ to_fun := f,
  map_zero' := h0,
  map_add' := λ x y,
    calc f (x + y) = f 0 + f (x + y) : by rw [h0, zero_add]
    ... = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :
      (midpoint_add_self _ _ _).symm
    ... = f (midpoint R x y) + f (midpoint R x y) : by rw [← hm, midpoint_zero_add]
    ... = f x + f y : by rw [hm, midpoint_add_self] }

@[simp] lemma coe_of_map_midpoint (f : E → F) (h0 : f 0 = 0)
  (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
  ⇑(of_map_midpoint R R' f h0 hm) = f := rfl

end add_monoid_hom
