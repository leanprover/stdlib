/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import tactic.ring_exp
import algebra.algebra.basic
import algebra.opposites
import data.equiv.ring

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `quaternion_algebra R a b`, `ℍ[R, a, b]` :
  [quaternion algebra](https://en.wikipedia.org/wiki/Quaternion_algebra) with coefficients `a`, `b`
* `quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a. `quaternion_algebra R (-1) (-1)`;
* `quaternion.norm_sq` : square of the norm of a quaternion;
* `quaternion.conj` : conjugate of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `ring ℍ[R, a, b]` and `algebra R ℍ[R, a, b]` : for any commutative ring `R`;
* `ring ℍ[R]` and `algebra R ℍ[R]` : for any commutative ring `R`;
* `domain ℍ[R]` : for a linear ordered commutative ring `R`;
* `division_algebra ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open_locale quaternion`.

* `ℍ[R, c₁, c₂]` : `quaternion_algebra R  c₁ c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/

/-- Quaternion algebra over a type with fixed coefficients $a=i^2$ and $b=j^2$.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
@[nolint unused_arguments, ext]
structure quaternion_algebra (R : Type*) (a b : R) :=
mk {} :: (re : R) (im_i : R) (im_j : R) (im_k : R)

localized "notation `ℍ[` R`,` a`,` b `]` := quaternion_algebra R a b" in quaternion

namespace quaternion_algebra

@[simp] lemma mk.eta {R : Type*} {c₁ c₂} : ∀ a : ℍ[R, c₁, c₂], mk a.1 a.2 a.3 a.4 = a
| ⟨a₁, a₂, a₃, a₄⟩ := rfl

variables {R : Type*} [comm_ring R] {c₁ c₂ : R} (r x y z : R) (a b c : ℍ[R, c₁, c₂])

instance : has_coe_t R (ℍ[R, c₁, c₂]) := ⟨λ x, ⟨x, 0, 0, 0⟩⟩

@[simp] lemma coe_re : (x : ℍ[R, c₁, c₂]).re = x := rfl
@[simp] lemma coe_im_i : (x : ℍ[R, c₁, c₂]).im_i = 0 := rfl
@[simp] lemma coe_im_j : (x : ℍ[R, c₁, c₂]).im_j = 0 := rfl
@[simp] lemma coe_im_k : (x : ℍ[R, c₁, c₂]).im_k = 0 := rfl

lemma coe_injective : function.injective (coe : R → ℍ[R, c₁, c₂]) :=
λ x y h, congr_arg re h

@[simp] lemma coe_inj {x y : R} : (x : ℍ[R, c₁, c₂]) = y ↔ x = y := coe_injective.eq_iff

@[simps] instance : has_zero ℍ[R, c₁, c₂] := ⟨⟨0, 0, 0, 0⟩⟩

@[simp, norm_cast] lemma coe_zero : ((0 : R) : ℍ[R, c₁, c₂]) = 0 := rfl

instance : inhabited ℍ[R, c₁, c₂] := ⟨0⟩

@[simps] instance : has_one ℍ[R, c₁, c₂] := ⟨⟨1, 0, 0, 0⟩⟩

@[simp, norm_cast] lemma coe_one : ((1 : R) : ℍ[R, c₁, c₂]) = 1 := rfl

@[simps] instance : has_add ℍ[R, c₁, c₂] :=
⟨λ a b, ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp] lemma mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
  (mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) + mk b₁ b₂ b₃ b₄ = mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
rfl

@[simps] instance : has_neg ℍ[R, c₁, c₂] := ⟨λ a, ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp] lemma neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
rfl

@[simps] instance : has_sub ℍ[R, c₁, c₂] :=
⟨λ a b, ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

@[simp] lemma mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
  (mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) - mk b₁ b₂ b₃ b₄ = mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
rfl

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁`;
* `j * j = c₂`;
* `i * j = k`, `j * i = -k`;
* `k * k = -c₁ * c₂`;
* `i * k = c₁ * j`, `k * i = `-c₁ * j`;
* `j * k = -c₂ * i`, `k * j = c₂ * i`.  -/
@[simps] instance : has_mul ℍ[R, c₁, c₂] := ⟨λ a b,
  ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₂ * a.3 * b.3 - c₁ * c₂ * a.4 * b.4,
   a.1 * b.2 + a.2 * b.1 - c₂ * a.3 * b.4 + c₂ * a.4 * b.3,
   a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 - c₁ *  a.4 * b.2,
   a.1 * b.4 + a.2 * b.3 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp] lemma mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
  (mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) * mk b₁ b₂ b₃ b₄ =
    ⟨a₁ * b₁ + c₁ * a₂ * b₂ + c₂ * a₃ * b₃ - c₁ * c₂ * a₄ * b₄,
     a₁ * b₂ + a₂ * b₁ - c₂ * a₃ * b₄ + c₂ * a₄ * b₃,
     a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ - c₁ *  a₄ * b₂,
     a₁ * b₄ + a₂ * b₃ - a₃ * b₂ + a₄ * b₁⟩ := rfl

instance : ring ℍ[R, c₁, c₂] :=
by refine_struct
  { add := (+),
    zero := (0 : ℍ[R, c₁, c₂]),
    neg := has_neg.neg,
    sub := has_sub.sub,
    mul := (*),
    one := 1,
    nsmul := @nsmul_rec _ ⟨0⟩ ⟨(+)⟩,
    gsmul := @gsmul_rec _ ⟨0⟩ ⟨(+)⟩ ⟨has_neg.neg⟩,
    npow := @npow_rec _ ⟨1⟩ ⟨(*)⟩ };
  intros; try { refl }; ext; simp; ring_exp

instance : algebra R ℍ[R, c₁, c₂] :=
{ smul := λ r a, ⟨r * a.1, r * a.2, r * a.3, r * a.4⟩,
  to_fun := coe,
  map_one' := rfl,
  map_zero' := rfl,
  map_mul' := λ x y, by ext; simp,
  map_add' := λ x y, by ext; simp,
  smul_def' := λ r x, by ext; simp,
  commutes' := λ r x, by ext; simp [mul_comm] }

@[simp] lemma smul_re : (r • a).re = r • a.re := rfl
@[simp] lemma smul_im_i : (r • a).im_i = r • a.im_i := rfl
@[simp] lemma smul_im_j : (r • a).im_j = r • a.im_j := rfl
@[simp] lemma smul_im_k : (r • a).im_k = r • a.im_k := rfl

@[norm_cast, simp] lemma coe_add : ((x + y : R) : ℍ[R, c₁, c₂]) = x + y :=
(algebra_map R ℍ[R, c₁, c₂]).map_add x y

@[norm_cast, simp] lemma coe_sub : ((x - y : R) : ℍ[R, c₁, c₂]) = x - y :=
(algebra_map R ℍ[R, c₁, c₂]).map_sub x y

@[norm_cast, simp] lemma coe_neg : ((-x : R) : ℍ[R, c₁, c₂]) = -x :=
(algebra_map R ℍ[R, c₁, c₂]).map_neg x

@[norm_cast, simp] lemma coe_mul : ((x * y : R) : ℍ[R, c₁, c₂]) = x * y :=
(algebra_map R ℍ[R, c₁, c₂]).map_mul x y

lemma coe_commutes : ↑r * a = a * r := algebra.commutes r a

lemma coe_commute : commute ↑r a := coe_commutes r a

lemma coe_mul_eq_smul : ↑r * a = r • a := (algebra.smul_def r a).symm

lemma mul_coe_eq_smul : a * r = r • a :=
by rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp] lemma coe_algebra_map : ⇑(algebra_map R ℍ[R, c₁, c₂]) = coe := rfl

lemma smul_coe : x • (y : ℍ[R, c₁, c₂]) = ↑(x * y) := by rw [coe_mul, coe_mul_eq_smul]

/-- Quaternion conjugate. -/
def conj : ℍ[R, c₁, c₂] ≃ₗ[R] ℍ[R, c₁, c₂] :=
linear_equiv.of_involutive
{ to_fun := λ a, ⟨a.1, -a.2, -a.3, -a.4⟩,
  map_add' := λ a b, by ext; simp [neg_add],
  map_smul' := λ r a, by ext; simp } $
λ a, by simp

@[simp] lemma re_conj : (conj a).re = a.re := rfl
@[simp] lemma im_i_conj : (conj a).im_i = - a.im_i := rfl
@[simp] lemma im_j_conj : (conj a).im_j = - a.im_j := rfl
@[simp] lemma im_k_conj : (conj a).im_k = - a.im_k := rfl

@[simp] lemma conj_conj : a.conj.conj = a := ext _ _ rfl (neg_neg _) (neg_neg _) (neg_neg _)

lemma conj_add : (a + b).conj = a.conj + b.conj := conj.map_add a b

@[simp] lemma conj_mul : (a * b).conj = b.conj * a.conj := by ext; simp; ring_exp

lemma conj_conj_mul : (a.conj * b).conj = b.conj * a :=
by rw [conj_mul, conj_conj]

lemma conj_mul_conj : (a * b.conj).conj = b * a.conj :=
by rw [conj_mul, conj_conj]

lemma self_add_conj' : a + a.conj = ↑(2 * a.re) := by ext; simp [two_mul]

lemma self_add_conj : a + a.conj = 2 * a.re :=
by simp only [self_add_conj', two_mul, coe_add]

lemma conj_add_self' : a.conj + a = ↑(2 * a.re) := by rw [add_comm, self_add_conj']

lemma conj_add_self : a.conj + a = 2 * a.re := by rw [add_comm, self_add_conj]

lemma conj_eq_two_re_sub : a.conj = ↑(2 * a.re) - a := eq_sub_iff_add_eq.2 a.conj_add_self'

lemma commute_conj_self : commute a.conj a :=
begin
  rw [a.conj_eq_two_re_sub],
  exact (coe_commute (2 * a.re) a).sub_left (commute.refl a)
end

lemma commute_self_conj : commute a a.conj :=
a.commute_conj_self.symm

lemma commute_conj_conj {a b : ℍ[R, c₁, c₂]} (h : commute a b) : commute a.conj b.conj :=
calc a.conj * b.conj = (b * a).conj    : (conj_mul b a).symm
                 ... = (a * b).conj    : by rw h.eq
                 ... = b.conj * a.conj : conj_mul a b

@[simp] lemma conj_coe : conj (x : ℍ[R, c₁, c₂]) = x := by ext; simp

lemma conj_smul : conj (r • a) = r • conj a := conj.map_smul r a

@[simp] lemma conj_one : conj (1 : ℍ[R, c₁, c₂]) = 1 := conj_coe 1

lemma eq_re_of_eq_coe {a : ℍ[R, c₁, c₂]} {x : R} (h : a = x) : a = a.re :=
by rw [h, coe_re]

lemma eq_re_iff_mem_range_coe {a : ℍ[R, c₁, c₂]} :
  a = a.re ↔ a ∈ set.range (coe : R → ℍ[R, c₁, c₂]) :=
⟨λ h, ⟨a.re, h.symm⟩, λ ⟨x, h⟩, eq_re_of_eq_coe h.symm⟩

@[simp]
lemma conj_fixed {R : Type*} [comm_ring R] [no_zero_divisors R] [char_zero R]
  {c₁ c₂ : R} {a : ℍ[R, c₁, c₂]} :
  conj a = a ↔ a = a.re :=
by simp [ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]

-- Can't use `rw ← conj_fixed` in the proof without additional assumptions

lemma conj_mul_eq_coe : conj a * a = (conj a * a).re := by ext; simp; ring_exp

lemma mul_conj_eq_coe : a * conj a = (a * conj a).re :=
by { rw a.commute_self_conj.eq, exact a.conj_mul_eq_coe }

lemma conj_zero : conj (0 : ℍ[R, c₁, c₂]) = 0 := conj.map_zero

lemma conj_neg : (-a).conj = -a.conj := (conj : ℍ[R, c₁, c₂] ≃ₗ[R] _).map_neg a

lemma conj_sub : (a - b).conj = a.conj - b.conj := (conj : ℍ[R, c₁, c₂] ≃ₗ[R] _).map_sub a b

instance : star_ring ℍ[R, c₁, c₂] :=
{ star := conj,
  star_involutive := conj_conj,
  star_add := conj_add,
  star_mul := conj_mul }

@[simp] lemma star_def (a : ℍ[R, c₁, c₂]) : star a = conj a := rfl

open opposite

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conj_ae : ℍ[R, c₁, c₂] ≃ₐ[R] (ℍ[R, c₁, c₂]ᵒᵖ) :=
{ to_fun := op ∘ conj,
  inv_fun := conj ∘ unop,
  map_mul' := λ x y, by simp,
  commutes' := λ r, by simp,
  .. conj.to_add_equiv.trans op_add_equiv }

@[simp] lemma coe_conj_ae : ⇑(conj_ae : ℍ[R, c₁, c₂] ≃ₐ[R] _) = op ∘ conj := rfl

end quaternion_algebra

/-- Space of quaternions over a type. Implemented as a structure with four fields:
`re`, `im_i`, `im_j`, and `im_k`. -/
def quaternion (R : Type*) [has_one R] [has_neg R] := quaternion_algebra R (-1) (-1)

localized "notation `ℍ[` R `]` := quaternion R" in quaternion

namespace quaternion

variables {R : Type*} [comm_ring R] (r x y z : R) (a b c : ℍ[R])

export quaternion_algebra (re im_i im_j im_k)

instance : has_coe_t R ℍ[R] := quaternion_algebra.has_coe_t
instance : ring ℍ[R] := quaternion_algebra.ring
instance : inhabited ℍ[R] := quaternion_algebra.inhabited
instance : algebra R ℍ[R] := quaternion_algebra.algebra
instance : star_ring ℍ[R] := quaternion_algebra.star_ring

@[ext] lemma ext : a.re = b.re → a.im_i = b.im_i → a.im_j = b.im_j → a.im_k = b.im_k → a = b :=
quaternion_algebra.ext a b

lemma ext_iff {a b : ℍ[R]} :
  a = b ↔ a.re = b.re ∧ a.im_i = b.im_i ∧ a.im_j = b.im_j ∧ a.im_k = b.im_k :=
quaternion_algebra.ext_iff a b

@[simp, norm_cast] lemma coe_re : (x : ℍ[R]).re = x := rfl
@[simp, norm_cast] lemma coe_im_i : (x : ℍ[R]).im_i = 0 := rfl
@[simp, norm_cast] lemma coe_im_j : (x : ℍ[R]).im_j = 0 := rfl
@[simp, norm_cast] lemma coe_im_k : (x : ℍ[R]).im_k = 0 := rfl

@[simp] lemma zero_re : (0 : ℍ[R]).re = 0 := rfl
@[simp] lemma zero_im_i : (0 : ℍ[R]).im_i = 0 := rfl
@[simp] lemma zero_im_j : (0 : ℍ[R]).im_j = 0 := rfl
@[simp] lemma zero_im_k : (0 : ℍ[R]).im_k = 0 := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : R) : ℍ[R]) = 0 := rfl

@[simp] lemma one_re : (1 : ℍ[R]).re = 1 := rfl
@[simp] lemma one_im_i : (1 : ℍ[R]).im_i = 0 := rfl
@[simp] lemma one_im_j : (1 : ℍ[R]).im_j = 0 := rfl
@[simp] lemma one_im_k : (1 : ℍ[R]).im_k = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : R) : ℍ[R]) = 1 := rfl

@[simp] lemma add_re : (a + b).re = a.re + b.re := rfl
@[simp] lemma add_im_i : (a + b).im_i = a.im_i + b.im_i := rfl
@[simp] lemma add_im_j : (a + b).im_j = a.im_j + b.im_j := rfl
@[simp] lemma add_im_k : (a + b).im_k = a.im_k + b.im_k := rfl
@[simp, norm_cast] lemma coe_add : ((x + y : R) : ℍ[R]) = x + y := quaternion_algebra.coe_add x y

@[simp] lemma neg_re : (-a).re = -a.re := rfl
@[simp] lemma neg_im_i : (-a).im_i = -a.im_i := rfl
@[simp] lemma neg_im_j : (-a).im_j = -a.im_j := rfl
@[simp] lemma neg_im_k : (-a).im_k = -a.im_k := rfl
@[simp, norm_cast] lemma coe_neg : ((-x : R) : ℍ[R]) = -x := quaternion_algebra.coe_neg x

@[simp] lemma sub_re : (a - b).re = a.re - b.re := rfl
@[simp] lemma sub_im_i : (a - b).im_i = a.im_i - b.im_i := rfl
@[simp] lemma sub_im_j : (a - b).im_j = a.im_j - b.im_j := rfl
@[simp] lemma sub_im_k : (a - b).im_k = a.im_k - b.im_k := rfl
@[simp, norm_cast] lemma coe_sub : ((x - y : R) : ℍ[R]) = x - y := quaternion_algebra.coe_sub x y

@[simp] lemma mul_re :
  (a * b).re = a.re * b.re - a.im_i * b.im_i - a.im_j * b.im_j - a.im_k * b.im_k :=
(quaternion_algebra.has_mul_mul_re a b).trans $
  by simp only [one_mul, ← neg_mul_eq_neg_mul, sub_eq_add_neg, neg_neg]

@[simp] lemma mul_im_i :
  (a * b).im_i = a.re * b.im_i + a.im_i * b.re + a.im_j * b.im_k - a.im_k * b.im_j :=
(quaternion_algebra.has_mul_mul_im_i a b).trans $
  by simp only [one_mul, ← neg_mul_eq_neg_mul, sub_eq_add_neg, neg_neg]

@[simp] lemma mul_im_j :
  (a * b).im_j = a.re * b.im_j - a.im_i * b.im_k + a.im_j * b.re + a.im_k * b.im_i :=
(quaternion_algebra.has_mul_mul_im_j a b).trans $
  by simp only [one_mul, ← neg_mul_eq_neg_mul, sub_eq_add_neg, neg_neg]

@[simp] lemma mul_im_k :
  (a * b).im_k = a.re * b.im_k + a.im_i * b.im_j - a.im_j * b.im_i + a.im_k * b.re :=
(quaternion_algebra.has_mul_mul_im_k a b).trans $
  by simp only [one_mul, ← neg_mul_eq_neg_mul, sub_eq_add_neg, neg_neg]

@[simp, norm_cast] lemma coe_mul : ((x * y : R) : ℍ[R]) = x * y := quaternion_algebra.coe_mul x y

lemma coe_injective : function.injective (coe : R → ℍ[R]) := quaternion_algebra.coe_injective

@[simp] lemma coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y := coe_injective.eq_iff

@[simp] lemma smul_re : (r • a).re = r • a.re := rfl
@[simp] lemma smul_im_i : (r • a).im_i = r • a.im_i := rfl
@[simp] lemma smul_im_j : (r • a).im_j = r • a.im_j := rfl
@[simp] lemma smul_im_k : (r • a).im_k = r • a.im_k := rfl

lemma coe_commutes : ↑r * a = a * r := quaternion_algebra.coe_commutes r a

lemma coe_commute : commute ↑r a := quaternion_algebra.coe_commute r a

lemma coe_mul_eq_smul : ↑r * a = r • a := quaternion_algebra.coe_mul_eq_smul r a

lemma mul_coe_eq_smul : a * r = r • a := quaternion_algebra.mul_coe_eq_smul r a

@[simp] lemma algebra_map_def : ⇑(algebra_map R ℍ[R]) = coe := rfl

lemma smul_coe : x • (y : ℍ[R]) = ↑(x * y) := quaternion_algebra.smul_coe x y

/-- Quaternion conjugate. -/
def conj : ℍ[R] ≃ₗ[R]  ℍ[R] := quaternion_algebra.conj

@[simp] lemma conj_re : a.conj.re = a.re := rfl
@[simp] lemma conj_im_i : a.conj.im_i = - a.im_i := rfl
@[simp] lemma conj_im_j : a.conj.im_j = - a.im_j := rfl
@[simp] lemma conj_im_k : a.conj.im_k = - a.im_k := rfl

@[simp] lemma conj_conj : a.conj.conj = a := a.conj_conj

@[simp] lemma conj_add : (a + b).conj = a.conj + b.conj := a.conj_add b

@[simp] lemma conj_mul : (a * b).conj = b.conj * a.conj := a.conj_mul b

lemma conj_conj_mul : (a.conj * b).conj = b.conj * a := a.conj_conj_mul b

lemma conj_mul_conj : (a * b.conj).conj = b * a.conj := a.conj_mul_conj b

lemma self_add_conj' : a + a.conj = ↑(2 * a.re) := a.self_add_conj'

lemma self_add_conj : a + a.conj = 2 * a.re := a.self_add_conj

lemma conj_add_self' : a.conj + a = ↑(2 * a.re) := a.conj_add_self'

lemma conj_add_self : a.conj + a = 2 * a.re := a.conj_add_self

lemma conj_eq_two_re_sub : a.conj = ↑(2 * a.re) - a := a.conj_eq_two_re_sub

lemma commute_conj_self : commute a.conj a := a.commute_conj_self

lemma commute_self_conj : commute a a.conj := a.commute_self_conj

lemma commute_conj_conj {a b : ℍ[R]} (h : commute a b) : commute a.conj b.conj :=
quaternion_algebra.commute_conj_conj h

alias commute_conj_conj ← commute.quaternion_conj

@[simp] lemma conj_coe : conj (x : ℍ[R]) = x := quaternion_algebra.conj_coe x

@[simp] lemma conj_smul : conj (r • a) = r • conj a := a.conj_smul r

@[simp] lemma conj_one : conj (1 : ℍ[R]) = 1 := conj_coe 1

lemma eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
quaternion_algebra.eq_re_of_eq_coe h

lemma eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ set.range (coe : R → ℍ[R]) :=
quaternion_algebra.eq_re_iff_mem_range_coe

@[simp] lemma conj_fixed {R : Type*} [comm_ring R] [no_zero_divisors R] [char_zero R] {a : ℍ[R]} :
  conj a = a ↔ a = a.re :=
quaternion_algebra.conj_fixed

lemma conj_mul_eq_coe : conj a * a = (conj a * a).re := a.conj_mul_eq_coe

lemma mul_conj_eq_coe : a * conj a = (a * conj a).re := a.mul_conj_eq_coe

@[simp] lemma conj_zero : conj (0:ℍ[R]) = 0 := quaternion_algebra.conj_zero

@[simp] lemma conj_neg : (-a).conj = -a.conj := a.conj_neg

@[simp] lemma conj_sub : (a - b).conj = a.conj - b.conj := a.conj_sub b

open opposite

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conj_ae : ℍ[R] ≃ₐ[R] (ℍ[R]ᵒᵖ) := quaternion_algebra.conj_ae

@[simp] lemma coe_conj_ae : ⇑(conj_ae : ℍ[R] ≃ₐ[R] ℍ[R]ᵒᵖ) = op ∘ conj := rfl

/-- Square of the norm. -/
def norm_sq : monoid_with_zero_hom ℍ[R] R :=
{ to_fun := λ a, (a * a.conj).re,
  map_zero' := by rw [conj_zero, zero_mul, zero_re],
  map_one' := by rw [conj_one, one_mul, one_re],
  map_mul' := λ x y, coe_injective $ by conv_lhs { rw [← mul_conj_eq_coe, conj_mul, mul_assoc,
    ← mul_assoc y, y.mul_conj_eq_coe, coe_commutes, ← mul_assoc, x.mul_conj_eq_coe, ← coe_mul] } }

lemma norm_sq_def : norm_sq a = (a * a.conj).re := rfl

lemma norm_sq_def' : norm_sq a = a.1^2 + a.2^2 + a.3^2 + a.4^2 :=
by simp only [norm_sq_def, sq, ← neg_mul_eq_mul_neg, sub_neg_eq_add,
  mul_re, conj_re, conj_im_i, conj_im_j, conj_im_k]

lemma norm_sq_coe : norm_sq (x : ℍ[R]) = x^2 :=
by rw [norm_sq_def, conj_coe, ← coe_mul, coe_re, sq]

@[simp] lemma norm_sq_neg : norm_sq (-a) = norm_sq a :=
by simp only [norm_sq_def, conj_neg, neg_mul_neg]

lemma self_mul_conj : a * a.conj = norm_sq a := by rw [mul_conj_eq_coe, norm_sq_def]

lemma conj_mul_self : a.conj * a = norm_sq a := by rw [← a.commute_self_conj.eq, self_mul_conj]

lemma coe_norm_sq_add :
  (norm_sq (a + b) : ℍ[R]) = norm_sq a + a * b.conj + b * a.conj + norm_sq b :=
by simp [← self_mul_conj, mul_add, add_mul, add_assoc]

end quaternion

namespace quaternion

variables {R : Type*}

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring R] {a : ℍ[R]}

@[simp] lemma norm_sq_eq_zero : norm_sq a = 0 ↔ a = 0 :=
begin
  refine ⟨λ h, _, λ h, h.symm ▸ norm_sq.map_zero⟩,
  rw [norm_sq_def', add_eq_zero_iff', add_eq_zero_iff', add_eq_zero_iff'] at h,
  exact ext a 0 (pow_eq_zero h.1.1.1) (pow_eq_zero h.1.1.2) (pow_eq_zero h.1.2) (pow_eq_zero h.2),
  all_goals { apply_rules [sq_nonneg, add_nonneg] }
end

lemma norm_sq_ne_zero : norm_sq a ≠ 0 ↔ a ≠ 0 := not_congr norm_sq_eq_zero

@[simp] lemma norm_sq_nonneg : 0 ≤ norm_sq a :=
by { rw norm_sq_def', apply_rules [sq_nonneg, add_nonneg] }

@[simp] lemma norm_sq_le_zero : norm_sq a ≤ 0 ↔ a = 0 :=
by simpa only [le_antisymm_iff, norm_sq_nonneg, and_true] using @norm_sq_eq_zero _ _ a

instance : domain ℍ[R] :=
{ exists_pair_ne := ⟨0, 1, mt (congr_arg re) zero_ne_one⟩,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ a b hab,
    have norm_sq a * norm_sq b = 0, by rwa [← norm_sq.map_mul, norm_sq_eq_zero],
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp norm_sq_eq_zero.1 norm_sq_eq_zero.1,
  .. quaternion.ring }

end linear_ordered_comm_ring

section field

variables [linear_ordered_field R] (a b : ℍ[R])

@[simps { attrs := [] }]instance : has_inv ℍ[R] := ⟨λ a, (norm_sq a)⁻¹ • a.conj⟩

instance : division_ring ℍ[R] :=
{ inv := has_inv.inv,
  inv_zero := by rw [has_inv_inv, conj_zero, smul_zero],
  mul_inv_cancel := λ a ha, by rw [has_inv_inv, algebra.mul_smul_comm, self_mul_conj, smul_coe,
    inv_mul_cancel (norm_sq_ne_zero.2 ha), coe_one],
  .. quaternion.domain }

@[simp] lemma norm_sq_inv : norm_sq a⁻¹ = (norm_sq a)⁻¹ :=
monoid_with_zero_hom.map_inv' norm_sq _

@[simp] lemma norm_sq_div : norm_sq (a / b) = norm_sq a / norm_sq b :=
monoid_with_zero_hom.map_div norm_sq a b

end field

end quaternion
