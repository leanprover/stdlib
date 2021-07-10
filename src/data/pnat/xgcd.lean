/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import tactic.ring
import data.pnat.prime

/-!
# Euclidean algorithm for ℕ

This file sets up a version of the Euclidean algorithm that only works with natural numbers.
Given `0 < a, b`, it computes the unique `(w, x, y, z, d)` such that the following identities hold:
* `a = (w + x) d`
* `b = (y + z) d`
* `w * z = x * y + 1`
`d` is then the gcd of `a` and `b`, and `a' := a / d = w + x` and `b' := b / d = y + z` are coprime.

This story is closely related to the structure of SL₂(ℕ) (as a free monoid on two generators) and
the theory of continued fractions.

## Main declarations

* `xgcd_type`: Helper type in defining the gcd. Encapsulates `(wp, x, y, zp, ap, bp)`. where `wp`
  `zp`, `ap`, `bp` are the variables getting changed through the algorithm.
* `is_special`: States `wp * zp = x * y + 1`
* `is_reduced`: States `ap = a ∧ bp = b`

## Notes

See `nat.xgcd` for a very similar algorithm allowing values in `ℤ`.
-/

open nat

namespace pnat

/-- A term of xgcd_type is a system of six naturals.  They should
 be thought of as representing the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 together with the vector [a, b] = [ap + 1, bp + 1].
-/
@[derive inhabited]
structure xgcd_type :=
(wp x y zp ap bp : ℕ)

namespace xgcd_type

variable (u : xgcd_type)

instance : has_sizeof xgcd_type := ⟨λ u, u.bp⟩

/-- The has_repr instance converts terms to strings in a way that
 reflects the matrix/vector interpretation as above. -/
instance : has_repr xgcd_type :=
⟨λ u, "[[[" ++ (repr (u.wp + 1)) ++ ", " ++ (repr u.x) ++
      "], [" ++ (repr u.y) ++ ", " ++ (repr (u.zp + 1)) ++ "]], [" ++
      (repr (u.ap + 1)) ++ ", " ++ (repr (u.bp + 1)) ++ "]]"⟩

def mk' (w : ℕ+) (x : ℕ) (y : ℕ) (z : ℕ+) (a : ℕ+) (b : ℕ+) : xgcd_type :=
mk w.val.pred x y z.val.pred a.val.pred b.val.pred

def w : ℕ+ := succ_pnat u.wp
def z : ℕ+ := succ_pnat u.zp
def a : ℕ+ := succ_pnat u.ap
def b : ℕ+ := succ_pnat u.bp
def r : ℕ := (u.ap + 1) % (u.bp + 1)
def q : ℕ := (u.ap + 1) / (u.bp + 1)
def qp : ℕ := u.q - 1

/-- The map v gives the product of the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 and the vector [a, b] = [ap + 1, bp + 1].  The map
 vp gives [sp, tp] such that v = [sp + 1, tp + 1].
-/
def vp : ℕ × ℕ :=
⟨ u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp,
  u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp ⟩

def v : ℕ × ℕ := ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩
def succ₂ (t : ℕ × ℕ) : ℕ × ℕ := ⟨t.1.succ, t.2.succ⟩

theorem v_eq_succ_vp : u.v = succ₂ u.vp :=
by { ext; dsimp [v, vp, w, z, a, b, succ₂];
     repeat { rw [nat.succ_eq_add_one] }; ring }

/-- is_special holds if the matrix has determinant one. -/
def is_special : Prop := u.wp + u.zp + u.wp * u.zp = u.x * u.y
def is_special' : Prop := u.w * u.z = succ_pnat (u.x * u.y)

theorem is_special_iff : u.is_special ↔ u.is_special' :=
begin
  dsimp [is_special, is_special'],
  split; intro h,
  { apply eq, dsimp [w, z, succ_pnat], rw [← h],
    repeat { rw [nat.succ_eq_add_one] }, ring },
  { apply nat.succ.inj,
    replace h := congr_arg (coe : ℕ+ → ℕ) h,
    rw [mul_coe, w, z] at h,
    repeat { rw [succ_pnat_coe, nat.succ_eq_add_one] at h },
    repeat { rw [nat.succ_eq_add_one] }, rw [← h], ring }
end

/-- is_reduced holds if the two entries in the vector are the
 same.  The reduction algorithm will produce a system with this
 property, whose product vector is the same as for the original
 system. -/
def is_reduced : Prop := u.ap = u.bp
def is_reduced' : Prop := u.a = u.b

theorem is_reduced_iff : u.is_reduced ↔ u.is_reduced' :=
⟨ congr_arg succ_pnat, succ_pnat_inj ⟩

def flip : xgcd_type :=
{ wp := u.zp, x := u.y, y := u.x, zp := u.wp, ap := u.bp, bp := u.ap }

@[simp] theorem flip_w : (flip u).w = u.z := rfl
@[simp] theorem flip_x : (flip u).x = u.y := rfl
@[simp] theorem flip_y : (flip u).y = u.x := rfl
@[simp] theorem flip_z : (flip u).z = u.w := rfl
@[simp] theorem flip_a : (flip u).a = u.b := rfl
@[simp] theorem flip_b : (flip u).b = u.a := rfl

theorem flip_is_reduced : (flip u).is_reduced ↔ u.is_reduced :=
by { dsimp [is_reduced, flip], split; intro h; exact h.symm }

theorem flip_is_special : (flip u).is_special ↔ u.is_special :=
by { dsimp [is_special, flip], rw[mul_comm u.x, mul_comm u.zp, add_comm u.zp] }

theorem flip_v : (flip u).v = (u.v).swap :=
by { dsimp [v], ext, { simp only, ring }, { simp only, ring } }

/-- Properties of division with remainder for a / b.  -/
theorem rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1 :=
nat.mod_add_div (u.ap + 1) (u.bp + 1)

theorem qp_eq (hr : u.r = 0) : u.q = u.qp + 1 :=
begin
  by_cases hq : u.q = 0,
  { let h := u.rq_eq, rw [hr, hq, mul_zero, add_zero] at h, cases h },
  { exact (nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hq)).symm }
end

/-- The following function provides the starting point for
 our algorithm.  We will apply an iterative reduction process
 to it, which will produce a system satisfying is_reduced.
 The gcd can be read off from this final system.
-/
def start (a b : ℕ+) : xgcd_type := ⟨0, 0, 0, 0, a - 1, b - 1⟩

theorem start_is_special (a b : ℕ+) : (start a b).is_special :=
by { dsimp [start, is_special], refl }

theorem start_v (a b : ℕ+) : (start a b).v = ⟨a, b⟩ :=
begin
  dsimp [start, v, xgcd_type.a, xgcd_type.b, w, z],
  rw [one_mul, one_mul, zero_mul, zero_mul, zero_add, add_zero],
  rw [← nat.pred_eq_sub_one, ← nat.pred_eq_sub_one],
  rw [nat.succ_pred_eq_of_pos a.pos, nat.succ_pred_eq_of_pos b.pos]
end

def finish : xgcd_type :=
xgcd_type.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp

theorem finish_is_reduced : u.finish.is_reduced :=
by { dsimp [is_reduced], refl }

theorem finish_is_special (hs : u.is_special) : u.finish.is_special :=
begin
  dsimp [is_special, finish] at hs ⊢,
  rw [add_mul _ _ u.y, add_comm _ (u.x * u.y), ← hs],
  ring
end

theorem finish_v (hr : u.r = 0) : u.finish.v = u.v :=
begin
  let ha : u.r + u.b * u.q = u.a := u.rq_eq,
  rw [hr, zero_add] at ha,
  ext,
  { change (u.wp + 1) * u.b + ((u.wp + 1) * u.qp + u.x) * u.b = u.w * u.a + u.x * u.b,
    have : u.wp + 1 = u.w := rfl, rw [this, ← ha, u.qp_eq hr], ring },
  { change u.y * u.b + (u.y * u.qp + u.z) * u.b = u.y * u.a + u.z * u.b,
    rw [← ha, u.qp_eq hr], ring }
end

/-- This is the main reduction step, which is used when u.r ≠ 0, or
 equivalently b does not divide a. -/
def step : xgcd_type :=
xgcd_type.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.r - 1)

/-- We will apply the above step recursively.  The following result
 is used to ensure that the process terminates. -/
theorem step_wf (hr : u.r ≠ 0) : sizeof u.step < sizeof u :=
begin
  change u.r - 1 < u.bp,
  have h₀ : (u.r - 1) + 1 = u.r := nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hr),
  have h₁ : u.r < u.bp + 1 := nat.mod_lt (u.ap + 1) u.bp.succ_pos,
  rw[← h₀] at h₁,
  exact lt_of_succ_lt_succ h₁,
end

theorem step_is_special (hs : u.is_special) : u.step.is_special :=
begin
  dsimp [is_special, step] at hs ⊢,
  rw [mul_add, mul_comm u.y u.x, ← hs],
  ring
end

/-- The reduction step does not change the product vector. -/
theorem step_v (hr : u.r ≠ 0) : u.step.v = (u.v).swap :=
begin
  let ha : u.r + u.b * u.q = u.a := u.rq_eq,
  let hr : (u.r - 1) + 1 = u.r :=
    (add_comm _ 1).trans (nat.add_sub_of_le (nat.pos_of_ne_zero hr)),
  ext,
  { change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : ℕ) = u.y * u.a + u.z * u.b,
    rw [← ha, hr], ring },
  { change ((u.w * u.q + u.x) * u.b + u.w * (u.r - 1 + 1) : ℕ) = u.w * u.a + u.x * u.b,
    rw [← ha, hr], ring }
end

/-- We can now define the full reduction function, which applies
 step as long as possible, and then applies finish. Note that the
 "have" statement puts a fact in the local context, and the
 equation compiler uses this fact to help construct the full
 definition in terms of well-founded recursion.  The same fact
 needs to be introduced in all the inductive proofs of properties
 given below. -/
def reduce : xgcd_type → xgcd_type
| u := dite (u.r = 0)
    (λ h, u.finish)
    (λ h, have sizeof u.step < sizeof u, from u.step_wf h,
     flip (reduce u.step))

theorem reduce_a {u : xgcd_type} (h : u.r = 0) :
u.reduce = u.finish := by { rw [reduce], simp only, rw [if_pos h] }

theorem reduce_b {u : xgcd_type} (h : u.r ≠ 0) :
u.reduce = u.step.reduce.flip := by { rw [reduce], simp only, rw [if_neg h, step] }

theorem reduce_reduced : ∀ (u : xgcd_type), u.reduce.is_reduced
| u := dite (u.r = 0) (λ h, by { rw [reduce_a h], exact u.finish_is_reduced })
    (λ h,  have sizeof u.step < sizeof u, from u.step_wf h,
     by { rw [reduce_b h, flip_is_reduced], apply reduce_reduced })

theorem reduce_reduced' (u : xgcd_type) : u.reduce.is_reduced' :=
(is_reduced_iff _).mp u.reduce_reduced

theorem reduce_special : ∀ (u : xgcd_type), u.is_special → u.reduce.is_special
| u := dite (u.r = 0)
    (λ h hs, by { rw [reduce_a h], exact u.finish_is_special hs })
    (λ h hs, have sizeof u.step < sizeof u, from u.step_wf h,
     by { rw [reduce_b h],
          exact (flip_is_special _).mpr (reduce_special _ (u.step_is_special hs)) })

theorem reduce_special' (u : xgcd_type) (hs : u.is_special) : u.reduce.is_special' :=
(is_special_iff _).mp (u.reduce_special hs)

theorem reduce_v : ∀ (u : xgcd_type), u.reduce.v = u.v
| u := dite (u.r = 0)
 (λ h, by {rw[reduce_a h, finish_v u h]})
 (λ h, have sizeof u.step < sizeof u, from u.step_wf h,
       by { rw[reduce_b h, flip_v, reduce_v (step u), step_v u h, prod.swap_swap] })

end xgcd_type

section gcd

variables (a b : ℕ+)

def xgcd : xgcd_type := (xgcd_type.start a b).reduce

def gcd_d : ℕ+ := (xgcd a b).a
def gcd_w : ℕ+ := (xgcd a b).w
def gcd_x : ℕ  := (xgcd a b).x
def gcd_y : ℕ  := (xgcd a b).y
def gcd_z : ℕ+ := (xgcd a b).z

def gcd_a' : ℕ+ := succ_pnat ((xgcd a b).wp + (xgcd a b).x)
def gcd_b' : ℕ+ := succ_pnat ((xgcd a b).y + (xgcd a b).zp)

theorem gcd_a'_coe : ((gcd_a' a b) : ℕ) = (gcd_w a b) + (gcd_x a b) :=
by { dsimp [gcd_a', gcd_x, gcd_w, xgcd_type.w],
     rw [nat.succ_eq_add_one, nat.succ_eq_add_one, add_right_comm] }

theorem gcd_b'_coe : ((gcd_b' a b) : ℕ) = (gcd_y a b) + (gcd_z a b) :=
by { dsimp [gcd_b', gcd_y, gcd_z, xgcd_type.z],
     rw [nat.succ_eq_add_one, nat.succ_eq_add_one, add_assoc] }

theorem gcd_props :
 let d := gcd_d a b,
  w := gcd_w a b, x := gcd_x a b, y := gcd_y a b, z := gcd_z a b,
  a' := gcd_a' a b, b' := gcd_b' a b in
 (w * z = succ_pnat (x * y) ∧
  (a = a' * d) ∧ (b = b' * d) ∧
  z * a' = succ_pnat (x * b') ∧ w * b' = succ_pnat (y * a') ∧
  (z * a : ℕ) = x * b + d ∧ (w * b : ℕ) = y * a + d
 ) :=
begin
  intros,
  let u := (xgcd_type.start a b),
  let ur := u.reduce,
  have ha : d = ur.a := rfl,
  have hb : d = ur.b := u.reduce_reduced',
  have ha' : (a' : ℕ) = w + x := gcd_a'_coe a b,
  have hb' : (b' : ℕ) = y + z := gcd_b'_coe a b,
  have hdet : w * z = succ_pnat (x * y) := u.reduce_special' rfl,
  split, exact hdet,
  have hdet' : ((w * z) : ℕ) = x * y + 1 :=
    by { rw [← mul_coe, hdet, succ_pnat_coe] },
  have huv : u.v = ⟨a, b⟩ := (xgcd_type.start_v a b),
  let hv : prod.mk (w * d + x * ur.b : ℕ) (y * d + z * ur.b : ℕ) = ⟨a, b⟩ :=
   u.reduce_v.trans (xgcd_type.start_v a b),
  rw [← hb, ← add_mul, ← add_mul, ← ha', ← hb'] at hv,
  have ha'' : (a : ℕ) = a' * d := (congr_arg prod.fst hv).symm,
  have hb'' : (b : ℕ) = b' * d := (congr_arg prod.snd hv).symm,
  split, exact eq ha'', split, exact eq hb'',
  have hza' : (z * a' : ℕ) = x * b' + 1,
  by { rw [ha', hb', mul_add, mul_add, mul_comm (z : ℕ), hdet'], ring },
  have hwb' : (w * b' : ℕ) = y * a' + 1,
  by { rw [ha', hb', mul_add, mul_add, hdet'], ring },
  split,
  { apply eq, rw [succ_pnat_coe, nat.succ_eq_add_one, mul_coe, hza'] },
  split,
  { apply eq, rw [succ_pnat_coe, nat.succ_eq_add_one, mul_coe, hwb'] },
  rw [ha'', hb''], repeat { rw [← mul_assoc] }, rw [hza', hwb'],
  split; ring,
end

theorem gcd_eq : gcd_d a b = gcd a b :=
begin
  rcases gcd_props a b with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩,
  apply dvd_antisymm,
  { apply dvd_gcd,
    exact dvd.intro (gcd_a' a b) (h₁.trans (mul_comm _ _)).symm,
    exact dvd.intro (gcd_b' a b) (h₂.trans (mul_comm _ _)).symm},
  { have h₇ : (gcd a b : ℕ) ∣ (gcd_z a b) * a :=
      dvd_trans (nat.gcd_dvd_left a b) (dvd_mul_left _ _),
    have h₈ : (gcd a b : ℕ) ∣ (gcd_x a b) * b :=
      dvd_trans (nat.gcd_dvd_right a b) (dvd_mul_left _ _),
    rw[h₅] at h₇, rw dvd_iff,
    exact (nat.dvd_add_iff_right h₈).mpr h₇,}
end

theorem gcd_det_eq :
  (gcd_w a b) * (gcd_z a b) = succ_pnat ((gcd_x a b) * (gcd_y a b)) :=
(gcd_props a b).1

theorem gcd_a_eq : a = (gcd_a' a b) * (gcd a b) :=
(gcd_eq a b) ▸ (gcd_props a b).2.1

theorem gcd_b_eq : b = (gcd_b' a b) * (gcd a b) :=
(gcd_eq a b) ▸ (gcd_props a b).2.2.1

theorem gcd_rel_left' :
  (gcd_z a b) * (gcd_a' a b) = succ_pnat ((gcd_x a b) * (gcd_b' a b)) :=
(gcd_props a b).2.2.2.1

theorem gcd_rel_right' :
  (gcd_w a b) * (gcd_b' a b) = succ_pnat ((gcd_y a b) * (gcd_a' a b)) :=
(gcd_props a b).2.2.2.2.1

theorem gcd_rel_left :
  ((gcd_z a b) * a : ℕ) = (gcd_x a b) * b + (gcd a b) :=
(gcd_eq a b) ▸ (gcd_props a b).2.2.2.2.2.1

theorem gcd_rel_right :
  ((gcd_w a b) * b : ℕ) = (gcd_y a b) * a + (gcd a b) :=
(gcd_eq a b) ▸ (gcd_props a b).2.2.2.2.2.2

end gcd
end pnat
