/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.char_p.basic
import algebra.group_with_zero.power

/-!
# The perfect closure of a field
-/

universes u v

open function

section defs

variables (R : Type u) [comm_semiring R] (p : ℕ) [fact p.prime] [char_p R p]

/-- A perfect ring is a ring of characteristic p that has p-th root. -/
class perfect_ring : Type u :=
(pth_root' : R → R)
(frobenius_pth_root' : ∀ x, frobenius R p (pth_root' x) = x)
(pth_root_frobenius' : ∀ x, pth_root' (frobenius R p x) = x)

/-- Frobenius automorphism of a perfect ring. -/
def frobenius_equiv [perfect_ring R p] : R ≃+* R :=
{ inv_fun := perfect_ring.pth_root' p,
  left_inv := perfect_ring.pth_root_frobenius',
  right_inv := perfect_ring.frobenius_pth_root',
  .. frobenius R p }

/-- `p`-th root of an element in a `perfect_ring` as a `ring_hom`. -/
def pth_root [perfect_ring R p] : R →+* R :=
(frobenius_equiv R p).symm

end defs

section

variables {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (f : R →* S) (g : R →+* S)
  {p : ℕ} [fact p.prime] [char_p R p] [perfect_ring R p] [char_p S p] [perfect_ring S p]

@[simp] lemma coe_frobenius_equiv : ⇑(frobenius_equiv R p) = frobenius R p := rfl

@[simp] lemma coe_frobenius_equiv_symm : ⇑(frobenius_equiv R p).symm = pth_root R p := rfl

@[simp] theorem frobenius_pth_root (x : R) : frobenius R p (pth_root R p x) = x :=
(frobenius_equiv R p).apply_symm_apply x

@[simp] theorem pth_root_pow_p (x : R) : pth_root R p x ^ p = x :=
frobenius_pth_root x

@[simp] theorem pth_root_frobenius (x : R) : pth_root R p (frobenius R p x) = x :=
(frobenius_equiv R p).symm_apply_apply x

@[simp] theorem pth_root_pow_p' (x : R) : pth_root R p (x ^ p) = x :=
pth_root_frobenius x

theorem left_inverse_pth_root_frobenius : left_inverse (pth_root R p) (frobenius R p) :=
pth_root_frobenius

theorem right_inverse_pth_root_frobenius : function.right_inverse (pth_root R p) (frobenius R p) :=
frobenius_pth_root

theorem commute_frobenius_pth_root : function.commute (frobenius R p) (pth_root R p) :=
λ x, (frobenius_pth_root x).trans (pth_root_frobenius x).symm

theorem eq_pth_root_iff {x y : R} : x = pth_root R p y ↔ frobenius R p x = y :=
(frobenius_equiv R p).to_equiv.eq_symm_apply

theorem pth_root_eq_iff {x y : R} : pth_root R p x = y ↔ x = frobenius R p y :=
(frobenius_equiv R p).to_equiv.symm_apply_eq

theorem monoid_hom.map_pth_root (x : R) : f (pth_root R p x) = pth_root S p (f x) :=
eq_pth_root_iff.2 $ by rw [← f.map_frobenius, frobenius_pth_root]

theorem monoid_hom.map_iterate_pth_root (x : R) (n : ℕ) :
  f (pth_root R p^[n] x) = (pth_root S p^[n] (f x)) :=
semiconj.iterate_right f.map_pth_root n x

theorem ring_hom.map_pth_root (x : R) :
  g (pth_root R p x) = pth_root S p (g x) :=
g.to_monoid_hom.map_pth_root x

theorem ring_hom.map_iterate_pth_root (x : R) (n : ℕ) :
  g (pth_root R p^[n] x) = (pth_root S p^[n] (g x)) :=
g.to_monoid_hom.map_iterate_pth_root x n

variables (p)
lemma injective_pow_p {x y : R} (hxy : x ^ p = y ^ p) : x = y :=
left_inverse_pth_root_frobenius.injective hxy

end

section

variables (K : Type u) [comm_ring K] (p : ℕ) [fact p.prime] [char_p K p]

/-- `perfect_closure K p` is the quotient by this relation. -/
@[mk_iff] inductive perfect_closure.r : (ℕ × K) → (ℕ × K) → Prop
| intro : ∀ n x, perfect_closure.r (n, x) (n+1, frobenius K p x)

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
def perfect_closure : Type u := quot (perfect_closure.r K p)

end

namespace perfect_closure

variables (K : Type u)

section ring

variables [comm_ring K] (p : ℕ) [fact p.prime] [char_p K p]

/-- Constructor for `perfect_closure`. -/
def mk (x : ℕ × K) : perfect_closure K p := quot.mk (r K p) x

@[simp] lemma quot_mk_eq_mk (x : ℕ × K) :
  (quot.mk (r K p) x : perfect_closure K p) = mk K p x := rfl

variables {K p}

/-- Lift a function `ℕ × K → L` to a function on `perfect_closure K p`. -/
@[elab_as_eliminator]
def lift_on {L : Type*} (x : perfect_closure K p) (f : ℕ × K → L)
  (hf : ∀ x y, r K p x y → f x = f y) : L :=
quot.lift_on x f hf

@[simp] lemma lift_on_mk {L : Sort*} (f : ℕ × K → L)
  (hf : ∀ x y, r K p x y → f x = f y) (x : ℕ × K) :
  (mk K p x).lift_on f hf = f x :=
rfl

@[elab_as_eliminator]
lemma induction_on (x : perfect_closure K p) {q : perfect_closure K p → Prop}
  (h : ∀ x, q (mk K p x)) : q x :=
quot.induction_on x h

variables (K p)

private lemma mul_aux_left (x1 x2 y : ℕ × K) (H : r K p x1 x2) :
  mk K p (x1.1 + y.1, ((frobenius K p)^[y.1] x1.2) * ((frobenius K p)^[x1.1] y.2)) =
  mk K p (x2.1 + y.1, ((frobenius K p)^[y.1] x2.2) * ((frobenius K p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro n x := quot.sound $ by rw [← iterate_succ_apply, iterate_succ',
    iterate_succ', ← frobenius_mul, nat.succ_add]; apply r.intro
end

private lemma mul_aux_right (x y1 y2 : ℕ × K) (H : r K p y1 y2) :
  mk K p (x.1 + y1.1, ((frobenius K p)^[y1.1] x.2) * ((frobenius K p)^[x.1] y1.2)) =
  mk K p (x.1 + y2.1, ((frobenius K p)^[y2.1] x.2) * ((frobenius K p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro n y := quot.sound $ by rw [← iterate_succ_apply, iterate_succ',
    iterate_succ', ← frobenius_mul]; apply r.intro
end

instance : has_mul (perfect_closure K p) :=
⟨quot.lift (λ x:ℕ×K, quot.lift (λ y:ℕ×K, mk K p
    (x.1 + y.1, ((frobenius K p)^[y.1] x.2) * ((frobenius K p)^[x.1] y.2))) (mul_aux_right K p x))
  (λ x1 x2 (H : r K p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
mul_aux_left K p x1 x2 y H)⟩

@[simp] lemma mk_mul_mk (x y : ℕ × K) :
  mk K p x * mk K p y = mk K p
    (x.1 + y.1, ((frobenius K p)^[y.1] x.2) * ((frobenius K p)^[x.1] y.2)) :=
rfl

instance : comm_monoid (perfect_closure K p) :=
{ mul_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, mul_assoc, ring_hom.iterate_map_mul,
      ← iterate_add_apply, add_comm, add_left_comm],
  one := mk K p (0, 1),
  one_mul := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [ring_hom.iterate_map_one, iterate_zero_apply, one_mul, zero_add]),
  mul_one := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [ring_hom.iterate_map_one, iterate_zero_apply, mul_one, add_zero]),
  mul_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm, mul_comm])),
  .. (infer_instance : has_mul (perfect_closure K p)) }

lemma one_def : (1 : perfect_closure K p) = mk K p (0, 1) := rfl

instance : inhabited (perfect_closure K p) := ⟨1⟩

private lemma add_aux_left (x1 x2 y : ℕ × K) (H : r K p x1 x2) :
  mk K p (x1.1 + y.1, ((frobenius K p)^[y.1] x1.2) + ((frobenius K p)^[x1.1] y.2)) =
  mk K p (x2.1 + y.1, ((frobenius K p)^[y.1] x2.2) + ((frobenius K p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro n x := quot.sound $ by rw [← iterate_succ_apply, iterate_succ',
    iterate_succ', ← frobenius_add, nat.succ_add]; apply r.intro
end

private lemma add_aux_right (x y1 y2 : ℕ × K) (H : r K p y1 y2) :
  mk K p (x.1 + y1.1, ((frobenius K p)^[y1.1] x.2) + ((frobenius K p)^[x.1] y1.2)) =
  mk K p (x.1 + y2.1, ((frobenius K p)^[y2.1] x.2) + ((frobenius K p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro n y := quot.sound $ by rw [← iterate_succ_apply, iterate_succ',
    iterate_succ', ← frobenius_add]; apply r.intro
end

instance : has_add (perfect_closure K p) :=
⟨quot.lift (λ x:ℕ×K, quot.lift (λ y:ℕ×K, mk K p
    (x.1 + y.1, ((frobenius K p)^[y.1] x.2) + ((frobenius K p)^[x.1] y.2))) (add_aux_right K p x))
  (λ x1 x2 (H : r K p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
add_aux_left K p x1 x2 y H)⟩

@[simp] lemma mk_add_mk (x y : ℕ × K) :
  mk K p x + mk K p y =
    mk K p (x.1 + y.1, ((frobenius K p)^[y.1] x.2) + ((frobenius K p)^[x.1] y.2)) := rfl

instance : has_neg (perfect_closure K p) :=
⟨quot.lift (λ x:ℕ×K, mk K p (x.1, -x.2)) (λ x y (H : r K p x y), match x, y, H with
| _, _, r.intro n x := quot.sound $ by rw ← frobenius_neg; apply r.intro
end)⟩

@[simp] lemma neg_mk (x : ℕ × K) : - mk K p x = mk K p (x.1, -x.2) := rfl

instance : has_zero (perfect_closure K p) := ⟨mk K p (0, 0)⟩

lemma zero_def : (0 : perfect_closure K p) = mk K p (0, 0) := rfl

theorem mk_zero (n : ℕ) : mk K p (n, 0) = 0 :=
by induction n with n ih; [refl, rw ← ih]; symmetry; apply quot.sound;
have := r.intro n (0:K); rwa [frobenius_zero K p] at this

theorem r.sound (m n : ℕ) (x y : K) (H : frobenius K p^[m] x = y) :
  mk K p (n, x) = mk K p (m + n, y) :=
by subst H; induction m with m ih; [simp only [zero_add, iterate_zero_apply],
  rw [ih, nat.succ_add, iterate_succ']]; apply quot.sound; apply r.intro

instance : comm_ring (perfect_closure K p) :=
{ add_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, ring_hom.iterate_map_add,
      ← iterate_add_apply, add_comm, add_left_comm],
  zero := 0,
  zero_add := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [ring_hom.iterate_map_zero, iterate_zero_apply, zero_add]),
  add_zero := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [ring_hom.iterate_map_zero, iterate_zero_apply, add_zero]),
  sub_eq_add_neg := λ a b, rfl,
  add_left_neg := λ e, quot.induction_on e (λ ⟨n, x⟩,
    by simp only [quot_mk_eq_mk, neg_mk, mk_add_mk,
      ring_hom.iterate_map_neg, add_left_neg, mk_zero]),
  add_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm])),
  left_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm, add_left_comm]; apply r.sound;
    simp only [ring_hom.iterate_map_mul, ring_hom.iterate_map_add,
      ← iterate_add_apply, mul_add, add_comm, add_left_comm],
  right_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm _ s, add_left_comm _ s]; apply r.sound;
    simp only [ring_hom.iterate_map_mul, ring_hom.iterate_map_add,
      ← iterate_add_apply, add_mul, add_comm, add_left_comm],
  .. (infer_instance : has_add (perfect_closure K p)),
  .. (infer_instance : has_neg (perfect_closure K p)),
  .. (infer_instance : comm_monoid (perfect_closure K p)) }

theorem eq_iff' (x y : ℕ × K) : mk K p x = mk K p y ↔
    ∃ z, (frobenius K p^[y.1 + z] x.2) = (frobenius K p^[x.1 + z] y.2) :=
begin
  split,
  { intro H,
    replace H := quot.exact _ H,
    induction H,
    case eqv_gen.rel : x y H
    { cases H with n x, exact ⟨0, rfl⟩ },
    case eqv_gen.refl : H
    { exact ⟨0, rfl⟩ },
    case eqv_gen.symm : x y H ih
    { cases ih with w ih, exact ⟨w, ih.symm⟩ },
    case eqv_gen.trans : x y z H1 H2 ih1 ih2
    { cases ih1 with z1 ih1,
      cases ih2 with z2 ih2,
      existsi z2+(y.1+z1),
      rw [← add_assoc, iterate_add_apply, ih1],
      rw [← iterate_add_apply, add_comm, iterate_add_apply, ih2],
      rw [← iterate_add_apply],
      simp only [add_comm, add_left_comm] } },
  intro H,
  cases x with m x,
  cases y with n y,
  cases H with z H, dsimp only at H,
  rw [r.sound K p (n+z) m x _ rfl, r.sound K p (m+z) n y _ rfl, H],
  rw [add_assoc, add_comm, add_comm z]
end

theorem nat_cast (n x : ℕ) : (x : perfect_closure K p) = mk K p (n, x) :=
begin
  induction n with n ih,
  { induction x with x ih, {refl},
    rw [nat.cast_succ, nat.cast_succ, ih], refl },
  rw ih, apply quot.sound,
  conv {congr, skip, skip, rw ← frobenius_nat_cast K p x},
  apply r.intro
end

theorem int_cast (x : ℤ) : (x : perfect_closure K p) = mk K p (0, x) :=
by induction x; simp only [int.cast_of_nat, int.cast_neg_succ_of_nat, nat_cast K p 0]; refl

theorem nat_cast_eq_iff (x y : ℕ) : (x : perfect_closure K p) = y ↔ (x : K) = y :=
begin
  split; intro H,
  { rw [nat_cast K p 0, nat_cast K p 0, eq_iff'] at H,
    cases H with z H,
    simpa only [zero_add, iterate_fixed (frobenius_nat_cast K p _)] using H },
  rw [nat_cast K p 0, nat_cast K p 0, H]
end

instance : char_p (perfect_closure K p) p :=
begin
  constructor, intro x, rw ← char_p.cast_eq_zero_iff K,
  rw [← nat.cast_zero, nat_cast_eq_iff, nat.cast_zero]
end

theorem frobenius_mk (x : ℕ × K) :
  (frobenius (perfect_closure K p) p : perfect_closure K p → perfect_closure K p)
    (mk K p x) = mk _ _ (x.1, x.2^p) :=
begin
  simp only [frobenius_def], cases x with n x, dsimp only,
  suffices : ∀ p':ℕ, mk K p (n, x) ^ p' = mk K p (n, x ^ p'),
  { apply this },
  intro p, induction p with p ih,
  case nat.zero { apply r.sound, rw [(frobenius _ _).iterate_map_one, pow_zero] },
  case nat.succ {
    rw [pow_succ, ih],
    symmetry,
    apply r.sound,
    simp only [pow_succ, (frobenius _ _).iterate_map_mul]
  }
end

/-- Embedding of `K` into `perfect_closure K p` -/
def of : K →+* perfect_closure K p :=
{ to_fun := λ x, mk _ _ (0, x),
  map_one' := rfl,
  map_mul' := λ x y, rfl,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

lemma of_apply (x : K) : of K p x = mk _ _ (0, x) := rfl

end ring

theorem eq_iff [integral_domain K] (p : ℕ) [fact p.prime] [char_p K p]
  (x y : ℕ × K) : quot.mk (r K p) x = quot.mk (r K p) y ↔
    (frobenius K p^[y.1] x.2) = (frobenius K p^[x.1] y.2) :=
(eq_iff' K p x y).trans ⟨λ ⟨z, H⟩, (frobenius_inj K p).iterate z $
  by simpa only [add_comm, iterate_add] using H,
λ H, ⟨0, H⟩⟩

section field

variables [field K] (p : ℕ) [fact p.prime] [char_p K p]

instance : has_inv (perfect_closure K p) :=
⟨quot.lift (λ x:ℕ×K, quot.mk (r K p) (x.1, x.2⁻¹)) (λ x y (H : r K p x y), match x, y, H with
| _, _, r.intro n x := quot.sound $ by { simp only [frobenius_def], rw ← inv_pow', apply r.intro }
end)⟩

instance : field (perfect_closure K p) :=
{ exists_pair_ne := ⟨0, 1, λ H, zero_ne_one ((eq_iff _ _ _ _).1 H)⟩,
  mul_inv_cancel := λ e, induction_on e $ λ ⟨m, x⟩ H,
    have _ := mt (eq_iff _ _ _ _).2 H, (eq_iff _ _ _ _).2
      (by simp only [(frobenius _ _).iterate_map_one, (frobenius K p).iterate_map_zero,
        iterate_zero_apply, ← (frobenius _ p).iterate_map_mul] at this ⊢;
        rw [mul_inv_cancel this, (frobenius _ _).iterate_map_one]),
  inv_zero := congr_arg (quot.mk (r K p)) (by rw [inv_zero]),
  .. (infer_instance : has_inv (perfect_closure K p)),
  .. (infer_instance : comm_ring (perfect_closure K p)) }


instance : perfect_ring (perfect_closure K p) p :=
{ pth_root' := λ e, lift_on e (λ x, mk K p (x.1 + 1, x.2)) (λ x y H,
    match x, y, H with
    | _, _, r.intro n x := quot.sound (r.intro _ _)
    end),
  frobenius_pth_root' := λ e, induction_on e (λ ⟨n, x⟩,
    by { simp only [lift_on_mk, frobenius_mk], exact (quot.sound $ r.intro _ _).symm }),
  pth_root_frobenius' := λ e, induction_on e (λ ⟨n, x⟩,
    by { simp only [lift_on_mk, frobenius_mk], exact (quot.sound $ r.intro _ _).symm }) }

theorem eq_pth_root (x : ℕ × K) :
  mk K p x = (pth_root (perfect_closure K p) p^[x.1] (of K p x.2)) :=
begin
  rcases x with ⟨m, x⟩,
  induction m with m ih, {refl},
  rw [iterate_succ_apply', ← ih]; refl
end

/-- Given a field `K` of characteristic `p` and a perfect ring `L` of the same characteristic,
any homomorphism `K →+* L` can be lifted to `perfect_closure K p`. -/
def lift (L : Type v) [comm_semiring L] [char_p L p] [perfect_ring L p] :
  (K →+* L) ≃ (perfect_closure K p →+* L) :=
begin
  have := left_inverse_pth_root_frobenius.iterate,
  refine_struct { .. },
  field to_fun { intro f,
    refine_struct { .. },
    field to_fun { refine λ e, lift_on e (λ x, pth_root L p^[x.1] (f x.2)) _,
      rintro a b ⟨n⟩,
      simp only [f.map_frobenius, iterate_succ_apply, pth_root_frobenius] },
    field map_one' { exact f.map_one },
    field map_zero' { exact f.map_zero },
    field map_mul' { rintro ⟨x⟩ ⟨y⟩,
      simp only [quot_mk_eq_mk, lift_on_mk, mk_mul_mk, ring_hom.map_iterate_frobenius,
        ring_hom.iterate_map_mul, ring_hom.map_mul],
      rw [iterate_add_apply, this _ _, add_comm, iterate_add_apply, this _ _] },
    field map_add' { rintro ⟨x⟩ ⟨y⟩,
      simp only [quot_mk_eq_mk, lift_on_mk, mk_add_mk, ring_hom.map_iterate_frobenius,
        ring_hom.iterate_map_add, ring_hom.map_add],
      rw [iterate_add_apply, this _ _, add_comm x.1, iterate_add_apply, this _ _] } },
  field inv_fun { exact λ f, f.comp (of K p) },
  field left_inv { intro f, ext x, refl },
  field right_inv { intro f, ext ⟨x⟩,
    simp only [ring_hom.coe_mk, quot_mk_eq_mk, ring_hom.comp_apply, lift_on_mk],
    rw [eq_pth_root, ring_hom.map_iterate_pth_root] }
end

end field

end perfect_closure
