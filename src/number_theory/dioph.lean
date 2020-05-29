/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import number_theory.pell
import data.pfun

universe u

open nat function

namespace int

lemma eq_nat_abs_iff_mul (x n) : nat_abs x = n ↔ (x - n) * (x + n) = 0 :=
begin
  refine iff.trans _ mul_eq_zero.symm,
  refine iff.trans _ (or_congr sub_eq_zero add_eq_zero_iff_eq_neg).symm,
  exact ⟨λe, by rw ← e; apply nat_abs_eq,
    λo, by cases o; subst x; simp [nat_abs_of_nat]⟩
end

end int

/-- An alternate definition of `fin n` defined as an inductive type
  instead of a subtype of `nat`. This is useful for its induction
  principle and different definitional equalities. -/
inductive fin2 : ℕ → Type
| fz {n} : fin2 (succ n)
| fs {n} : fin2 n → fin2 (succ n)

namespace fin2

@[elab_as_eliminator]
protected def cases' {n} {C : fin2 (succ n) → Sort u} (H1 : C fz) (H2 : Π n, C (fs n)) :
  Π (i : fin2 (succ n)), C i
| fz     := H1
| (fs n) := H2 n

def elim0 {C : fin2 0 → Sort u} : Π (i : fin2 0), C i.

/-- convert a `fin2` into a `nat` -/
def to_nat : Π {n}, fin2 n → ℕ
| ._ (@fz n)   := 0
| ._ (@fs n i) := succ (to_nat i)

/-- convert a `nat` into a `fin2` if it is in range -/
def opt_of_nat : Π {n} (k : ℕ), option (fin2 n)
| 0 _ := none
| (succ n) 0 := some fz
| (succ n) (succ k) := fs <$> @opt_of_nat n k

/-- `i + k : fin2 (n + k)` when `i : fin2 n` and `k : ℕ` -/
def add {n} (i : fin2 n) : Π k, fin2 (n + k)
| 0        := i
| (succ k) := fs (add k)

/-- `left k` is the embedding `fin2 n → fin2 (k + n)` -/
def left (k) : Π {n}, fin2 n → fin2 (k + n)
| ._ (@fz n)   := fz
| ._ (@fs n i) := fs (left i)

/-- `insert_perm a` is a permutation of `fin2 n` with the following properties:
  * `insert_perm a i = i+1` if `i < a`
  * `insert_perm a a = 0`
  * `insert_perm a i = i` if `i > a` -/
def insert_perm : Π {n}, fin2 n → fin2 n → fin2 n
| ._ (@fz n)          (@fz ._)   := fz
| ._ (@fz n)          (@fs ._ j) := fs j
| ._ (@fs (succ n) i) (@fz ._)   := fs fz
| ._ (@fs (succ n) i) (@fs ._ j) := match insert_perm i j with fz := fz | fs k := fs (fs k) end

/-- `remap_left f k : fin2 (m + k) → fin2 (n + k)` applies the function
  `f : fin2 m → fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remap_left f k (m + i) = n + i`). -/
def remap_left {m n} (f : fin2 m → fin2 n) : Π k, fin2 (m + k) → fin2 (n + k)
| 0        i          := f i
| (succ k) (@fz ._)   := fz
| (succ k) (@fs ._ i) := fs (remap_left _ i)

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : ℕ`. -/
class is_lt (m n : ℕ) := (h : m < n)
instance is_lt.zero (n) : is_lt 0 (succ n) := ⟨succ_pos _⟩
instance is_lt.succ (m n) [l : is_lt m n] : is_lt (succ m) (succ n) := ⟨succ_lt_succ l.h⟩

/-- Use type class inference to infer the boundedness proof, so that we
  can directly convert a `nat` into a `fin2 n`. This supports
  notation like `&1 : fin 3`. -/
def of_nat' : Π {n} m [is_lt m n], fin2 n
| 0        m        ⟨h⟩ := absurd h (not_lt_zero _)
| (succ n) 0        ⟨h⟩ := fz
| (succ n) (succ m) ⟨h⟩ := fs (@of_nat' n m ⟨lt_of_succ_lt_succ h⟩)

local prefix `&`:max := of_nat'

end fin2

open fin2

/-- Alternate definition of `vector` based on `fin2`. -/
def vector3 (α : Type u) (n : ℕ) : Type u := fin2 n → α

namespace vector3

/-- The empty vector -/
@[pattern] def nil {α} : vector3 α 0.

/-- The vector cons operation -/
@[pattern] def cons {α} {n} (a : α) (v : vector3 α n) : vector3 α (succ n) :=
λi, by {refine i.cases' _ _, exact a, exact v}

/- We do not want to make the following notation global, because then these expressions will be
overloaded, and only the expected type will be able to disambiguate the meaning. Worse: Lean will
try to insert a coercion from `vector3 α _` to `list α`, if a list is expected. -/
localized "notation `[` l:(foldr `, ` (h t, vector3.cons h t) nil `]`) := l" in vector3
notation a :: b := cons a b

@[simp] theorem cons_fz {α} {n} (a : α) (v : vector3 α n) : (a :: v) fz = a := rfl
@[simp] theorem cons_fs {α} {n} (a : α) (v : vector3 α n) (i) : (a :: v) (fs i) = v i := rfl

/-- Get the `i`th element of a vector -/
@[reducible] def nth {α} {n} (i : fin2 n) (v : vector3 α n) : α := v i

/-- Construct a vector from a function on `fin2`. -/
@[reducible] def of_fn {α} {n} (f : fin2 n → α) : vector3 α n := f

/-- Get the head of a nonempty vector. -/
def head {α} {n} (v : vector3 α (succ n)) : α := v fz

/-- Get the tail of a nonempty vector. -/
def tail {α} {n} (v : vector3 α (succ n)) : vector3 α n := λi, v (fs i)

theorem eq_nil {α} (v : vector3 α 0) : v = [] :=
funext $ λi, match i with end

theorem cons_head_tail {α} {n} (v : vector3 α (succ n)) : head v :: tail v = v :=
funext $ λi, fin2.cases' rfl (λ_, rfl) i

def nil_elim {α} {C : vector3 α 0 → Sort u} (H : C []) (v : vector3 α 0) : C v :=
by rw eq_nil v; apply H

def cons_elim {α n} {C : vector3 α (succ n) → Sort u} (H : Π (a : α) (t : vector3 α n), C (a :: t))
  (v : vector3 α (succ n)) : C v :=
by rw ← (cons_head_tail v); apply H

@[simp] theorem cons_elim_cons {α n C H a t} : @cons_elim α n C H (a :: t) = H a t := rfl

@[elab_as_eliminator]
protected def rec_on {α} {C : Π {n}, vector3 α n → Sort u} {n} (v : vector3 α n)
  (H0 : C [])
  (Hs : Π {n} (a) (w : vector3 α n), C w → C (a :: w)) : C v :=
nat.rec_on n
  (λv, v.nil_elim H0)
  (λn IH v, v.cons_elim (λa t, Hs _ _ (IH _))) v

@[simp] theorem rec_on_nil {α C H0 Hs} : @vector3.rec_on α @C 0 [] H0 @Hs = H0 :=
rfl

@[simp] theorem rec_on_cons {α C H0 Hs n a v} :
  @vector3.rec_on α @C (succ n) (a :: v) H0 @Hs = Hs a v (@vector3.rec_on α @C n v H0 @Hs) :=
rfl

/-- Append two vectors -/
def append {α} {m} (v : vector3 α m) {n} (w : vector3 α n) : vector3 α (n+m) :=
nat.rec_on m (λ_, w) (λm IH v, v.cons_elim $ λa t, @fin2.cases' (n+m) (λ_, α) a (IH t)) v

local infix ` +-+ `:65 := vector3.append

@[simp] theorem append_nil {α} {n} (w : vector3 α n) : [] +-+ w = w := rfl

@[simp] theorem append_cons {α} (a : α) {m} (v : vector3 α m) {n} (w : vector3 α n) :
  (a::v) +-+ w = a :: (v +-+ w) := rfl

@[simp] theorem append_left {α} : ∀ {m} (i : fin2 m) (v : vector3 α m) {n} (w : vector3 α n),
  (v +-+ w) (left n i) = v i
| ._ (@fz m)   v n w := v.cons_elim (λa t, by simp [*, left])
| ._ (@fs m i) v n w := v.cons_elim (λa t, by simp [*, left])

@[simp] theorem append_add {α} : ∀ {m} (v : vector3 α m) {n} (w : vector3 α n) (i : fin2 n),
  (v +-+ w) (add i m) = w i
| 0        v n w i := rfl
| (succ m) v n w i := v.cons_elim (λa t, by simp [*, add])

/-- Insert `a` into `v` at index `i`. -/
def insert {α} (a : α) {n} (v : vector3 α n) (i : fin2 (succ n)) : vector3 α (succ n) :=
λj, (a :: v) (insert_perm i j)

@[simp] theorem insert_fz {α} (a : α) {n} (v : vector3 α n) : insert a v fz = a :: v :=
by refine funext (λj, j.cases' _ _); intros; refl

@[simp] theorem insert_fs {α} (a : α) {n} (b : α) (v : vector3 α n) (i : fin2 (succ n)) :
  insert a (b :: v) (fs i) = b :: insert a v i :=
funext $ λj, by {
  refine j.cases' _ (λj, _); simp [insert, insert_perm],
  refine fin2.cases' _ _ (insert_perm i j); simp [insert_perm] }

theorem append_insert {α} (a : α) {k} (t : vector3 α k) {n} (v : vector3 α n) (i : fin2 (succ n))
  (e : succ n + k = succ (n + k)) :
  insert a (t +-+ v) (eq.rec_on e (i.add k)) = eq.rec_on e (t +-+ insert a v i) :=
begin
  refine vector3.rec_on t (λe, _) (λk b t IH e, _) e, refl,
  have e' := succ_add n k,
  change insert a (b :: (t +-+ v)) (eq.rec_on (congr_arg succ e') (fs (add i k)))
    = eq.rec_on (congr_arg succ e') (b :: (t +-+ insert a v i)),
  rw ← (eq.drec_on e' rfl : fs (eq.rec_on e' (i.add k) : fin2 (succ (n + k))) = eq.rec_on
    (congr_arg succ e') (fs (i.add k))),
  simp, rw IH, exact eq.drec_on e' rfl
end

end vector3

section vector3
open vector3
open_locale vector3

/-- "Curried" exists, i.e. ∃ x1 ... xn, f [x1, ..., xn] -/
def vector_ex {α} : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∃x : α, vector_ex k (λv, f (x :: v))

/-- "Curried" forall, i.e. ∀ x1 ... xn, f [x1, ..., xn] -/
def vector_all {α} : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∀x : α, vector_all k (λv, f (x :: v))

theorem exists_vector_zero {α} (f : vector3 α 0 → Prop) : Exists f ↔ f [] :=
⟨λ⟨v, fv⟩, by rw ← (eq_nil v); exact fv, λf0, ⟨[], f0⟩⟩

theorem exists_vector_succ {α n} (f : vector3 α (succ n) → Prop) : Exists f ↔ ∃x v, f (x :: v) :=
⟨λ⟨v, fv⟩, ⟨_, _, by rw cons_head_tail v; exact fv⟩, λ⟨x, v, fxv⟩, ⟨_, fxv⟩⟩

theorem vector_ex_iff_exists {α} : ∀ {n} (f : vector3 α n → Prop), vector_ex n f ↔ Exists f
| 0        f := (exists_vector_zero f).symm
| (succ n) f := iff.trans (exists_congr (λx, vector_ex_iff_exists _)) (exists_vector_succ f).symm

theorem vector_all_iff_forall {α} : ∀ {n} (f : vector3 α n → Prop), vector_all n f ↔ ∀ v, f v
| 0        f := ⟨λf0 v, v.nil_elim f0, λal, al []⟩
| (succ n) f := (forall_congr (λx, vector_all_iff_forall (λv, f (x :: v)))).trans
  ⟨λal v, v.cons_elim al, λal x v, al (x::v)⟩

/-- `vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def vector_allp {α} (p : α → Prop) {n} (v : vector3 α n) : Prop :=
vector3.rec_on v true (λn a v IH, @vector3.rec_on _ (λn v, Prop) _ v (p a) (λn b v' _, p a ∧ IH))

@[simp] theorem vector_allp_nil {α} (p : α → Prop) : vector_allp p [] = true := rfl
@[simp] theorem vector_allp_singleton {α} (p : α → Prop) (x : α) : vector_allp p [x] = p x := rfl
@[simp] theorem vector_allp_cons {α} (p : α → Prop) {n} (x : α) (v : vector3 α n) :
  vector_allp p (x :: v) ↔ p x ∧ vector_allp p v :=
vector3.rec_on v (and_true _).symm (λn a v IH, iff.rfl)

theorem vector_allp_iff_forall {α} (p : α → Prop) {n} (v : vector3 α n) :
  vector_allp p v ↔ ∀ i, p (v i) :=
begin refine v.rec_on _ _,
  { exact ⟨λ_, fin2.elim0, λ_, trivial⟩ },
  { simp, refine λn a v IH, (and_congr_right (λ_, IH)).trans
      ⟨λ⟨pa, h⟩ i, by {refine i.cases' _ _, exacts [pa, h]}, λh, ⟨_, λi, _⟩⟩,
    { have h0 := h fz, simp at h0, exact h0 },
    { have hs := h (fs i), simp at hs, exact hs } }
end

theorem vector_allp.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x)
  {n} {v : vector3 α n} (al : vector_allp p v) : vector_allp q v :=
(vector_allp_iff_forall _ _).2 (λi, h _ $ (vector_allp_iff_forall _ _).1 al _)
end vector3

/-- `list_all p l` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction,
  i.e. `list_all p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp] def list_all {α} (p : α → Prop) : list α → Prop
| []        := true
| (x :: []) := p x
| (x :: l)  := p x ∧ list_all l

@[simp] theorem list_all_cons {α} (p : α → Prop) (x : α) :
  ∀ (l : list α), list_all p (x :: l) ↔ p x ∧ list_all p l
| []       := (and_true _).symm
| (x :: l) := iff.rfl

theorem list_all_iff_forall {α} (p : α → Prop) : ∀ (l : list α), list_all p l ↔ ∀ x ∈ l, p x
| []       := (iff_true_intro $ list.ball_nil _).symm
| (x :: l) := by rw [list.ball_cons, ← list_all_iff_forall l]; simp

theorem list_all.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x) :
  ∀ {l : list α}, list_all p l → list_all q l
| []       := id
| (x :: l) := by simpa using and.imp (h x) list_all.imp

@[simp] theorem list_all_map {α β} {p : β → Prop} (f : α → β) {l : list α} :
  list_all p (l.map f) ↔ list_all (p ∘ f) l :=
by induction l; simp *

theorem list_all_congr {α} {p q : α → Prop} (h : ∀ x, p x ↔ q x) {l : list α} :
  list_all p l ↔ list_all q l :=
⟨list_all.imp (λx, (h x).1), list_all.imp (λx, (h x).2)⟩

instance decidable_list_all {α} (p : α → Prop) [decidable_pred p] (l : list α) :
  decidable (list_all p l) :=
decidable_of_decidable_of_iff (by apply_instance) (list_all_iff_forall _ _).symm

/- poly -/

/-- A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplication,
  rather than only allowing monomials and addition, but the definition is equivalent
  and this is easier to use.) -/
inductive is_poly {α} : ((α → ℕ) → ℤ) → Prop
| proj : ∀ i, is_poly (λx : α → ℕ, x i)
| const : Π (n : ℤ), is_poly (λx : α → ℕ, n)
| sub : Π {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly (λx, f x - g x)
| mul : Π {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly (λx, f x * g x)

/-- The type of multivariate integer polynomials -/
def poly (α : Type u) := {f : (α → ℕ) → ℤ // is_poly f}

namespace poly
section
parameter {α : Type u}

instance : has_coe_to_fun (poly α) := ⟨_, λ f, f.1⟩

/-- The underlying function of a `poly` is a polynomial -/
lemma isp (f : poly α) : is_poly f := f.2

/-- Extensionality for `poly α` -/
lemma ext {f g : poly α} (e : ∀x, f x = g x) : f = g :=
subtype.eq (funext e)

/-- Construct a `poly` given an extensionally equivalent `poly`. -/
def subst (f : poly α) (g : (α → ℕ) → ℤ) (e : ∀x, f x = g x) : poly α :=
⟨g, by rw ← (funext e : coe_fn f = g); exact f.isp⟩
@[simp] theorem subst_eval (f g e x) : subst f g e x = g x := rfl

/-- The `i`th projection function, `x_i`. -/
def proj (i) : poly α := ⟨_, is_poly.proj i⟩
@[simp] theorem proj_eval (i x) : proj i x = x i := rfl

/-- The constant function with value `n : ℤ`. -/
def const (n) : poly α := ⟨_, is_poly.const n⟩
@[simp] theorem const_eval (n x) : const n x = n := rfl

/-- The zero polynomial -/
def zero : poly α := const 0
instance : has_zero (poly α) := ⟨poly.zero⟩
@[simp] theorem zero_eval (x) : (0 : poly α) x = 0 := rfl

/-- The zero polynomial -/
def one : poly α := const 1
instance : has_one (poly α) := ⟨poly.one⟩
@[simp] theorem one_eval (x) : (1 : poly α) x = 1 := rfl

/-- Subtraction of polynomials -/
def sub : poly α → poly α → poly α | ⟨f, pf⟩ ⟨g, pg⟩ :=
⟨_, is_poly.sub pf pg⟩
instance : has_sub (poly α) := ⟨poly.sub⟩
@[simp] theorem sub_eval : Π (f g x), (f - g : poly α) x = f x - g x
| ⟨f, pf⟩ ⟨g, pg⟩ x := rfl

/-- Negation of a polynomial -/
def neg (f : poly α) : poly α := 0 - f
instance : has_neg (poly α) := ⟨poly.neg⟩
@[simp] theorem neg_eval (f x) : (-f : poly α) x = -f x :=
show (0-f) x = _, by simp

/-- Addition of polynomials -/
def add : poly α → poly α → poly α | ⟨f, pf⟩ ⟨g, pg⟩ :=
subst (⟨f, pf⟩ - -⟨g, pg⟩) _
 (λx, show f x - (0 - g x) = f x + g x, by simp)
instance : has_add (poly α) := ⟨poly.add⟩
@[simp] theorem add_eval : Π (f g x), (f + g : poly α) x = f x + g x
| ⟨f, pf⟩ ⟨g, pg⟩ x := rfl

/-- Multiplication of polynomials -/
def mul : poly α → poly α → poly α | ⟨f, pf⟩ ⟨g, pg⟩ :=
⟨_, is_poly.mul pf pg⟩
instance : has_mul (poly α) := ⟨poly.mul⟩
@[simp] theorem mul_eval : Π (f g x), (f * g : poly α) x = f x * g x
| ⟨f, pf⟩ ⟨g, pg⟩ x := rfl

instance : comm_ring (poly α) := by refine
{ add  := (+),
  zero := 0,
  neg  := has_neg.neg,
  mul  := (*),
  one  := 1, .. };
  {intros, exact ext (λx, by simp [mul_add, mul_left_comm, mul_comm, add_comm, add_assoc])}

lemma induction {C : poly α → Prop}
  (H1 : ∀i, C (proj i)) (H2 : ∀n, C (const n))
  (H3 : ∀f g, C f → C g → C (f - g))
  (H4 : ∀f g, C f → C g → C (f * g)) (f : poly α) : C f :=
begin
  cases f with f pf,
  induction pf with i n f g pf pg ihf ihg f g pf pg ihf ihg,
  apply H1, apply H2, apply H3 _ _ ihf ihg, apply H4 _ _ ihf ihg
end

/-- The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`. -/
def sumsq : list (poly α) → poly α
| []      := 0
| (p::ps) := p*p + sumsq ps

theorem sumsq_nonneg (x) : ∀ l, 0 ≤ sumsq l x
| []      := le_refl 0
| (p::ps) := by rw sumsq; simp [-add_comm];
                exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg ps)

theorem sumsq_eq_zero (x) : ∀ l, sumsq l x = 0 ↔ list_all (λa : poly α, a x = 0) l
| []      := eq_self_iff_true _
| (p::ps) := by rw [list_all_cons, ← sumsq_eq_zero ps]; rw sumsq; simp [-add_comm]; exact
  ⟨λ(h : p x * p x + sumsq ps x = 0),
   have p x = 0, from eq_zero_of_mul_self_eq_zero $ le_antisymm
     (by rw ← h; have t := add_le_add_left (sumsq_nonneg x ps) (p x * p x); rwa [add_zero] at t)
     (mul_self_nonneg _),
   ⟨this, by simp [this] at h; exact h⟩,
  λ⟨h1, h2⟩, by rw [h1, h2]; refl⟩

end

/-- Map the index set of variables, replacing `x_i` with `x_(f i)`. -/
def remap {α β} (f : α → β) (g : poly α) : poly β :=
⟨λv, g $ v ∘ f, g.induction
  (λi, by simp; apply is_poly.proj)
  (λn, by simp; apply is_poly.const)
  (λf g pf pg, by simp; apply is_poly.sub pf pg)
  (λf g pf pg, by simp; apply is_poly.mul pf pg)⟩
@[simp] theorem remap_eval {α β} (f : α → β) (g : poly α) (v) : remap f g v = g (v ∘ f) := rfl

end poly

namespace sum

/-- combine two functions into a function on the disjoint union -/
def join {α β γ} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
by {refine sum.rec _ _, exacts [f, g]}

end sum

local infixr ` ⊗ `:65 := sum.join

open sum

namespace option

/-- Functions from `option` can be combined similarly to `vector.cons` -/
def cons {α β} (a : β) (v : α → β) : option α → β :=
by {refine option.rec _ _, exacts [a, v]}

notation a :: b := cons a b

@[simp] theorem cons_head_tail {α β} (v : option α → β) : v none :: v ∘ some = v :=
funext $ λo, by cases o; refl
end option

/- dioph -/

/-- A set `S ⊆ ℕ^α` is diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. -/
def dioph {α : Type u} (S : set (α → ℕ)) : Prop :=
∃ {β : Type u} (p : poly (α ⊕ β)), ∀ (v : α → ℕ), S v ↔ ∃t, p (v ⊗ t) = 0

namespace dioph
section
variables {α β γ : Type u}
theorem ext {S S' : set (α → ℕ)} (d : dioph S) (H : ∀v, S v ↔ S' v) : dioph S' :=
eq.rec d $ show S = S', from set.ext H

theorem of_no_dummies (S : set (α → ℕ)) (p : poly α) (h : ∀ (v : α → ℕ), S v ↔ p v = 0) :
  dioph S :=
⟨ulift empty, p.remap inl, λv, (h v).trans
  ⟨λh, ⟨λt, empty.rec _ t.down, by simp; rw [
    show (v ⊗ λt:ulift empty, empty.rec _ t.down) ∘ inl = v, from rfl, h]⟩,
  λ⟨t, ht⟩, by simp at ht; rwa [show (v ⊗ t) ∘ inl = v, from rfl] at ht⟩⟩

lemma inject_dummies_lem (f : β → γ) (g : γ → option β) (inv : ∀ x, g (f x) = some x)
  (p : poly (α ⊕ β)) (v : α → ℕ) : (∃t, p (v ⊗ t) = 0) ↔
    (∃t, p.remap (inl ⊗ (inr ∘ f)) (v ⊗ t) = 0) :=
begin
  simp, refine ⟨λt, _, λt, _⟩; cases t with t ht,
  { have : (v ⊗ (0 :: t) ∘ g) ∘ (inl ⊗ inr ∘ f) = v ⊗ t :=
    funext (λs, by cases s with a b; dsimp [join, (∘)]; try {rw inv}; refl),
    exact ⟨(0 :: t) ∘ g, by rwa this⟩ },
  { have : v ⊗ t ∘ f = (v ⊗ t) ∘ (inl ⊗ inr ∘ f) :=
    funext (λs, by cases s with a b; refl),
    exact ⟨t ∘ f, by rwa this⟩ }
end

theorem inject_dummies {S : set (α → ℕ)} (f : β → γ) (g : γ → option β)
  (inv : ∀ x, g (f x) = some x) (p : poly (α ⊕ β)) (h : ∀ (v : α → ℕ), S v ↔ ∃t, p (v ⊗ t) = 0) :
  ∃ q : poly (α ⊕ γ), ∀ (v : α → ℕ), S v ↔ ∃t, q (v ⊗ t) = 0 :=
⟨p.remap (inl ⊗ (inr ∘ f)), λv, (h v).trans $ inject_dummies_lem f g inv _ _⟩

theorem reindex_dioph {S : set (α → ℕ)} : Π (d : dioph S) (f : α → β), dioph (λv, S (v ∘ f))
| ⟨γ, p, pe⟩ f := ⟨γ, p.remap ((inl ∘ f) ⊗ inr), λv, (pe _).trans $ exists_congr $ λt,
  suffices v ∘ f ⊗ t = (v ⊗ t) ∘ (inl ∘ f ⊗ inr), by simp [this],
  funext $ λs, by cases s with a b; refl⟩

theorem dioph_list_all (l) (d : list_all dioph l) :
  dioph (λv, list_all (λS : set (α → ℕ), S v) l) :=
suffices ∃ β (pl : list (poly (α ⊕ β))), ∀ v,
  list_all (λS : set _, S v) l ↔ ∃t, list_all (λp : poly (α ⊕ β), p (v ⊗ t) = 0) pl,
from let ⟨β, pl, h⟩ := this
  in ⟨β, poly.sumsq pl, λv, (h v).trans $ exists_congr $ λt, (poly.sumsq_eq_zero _ _).symm⟩,
begin
  induction l with S l IH,
  exact ⟨ulift empty, [], λv, by simp; exact ⟨λ⟨t⟩, empty.rec _ t, trivial⟩⟩,
  simp at d,
  exact let ⟨⟨β, p, pe⟩, dl⟩ := d, ⟨γ, pl, ple⟩ := IH dl in
  ⟨β ⊕ γ, p.remap (inl ⊗ inr ∘ inl) :: pl.map (λq, q.remap (inl ⊗ (inr ∘ inr))), λv,
    by simp; exact iff.trans (and_congr (pe v) (ple v))
    ⟨λ⟨⟨m, hm⟩, ⟨n, hn⟩⟩,
      ⟨m ⊗ n, by rw [
        show (v ⊗ m ⊗ n) ∘ (inl ⊗ inr ∘ inl) = v ⊗ m,
        from funext $ λs, by cases s with a b; refl]; exact hm,
      by { refine list_all.imp (λq hq, _) hn, dsimp [(∘)],
           rw [show (λ (x : α ⊕ γ), (v ⊗ m ⊗ n) ((inl ⊗ λ (x : γ), inr (inr x)) x)) = v ⊗ n,
               from funext $ λs, by cases s with a b; refl]; exact hq }⟩,
    λ⟨t, hl, hr⟩,
      ⟨⟨t ∘ inl, by rwa [
        show (v ⊗ t) ∘ (inl ⊗ inr ∘ inl) = v ⊗ t ∘ inl,
        from funext $ λs, by cases s with a b; refl] at hl⟩,
      ⟨t ∘ inr, by {
        refine list_all.imp (λq hq, _) hr, dsimp [(∘)] at hq,
        rwa [show (λ (x : α ⊕ γ), (v ⊗ t) ((inl ⊗ λ (x : γ), inr (inr x)) x)) = v ⊗ t ∘ inr,
             from funext $ λs, by cases s with a b; refl] at hq }⟩⟩⟩⟩
end

theorem and_dioph {S S' : set (α → ℕ)} (d : dioph S) (d' : dioph S') : dioph (λv, S v ∧ S' v) :=
dioph_list_all [S, S'] ⟨d, d'⟩

theorem or_dioph {S S' : set (α → ℕ)} : ∀ (d : dioph S) (d' : dioph S'), dioph (λv, S v ∨ S' v)
| ⟨β, p, pe⟩ ⟨γ, q, qe⟩ := ⟨β ⊕ γ, p.remap (inl ⊗ inr ∘ inl) * q.remap (inl ⊗ inr ∘ inr), λv,
  begin
    refine iff.trans (or_congr ((pe v).trans _) ((qe v).trans _))
      (exists_or_distrib.symm.trans (exists_congr $ λt,
      (@mul_eq_zero_iff_eq_zero_or_eq_zero _ _ (p ((v ⊗ t) ∘ (inl ⊗ inr ∘ inl)))
        (q ((v ⊗ t) ∘ (inl ⊗ inr ∘ inr)))).symm)),
    exact inject_dummies_lem _ (some ⊗ (λ_, none)) (λx, rfl) _ _,
    exact inject_dummies_lem _ ((λ_, none) ⊗ some) (λx, rfl) _ _,
  end⟩

/-- A partial function is Diophantine if its graph is Diophantine. -/
def dioph_pfun (f : (α → ℕ) →. ℕ) := dioph (λv : option α → ℕ, f.graph (v ∘ some, v none))

/-- A function is Diophantine if its graph is Diophantine. -/
def dioph_fn (f : (α → ℕ) → ℕ) := dioph (λv : option α → ℕ, f (v ∘ some) = v none)

theorem reindex_dioph_fn {f : (α → ℕ) → ℕ} (d : dioph_fn f) (g : α → β) :
  dioph_fn (λv, f (v ∘ g)) :=
reindex_dioph d (functor.map g)

theorem ex_dioph {S : set (α ⊕ β → ℕ)} : dioph S → dioph (λv, ∃x, S (v ⊗ x))
| ⟨γ, p, pe⟩ := ⟨β ⊕ γ, p.remap ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr), λv,
  ⟨λ⟨x, hx⟩, let ⟨t, ht⟩ := (pe _).1 hx in ⟨x ⊗ t, by simp; rw [
    show (v ⊗ x ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ x) ⊗ t,
    from funext $ λs, by cases s with a b; try {cases a}; refl]; exact ht⟩,
  λ⟨t, ht⟩, ⟨t ∘ inl, (pe _).2 ⟨t ∘ inr, by simp at ht; rwa [
    show (v ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ t ∘ inl) ⊗ t ∘ inr,
    from funext $ λs, by cases s with a b; try {cases a}; refl] at ht⟩⟩⟩⟩

theorem ex1_dioph {S : set (option α → ℕ)} : dioph S → dioph (λv, ∃x, S (x :: v))
| ⟨β, p, pe⟩ := ⟨option β, p.remap (inr none :: inl ⊗ inr ∘ some), λv,
  ⟨λ⟨x, hx⟩, let ⟨t, ht⟩ := (pe _).1 hx in ⟨x :: t, by simp; rw [
    show (v ⊗ x :: t) ∘ (inr none :: inl ⊗ inr ∘ some) = x :: v ⊗ t,
    from funext $ λs, by cases s with a b; try {cases a}; refl]; exact ht⟩,
  λ⟨t, ht⟩, ⟨t none, (pe _).2 ⟨t ∘ some, by simp at ht; rwa [
    show (v ⊗ t) ∘ (inr none :: inl ⊗ inr ∘ some) = t none :: v ⊗ t ∘ some,
    from funext $ λs, by cases s with a b; try {cases a}; refl] at ht⟩⟩⟩⟩

theorem dom_dioph {f : (α → ℕ) →. ℕ} (d : dioph_pfun f) : dioph f.dom :=
cast (congr_arg dioph $ set.ext $ λv, (pfun.dom_iff_graph _ _).symm) (ex1_dioph d)

theorem dioph_fn_iff_pfun (f : (α → ℕ) → ℕ) : dioph_fn f = @dioph_pfun α f :=
by refine congr_arg dioph (set.ext $ λv, _); exact pfun.lift_graph.symm

theorem abs_poly_dioph (p : poly α) : dioph_fn (λv, (p v).nat_abs) :=
by refine of_no_dummies _ ((p.remap some - poly.proj none) * (p.remap some + poly.proj none))
  (λv, _); apply int.eq_nat_abs_iff_mul

theorem proj_dioph (i : α) : dioph_fn (λv, v i) :=
abs_poly_dioph (poly.proj i)

theorem dioph_pfun_comp1 {S : set (option α → ℕ)} (d : dioph S) {f} (df : dioph_pfun f) :
  dioph (λv : α → ℕ, ∃ h : f.dom v, S (f.fn v h :: v)) :=
ext (ex1_dioph (and_dioph d df)) $ λv,
⟨λ⟨x, hS, (h: Exists _)⟩, by
  rw [show (x :: v) ∘ some = v, from funext $ λs, rfl] at h;
  cases h with hf h; refine ⟨hf, _⟩; rw [pfun.fn, h]; exact hS,
λ⟨x, hS⟩, ⟨f.fn v x, hS, show Exists _,
  by rw [show (f.fn v x :: v) ∘ some = v, from funext $ λs, rfl]; exact ⟨x, rfl⟩⟩⟩

theorem dioph_fn_comp1 {S : set (option α → ℕ)} (d : dioph S) {f : (α → ℕ) → ℕ} (df : dioph_fn f) :
  dioph (λv : α → ℕ, S (f v :: v)) :=
ext (dioph_pfun_comp1 d (cast (dioph_fn_iff_pfun f) df)) $ λv,
⟨λ⟨_, h⟩, h, λh, ⟨trivial, h⟩⟩

end

section
variables {α β γ : Type}
open vector3
open_locale vector3
theorem dioph_fn_vec_comp1 {n} {S : set (vector3 ℕ (succ n))} (d : dioph S) {f : (vector3 ℕ n) → ℕ}
  (df : dioph_fn f) :
  dioph (λv : vector3 ℕ n, S (cons (f v) v)) :=
ext (dioph_fn_comp1 (reindex_dioph d (none :: some)) df) $ λv, by rw [
  show option.cons (f v) v ∘ (cons none some) = f v :: v,
  from funext $ λs, by cases s with a b; refl]

theorem vec_ex1_dioph (n) {S : set (vector3 ℕ (succ n))} (d : dioph S) :
  dioph (λv : vector3 ℕ n, ∃x, S (x :: v)) :=
ext (ex1_dioph $ reindex_dioph d (none :: some)) $ λv, exists_congr $ λx, by rw [
  show (option.cons x v) ∘ (cons none some) = x :: v,
  from funext $ λs, by cases s with a b; refl]

theorem dioph_fn_vec {n} (f : vector3 ℕ n → ℕ) :
  dioph_fn f ↔ dioph (λv : vector3 ℕ (succ n), f (v ∘ fs) = v fz) :=
⟨λh, reindex_dioph h (fz :: fs), λh, reindex_dioph h (none :: some)⟩

theorem dioph_pfun_vec {n} (f : vector3 ℕ n →. ℕ) :
  dioph_pfun f ↔ dioph (λv : vector3 ℕ (succ n), f.graph (v ∘ fs, v fz)) :=
⟨λh, reindex_dioph h (fz :: fs), λh, reindex_dioph h (none :: some)⟩

theorem dioph_fn_compn {α : Type} : ∀ {n} {S : set (α ⊕ fin2 n → ℕ)} (d : dioph S)
  {f : vector3 ((α → ℕ) → ℕ) n} (df : vector_allp dioph_fn f),
  dioph (λv : α → ℕ, S (v ⊗ λi, f i v))
| 0 S d f := λdf, ext (reindex_dioph d (id ⊗ fin2.elim0)) $ λv,
  by refine eq.to_iff (congr_arg S $ funext $ λs, _); {cases s with a b, refl, cases b}
| (succ n) S d f := f.cons_elim $ λf fl, by simp; exact λ df dfl,
  have dioph (λv, S (v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr)),
  from ext (dioph_fn_comp1 (reindex_dioph d (some ∘ inl ⊗ none :: some ∘ inr))
    (reindex_dioph_fn df inl)) $
    λv, by {refine eq.to_iff (congr_arg S $ funext $ λs, _); cases s with a b, refl, cases b; refl},
  have dioph (λv, S (v ⊗ f v :: λ (i : fin2 n), fl i v)),
  from @dioph_fn_compn n (λv, S (v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr)) this _ dfl,
  ext this $ λv, by rw [
    show cons (f v) (λ (i : fin2 n), fl i v) = λ (i : fin2 (succ n)), (f :: fl) i v,
    from funext $ λs, by cases s with a b; refl]

theorem dioph_comp {n} {S : set (vector3 ℕ n)} (d : dioph S)
  (f : vector3 ((α → ℕ) → ℕ) n) (df : vector_allp dioph_fn f) : dioph (λv, S (λi, f i v)) :=
dioph_fn_compn (reindex_dioph d inr) df

theorem dioph_fn_comp {n} {f : vector3 ℕ n → ℕ} (df : dioph_fn f)
  (g : vector3 ((α → ℕ) → ℕ) n) (dg : vector_allp dioph_fn g) : dioph_fn (λv, f (λi, g i v)) :=
dioph_comp ((dioph_fn_vec _).1 df) ((λv, v none) :: λi v, g i (v ∘ some)) $
by simp; exact ⟨proj_dioph none, (vector_allp_iff_forall _ _).2 $ λi,
  reindex_dioph_fn ((vector_allp_iff_forall _ _).1 dg _) _⟩

localized "notation x ` D∧ `:35 y := dioph.and_dioph x y" in dioph
localized "notation x ` D∨ `:35 y := dioph.or_dioph x y" in dioph

localized "notation `D∃`:30 := dioph.vec_ex1_dioph" in dioph

localized "prefix `&`:max := of_nat'" in dioph
theorem proj_dioph_of_nat {n : ℕ} (m : ℕ) [is_lt m n] : dioph_fn (λv : vector3 ℕ n, v &m) :=
proj_dioph &m
localized "prefix `D&`:100 := dioph.proj_dioph_of_nat" in dioph

theorem const_dioph (n : ℕ) : dioph_fn (const (α → ℕ) n) :=
abs_poly_dioph (poly.const n)
localized "prefix `D.`:100 := dioph.const_dioph" in dioph

variables {f g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g)
include df dg

theorem dioph_comp2 {S : ℕ → ℕ → Prop} (d : dioph (λv:vector3 ℕ 2, S (v &0) (v &1))) :
  dioph (λv, S (f v) (g v)) :=
dioph_comp d [f, g] (by exact ⟨df, dg⟩)

theorem dioph_fn_comp2 {h : ℕ → ℕ → ℕ} (d : dioph_fn (λv:vector3 ℕ 2, h (v &0) (v &1))) :
  dioph_fn (λv, h (f v) (g v)) :=
dioph_fn_comp d [f, g] (by exact ⟨df, dg⟩)

theorem eq_dioph : dioph (λv, f v = g v) :=
dioph_comp2 df dg $ of_no_dummies _ (poly.proj &0 - poly.proj &1)
  (λv, (int.coe_nat_eq_coe_nat_iff _ _).symm.trans
  ⟨@sub_eq_zero_of_eq ℤ _ (v &0) (v &1), λ h, eq_of_sub_eq_zero h⟩)
localized "infix ` D= `:50 := dioph.eq_dioph" in dioph

theorem add_dioph : dioph_fn (λv, f v + g v) :=
dioph_fn_comp2 df dg $ abs_poly_dioph (poly.proj &0 + poly.proj &1)
localized "infix ` D+ `:80 := dioph.add_dioph" in dioph

theorem mul_dioph : dioph_fn (λv, f v * g v) :=
dioph_fn_comp2 df dg $ abs_poly_dioph (poly.proj &0 * poly.proj &1)
localized "infix ` D* `:90 := dioph.mul_dioph" in dioph

theorem le_dioph : dioph (λv, f v ≤ g v) :=
dioph_comp2 df dg $ ext (D∃2 $ D&1 D+ D&0 D= D&2) (λv, ⟨λ⟨x, hx⟩, le.intro hx, le.dest⟩)
localized "infix ` D≤ `:50 := dioph.le_dioph" in dioph

theorem lt_dioph : dioph (λv, f v < g v) := df D+ (D. 1) D≤ dg
localized "infix ` D< `:50 := dioph.lt_dioph" in dioph

theorem ne_dioph : dioph (λv, f v ≠ g v) :=
ext (df D< dg D∨ dg D< df) $ λv, ne_iff_lt_or_gt.symm
localized "infix ` D≠ `:50 := dioph.ne_dioph" in dioph

theorem sub_dioph : dioph_fn (λv, f v - g v) :=
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $
ext (D&1 D= D&0 D+ D&2 D∨ D&1 D≤ D&2 D∧ D&0 D= D.0) $ (vector_all_iff_forall _).1 $ λx y z,
show (y = x + z ∨ y ≤ z ∧ x = 0) ↔ y - z = x, from
⟨λo, begin
  rcases o with ae | ⟨yz, x0⟩,
  { rw [ae, nat.add_sub_cancel] },
  { rw [x0, nat.sub_eq_zero_of_le yz] }
end, λh, begin
  subst x,
  cases le_total y z with yz zy,
  { exact or.inr ⟨yz, nat.sub_eq_zero_of_le yz⟩ },
  { exact or.inl (nat.sub_add_cancel zy).symm },
end⟩
localized "infix ` D- `:80 := dioph.sub_dioph" in dioph

theorem dvd_dioph : dioph (λv, f v ∣ g v) :=
dioph_comp (D∃2 $ D&2 D= D&1 D* D&0) [f, g] (by exact ⟨df, dg⟩)
localized "infix ` D∣ `:50 := dioph.dvd_dioph" in dioph

theorem mod_dioph : dioph_fn (λv, f v % g v) :=
have dioph (λv : vector3 ℕ 3, (v &2 = 0 ∨ v &0 < v &2) ∧ ∃ (x : ℕ), v &0 + v &2 * x = v &1),
from (D&2 D= D.0 D∨ D&0 D< D&2) D∧ (D∃3 $ D&1 D+ D&3 D* D&0 D= D&2),
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ ext this $ (vector_all_iff_forall _).1 $ λz x y,
show ((y = 0 ∨ z < y) ∧ ∃ c, z + y * c = x) ↔ x % y = z, from
⟨λ⟨h, c, hc⟩, begin rw ← hc; simp; cases h with x0 hl, rw [x0, mod_zero], exact mod_eq_of_lt hl end,
λe, by rw ← e; exact ⟨or_iff_not_imp_left.2 $ λh, mod_lt _ (nat.pos_of_ne_zero h), x / y,
  mod_add_div _ _⟩⟩

localized "infix ` D% `:80 := dioph.mod_dioph" in dioph

theorem modeq_dioph {h : (α → ℕ) → ℕ} (dh : dioph_fn h) : dioph (λv, f v ≡ g v [MOD h v]) :=
df D% dh D= dg D% dh
localized "notation `D≡` := dioph.modeq_dioph" in dioph

theorem div_dioph : dioph_fn (λv, f v / g v) :=
have dioph (λv : vector3 ℕ 3, v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 ≤ v &1 ∧ v &1 < (v &0 + 1) * v &2),
from (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D≤ D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2,
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ ext this $ (vector_all_iff_forall _).1 $ λz x y,
show y = 0 ∧ z = 0 ∨ z * y ≤ x ∧ x < (z + 1) * y ↔ x / y = z,
by refine iff.trans _ eq_comm; exact y.eq_zero_or_pos.elim
  (λy0, by rw [y0, nat.div_zero]; exact
    ⟨λo, (o.resolve_right $ λ⟨_, h2⟩, not_lt_zero _ h2).right, λz0, or.inl ⟨rfl, z0⟩⟩)
  (λypos, iff.trans ⟨λo, o.resolve_left $ λ⟨h1, _⟩, ne_of_gt ypos h1, or.inr⟩
    (le_antisymm_iff.trans $ and_congr (nat.le_div_iff_mul_le _ _ ypos) $
      iff.trans ⟨lt_succ_of_le, le_of_lt_succ⟩ (div_lt_iff_lt_mul _ _ ypos)).symm)
localized "infix ` D/ `:80 := dioph.div_dioph" in dioph

omit df dg
open pell

theorem pell_dioph : dioph (λv:vector3 ℕ 4, ∃ h : v &0 > 1,
  xn h (v &1) = v &2 ∧ yn h (v &1) = v &3) :=
have dioph {v : vector3 ℕ 4 |
v &0 > 1 ∧ v &1 ≤ v &3 ∧
(v &2 = 1 ∧ v &3 = 0 ∨
∃ (u w s t b : ℕ),
  v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
  u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
  s * s - (b * b - 1) * t * t = 1 ∧
  b > 1 ∧ (b ≡ 1 [MOD 4 * v &3]) ∧ (b ≡ v &0 [MOD u]) ∧
  w > 0 ∧ v &3 * v &3 ∣ w ∧
  (s ≡ v &2 [MOD u]) ∧
  (t ≡ v &1 [MOD 4 * v &3]))}, from
D.1 D< D&0 D∧ D&1 D≤ D&3 D∧
((D&2 D= D.1 D∧ D&3 D= D.0) D∨
 (D∃4 $ D∃5 $ D∃6 $ D∃7 $ D∃8 $
  D&7 D* D&7 D- (D&5 D* D&5 D- D.1) D* D&8 D* D&8 D= D.1 D∧
  D&4 D* D&4 D- (D&5 D* D&5 D- D.1) D* D&3 D* D&3 D= D.1 D∧
  D&2 D* D&2 D- (D&0 D* D&0 D- D.1) D* D&1 D* D&1 D= D.1 D∧
  D.1 D< D&0 D∧ (D≡ (D&0) (D.1) (D.4 D* D&8)) D∧ (D≡ (D&0) (D&5) D&4) D∧
  D.0 D< D&3 D∧ D&8 D* D&8 D∣ D&3 D∧
  (D≡ (D&2) (D&7) D&4) D∧
  (D≡ (D&1) (D&6) (D.4 D* D&8)))),
dioph.ext this $ λv, matiyasevic.symm

theorem xn_dioph : dioph_pfun (λv:vector3 ℕ 2, ⟨v &0 > 1, λh, xn h (v &1)⟩) :=
have dioph (λv:vector3 ℕ 3, ∃ y, ∃ h : v &1 > 1, xn h (v &2) = v &0 ∧ yn h (v &2) = y), from
let D_pell := @reindex_dioph _ (fin2 4) _ pell_dioph [&2, &3, &1, &0] in D∃3 D_pell,
(dioph_pfun_vec _).2 $ dioph.ext this $ λv, ⟨λ⟨y, h, xe, ye⟩, ⟨h, xe⟩, λ⟨h, xe⟩, ⟨_, h, xe, rfl⟩⟩

include df dg
theorem pow_dioph : dioph_fn (λv, f v ^ g v) :=
have dioph {v : vector3 ℕ 3 |
v &2 = 0 ∧ v &0 = 1 ∨ v &2 > 0 ∧
(v &1 = 0 ∧ v &0 = 0 ∨ v &1 > 0 ∧
∃ (w a t z x y : ℕ),
  (∃ (a1 : a > 1), xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
  (x ≡ y * (a - v &1) + v &0 [MOD t]) ∧
  2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
  v &0 < t ∧ v &1 ≤ w ∧ v &2 ≤ w ∧
  a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)}, from
let D_pell := @reindex_dioph _ (fin2 9) _ pell_dioph [&4, &8, &1, &0] in
(D&2 D= D.0 D∧ D&0 D= D.1) D∨ (D.0 D< D&2 D∧
((D&1 D= D.0 D∧ D&0 D= D.0) D∨ (D.0 D< D&1 D∧
 (D∃3 $ D∃4 $ D∃5 $ D∃6 $ D∃7 $ D∃8 $ D_pell D∧
  (D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3)) D∧
  D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
  D&6 D< D&3 D∧ D&7 D≤ D&5 D∧ D&8 D≤ D&5 D∧
  D&4 D* D&4 D- ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D= D.1)))),
dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ dioph.ext this $ λv, iff.symm $
eq_pow_of_pell.trans $ or_congr iff.rfl $ and_congr iff.rfl $ or_congr iff.rfl $ and_congr iff.rfl $
⟨λ⟨w, a, t, z, a1, h⟩, ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
 λ⟨w, a, t, z, ._, ._, ⟨a1, rfl, rfl⟩, h⟩, ⟨w, a, t, z, a1, h⟩⟩

end
end dioph
