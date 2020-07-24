/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Basic machinery for defining general coinductive types

Work in progress
-/
import data.pfun
import data.pfunctor.indexed.basic
import tactic.wlog meta.coinductive_predicates
import tactic.interactive

universes u v w

open nat function (hiding comp) list (hiding head')
open category_theory.functor

variables {I J : Type u}

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

namespace ipfunctor₀

variables (F : ipfunctor₀.{u} I)

namespace approx

inductive cofix_a : ℕ → I → Type u
| continue {i} : cofix_a 0 i
| intro {n} {i} : ∀ a, (F.B i a ⟶ cofix_a n) → cofix_a (succ n) i

@[ext]
lemma cofix_a_eq_zero : ∀ {i} (x y : cofix_a F 0 i), x = y
| i cofix_a.continue cofix_a.continue := rfl

variables {F}

def head' : Π {i n}, cofix_a F (succ n) i → F.A i
 | _ n (cofix_a.intro i _) := i

def children' : Π {i n} (x : cofix_a F (succ n) i), F.B i (head' x) ⟶ cofix_a F n
 | i n (cofix_a.intro a f) := f

lemma approx_eta {i} {n : ℕ} (x : cofix_a F (n+1) i) :
  x = cofix_a.intro (head' x) (children' x) :=
by cases x; refl

inductive agree
: ∀ {i} {n : ℕ}, cofix_a F n i → cofix_a F (n+1) i → Prop
 | continue {i} (x : cofix_a F 0 i) (y : cofix_a F 1 i) : agree x y
 | intro {i n} {a} (x : F.B i a ⟶ cofix_a F n) (x' : F.B i a ⟶ cofix_a F (n+1)) :
   (∀ j (b : F.B i a j), agree ((x : Π j, F.B i a j → cofix_a F n j) b) (x' b)) →
   agree (cofix_a.intro a x) (cofix_a.intro a x')

def all_agree {i} (x : Π n, cofix_a F n i) :=
∀ n, agree (x n) (x (succ n))

@[simp]
lemma agree_trival {i} {x : cofix_a F 0 i} {y : cofix_a F 1 i} : agree x y :=
by { constructor }

lemma agree_children {i} {n : ℕ} (x : cofix_a F (succ n) i) (y : cofix_a F (succ n+1) i)
  {j a b}
  (h₀ : a == b)
  (h₁ : agree x y)
: agree (@children' I _ _ _ x j a) (children' y b) :=
begin
  cases h₁, cases h₀,
  apply h₁_a_1,
end

def truncate
: ∀ {n : ℕ}, cofix_a F (n+1) ⟶ cofix_a F n
 | 0 _ (cofix_a.intro _ _) := cofix_a.continue
 | (succ n) _ (cofix_a.intro i f) := cofix_a.intro i $ f ≫ truncate

lemma truncate_eq_of_agree {i} {n : ℕ}
  (x : cofix_a F n i)
  (y : cofix_a F (succ n) i)
  (h : agree x y)
: truncate y = x :=
begin
  induction n generalizing i x y
  ; cases x ; cases y,
  { refl },
  { cases h with _ h₀ h₁,
    simp [truncate,exists_imp_distrib,(∘)],
    ext y, apply n_ih _ (h_x' _),
    apply_assumption }
end

variables {X : fam I}
variables (f : X ⟶ F.obj X)

def s_corec : Π n, X ⟶ cofix_a F n
 | 0 _ _ := cofix_a.continue
 | (succ n) _ j :=
   let ⟨y,g⟩ := f j in
   cofix_a.intro y $ g ≫ s_corec _

lemma P_corec {i} (x : X i) (n : ℕ) : agree (s_corec f n x) (s_corec f (succ n) x) :=
begin
  induction n with n generalizing i x,
  constructor,
  cases h : f x with y g,
  simp [s_corec,h,s_corec._match_1] at ⊢ n_ih,
  constructor,
  introv,
  apply n_ih,
end

def path (F : ipfunctor.{u} I I) := list $ sigma F.Idx

open list

instance {i} : subsingleton (cofix_a F 0 i) :=
⟨ by { intros, casesm* cofix_a F 0 i, refl } ⟩

open list nat
lemma head_succ' {i} (n m : ℕ) (x : Π n, cofix_a F n i)
  (Hconsistent : all_agree x)
: head' (x (succ n)) = head' (x (succ m)) :=
begin
  suffices : ∀ n, head' (x (succ n)) = head' (x 1),
  { simp [this] },
  clear m n, intro,
  cases h₀ : x (succ n) with _ _ _ i₀ f₀,
  cases h₁ : x 1 with _ i₁ f₁,
  simp [head'],
  induction n with n,
  { rw h₁ at h₀, cases h₀, trivial },
  { have H := Hconsistent (succ n),
    cases h₂ : x (succ n) with _ i₂ f₂,
    rw [h₀,h₂] at H,
    apply n_ih (f₀ ≫ truncate),
    rw h₂,
    cases H,
    congr, funext j k, dsimp [comp],
    rw truncate_eq_of_agree,
    apply H_a_1 }
end

end approx
open approx

structure M_intl (i : I) :=
(approx : ∀ n, cofix_a F n i)
(consistent : all_agree approx)

def M := @M_intl

namespace M

lemma ext' {i} (x y : M F i)
  (H : ∀ i : ℕ, x.approx i = y.approx i)
: x = y :=
begin
  cases x, cases y,
  congr, ext, apply H,
end

variables {X : fam I}
variables (f : X ⟶ F.obj X)
variables {F}

protected def corec : X ⟶ M F :=
λ i x,
{ M_intl . approx := λ n, s_corec f n x
, consistent := λ n, P_corec f x n }

variables {F}

def head : M F ⟶ F.A :=
λ i (x : M F i), head' (x.1 1)

def children : Π {i} (x : M F i), F.B i (head x) ⟶ M F
| j x i y :=
   let H := λ n : ℕ, @head_succ' _ F j n 0 x.1 x.2 in
   { M_intl . approx := λ n, children' (x.1 _) (cast (by simp [head,H]; refl) y)
   , consistent :=
     begin
       intro,
       have P' := x.2 (succ n),
       apply agree_children _ _ _ P',
       transitivity y,
       apply cast_heq,
       symmetry,
       apply cast_heq,
     end }

def ichildren {i} (x : F.Idx i) [inhabited (M F x.idx)] [decidable_eq $ F.A i] : M F i → M F x.idx
 | y :=
if H' : x.1 = head y
  then children y (cast (by simp [head,H']; refl) x.2.2)
  else default _

lemma head_succ {i} (n m : ℕ) (x : M F i)
: head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
head_succ' n m _ x.consistent

lemma head_eq_head' {i} : Π (x : M F i) (n : ℕ),
  head x = head' (x.approx $ n+1)
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma head'_eq_head {i} : Π (x : M F i) (n : ℕ),
  head' (x.approx $ n+1) = head x
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma truncate_approx {i} (x : M F i) (n : ℕ) :
  truncate (x.approx $ n+1) = x.approx n :=
truncate_eq_of_agree _ _ (x.consistent _)

def from_cofix : M F ⟶ F.obj (M F) :=
λ i x, (⟨head x,λ i a, children x a ⟩ : F.obj (M F) i)

namespace approx

protected def s_mk {i} (x : F.obj (M F) i) : Π n, cofix_a F n i
 | 0 :=  cofix_a.continue
 | (succ n) := cofix_a.intro x.1 (λ i j, (x.2 j).approx n)

protected def P_mk {i} (x : F.obj (M F) i)
: all_agree (approx.s_mk x)
 | 0 := by { constructor }
 | (succ n) := by { constructor, introv,
                    apply (x.2 _).consistent }

end approx

protected def mk : F.obj (M F) ⟶ M F :=
λ i x,
{ M_intl . approx := approx.s_mk x
, consistent := approx.P_mk x }

inductive agree' : Π {i}, ℕ → M F i → M F i → Prop
| trivial {i} (x y : M F i) : agree' 0 x y
| step {i} {n : ℕ} {a} (x y : F.B i a ⟶ M F) {x' y'} :
  x' = M.mk ⟨a,x⟩ →
  y' = M.mk ⟨a,y⟩ →
  (∀ j (a : F.B i a j), agree' n (x a) (y a)) →
  agree' (succ n) x' y'

@[simp]
lemma from_cofix_mk {i} (x : F.obj (M F) i)
: from_cofix (M.mk x) = x :=
begin
  dsimp [M.mk,from_cofix],
  cases x with x ch, congr, ext i,
  cases h : ch x_1,
  simp [children,M.approx.s_mk,children',cast_eq],
  dsimp [M.approx.s_mk,children'],
  congr, rw h,
end

lemma mk_from_cofix {i} (x : M F i)
: M.mk (from_cofix x) = x :=
begin
  apply ext', intro n,
  dsimp [M.mk],
  induction n with n,
  { dsimp [head], ext },
  dsimp [approx.s_mk,from_cofix,head],
  cases h : x.approx (succ n) with _ _ _ hd ch,
  have h' : hd = head' (x.approx 1),
  { rw [← head_succ' n,h,head'], apply x.consistent },
  revert ch, rw h', intros, congr,
  { ext _ a, dsimp [children],
    h_generalize! hh : a == a'',
    rw h, intros, cases hh, refl },
end

lemma mk_inj {i} {x y : F.obj (M F) i}
  (h : M.mk x = M.mk y) : x = y :=
by rw [← from_cofix_mk x,h,from_cofix_mk]

@[simp]
lemma mk_inj_iff {i} {x y : F.obj (M F) i} :
  M.mk x = M.mk y ↔ x = y :=
⟨mk_inj,congr_arg _⟩

protected def cases {r : Π {i}, M F i → Sort w}
  (f : ∀ {i} (x : F.obj (M F) i), r (M.mk x)) {i} (x : M F i) : r x :=
suffices r (M.mk (from_cofix x)),
  by { haveI := classical.prop_decidable,
       haveI := inhabited.mk x,
       rw [← mk_from_cofix x], exact this },
f _

protected def cases_on {r : Π {i}, M F i → Sort w}
  {i} (x : M F i) (f : ∀ {i} (x : F.obj (M F) i), r (M.mk x)) : r x :=
M.cases @f x

protected def cases_on' {r : Π {i}, M F i → Sort w}
  {i} (x : M F i) (f : ∀ {i} (a : F.A i) f, r (M.mk ⟨a,f⟩)) : r x :=
M.cases_on x (λ i ⟨a,g⟩, f a _)

lemma approx_mk {i} (a : F.A i) (f : F.B i a ⟶ M F) (i : ℕ) :
  (M.mk ⟨a, f⟩).approx (succ i) = cofix_a.intro a (λ j x, (f x).approx i) :=
by refl

lemma agree'_refl {i} {n : ℕ} (x : M F i) :
  agree' n x x :=
by { resetI, induction n generalizing i x;
     induction x using ipfunctor₀.M.cases_on'; constructor;
     try { refl }, intros, apply n_ih }

lemma agree_iff_agree' {i} {n : ℕ} (x y : M F i) :
  agree (x.approx n) (y.approx $ n+1) ↔ agree' n x y :=
begin
  split; intros h,
  { induction n generalizing i x y, constructor,
    { induction x using ipfunctor₀.M.cases_on',
      induction y using ipfunctor₀.M.cases_on',
      simp only [approx_mk] at h, cases h,
      constructor; try { refl },
      intros j a, apply n_ih, apply h_a_1 } },
  { induction n generalizing x y i, constructor,
    { cases h,
      induction x using ipfunctor₀.M.cases_on',
      induction y using ipfunctor₀.M.cases_on',
      simp only [approx_mk],
      replace h_a_1 := mk_inj h_a_1, cases h_a_1, clear h_a_1,
      replace h_a_2 := mk_inj h_a_2, cases h_a_2, clear h_a_2 i,
      constructor, intros j a,
      apply n_ih, apply h_a_3 } },
end

@[simp]
lemma cases_mk {r : Π {i}, M F i → Sort*} {i} (x : F.obj (M F) i) (f : Π i (x : F.obj (M F) i), r (M.mk x))
: ipfunctor₀.M.cases f (M.mk x) = f _ x :=
begin
  dsimp [M.mk,ipfunctor₀.M.cases,from_cofix,head,approx.s_mk,head'],
  cases x, dsimp [approx.s_mk],
  apply eq_of_heq,
  apply rec_heq_of_heq, congr,
  ext, dsimp [children,approx.s_mk,children'],
  cases h : x_snd x_1, dsimp [head],
  congr, ext,
  change (x_snd x_1).approx x_2 = _,
  rw h
end

@[simp]
lemma cases_on_mk {r : Π {i}, M F i → Sort*} {i} (x : F.obj (M F) i) (f : Π i (x : F.obj (M F) i), r (M.mk x))
: ipfunctor₀.M.cases_on (M.mk x) f = f _ x :=
cases_mk x f

@[simp]
lemma cases_on_mk' {r : Π {i}, M F i → Sort*} {i a} (x : F.B i a ⟶ M F) (f : Π {i} a (f : F.B i a ⟶ M F), r (M.mk ⟨a,f⟩))
: ipfunctor₀.M.cases_on' (M.mk ⟨a,x⟩) @f = f a x :=
cases_mk ⟨_,x⟩ _

inductive is_path : Π {i}, path F → M F i → Prop
| nil {i} (x : M F i) : is_path [] x
| cons {i} (xs : path F) {a} (x : M F i) (f : F.B i a ⟶ M F) {j} (b : F.B _ a j) :
  x = M.mk ⟨_,f⟩ →
  is_path xs (f b) →
  is_path (⟨_,a,j,b⟩ :: xs) x

lemma is_path_cons {i k} {xs : path F} {a a'} {f : F.B i a ⟶ M F} {j} {x : F.B k a' j}
  (h : is_path (⟨k,a',j,x⟩ :: xs) (M.mk ⟨a,f⟩)) :
  sigma.mk i a = ⟨k,a'⟩ :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = y,
  intros h', cases h', subst y,
  cases mk_inj h'_a_1, refl,
end

lemma is_path_cons' {i} {xs : path F} {a} {f : F.B i a ⟶ M F} {j} {x : F.B i a j}
  (h : is_path (⟨_,a,j,x⟩ :: xs) (M.mk ⟨a,f⟩)) :
  is_path xs (f x) :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = x,
  intros h', cases h', subst x,
  cases mk_inj h'_a_1, exact h'_a_2,
end

inductive isubtree {j} : Π {i}, path F → M F i → M F j → Prop
| nil (t : M F j) : isubtree [] t t
| cons {i k} (a : F.A i) (t : F.B i a ⟶ M F) (x : F.B i a k) (xs : path F) (t' : M F j) :
  isubtree xs ((t : Π j, F.B i a j → M F j) x) t' →
  isubtree (⟨i,a,_,x⟩ :: xs) (M.mk ⟨a,t⟩) t'

def iselect (ps : path F) {i j} (t : M F i) (a : F.A j) : Prop :=
∃ t' : F.B j a ⟶ M F, isubtree ps t (M.mk ⟨a,t'⟩)

lemma head_mk {i} (x : F.obj (M F) i) :
  head (M.mk x) = x.1 :=
eq.symm $
calc  x.1
    = (from_cofix (M.mk x)).1 : by rw from_cofix_mk
... = head (M.mk x)           : by refl

lemma children_mk {i j a} (f : F.B i a ⟶ M F) (x : F.B _ (head (M.mk ⟨a,f⟩)) j) :
  children (M.mk ⟨a,f⟩) x = f (cast (by rw head_mk) x) :=
by apply ext'; intro n; refl

lemma isubtree_nil {i j} (t : M F i) (t' : M F j) :
  isubtree [] t t' ↔ sigma.mk i t = ⟨j,t'⟩ :=
by split; intros h; cases h; constructor

lemma isubtree_cons (ps : path F) {i j k a b} (f : F.B i a ⟶ M F) (t : M F k) :
  isubtree (⟨i,a,j,b⟩ :: ps) (M.mk ⟨a,f⟩) t ↔ isubtree ps (f b) t :=
begin
  split; intro h,
  { generalize_hyp hh : (M.mk ⟨a, f⟩) = t' at h,
    generalize_hyp hh' : (⟨i, ⟨a, ⟨j, b⟩⟩⟩ :: ps : path F) = t'' at h,
    induction h; cases hh',
    cases M.mk_inj hh, assumption },
  { constructor, assumption }
end

lemma eq_of_isubtree_cons {ps : path F} {i i' j k a a' b} {f : F.B i a ⟶ M F} {t : M F k} :
  isubtree (⟨i',a',j,b⟩ :: ps) (M.mk ⟨a,f⟩) t → sigma.mk i' a' = ⟨i,a⟩ :=
begin
  generalize h : (M.mk ⟨a,f⟩) = z,
  intro h', cases h', cases M.mk_inj h, refl
end

lemma iselect_nil' {i a} (f : F.B i a ⟶ M F) :
  iselect nil (M.mk ⟨a,f⟩) a :=
⟨f,isubtree.nil _⟩

lemma iselect_nil {i a j a'} (f : F.B i a ⟶ M F) :
  iselect nil (M.mk ⟨a,f⟩) a' ↔ sigma.mk i a = ⟨j,a'⟩ :=
begin
  simp only [iselect,isubtree_nil] { constructor_eq := ff },
  split; intros h,
  { cases h with t' h, cases congr_arg sigma.fst h, simp only [true_and, heq_iff_eq, mk_inj_iff] at h,
    cases h.2, refl },
  { cases h, refine ⟨_,rfl⟩ }
end

lemma eq_of_iselect_cons {ps : path F} {i i' j k a a' b} {f : F.B i a ⟶ M F} {t : F.A k} :
  iselect (⟨i',a',j,b⟩ :: ps) (M.mk ⟨a,f⟩) t → sigma.mk i' a' = ⟨i,a⟩ :=
λ ⟨f,h⟩, eq_of_isubtree_cons h

lemma iselect_cons (ps : path F) {i j k a b} (f : F.B i a ⟶ M F) (t : F.A k) :
  iselect (⟨i,a,j,b⟩ :: ps) (M.mk ⟨a,f⟩) t ↔ iselect ps (f b) t :=
by simp only [iselect,isubtree_cons]

lemma isubtree_eq_default (ps : path F) {i} (x : M F i) {j} (t : M F j)
  (h : ¬ is_path ps x) :
  ¬ isubtree ps x t :=
begin
  intro h', apply h _, clear h,
  induction ps generalizing i j x t,
  { constructor },
  { rcases ps_hd with ⟨i',a,j,b⟩,
    induction x using ipfunctor₀.M.cases_on',
    classical,
    by_cases h'' : @sigma.mk _ F.A i' a = ⟨x_i,x_a⟩, cases h'',
    { rw [isubtree_cons] at h', -- rw ps_ih, intro h', apply h,
      constructor; try { refl },
      apply ps_ih (x_f b) _ h' },
    { cases eq_of_isubtree_cons h',
      rw [isubtree_cons] at h',
      constructor, refl,
      apply ps_ih _ _ h', } }
end

lemma iselect_eq_default (ps : path F) {i} (x : M F i) {j} (y : F.A j)
  (h : ¬ is_path ps x) :
  ¬ iselect ps x y :=
λ ⟨f,h'⟩, isubtree_eq_default ps _ _ h h'

lemma corec_def {i X} (f : X ⟶ F.obj X) (x₀ : X i) :
  M.corec f x₀ = M.mk (F.map (M.corec f) (f x₀))  :=
begin
  dsimp [M.corec,M.mk],
  congr, ext n,
  cases n with n,
  { dsimp [s_corec,approx.s_mk], refl, },
  { dsimp [s_corec,approx.s_mk], cases h : (f x₀),
    dsimp [s_corec._match_1,(<$>),ipfunctor.map],
    congr, }
end

lemma ext_aux {n : ℕ} {i} (x y z : M F i)
  (hx : agree' n z x)
  (hy : agree' n z y)
  (hrec : ∀ (ps : path F) {j} (a : F.A j),
             n = ps.length →
            (iselect ps x a ↔ iselect ps y a))
: x.approx (n+1) = y.approx (n+1) :=
begin
  induction n with n generalizing i x y z,
  { specialize hrec [] (head x) rfl,
    induction x using ipfunctor₀.M.cases_on', induction y using ipfunctor₀.M.cases_on',
    simp only [iselect_nil,head_mk] at hrec { constructor_eq := ff },
    cases hrec.1 rfl,
    simp only [approx_mk, true_and, eq_self_iff_true, heq_iff_eq],
    ext, },
  { cases hx, cases hy,
    induction x using ipfunctor₀.M.cases_on', induction y using ipfunctor₀.M.cases_on',
    subst z,
    replace hx_a_2 := mk_inj hx_a_2, cases hx_a_2,
    replace hy_a_1 := mk_inj hy_a_1, cases hy_a_1,
    replace hy_a_2 := mk_inj hy_a_2, cases hy_a_2,
    simp [approx_mk], ext i, apply n_ih,
    { apply hx_a_3 }, { apply hy_a_3 },
    introv h, specialize hrec (⟨_,y_a,_,x⟩ :: ps) a (congr_arg _ h),
    simp [iselect_cons] at hrec, exact hrec }
end

open ipfunctor₀.approx

variables {F}

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

local attribute [instance, priority 0] classical.prop_decidable

lemma ext
  {i} (x y : M F i)
  (H : ∀ (ps : path F) {j} (a : F.A j), iselect ps x a ↔ iselect ps y a)
: x = y :=
begin
  apply ext', intro i,
  induction i with i,
  { cases x.approx 0, cases y.approx 0, constructor },
  { apply ext_aux x y x,
    { rw ← agree_iff_agree', apply x.consistent },
    { rw [← agree_iff_agree',i_ih], apply y.consistent },
    introv H',
    simp [iselect] at H,
    cases H',
    apply H ps }
end

section bisim
  variable (R : Π {i}, M F i → M F i → Prop)
  local infix ~ := R

  structure is_bisimulation :=
  (head : ∀ {i} {a a' : F.A i} {f f'}, M.mk ⟨a,f⟩ ~ M.mk ⟨a',f'⟩ → a = a')
  (tail : ∀ {j a} {f f' : F.B j a ⟶ M F},
    M.mk ⟨a,f⟩ ~ M.mk ⟨a,f'⟩ →
    (∀ {i} (x : F.B j a i), f x ~ f' x) )

  theorem nth_of_bisim (bisim : is_bisimulation @R) {i} (s₁ s₂ : M F i) (ps : path F) :
       s₁ ~ s₂ →
         is_path ps s₁ ∨ is_path ps s₂ →
         -- (∃ a : F.A j, iselect ps s₁ a ∧ iselect ps s₂ a) ∧
         ∃ j a (f f' : F.B j a ⟶ M F),
           isubtree ps s₁ (M.mk ⟨a,f⟩) ∧
           isubtree ps s₂ (M.mk ⟨a,f'⟩) ∧
         ∀ {k} (x : F.B j a k), f x ~ f' x :=
  begin
    intros hh,
    induction s₁ using ipfunctor₀.M.cases_on' with i a f,
    induction s₂ using ipfunctor₀.M.cases_on' with i' a' f',
    have : a = a' := bisim.head hh, subst a',
    induction ps with p ps generalizing i' a f f',
    { intro, existsi [_,a,f,f'], simp [isubtree_nil],
      intros, apply bisim.tail hh, },
    rintro hh',
    rcases p with ⟨aa,b,c,d⟩,
    have : sigma.mk _ a = ⟨aa,b⟩,
    { cases hh'; cases is_path_cons hh'; refl },
    cases this, simp only [isubtree_cons] at ⊢,
    have h₁ := bisim.tail hh d,
    induction h : (f d) using ipfunctor₀.M.cases_on' with i₀ a₀ f₀,
    induction h' : (f' d) using ipfunctor₀.M.cases_on' with i₁ a₁ f₁,
    rw [h,h'] at h₁,
    have : a₀ = a₁ := bisim.head h₁, subst a₁,
    apply (ps_ih _ _ _ h₁),
    rw [← h,← h'], apply or_of_or_of_imp_of_imp hh' is_path_cons' is_path_cons'
  end

  lemma det {i j k} {x : M F i} {s₁ : M F j} {s₂ : M F k} (ps : path F)
    (h : isubtree ps x s₁)
    (h' : isubtree ps x s₂) : sigma.mk j s₁ = ⟨k,s₂⟩ :=
  begin
    induction ps generalizing i x; cases h, cases h', refl,
    erw isubtree_cons at h h', apply @ps_ih _ (h_t h_x) h h',
  end

  lemma det' {i j k} {x : M F i} {s₁ : F.A j} {s₂ : F.A k} (ps : path F)
    (h : iselect ps x s₁)
    (h' : iselect ps x s₂) : sigma.mk j s₁ = ⟨k,s₂⟩ :=
  begin
    cases h with f h,
    cases h' with f' h',
    have := det _ h h', cases congr_arg sigma.fst this,
    simp [-sigma.mk.inj_iff] at this, cases this, refl,
  end

  lemma d {i j} {s₁ s₂ : M F i} (ps : path F)
    (h : ∃ {j} (a : F.A j), iselect ps s₁ a ∧ iselect ps s₂ a) :
    (∀ (a : F.A j), iselect ps s₁ a ↔ iselect ps s₂ a) :=
  begin
    introv, rcases h with ⟨k,b,h,h'⟩,
    by_cases h₁ : sigma.mk j a = ⟨k,b⟩,
    { cases h₁, apply iff_of_true h h' },
    { apply iff_of_false,
      { intro h₂, cases det' ps h h₂,
        apply h₁ rfl },
      { intro h₂, cases det' ps h' h₂,
        apply h₁ rfl }  }
  end

  theorem eq_of_bisim (bisim : is_bisimulation @R) : ∀ {i} {s₁ s₂ : M F i}, s₁ ~ s₂ → s₁ = s₂ :=
  begin
    introv Hr, apply ext,
    intros ps j,
    by_cases h : is_path ps s₁ ∨ is_path ps s₂,
    { have H := nth_of_bisim @R bisim _ _ ps Hr h,
      apply d, rcases H with ⟨k,a,f,f',h₀,h₁,h₂⟩,
      refine ⟨k,a,⟨f,h₀⟩,⟨f',h₁⟩⟩ },
    { rw not_or_distrib at h, cases h with h₀ h₁,
      simp only [iselect_eq_default,*,not_false_iff,false_iff,forall_true_iff], }
  end
end bisim

section coinduction

variables F

coinductive R : Π i (s₁ s₂ : M F i), Prop
| intro {i a} (s₁ s₂ : F.B i a ⟶ M F) :
   (∀ j (x : F.B i a j), R j ((s₁ : Π {j}, F.B i a j → M F j) x) (s₂ x)) →
   R i (M.mk ⟨_,s₁⟩) (M.mk ⟨_,s₂⟩)

section

open ulift

lemma R_is_bisimulation : is_bisimulation (R F) :=
begin
  constructor; introv hr,
  { suffices : (λ a b, head a = head b) (M.mk ⟨a, f⟩) (M.mk ⟨a', f'⟩),
    { simp only [head_mk] at this, exact this },
    refine R.cases_on _ hr _,
    intros, simp only [head_mk] },
  { revert hr,
    suffices : ∀ k (y z : M F k)
      (hy : sigma.mk k y = ⟨j,M.mk ⟨a, f⟩⟩)
      (hz : sigma.mk k z = ⟨j,M.mk ⟨a, f'⟩⟩)
      (hr : R F k y z), R F i (f x) (f' x),
    { apply this _ _ _ rfl rfl },
    intros, revert hy hz,
    refine R.cases_on _ hr _,
    introv h₂ hy hz,
    cases congr_arg sigma.fst hy, simp only [true_and, heq_iff_eq, mk_inj_iff] at hy,
    cases congr_arg sigma.fst hz, simp only [true_and, heq_iff_eq, mk_inj_iff] at hz,
    cases hy.2, cases hz.2,
    apply h₂ },
end

end
variables {F}

lemma coinduction {i} {s₁ s₂ : M F i}
  (hh : R F i s₁ s₂)
: s₁ = s₂ :=
begin
  exact eq_of_bisim
    (R F) (R_is_bisimulation F)
    hh
end

lemma coinduction' {i} {s₁ s₂ : M F i}
  (hh : R F _ s₁ s₂)
: s₁ = s₂ :=
begin
  have hh' := hh, revert hh',
  apply R.cases_on F hh, clear hh s₁ s₂,
  introv h₀ h₁,
  rw coinduction h₁
end

end coinduction

universes u' v'

def corec_on {X : fam I} {i} (x₀ : X i) (f : X ⟶ F.obj X) : M F i :=
M.corec f x₀

end M

end ipfunctor₀

namespace tactic.interactive
open tactic (hiding coinduction) lean.parser interactive interactive.types

meta def ibisim (ns : parse with_ident_list) (g : parse $ optional (tk "generalizing" *> many ident)) : tactic unit :=
do applyc ``ipfunctor₀.M.coinduction,
   coinduction ``ipfunctor₀.M.R.corec_on ns g

end tactic.interactive

namespace ipfunctor₀

open M

variables {P : ipfunctor.{u} I I} {α : fam I}

def M_dest : M P ⟶ P.obj (M P) := from_cofix

def M_corec : (α ⟶ P.obj α) → (α ⟶ M P) := M.corec

lemma M_dest_corec (g : α ⟶ P.obj α) {i} (x : α i) :
  M_dest (M_corec g x) = P.map (M_corec g) (g x) :=
by rw [M_corec,M_dest,corec_def,from_cofix_mk]

lemma M_dest_corec' (g : α ⟶ P.obj α) :
  M_corec g ≫ M_dest = g ≫ P.map (M_corec g) :=
funext $ λ i, funext $ λ x, M_dest_corec _ _

lemma M_bisim (R : Π i, M P i → M P i → Prop)
    (h : ∀ i x y, R i x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ j x', R j (f x') (f' x')) :
  ∀ i x y, R i x y → x = y :=
begin
  intros,
  ibisim with j _ _ ih generalizing i x y,
  rcases h _ _ _ ih with ⟨ a', f, f', h₀, h₁, h₂ ⟩, clear h,
  existsi [a',f,f'], split,
  { intros, existsi [_,_,_,h₂ _ x], refl },
  split,
  { rw [← h₀,M_dest,mk_from_cofix] },
  { rw [← h₁,M_dest,mk_from_cofix] },
end

theorem M_bisim' {α : fam I} (Q : Π j, α j → Prop) (u v : α ⟶ M P)
    (h : ∀ i x, Q i x → ∃ a f f',
      M_dest (u x) = ⟨a, f⟩ ∧
      M_dest (v x) = ⟨a, f'⟩ ∧
      ∀ j (y : P.B i a j), ∃ (x' : α j), Q j x' ∧ f y = u x' ∧ f' y = v x') :
  ∀ i x, Q i x → u x = v x :=
λ i x Qx,
let R := λ j (w z : M P j), ∃ x', Q j x' ∧ w = u x' ∧ z = v x' in
@M_bisim I P R
  (λ i x y ⟨x', Qx', xeq, yeq⟩,
    let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h i x' Qx' in
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
  _ _ _ ⟨x, Qx, rfl, rfl⟩

theorem M_bisim_equiv (R : Π i, M P i → M P i → Prop)
    (h : ∀ i x y, R i x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ j x', R j (f x') (f' x')) :
  ∀ i x y, R i x y → x = y :=
λ i x y Rxy,
let Q : Π i, M P i × M P i → Prop := λ i p, R i p.fst p.snd in
M_bisim' Q (λ _, prod.fst) (λ _, prod.snd)
  (λ i p Qp,
    let ⟨a, f, f', hx, hy, h'⟩ := h _ p.fst p.snd Qp in
    ⟨a, f, f', hx, hy, λ j y, ⟨⟨f y, f' y⟩, h' _ _, rfl, rfl⟩⟩)
  _ ⟨x, y⟩ Rxy

theorem M_corec_unique (g : α ⟶ P.obj α) (f : α ⟶ M P)
    (hyp : ∀ i x, M_dest (@f i x) = P.map f (g x)) :
  f = M_corec g :=
begin
  ext i x,
  apply M_bisim' (λ i x, true) _ _ _ _ _ trivial,
  clear x,
  intros i x _,
  cases gxeq : g x with a f',
  have h₀ : M_dest (f x) = ⟨a, f' ≫ f⟩,
  { rw [hyp, gxeq, ipfunctor.map_eq'] },
  have h₁ : M_dest (M_corec g x) = ⟨a, f' ≫ M_corec g⟩,
  { rw [M_dest_corec, gxeq, ipfunctor.map_eq'], },
  refine ⟨_, _, _, h₀, h₁, _⟩,
  intros i y,
  exact ⟨f' y, trivial, rfl, rfl⟩
end

def M_mk : P.obj (M P) ⟶ M P := M_corec (P.map M_dest)

theorem M_mk_M_dest {i} (x : M P i) : M_mk (M_dest x) = x :=
begin
  apply M_bisim' (λ i x, true) (M_dest ≫ M_mk) _ _ _ _ trivial,
  clear x,
  intros j x _,
  cases Mxeq : M_dest x with a f',
  have : M_dest (M_mk (M_dest x)) = ⟨a, _⟩,
  { rw [M_mk, M_dest_corec, Mxeq, ipfunctor.map_eq', ipfunctor.map_eq'] },
  refine ⟨_, _, _, this, rfl, _⟩,
  intros i y,
  exact ⟨f' y, trivial, rfl, rfl⟩
end

theorem M_mk_M_dest' : M_dest ≫ M_mk = 𝟙 (M P) :=
funext (λ i, funext $ λ i, M_mk_M_dest _)

theorem M_dest_M_mk : M_mk ≫ M_dest = 𝟙 (P.obj (M P)) :=
by rw [M_mk,M_dest_corec',←ipfunctor.map_comp, ←M_mk, M_mk_M_dest', ipfunctor.map_id]

theorem M_dest_M_mk' {i} (x : P.obj (M P) i) : M_dest (M_mk x) = x :=
show (M_mk ≫ M_dest) x = x,
by rw M_dest_M_mk; refl

end ipfunctor₀

namespace ipfunctor

variables (P : ipfunctor (I ⊕ J) J)

inductive M_path : Π {i : J}, P.last.M i → I → Type u
| root {i} (x : P.last.M i) (a : P.A i) (f : P.last.B i a ⟶ P.last.M) (h : ipfunctor₀.M_dest x = ⟨a, f⟩)
       (j : I) (c : P.drop.B i a j) :
    M_path x j
| child {i} (x : P.last.M i) (a : P.A i) (f : P.last.B i a ⟶ P.last.M)
        (h : ipfunctor₀.M_dest x = ⟨a, f⟩)
        (j : J) (a : P.last.B i a j) {i'} (c : M_path (f a) i') :
    M_path x i'

def Mp : ipfunctor I J :=
{ A := P.last.M, B := λ _, P.M_path }

def M (α : fam I) : fam J := P.Mp.obj α

def M_corec_shape {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₂ : Π {i} (b : β i), P.last.B i (g₀ b) ⟶ β) :
  β ⟶ P.last.M :=
ipfunctor₀.M_corec (λ j b, ⟨g₀ b, g₂ _⟩)

def cast_dropB {i} : Π {a a' : P.A i} (h : a = a'), P.drop.B i a ⟶ P.drop.B i a'
| _ _ rfl i b := b

def cast_lastB {i} : Π {a a' : P.A i} (h : a = a'), P.last.B i a ⟶ P.last.B i a'
| _ _ rfl i b := b

def M_corec_contents {α : fam I} {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₁ : Π ⦃i⦄ (b : β i), P.drop.B i (g₀ b) ⟶ α)
    (g₂ : Π ⦃i⦄ (b : β i), P.last.B i (g₀ b) ⟶ β) :
  Π {j} x (b : β j), x = P.M_corec_shape g₀ g₂ b → (P.M_path x ⟶ α)
| j ._ b h ._ (M_path.root x a f h' i c)    :=
  have a = g₀ b,
    by { rw [h, M_corec_shape, ipfunctor₀.M_dest_corec] at h', cases h', refl },
  g₁ b (P.cast_dropB this c)
| j ._ b h ._ (M_path.child x a f h' j' i c) :=
  have h₀ : a = g₀ b,
    by { rw [h, M_corec_shape, ipfunctor₀.M_dest_corec] at h', cases h', refl },
  have h₁ : f i = M_corec_shape P g₀ g₂ (g₂ b (cast_lastB P h₀ i)),
    by { rw [h, M_corec_shape, ipfunctor₀.M_dest_corec] at h', cases h', refl },
  M_corec_contents (f i) (g₂ b (P.cast_lastB h₀ _)) h₁ c

def M_corec' {α : fam I} {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₁ : Π ⦃i⦄ (b : β i), P.drop.B i (g₀ b) ⟶ α) :
  Π (g₂ : Π ⦃i⦄ (b : β i), P.last.B i (g₀ b) ⟶ β),
  β ⟶ P.M α
| g₂ j b := ⟨M_corec_shape P g₀ g₂ b, M_corec_contents P g₀ g₁ g₂ _ _ rfl⟩

open fam

def M_corec {α : fam I} {β : fam J} (g : β ⟶ P.obj (α.append1 β)) :
  β ⟶ P.M α :=
M_corec' P
  (λ i b, (g b).fst)
  (λ i b, drop_fun (g b).snd)
  (λ i b, last_fun (g b).snd)

def M_path_dest_left {α : fam I} {j} {x : P.last.M j}
    {a : P.A j} {f : P.last.B j a ⟶ P.last.M} (h : ipfunctor₀.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) :
  P.drop.B j a ⟶ α :=
λ i c, f' (M_path.root x a f h i c)

def M_path_dest_right {α : fam I} {j} {x : P.last.M j}
    {a : P.A j} {f : P.last.B j a ⟶ P.last.M} (h : ipfunctor₀.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) :
  Π {i} j : P.last.B _ a i, P.M_path (f j) ⟶ α :=
λ j i k c, f' (M_path.child x a f h j i c)

def M_dest' {α : fam I}
    {i} {x : P.last.M i} {a : P.A i}
    {f : P.last.B i a ⟶ P.last.M} (h : ipfunctor₀.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) :
  P.obj (α.append1 (P.M α)) _ :=
⟨a, split_fun (P.M_path_dest_left h f') (λ j x, ⟨f x, P.M_path_dest_right h f' x⟩)⟩

def M_dest : Π {α : fam I}, P.M α ⟶ P.obj (α.append1 (P.M α))
| α i x := P.M_dest' (sigma.eta $ ipfunctor₀.M_dest x.fst).symm x.snd

def M_mk : Π {α : fam I}, P.obj (α.append1 (P.M α)) ⟶ P.M α
| α := M_corec _ (P.map $ append_fun (𝟙 _) $ M_dest P)

theorem M_dest'_eq_dest' {α : fam I} {i} {x : P.last.M i}
    {a₁ : P.A i} {f₁ : P.last.B _ a₁ ⟶ P.last.M} (h₁ : ipfunctor₀.M_dest x = ⟨a₁, f₁⟩)
    {a₂ : P.A i} {f₂ : P.last.B _ a₂ ⟶ P.last.M} (h₂ : ipfunctor₀.M_dest x = ⟨a₂, f₂⟩)
    (f' : P.M_path x ⟶ α) : M_dest' P h₁ f' = M_dest' P h₂ f' :=
by cases h₁.symm.trans h₂; refl

theorem M_dest_eq_dest' {α : fam I} {i} {x : P.last.M i}
    {a : P.A i} {f : P.last.B i a ⟶ P.last.M} (h : ipfunctor₀.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) : M_dest P ⟨x, f'⟩ = M_dest' P h f' :=
M_dest'_eq_dest' _ _ _ _

theorem M_dest_corec' {α : fam I} {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₁ : Π ⦃i⦄ (b : β i), P.drop.B i (g₀ b) ⟶ α)
    (g₂ : Π ⦃i⦄ (b : β i), P.last.B i (g₀ b) ⟶ β)
    {i} (x : β i) :
  P.M_dest (P.M_corec' g₀ g₁ g₂ x) =
    ⟨g₀ x, split_fun (g₁ x) (g₂ x ≫ P.M_corec' g₀ g₁ g₂)⟩ :=
rfl

theorem M_dest_corec {α : fam I} {β : fam J}
  (g : β ⟶ P.obj (α.append1 β)) {i} (x : β i) :
  P.M_dest (P.M_corec g x) = P.map (append_fun (𝟙 _) (P.M_corec g)) (g x) :=
begin
  transitivity, apply M_dest_corec',
  cases g x with a f, dsimp,
  rw ipfunctor.map_eq', congr,
  conv { to_rhs, rw [←split_drop_fun_last_fun f, fam.append_fun_comp_split_fun] },
  refl
end

@[reassoc]
theorem M_dest_corec'' {α : fam I} {β : fam J}
  (g : β ⟶ P.obj (α.append1 β)) :
  P.M_corec g ≫ P.M_dest = g ≫ P.map (append_fun (𝟙 _) (P.M_corec g)) :=
by ext : 2; simp [M_dest_corec]

lemma M_bisim_lemma {α : fam I}
  {i} {a₁ : (Mp P).A i} {f₁ : (Mp P).B _ a₁ ⟶ α}
  {a' : P.A i} {f' : (P.B _ a').drop ⟶ α} {f₁' : (P.B _ a').last ⟶ M P α}
  (e₁ : M_dest P ⟨a₁, f₁⟩ = ⟨a', split_fun f' f₁'⟩) :
  ∃ g₁' (e₁' : ipfunctor₀.M_dest a₁ = ⟨a', g₁'⟩),
    f' = M_path_dest_left P e₁' f₁ ∧
    f₁' = λ i (x : (last P).B _ a' _),
      ⟨g₁' x, M_path_dest_right P e₁' f₁ x⟩ :=
begin
  generalize_hyp ef : @split_fun _ _ _ (append1 α (M P α)) f' f₁' = ff at e₁,
  cases e₁' : ipfunctor₀.M_dest a₁ with a₁' g₁',
  rw M_dest_eq_dest' _ e₁' at e₁,
  cases e₁, exact ⟨_, e₁', fam.split_fun_inj ef⟩,
end

theorem M_bisim {α : fam I} (R : Π ⦃j⦄, P.M α j → P.M α j → Prop)
  (h : ∀ j (x y : P.M α j), R x y → ∃ a f f₁ f₂,
    P.M_dest x = ⟨a, split_fun f f₁⟩ ∧
    P.M_dest y = ⟨a, split_fun f f₂⟩ ∧
    ∀ i x, @R i (f₁ x) (f₂ x))
  {j} (x y) (r : @R j x y) : x = y :=
begin
  cases x with a₁ f₁,
  cases y with a₂ f₂,
  dsimp [Mp] at *,
  have : a₁ = a₂, {
    refine ipfunctor₀.M_bisim
      (λ i (a₁ a₂ : ipfunctor₀.M (last P) i), ∃ x y, @R i x y ∧ x.1 = a₁ ∧ y.1 = a₂) _ _ _ _
      ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rintro _ _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rcases h _ _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩,
    rcases M_bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M_bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩,
    rw [e₁', e₂'],
    exact ⟨_, _, _, rfl, rfl, λ i b, ⟨_, _, h' _ b, rfl, rfl⟩⟩ },
  subst this, congr, ext i p,
  induction p with x i' a f h' i j c x a f h' i j c p IH generalizing f₁ f₂,
  all_goals {
    rcases h _ _ _ r with ⟨i, a', f', f₁', e₁, e₂, h''⟩,
    rcases M_bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M_bisim_lemma P e₂ with ⟨g₂', e₂', e₃, rfl⟩,
    cases h'.symm.trans e₁',
    cases h'.symm.trans e₂' },
  { exact (congr_fun (congr_fun e₃ i) _ : _) },
  { exact IH _ _ (h'' _ _) }
end

open ipfunctor

@[reassoc]
theorem M_dest_map {α β : fam I} (g : α ⟶ β) :
  P.Mp.map g ≫ P.M_dest = P.M_dest ≫ P.map (append_fun g (P.Mp.map g)) :=
begin
  ext i x : 2,
  cases x with a f,
  simp [map_eq],
  conv { to_rhs, rw [M_dest, M_dest', map_eq', fam.append_fun_comp_split_fun] },
  reflexivity,
end

end ipfunctor
