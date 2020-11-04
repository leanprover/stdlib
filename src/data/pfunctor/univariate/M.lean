/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.pfunctor.univariate.basic

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/

universes u v w

open nat function list (hiding head')

variables (F : pfunctor.{u})

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

namespace pfunctor
namespace approx

/-- `cofix_a F n` is an `n` level approximation of a M-type -/
inductive cofix_a : ℕ → Type u
| continue : cofix_a 0
| intro {n} : ∀ a, (F.B a → cofix_a n) → cofix_a (succ n)

/-- default inhabitant of `cofix_a` -/
protected def cofix_a.default [inhabited F.A] : Π n, cofix_a F n
| 0 := cofix_a.continue
| (succ n) := cofix_a.intro (default _) $ λ _, cofix_a.default n

instance [inhabited F.A] {n} : inhabited (cofix_a F n) := ⟨ cofix_a.default F n ⟩

lemma cofix_a_eq_zero : ∀ x y : cofix_a F 0, x = y
| cofix_a.continue cofix_a.continue := rfl

variables {F}

/--
The label of the root of the tree for a non-trivial
approximation of the cofix of a pfunctor.
-/
def head' : Π {n}, cofix_a F (succ n) → F.A
| n (cofix_a.intro i _) := i

/-- for a non-trivial approximation, return all the subtrees of the root -/
def children' : Π {n} (x : cofix_a F (succ n)), F.B (head' x) → cofix_a F n
| n (cofix_a.intro a f) := f

lemma approx_eta  {n : ℕ} (x : cofix_a F (n+1)) :
  x = cofix_a.intro (head' x) (children' x) :=
by cases x; refl

/-- Relation between two approximations of the cofix of a pfunctor that state they both contain the same
data until one of them is truncated -/
inductive agree : ∀ {n : ℕ}, cofix_a F n → cofix_a F (n+1) → Prop
 | continue (x : cofix_a F 0) (y : cofix_a F 1) : agree x y
 | intro {n} {a} (x : F.B a → cofix_a F n) (x' : F.B a → cofix_a F (n+1)) :
   (∀ i : F.B a, agree (x i) (x' i)) →
   agree (cofix_a.intro a x) (cofix_a.intro a x')

/--
Given an infinite series of approximations `approx`,
`all_agree approx` states that they are all consistent with each other.
-/
def all_agree (x : Π n, cofix_a F n) :=
∀ n, agree (x n) (x (succ n))

@[simp]
lemma agree_trival {x : cofix_a F 0} {y : cofix_a F 1} :
  agree x y :=
by { constructor }

lemma agree_children {n : ℕ} (x : cofix_a F (succ n)) (y : cofix_a F (succ n+1))
    {i j} (h₀ : i == j) (h₁ : agree x y) :
  agree (children' x i) (children' y j) :=
begin
  cases h₁ with _ _ _ _ _ _ hagree, cases h₀,
  apply hagree,
end

/-- `truncate a` turns `a` into a more limited approximation -/
def truncate : ∀ {n : ℕ}, cofix_a F (n+1) → cofix_a F n
| 0 (cofix_a.intro _ _) := cofix_a.continue
| (succ n) (cofix_a.intro i f) := cofix_a.intro i $ truncate ∘ f

lemma truncate_eq_of_agree {n : ℕ} (x : cofix_a F n) (y : cofix_a F (succ n)) (h : agree x y) :
  truncate y = x :=
begin
  induction n generalizing x y; cases x; cases y,
  { refl },
  { cases h with _ _ _ _ _ h₀ h₁,
    cases h,
    simp only [truncate, function.comp, true_and, eq_self_iff_true, heq_iff_eq],
    ext y, apply n_ih,
    apply h₁ }
end

variables {X : Type w}
variables (f : X → F.obj X)

/-- `s_corec f i n` creates an approximation of height `n`
of the final coalgebra of `f` -/
def s_corec : Π (i : X) n, cofix_a F n
| _ 0 := cofix_a.continue
| j (succ n) := cofix_a.intro (f j).1 (λ i, s_corec ((f j).2 i) _)

lemma P_corec (i : X) (n : ℕ) : agree (s_corec f i n) (s_corec f i (succ n)) :=
begin
  induction n with n generalizing i,
  constructor,
  cases h : f i with y g,
  constructor,
  introv,
  apply n_ih,
end

/-- `path F` provides indices to access internal nodes in `corec F` -/
def path (F : pfunctor.{u}) := list F.Idx

instance path.inhabited : inhabited (path F) := ⟨ [] ⟩

open list nat

instance : subsingleton (cofix_a F 0) :=
⟨ by { intros, casesm* cofix_a F 0, refl } ⟩

lemma head_succ' (n m : ℕ) (x : Π n, cofix_a F n) (Hconsistent : all_agree x) :
  head' (x (succ n)) = head' (x (succ m)) :=
begin
  suffices : ∀ n, head' (x (succ n)) = head' (x 1),
  { simp [this] },
  clear m n, intro,
  cases h₀ : x (succ n) with _ i₀ f₀,
  cases h₁ : x 1 with _ i₁ f₁,
  dsimp only [head'],
  induction n with n,
  { rw h₁ at h₀, cases h₀, trivial },
  { have H := Hconsistent (succ n),
    cases h₂ : x (succ n) with _ i₂ f₂,
    rw [h₀,h₂] at H,
    apply n_ih (truncate ∘ f₀),
    rw h₂,
    cases H with _ _ _ _ _ _ hagree,
    congr, funext j, dsimp only [comp_app],
    rw truncate_eq_of_agree,
    apply hagree }
end

end approx
open approx

/-- Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.cases_on` and the declarations generated for
the structure -/
structure M_intl :=
(approx : ∀ n, cofix_a F n)
(consistent : all_agree approx)

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
def M := M_intl F

lemma M.default_consistent [inhabited F.A] : Π n, agree (default (cofix_a F n)) (default (cofix_a F (succ n)))
| 0 := agree.continue _ _
| (succ n) := agree.intro _ _ $ λ _, M.default_consistent n

instance M.inhabited [inhabited F.A] : inhabited (M F) :=
⟨ { approx := λ n, default _,
    consistent := M.default_consistent _ } ⟩

instance M_intl.inhabited [inhabited F.A] : inhabited (M_intl F) :=
show inhabited (M F), by apply_instance

namespace M

lemma ext' (x y : M F) (H : ∀ i : ℕ, x.approx i = y.approx i) : x = y :=
by { cases x, cases y, congr' with n, apply H }

variables {X : Type*}
variables (f : X → F.obj X)
variables {F}

/-- Corecursor for the M-type defined by `F`. -/
protected def corec (i : X) : M F :=
{ approx := s_corec f i,
  consistent := P_corec _ _ }

variables {F}

/-- given a tree generated by `F`, `head` gives us the first piece of data
it contains -/
def head (x : M F) :=
head' (x.1 1)

/-- return all the subtrees of the root of a tree `x : M F` -/
def children (x : M F) (i : F.B (head x)) : M F :=
   let H := λ n : ℕ, @head_succ' _ n 0 x.1 x.2 in
   { approx := λ n, children' (x.1 _) (cast (congr_arg _ $ by simp only [head,H]; refl) i),
     consistent :=
     begin
       intro,
       have P' := x.2 (succ n),
       apply agree_children _ _ _ P',
       transitivity i,
       apply cast_heq,
       symmetry,
       apply cast_heq,
     end }

/-- select a subtree using a `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
def ichildren [inhabited (M F)] [decidable_eq F.A] (i : F.Idx) (x : M F) : M F :=
if H' : i.1 = head x
  then children x (cast (congr_arg _ $ by simp only [head,H']; refl) i.2)
  else default _

lemma head_succ (n m : ℕ) (x : M F) :
  head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
head_succ' n m _ x.consistent

lemma head_eq_head' : Π (x : M F) (n : ℕ),
  head x = head' (x.approx $ n+1)
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma head'_eq_head : Π (x : M F) (n : ℕ),
  head' (x.approx $ n+1) = head x
| ⟨x,h⟩ n := head_succ' _ _ _ h

lemma truncate_approx (x : M F) (n : ℕ) :
  truncate (x.approx $ n+1) = x.approx n :=
truncate_eq_of_agree _ _ (x.consistent _)

/-- unfold an M-type -/
def dest : M F → F.obj (M F)
| x := ⟨head x,λ i, children x i ⟩

namespace approx

/-- generates the approximations needed for `M.mk` -/
protected def s_mk (x : F.obj $ M F) : Π n, cofix_a F n
 | 0 :=  cofix_a.continue
 | (succ n) := cofix_a.intro x.1 (λ i, (x.2 i).approx n)

protected lemma P_mk  (x : F.obj $ M F)
: all_agree (approx.s_mk x)
 | 0 := by { constructor }
 | (succ n) := by { constructor, introv,
                    apply (x.2 i).consistent }

end approx

/-- constructor for M-types -/
protected def mk (x : F.obj $ M F) : M F :=
{ approx := approx.s_mk x,
  consistent := approx.P_mk x }

/-- `agree' n` relates two trees of type `M F` that
are the same up to dept `n` -/
inductive agree' : ℕ → M F → M F → Prop
| trivial (x y : M F) : agree' 0 x y
| step {n : ℕ} {a} (x y : F.B a → M F) {x' y'} :
  x' = M.mk ⟨a,x⟩ →
  y' = M.mk ⟨a,y⟩ →
  (∀ i, agree' n (x i) (y i)) →
  agree' (succ n) x' y'

@[simp]
lemma dest_mk (x : F.obj $ M F) :
  dest (M.mk x) = x :=
begin
  funext i,
  dsimp only [M.mk,dest],
  cases x with x ch, congr' with i,
  cases h : ch i,
  simp  only [children,M.approx.s_mk,children',cast_eq],
  dsimp only [M.approx.s_mk,children'],
  congr, rw h,
end

@[simp] lemma mk_dest (x : M F) :
  M.mk (dest x) = x :=
begin
  apply ext', intro n,
  dsimp only [M.mk],
  induction n with n,
  { apply subsingleton.elim },
  dsimp only [approx.s_mk,dest,head],
  cases h : x.approx (succ n) with _ hd ch,
  have h' : hd = head' (x.approx 1),
  { rw [← head_succ' n,h,head'], apply x.consistent },
  revert ch, rw h', intros, congr,
  { ext a, dsimp only [children],
    h_generalize! hh : a == a'',
    rw h, intros, cases hh, refl },
end

lemma mk_inj {x y : F.obj $ M F}
  (h : M.mk x = M.mk y) : x = y :=
by rw [← dest_mk x,h,dest_mk]

/-- destructor for M-types -/
protected def cases {r : M F → Sort w}
  (f : ∀ (x : F.obj $ M F), r (M.mk x)) (x : M F) : r x :=
suffices r (M.mk (dest x)),
  by { haveI := classical.prop_decidable,
       haveI := inhabited.mk x,
       rw [← mk_dest x], exact this },
f _

/-- destructor for M-types -/
protected def cases_on {r : M F → Sort w}
  (x : M F) (f : ∀ (x : F.obj $ M F), r (M.mk x)) : r x :=
M.cases f x

/-- destructor for M-types, similar to `cases_on` but also
gives access directly to the root and subtrees on an M-type -/
protected def cases_on' {r : M F → Sort w}
  (x : M F) (f : ∀ a f, r (M.mk ⟨a,f⟩)) : r x :=
M.cases_on x (λ ⟨a,g⟩, f a _)

lemma approx_mk (a : F.A) (f : F.B a → M F) (i : ℕ) :
  (M.mk ⟨a, f⟩).approx (succ i) = cofix_a.intro a (λ j, (f j).approx i) :=
rfl

@[simp] lemma agree'_refl {n : ℕ} (x : M F) :
  agree' n x x :=
by { induction n generalizing x; induction x using pfunctor.M.cases_on';
     constructor; try { refl }, intros, apply n_ih }

lemma agree_iff_agree' {n : ℕ} (x y : M F) :
  agree (x.approx n) (y.approx $ n+1) ↔ agree' n x y :=
begin
  split; intros h,
  { induction n generalizing x y, constructor,
    { induction x using pfunctor.M.cases_on',
      induction y using pfunctor.M.cases_on',
      simp only [approx_mk] at h, cases h with _ _ _ _ _ _ hagree,
      constructor; try { refl },
      intro i, apply n_ih, apply hagree } },
  { induction n generalizing x y, constructor,
    { cases h,
      induction x using pfunctor.M.cases_on',
      induction y using pfunctor.M.cases_on',
      simp only [approx_mk],
      have h_a_1 := mk_inj ‹M.mk ⟨x_a, x_f⟩ = M.mk ⟨h_a, h_x⟩›, cases h_a_1,
      replace h_a_2 := mk_inj ‹M.mk ⟨y_a, y_f⟩ = M.mk ⟨h_a, h_y⟩›, cases h_a_2,
      constructor, intro i, apply n_ih, simp * } },
end

@[simp]
lemma cases_mk {r : M F → Sort*} (x : F.obj $ M F) (f : Π (x : F.obj $ M F), r (M.mk x)) :
  pfunctor.M.cases f (M.mk x) = f x :=
begin
  dsimp only [M.mk,pfunctor.M.cases,dest,head,approx.s_mk,head'],
  cases x, dsimp only [approx.s_mk],
  apply eq_of_heq,
  apply rec_heq_of_heq, congr' with x,
  dsimp only [children,approx.s_mk,children'],
  cases h : x_snd x, dsimp only [head],
  congr' with n, change (x_snd (x)).approx n = _, rw h
end

@[simp]
lemma cases_on_mk {r : M F → Sort*} (x : F.obj $ M F) (f : Π x : F.obj $ M F, r (M.mk x)) :
  pfunctor.M.cases_on (M.mk x) f = f x :=
cases_mk x f

@[simp]
lemma cases_on_mk' {r : M F → Sort*} {a} (x : F.B a → M F) (f : Π a (f : F.B a → M F), r (M.mk ⟨a,f⟩)) :
  pfunctor.M.cases_on' (M.mk ⟨a,x⟩) f = f a x :=
cases_mk ⟨_,x⟩ _

/-- `is_path p x` tells us if `p` is a valid path through `x` -/
inductive is_path  : path F → M F → Prop
| nil (x : M F) : is_path [] x
| cons (xs : path F) {a} (x : M F) (f : F.B a → M F) (i : F.B a) :
  x = M.mk ⟨a,f⟩ →
  is_path xs (f i) →
  is_path (⟨a,i⟩ :: xs) x

lemma is_path_cons {xs : path F} {a a'} {f : F.B a → M F} {i : F.B a'}
  (h : is_path (⟨a',i⟩ :: xs) (M.mk ⟨a,f⟩)) :
  a = a' :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = x,
  intros h', cases h', subst x,
  cases mk_inj ‹_›, refl,
end

lemma is_path_cons' {xs : path F} {a} {f : F.B a → M F} {i : F.B a}
  (h : is_path (⟨a,i⟩ :: xs) (M.mk ⟨a,f⟩)) :
  is_path xs (f i) :=
begin
  revert h, generalize h : (M.mk ⟨a,f⟩) = x,
  intros h', cases h', subst x,
  have := mk_inj ‹_›, cases this, cases this,
  assumption,
end

/-- follow a path through a value of `M F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree -/
def isubtree [decidable_eq F.A] [inhabited (M F)] : path F → M F → M F
| [] x := x
| (⟨a, i⟩ :: ps) x :=
pfunctor.M.cases_on' x (λ a' f,
(if h : a = a' then isubtree ps (f $ cast (by rw h) i)
 else default (M F) : (λ x, M F) (M.mk ⟨a',f⟩)))

/-- similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree -/
def iselect [decidable_eq F.A] [inhabited (M F)] (ps : path F) : M F → F.A :=
λ (x : M F), head $ isubtree ps x

lemma iselect_eq_default [decidable_eq F.A] [inhabited (M F)] (ps : path F) (x : M F)
  (h : ¬ is_path ps x) :
  iselect ps x = head (default $ M F) :=
begin
  induction ps generalizing x,
  { exfalso, apply h, constructor },
  { cases ps_hd with a i,
    induction x using pfunctor.M.cases_on',
    simp only [iselect,isubtree] at ps_ih ⊢,
    by_cases h'' : a = x_a, subst x_a,
    { simp only [dif_pos, eq_self_iff_true, cases_on_mk'],
      rw ps_ih, intro h', apply h,
      constructor; try { refl }, apply h' },
    { simp * } }
end

@[simp] lemma head_mk (x : F.obj (M F)) :
  head (M.mk x) = x.1 :=
eq.symm $
calc  x.1
    = (dest (M.mk x)).1 : by rw dest_mk
... = head (M.mk x)           : by refl

lemma children_mk {a} (x : F.B a → (M F)) (i : F.B (head (M.mk ⟨a,x⟩))) :
  children (M.mk ⟨a,x⟩) i = x (cast (by rw head_mk) i) :=
by apply ext'; intro n; refl

@[simp]
lemma ichildren_mk [decidable_eq F.A] [inhabited (M F)] (x : F.obj (M F)) (i : F.Idx) :
  ichildren i (M.mk x) = x.iget i :=
by { dsimp only [ichildren,pfunctor.obj.iget],
     congr' with h, apply ext',
     dsimp only [children',M.mk,approx.s_mk],
     intros, refl,
     refl }

@[simp]
lemma isubtree_cons [decidable_eq F.A] [inhabited (M F)] (ps : path F) {a} (f : F.B a → M F) {i : F.B a} :
  isubtree (⟨_,i⟩ :: ps) (M.mk ⟨a,f⟩) = isubtree ps (f i) :=
by simp only [isubtree,ichildren_mk,pfunctor.obj.iget,dif_pos,isubtree,M.cases_on_mk']; refl

@[simp]
lemma iselect_nil [decidable_eq F.A] [inhabited (M F)] {a} (f : F.B a → M F) :
  iselect nil (M.mk ⟨a,f⟩) = a :=
by refl

@[simp]
lemma iselect_cons [decidable_eq F.A] [inhabited (M F)] (ps : path F) {a} (f : F.B a → M F) {i} :
  iselect (⟨a,i⟩ :: ps) (M.mk ⟨a,f⟩) = iselect ps (f i) :=
by simp only [iselect,isubtree_cons]

lemma corec_def {X} (f : X → F.obj X) (x₀ : X) :
  M.corec f x₀ = M.mk (M.corec f <$> f x₀)  :=
begin
  dsimp only [M.corec,M.mk],
  congr' with n,
  cases n with n,
  { dsimp only [s_corec,approx.s_mk], refl, },
  { dsimp only [s_corec,approx.s_mk], cases h : (f x₀),
    dsimp only [(<$>),pfunctor.map],
    congr, }
end

lemma ext_aux [inhabited (M F)] [decidable_eq F.A] {n : ℕ} (x y z : M F)
  (hx : agree' n z x)
  (hy : agree' n z y)
  (hrec : ∀ (ps : path F),
             n = ps.length →
            iselect ps x = iselect ps y) :
  x.approx (n+1) = y.approx (n+1) :=
begin
  induction n with n generalizing x y z,
  { specialize hrec [] rfl,
    induction x using pfunctor.M.cases_on', induction y using pfunctor.M.cases_on',
    simp only [iselect_nil] at hrec, subst hrec,
    simp only [approx_mk, true_and, eq_self_iff_true, heq_iff_eq],
    apply subsingleton.elim },
  { cases hx, cases hy,
    induction x using pfunctor.M.cases_on', induction y using pfunctor.M.cases_on',
    subst z,
    iterate 3 { have := mk_inj ‹_›, repeat { cases this } },
    simp only [approx_mk, true_and, eq_self_iff_true, heq_iff_eq],
    ext i, apply n_ih,
    { solve_by_elim },
    { solve_by_elim },
    introv h, specialize hrec (⟨_,i⟩ :: ps) (congr_arg _ h),
    simp only [iselect_cons] at hrec, exact hrec }
end

open pfunctor.approx

variables {F}

local attribute [instance, priority 0] classical.prop_decidable

lemma ext [inhabited (M F)]
  (x y : M F)
  (H : ∀ (ps : path F), iselect ps x = iselect ps y) :
  x = y :=
begin
  apply ext', intro i,
  induction i with i,
  { cases x.approx 0, cases y.approx 0, constructor },
  { apply ext_aux x y x,
    { rw ← agree_iff_agree', apply x.consistent },
    { rw [← agree_iff_agree',i_ih], apply y.consistent },
    introv H',
    dsimp only [iselect] at H,
    cases H',
    apply H ps }
end

section bisim

variable (R : M F → M F → Prop)
local infix ~ := R

/-- Bisimulation is the standard proof technique for equality between
infinite tree-like structures -/
structure is_bisimulation : Prop :=
(head : ∀ {a a'} {f f'}, M.mk ⟨a,f⟩ ~ M.mk ⟨a',f'⟩ → a = a')
(tail : ∀ {a} {f f' : F.B a → M F},
  M.mk ⟨a,f⟩ ~ M.mk ⟨a,f'⟩ →
  (∀ (i : F.B a), f i ~ f' i) )

theorem nth_of_bisim [inhabited (M F)] (bisim : is_bisimulation R) (s₁ s₂) (ps : path F) :
     s₁ ~ s₂ →
       is_path ps s₁ ∨ is_path ps s₂ →
       iselect ps s₁ = iselect ps s₂ ∧
       ∃ a (f f' : F.B a → M F),
         isubtree ps s₁ = M.mk ⟨a,f⟩ ∧
         isubtree ps s₂ = M.mk ⟨a,f'⟩ ∧
       ∀ (i : F.B a), f i ~ f' i :=
begin
  intros h₀ hh,
  induction s₁ using pfunctor.M.cases_on' with a f,
  induction s₂ using pfunctor.M.cases_on' with a' f',
  have : a = a' := bisim.head h₀, subst a',
  induction ps with i ps generalizing a f f',
  { existsi [rfl,a,f,f',rfl,rfl],
    apply bisim.tail h₀ },
  cases i with a' i,
  have : a = a',
  { cases hh; cases is_path_cons hh; refl },
  subst a', dsimp only [iselect] at ps_ih ⊢,
  have h₁ := bisim.tail h₀ i,
  induction h : (f i) using pfunctor.M.cases_on' with a₀ f₀,
  induction h' : (f' i) using pfunctor.M.cases_on' with a₁ f₁,
  simp only [h,h',isubtree_cons] at ps_ih ⊢,
  rw [h,h'] at h₁,
  have : a₀ = a₁ := bisim.head h₁, subst a₁,
  apply (ps_ih _ _ _ h₁),
  rw [← h,← h'], apply or_of_or_of_imp_of_imp hh is_path_cons' is_path_cons'
end

theorem eq_of_bisim [nonempty (M F)] (bisim : is_bisimulation R) : ∀ s₁ s₂, s₁ ~ s₂ → s₁ = s₂ :=
begin
  inhabit (M F),
  introv Hr, apply ext,
  introv,
  by_cases h : is_path ps s₁ ∨ is_path ps s₂,
  { have H := nth_of_bisim R bisim _ _ ps Hr h,
    exact H.left },
  { rw not_or_distrib at h, cases h with h₀ h₁,
    simp only [iselect_eq_default,*,not_false_iff] }
end

end bisim

universes u' v'

/-- corecursor for `M F` with swapped arguments -/
def corec_on {X : Type*} (x₀ : X) (f : X → F.obj X) : M F :=
M.corec f x₀

variables {P : pfunctor.{u}} {α : Type u}

lemma dest_corec (g : α → P.obj α) (x : α) :
  M.dest (M.corec g x) = M.corec g <$> g x :=
by rw [corec_def,dest_mk]

lemma bisim (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M.dest x = ⟨a, f⟩ ∧
      M.dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y :=
begin
  introv h',
  haveI := inhabited.mk x.head,
  apply eq_of_bisim R _ _ _ h', clear h' x y,
  split; introv ih;
    rcases h _ _ ih with ⟨ a'', g, g', h₀, h₁, h₂ ⟩; clear h,
  { replace h₀ := congr_arg sigma.fst h₀,
    replace h₁ := congr_arg sigma.fst h₁,
    simp only [dest_mk] at h₀ h₁,
    rw [h₀,h₁], },
  { simp only [dest_mk] at h₀ h₁,
    cases h₀, cases h₁,
    apply h₂, },
end

theorem bisim' {α : Type*} (Q : α → Prop) (u v : α → M P)
    (h : ∀ x, Q x → ∃ a f f',
      M.dest (u x) = ⟨a, f⟩ ∧
      M.dest (v x) = ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
  ∀ x, Q x → u x = v x :=
λ x Qx,
let R := λ w z : M P, ∃ x', Q x' ∧ w = u x' ∧ z = v x' in
@M.bisim P R
  (λ x y ⟨x', Qx', xeq, yeq⟩,
    let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx' in
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
  _ _ ⟨x, Qx, rfl, rfl⟩

-- for the record, show M_bisim follows from _bisim'
theorem bisim_equiv (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M.dest x = ⟨a, f⟩ ∧
      M.dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y :=
λ x y Rxy,
let Q : M P × M P → Prop := λ p, R p.fst p.snd in
bisim' Q prod.fst prod.snd
  (λ p Qp,
    let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp in
    ⟨a, f, f', hx, hy, λ i, ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
  ⟨x, y⟩ Rxy

theorem corec_unique (g : α → P.obj α) (f : α → M P)
    (hyp : ∀ x, M.dest (f x) = f <$> (g x)) :
  f = M.corec g :=
begin
  ext x,
  apply bisim' (λ x, true) _ _ _ _ trivial,
  clear x,
  intros x _,
  cases gxeq : g x with a f',
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩,
  { rw [hyp, gxeq, pfunctor.map_eq] },
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩,
  { rw [dest_corec, gxeq, pfunctor.map_eq], },
  refine ⟨_, _, _, h₀, h₁, _⟩,
  intro i,
  exact ⟨f' i, trivial, rfl, rfl⟩
end

/-- corecursor where the state of the computation can be sent downstream
in the form of a recursive call -/
def corec₁ {α : Type u} (F : Π X, (α → X) → α → P.obj X) : α → M P :=
M.corec (F _ id)

/-- corecursor where it is possible to return a fully formed value at any point
of the computation -/
def corec' {α : Type u} (F : Π {X : Type u}, (α → X) → α → M P ⊕ P.obj X) (x : α) : M P :=
corec₁
(λ X rec (a : M P ⊕ α),
     let y := a >>= F (rec ∘ sum.inr) in
     match y with
     | sum.inr y := y
     | sum.inl y := (rec ∘ sum.inl) <$> M.dest y
     end )
(@sum.inr (M P) _ x)

end M

end pfunctor
