/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import data.fin2
import logic.function.basic
import tactic.basic

/-!

Tuples of types, and their categorical structure.

Features:

`typevec n`   : n-tuples of types
`α ⟹ β`      : n-tuples of maps
`f ⊚ g`       : composition

Also, support functions for operating with n-tuples of types, such as:

`append1 α β`    : append type `β` to n-tuple `α` to obtain an (n+1)-tuple
`drop α`         : drops the last element of an (n+1)-tuple
`last α`         : returns the last element of an (n+1)-tuple
`append_fun f g` : appends a function g to an n-tuple of functions
`drop_fun f`     : drops the last function from an n+1-tuple
`last_fun f`     : returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/

universes u v w


/--
n-tuples of types, as a category
-/
def typevec (n : ℕ) := fin2 n → Type*

instance {n} : inhabited (typevec.{u} n) := ⟨ λ _, punit ⟩

namespace typevec

variable {n : ℕ}

/-- arrow in the category of `typevec` -/
def arrow (α β : typevec n) := Π i : fin2 n, α i → β i

localized "infixl ` ⟹ `:40 := typevec.arrow" in mvfunctor

instance arrow.inhabited (α β : typevec n) [Π i, inhabited (β i)] : inhabited (α ⟹ β) :=
⟨ λ _ _, default _ ⟩

/-- identity of arrow composition -/
def id {α : typevec n} : α ⟹ α := λ i x, x

/-- arrow composition in the category of `typevec` -/
def comp {α β γ : typevec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ :=
λ i x, g i (f i x)

localized "infixr ` ⊚ `:80 := typevec.comp" in mvfunctor -- type as \oo

@[simp] theorem id_comp {α β : typevec n} (f : α ⟹ β) : id ⊚ f = f :=
rfl

@[simp] theorem comp_id {α β : typevec n} (f : α ⟹ β) : f ⊚ id = f :=
rfl

theorem comp_assoc {α β γ δ : typevec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
  (h ⊚ g) ⊚ f = h ⊚ g ⊚ f := rfl

/--
Support for extending a typevec by one element.
-/
def append1 (α : typevec n) (β : Type*) : typevec (n+1)
| (fin2.fs i) := α i
| fin2.fz      := β

infixl ` ::: `:67 := append1

/-- retain only a `n-length` prefix of the argument -/
def drop (α : typevec.{u} (n+1)) : typevec n := λ i, α i.fs

/-- take the last value of a `(n+1)-length` vector -/
def last (α : typevec.{u} (n+1)) : Type* := α fin2.fz

/-- typevec of length 0 -/
def nil : typevec.{u} 0 := fin2.elim0

instance last.inhabited (α : typevec (n+1)) [inhabited (α fin2.fz)] : inhabited (last α) :=
⟨ (default (α fin2.fz) : α fin2.fz) ⟩

theorem drop_append1 {α : typevec n} {β : Type*} {i : fin2 n} : drop (append1 α β) i = α i := rfl

theorem drop_append1' {α : typevec n} {β : Type*} : drop (append1 α β) = α :=
by ext; apply drop_append1

theorem last_append1 {α : typevec n} {β : Type*} : last (append1 α β) = β := rfl

@[simp]
theorem append1_drop_last (α : typevec (n+1)) : append1 (drop α) (last α) = α :=
funext $ λ i, by cases i; refl

/-- cases on `(n+1)-length` vectors -/
@[elab_as_eliminator] def append1_cases
  {C : typevec (n+1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ :=
by rw [← @append1_drop_last _ γ]; apply H

@[simp] theorem append1_cases_append1 {C : typevec (n+1) → Sort u}
  (H : ∀ α β, C (append1 α β)) (α β) :
  @append1_cases _ C H (append1 α β) = H α β := rfl

/-- append an arrow and a function for arbitrary source and target
type vectors -/
def split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
| (fin2.fs i) := f i
| fin2.fz      := g

/-- append an arrow and a function as well as their respective source
and target types / typevecs -/
def append_fun {α α' : typevec n} {β β' : Type*}
  (f : α ⟹ α') (g : β → β') : append1 α β ⟹ append1 α' β' := split_fun f g

infixl ` ::: ` := append_fun

/-- split off the prefix of an arrow -/
def drop_fun {α β : typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
λ i, f i.fs

/-- split off the last function of an arrow -/
def last_fun {α β : typevec (n+1)} (f : α ⟹ β) : last α → last β :=
f fin2.fz

/-- arrow in the category of `0-length` vectors -/
def nil_fun {α : typevec 0} {β : typevec 0} : α ⟹ β :=
λ i, fin2.elim0 i

theorem eq_of_drop_last_eq {α β : typevec (n+1)} {f g : α ⟹ β}
  (h₀ : drop_fun f = drop_fun g) (h₁ : last_fun f = last_fun g) : f = g :=
by replace h₀ := congr_fun h₀;
   ext1 (ieq | ⟨j, ieq⟩); apply_assumption

@[simp] theorem drop_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  drop_fun (split_fun f g) = f := rfl

/-- turn an equality into an arrow -/
def arrow.mp {α β : typevec n} (h : α = β) : α ⟹ β
| i := eq.mp (congr_fun h _)

/-- turn an equality into an arrow, with reverse direction -/
def arrow.mpr {α β : typevec n} (h : α = β) : β ⟹ α
| i := eq.mpr (congr_fun h _)

/-- decompose a vector into its prefix appended with its last element -/
def to_append1_drop_last {α : typevec (n+1)} : α ⟹ drop α ::: last α :=
arrow.mpr (append1_drop_last _)

/-- stitch two bits of a vector back together -/
def from_append1_drop_last {α : typevec (n+1)} : drop α ::: last α ⟹ α :=
arrow.mp (append1_drop_last _)

@[simp] theorem last_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  last_fun (split_fun f g) = g := rfl

@[simp] theorem drop_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  drop_fun (f ::: g) = f := rfl

@[simp] theorem last_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  last_fun (f ::: g) = g := rfl

theorem split_drop_fun_last_fun {α α' : typevec (n+1)} (f : α ⟹ α') :
  split_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq rfl rfl

theorem split_fun_inj
  {α α' : typevec (n+1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
  (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

theorem append_fun_inj {α α' : typevec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β → β'} :
  f ::: g = f' ::: g' →  f = f' ∧ g = g' :=
split_fun_inj

theorem split_fun_comp {α₀ α₁ α₂ : typevec (n+1)}
    (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
    (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
  split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = split_fun f₁ g₁ ⊚ split_fun f₀ g₀ :=
eq_of_drop_last_eq rfl rfl

theorem append_fun_comp_split_fun
  {α γ : typevec n} {β δ : Type*} {ε : typevec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ)
    (g₀ : last ε → β) (g₁ : β → δ) :
  append_fun f₁ g₁ ⊚ split_fun f₀ g₀ = split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
(split_fun_comp _ _ _ _).symm

lemma append_fun_comp {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  f₁ ⊚ f₀ ::: g₁ ∘ g₀ = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
eq_of_drop_last_eq rfl rfl

lemma append_fun_comp' {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = f₁ ⊚ f₀ ::: g₁ ∘ g₀ :=
eq_of_drop_last_eq rfl rfl

lemma nil_fun_comp {α₀ : typevec 0} (f₀ : α₀ ⟹ nil) : nil_fun ⊚ f₀ = f₀ :=
funext $ λ x, fin2.elim0 x

theorem append_fun_comp_id {α : typevec n} {β₀ β₁ β₂ : Type*}
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  @id _ α ::: g₁ ∘ g₀ = (id ::: g₁) ⊚ (id ::: g₀) :=
eq_of_drop_last_eq rfl rfl

@[simp]
theorem drop_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  drop_fun (f₁ ⊚ f₀) = drop_fun f₁ ⊚ drop_fun f₀ := rfl

@[simp]
theorem last_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  last_fun (f₁ ⊚ f₀) = last_fun f₁ ∘ last_fun f₀ := rfl

theorem append_fun_aux {α α' : typevec n} {β β' : Type*}
  (f : α ::: β ⟹ α' ::: β') : drop_fun f ::: last_fun f = f :=
eq_of_drop_last_eq rfl rfl

theorem append_fun_id_id {α : typevec n} {β : Type*} :
  @typevec.id n α ::: @_root_.id β = typevec.id :=
eq_of_drop_last_eq rfl rfl

instance subsingleton0 : subsingleton (typevec 0) :=
⟨ λ a b, funext $ λ a, fin2.elim0 a  ⟩

run_cmd do
  mk_simp_attr `typevec,
  tactic.add_doc_string `simp_attr.typevec
"simp set for the manipulation of typevec and arrow expressions"

local prefix `♯`:0 := cast (by try { simp }; congr' 1; try { simp })

/-- cases distinction for 0-length type vector -/
protected def cases_nil {β : typevec 0 → Sort*} (f : β nil) :
  Π v, β v :=
λ v, ♯ f

/-- cases distinction for (n+1)-length type vector -/
protected def cases_cons (n : ℕ) {β : typevec (n+1) → Sort*} (f : Π t (v : typevec n), β (v ::: t)) :
  Π v, β v :=
λ v : typevec (n+1), ♯ f v.last v.drop

protected lemma cases_nil_append1 {β : typevec 0 → Sort*} (f : β nil) :
  typevec.cases_nil f nil = f := rfl

protected lemma cases_cons_append1 (n : ℕ) {β : typevec (n+1) → Sort*}
      (f : Π t (v : typevec n), β (v ::: t))
      (v : typevec n) (α) :
  typevec.cases_cons n f (v ::: α) = f α v := rfl

/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₃ {β : Π v v' : typevec 0, v ⟹ v' → Sort*} (f : β nil nil nil_fun) :
  Π v v' fs, β v v' fs :=
λ v v' fs,
begin
  refine cast _ f; congr' 1; ext; try { intros; casesm fin2 0 }, refl
end

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₃ (n : ℕ) {β : Π v v' : typevec (n+1), v ⟹ v' → Sort*}
  (F : Π t t' (f : t → t') (v v' : typevec n) (fs : v ⟹ v'), β (v ::: t) (v' ::: t') (fs ::: f)) :
  Π v v' fs, β v v' fs :=
begin
  intros v v',
  rw [←append1_drop_last v, ←append1_drop_last v'],
  intro fs,
  rw [←split_drop_fun_last_fun fs],
  apply F
end

/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₂ {β : nil ⟹ nil → Sort*}
  (f : β nil_fun) :
  Π f, β f :=
begin
  intro g, have : g = nil_fun, ext ⟨ ⟩,
  rw this, exact f
end

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₂ (n : ℕ) (t t' : Type*) (v v' : typevec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
  (F : Π (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) :
  Π fs, β fs :=
begin
  intro fs,
  rw [←split_drop_fun_last_fun fs],
  apply F
end

lemma typevec_cases_nil₂_append_fun {β : nil ⟹ nil → Sort*}
  (f : β nil_fun) :
  typevec_cases_nil₂ f nil_fun = f := rfl

lemma typevec_cases_cons₂_append_fun (n : ℕ) (t t' : Type*) (v v' : typevec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
  (F : Π (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) (f fs) :
  typevec_cases_cons₂ n t t' v v' F (fs ::: f) = F f fs := rfl

/- for lifting predicates and relations -/

/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def pred_last (α : typevec n) {β : Type*} (p : β → Prop) : Π ⦃i⦄, (α.append1 β) i → Prop
| (fin2.fs i) := λ x, true
| fin2.fz      := p

/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and all the other elements are equal. -/
def rel_last (α : typevec n) {β γ : Type*} (r : β → γ → Prop) :
  Π ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
| (fin2.fs i) := eq
| fin2.fz      := r

section liftp'
open nat

/-- `repeat n t` is a `n-length` type vector that contains `n` occurences of `t` -/
def repeat : Π (n : ℕ) (t : Sort*), typevec n
| 0 t := nil
| (nat.succ i) t := append1 (repeat i t) t

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def prod : Π {n} (α β : typevec.{u} n), typevec n
| 0 α β := nil
| (n+1) α β := prod (drop α) (drop β) ::: (last α × last β)

localized "infix ` ⊗ `:45 := typevec.prod" in mvfunctor

/-- `const x α` is an arrow that ignores its source and constructs a `typevec` that
contains nothing but `x` -/
protected def const {β} (x : β) : Π {n} (α : typevec n), α ⟹ repeat _ β
| (succ n) α (fin2.fs i) := const (drop α) _
| (succ n) α fin2.fz := λ _, x

open function (uncurry)

/-- vector of equality on a product of vectors -/
def repeat_eq : Π {n} (α : typevec n), α ⊗ α ⟹ repeat _ Prop
| 0 α := nil_fun
| (succ n) α := repeat_eq (drop α) ::: uncurry eq

lemma const_append1 {β γ} (x : γ) {n} (α : typevec n) : typevec.const x (α ::: β) = append_fun (typevec.const x α) (λ _, x) :=
by ext i : 1; cases i; refl

lemma eq_nil_fun {α β : typevec 0} (f : α ⟹ β) : f = nil_fun :=
by ext x; cases x

lemma id_eq_nil_fun {α : typevec 0} : @id _ α = nil_fun :=
by ext x; cases x

lemma const_nil {β} (x : β) (α : typevec 0) : typevec.const x α = nil_fun :=
by ext i : 1; cases i; refl

@[typevec]
lemma repeat_eq_append1 {β} {n} (α : typevec n) : repeat_eq (α ::: β) = split_fun (repeat_eq α) (uncurry eq) :=
by induction n; refl

@[typevec]
lemma repeat_eq_nil (α : typevec 0) : repeat_eq α = nil_fun :=
by ext i : 1; cases i; refl

/-- predicate on a type vector to constrain only the last object -/
def pred_last' (α : typevec n) {β : Type*} (p : β → Prop) : α ::: β ⟹ repeat (n+1) Prop :=
split_fun (typevec.const true α) p

/-- predicate on the product of two type vectors to constrain only their last object -/
def rel_last' (α : typevec n) {β : Type*} (p : β → β → Prop) : (α ::: β ⊗ α ::: β) ⟹ repeat (n+1) Prop :=
split_fun (repeat_eq α) (uncurry p)

/-- given `F : typevec.{u} (n+1) → Type u`, `curry F : Type u → typevec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def curry (F : typevec.{u} (n+1) → Type*) (α : Type u) (β : typevec.{u} n) : Type* :=
F (β ::: α)

instance curry.inhabited (F : typevec.{u} (n+1) → Type*) (α : Type u) (β : typevec.{u} n)
  [I : inhabited (F $ β ::: α)]:
  inhabited (curry F α β) := I

/-- arrow to remove one element of a `repeat` vector -/
def drop_repeat (α : Type*) : Π {n}, drop (repeat (succ n) α) ⟹ repeat n α
| (succ n) (fin2.fs i) := drop_repeat i
| (succ n) fin2.fz := _root_.id

/-- projection for a repeat vector -/
def of_repeat {α : Sort*} : Π {n i}, repeat n α i → α
| ._ fin2.fz := _root_.id
| ._ (fin2.fs i) := @of_repeat _ i

lemma const_iff_true {α : typevec n} {i x p} : of_repeat (typevec.const p α i x) ↔ p :=
by induction i; [refl, erw [typevec.const,@i_ih (drop α) x]]

-- variables  {F : typevec.{u} n → Type*} [mvfunctor F]
variables {α β γ : typevec.{u} n}
variables (p : α ⟹ repeat n Prop) (r : α ⊗ α ⟹ repeat n Prop)

/-- left projection of a `prod` vector -/
def prod.fst : Π {n} {α β : typevec.{u} n}, α ⊗ β ⟹ α
| (succ n) α β (fin2.fs i) := @prod.fst _ (drop α) (drop β) i
| (succ n) α β fin2.fz := _root_.prod.fst

/-- right projection of a `prod` vector -/
def prod.snd : Π {n} {α β : typevec.{u} n}, α ⊗ β ⟹ β
| (succ n) α β (fin2.fs i) := @prod.snd _ (drop α) (drop β) i
| (succ n) α β fin2.fz := _root_.prod.snd

/-- introduce a product where both components are the same -/
def prod.diag : Π {n} {α : typevec.{u} n}, α ⟹ α ⊗ α
| (succ n) α (fin2.fs i) x := @prod.diag _ (drop α) _ x
| (succ n) α fin2.fz x := (x,x)

/-- constructor for `prod` -/
def prod.mk : Π {n} {α β : typevec.{u} n} (i : fin2 n), α i → β i → (α ⊗ β) i
| (succ n) α β (fin2.fs i) := prod.mk i
| (succ n) α β fin2.fz := _root_.prod.mk

/-- `prod` is functorial -/
protected def prod.map : Π {n} {α α' β β' : typevec.{u} n}, (α ⟹ β) → (α' ⟹ β') → α ⊗ α' ⟹ β ⊗ β'
| (succ n) α α' β β' x y (fin2.fs i) a := @prod.map _ (drop α) (drop α') (drop β) (drop β') (drop_fun x) (drop_fun y) _ a
| (succ n) α α' β β' x y fin2.fz a := (x _ a.1,y _ a.2)

localized "infix ` ⊗' `:45 := typevec.prod.map" in mvfunctor

theorem fst_prod_mk {α α' β β' : typevec n} (f : α ⟹ β) (g : α' ⟹ β') :
  typevec.prod.fst ⊚ (f ⊗' g) = f ⊚ typevec.prod.fst :=
by ext i; induction i; [refl, apply i_ih]

theorem snd_prod_mk {α α' β β' : typevec n} (f : α ⟹ β) (g : α' ⟹ β') :
  typevec.prod.snd ⊚ (f ⊗' g) = g ⊚ typevec.prod.snd :=
by ext i; induction i; [refl, apply i_ih]

theorem fst_diag {α : typevec n} : typevec.prod.fst ⊚ (prod.diag : α ⟹ _) = id :=
by ext i; induction i; [refl, apply i_ih]

theorem snd_diag {α : typevec n} : typevec.prod.snd ⊚ (prod.diag : α ⟹ _) = id :=
by ext i; induction i; [refl, apply i_ih]

lemma repeat_eq_iff_eq {α : typevec n} {i x y} : of_repeat (repeat_eq α i (prod.mk _ x y)) ↔ x = y :=
by induction i; [refl, erw [repeat_eq,@i_ih (drop α) x y]]

/-- given a predicate vector `p` over vector `α`, `subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
def subtype_ : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), typevec n
| ._ α p fin2.fz := _root_.subtype (λ x, p fin2.fz x)
| ._ α p (fin2.fs i) := subtype_ (drop_fun p) i

/-- projection on `subtype_` -/
def subtype_val : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), subtype_ p ⟹ α
| (succ n) α p (fin2.fs i) := @subtype_val n _ _ i
| (succ n) α p fin2.fz := _root_.subtype.val

/-- arrow that rearranges the type of `subtype_` to turn a subtype of vector into
a vector of subtypes -/
def to_subtype : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), (λ (i : fin2 n), { x // of_repeat $ p i x }) ⟹ subtype_ p
| (succ n) α p (fin2.fs i) x := to_subtype (drop_fun p) i x
| (succ n) α p fin2.fz x := x

/-- arrow that rearranges the type of `subtype_` to turn a vector of subtypes
into a subtype of vector -/
def of_subtype : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), subtype_ p ⟹ (λ (i : fin2 n), { x // of_repeat $ p i x })
| (succ n) α p (fin2.fs i) x := of_subtype _ i x
| (succ n) α p fin2.fz x := x

/-- similar to `to_subtype` adapted to relations (i.e. predicate on product) -/
def to_subtype' : Π {n} {α : typevec.{u} n} (p : α ⊗ α ⟹ repeat n Prop),
  (λ (i : fin2 n), { x : α i × α i // of_repeat $ p i (prod.mk _ x.1 x.2) }) ⟹ subtype_ p
| (succ n) α p (fin2.fs i) x := to_subtype' (drop_fun p) i x
| (succ n) α p fin2.fz x := ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩

/-- similar to `of_subtype` adapted to relations (i.e. predicate on product) -/
def of_subtype' : Π {n} {α : typevec.{u} n} (p : α ⊗ α ⟹ repeat n Prop),
  subtype_ p ⟹ (λ (i : fin2 n), { x : α i × α i // of_repeat $ p i (prod.mk _ x.1 x.2) })
| ._ α p (fin2.fs i) x := of_subtype' _ i x
| ._ α p fin2.fz x := ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩

/-- similar to `diag` but the target vector is a `subtype_`
guaranteeing the equality of the components -/
def diag_sub  : Π {n} {α : typevec.{u} n}, α ⟹ subtype_ (repeat_eq α)
| (succ n) α (fin2.fs i) x := @diag_sub _ (drop α) _ x
| (succ n) α fin2.fz x := ⟨(x,x), rfl⟩

lemma subtype_val_nil {α : typevec.{u} 0} (ps : α ⟹ repeat 0 Prop) : typevec.subtype_val ps = nil_fun :=
funext $ by rintro ⟨ ⟩; refl

lemma diag_sub_val {n} {α : typevec.{u} n} :
  subtype_val (repeat_eq α) ⊚ diag_sub = prod.diag :=
by ext i; induction i; [refl, apply i_ih]

lemma prod_id : Π {n} {α β : typevec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) :=
begin
  intros, ext i a, induction i,
  { cases a, refl },
  { apply i_ih },
end

lemma append_prod_append_fun {n} {α α' β β' : typevec.{u} n}
  {φ φ' ψ ψ' : Type u}
  {f₀ : α ⟹ α'} {g₀ : β ⟹ β'}
  {f₁ : φ → φ'}  {g₁ : ψ → ψ'} :
  (f₀ ⊗' g₀) ::: _root_.prod.map f₁ g₁ = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) :=
by ext i a; cases i; [cases a, skip]; refl

end liftp'

@[simp]
lemma drop_fun_diag {α} :
  drop_fun (@prod.diag (n+1) α) = prod.diag :=
by { ext i : 2, induction i; simp [drop_fun,*]; refl }

@[simp]
lemma drop_fun_subtype_val {α} (p : α ⟹ repeat (n+1) Prop) :
  drop_fun (subtype_val p) = subtype_val _ := rfl

@[simp]
lemma last_fun_subtype_val {α} (p : α ⟹ repeat (n+1) Prop) :
  last_fun (subtype_val p) = subtype.val := rfl

@[simp]
lemma drop_fun_to_subtype {α} (p : α ⟹ repeat (n+1) Prop) :
  drop_fun (to_subtype p) = to_subtype _ :=
by { ext i : 2, induction i; simp [drop_fun,*]; refl }

@[simp]
lemma last_fun_to_subtype {α} (p : α ⟹ repeat (n+1) Prop) :
  last_fun (to_subtype p) = _root_.id :=
by { ext i : 2, induction i; simp [drop_fun,*]; refl }

@[simp]
lemma drop_fun_of_subtype {α} (p : α ⟹ repeat (n+1) Prop) :
  drop_fun (of_subtype p) = of_subtype _ :=
by { ext i : 2, induction i; simp [drop_fun,*]; refl }

@[simp]
lemma last_fun_of_subtype {α} (p : α ⟹ repeat (n+1) Prop) :
  last_fun (of_subtype p) = _root_.id :=
by { ext i : 2, induction i; simp [drop_fun,*]; refl }

@[simp]
lemma drop_fun_rel_last {α : typevec n} {β}
  (R : β → β → Prop) :
  drop_fun (rel_last' α R) = repeat_eq α := rfl

attribute [simp] drop_append1'
open_locale mvfunctor

@[simp]
lemma drop_fun_prod {α α' β β' : typevec (n+1)} (f : α ⟹ β) (f' : α' ⟹ β') :
  drop_fun (f ⊗' f') = (drop_fun f ⊗' drop_fun f') :=
by { ext i : 2, induction i; simp [drop_fun,*]; refl }

@[simp]
lemma last_fun_prod {α α' β β' : typevec (n+1)} (f : α ⟹ β) (f' : α' ⟹ β') :
  last_fun (f ⊗' f') = _root_.prod.map (last_fun f) (last_fun f') :=
by { ext i : 1, induction i; simp [last_fun,*]; refl }

@[simp]
lemma drop_fun_from_append1_drop_last {α : typevec (n+1)} :
  drop_fun (@from_append1_drop_last _ α) = id := rfl

@[simp]
lemma last_fun_from_append1_drop_last {α : typevec (n+1)} :
  last_fun (@from_append1_drop_last _ α) = _root_.id := rfl

@[simp]
lemma drop_fun_id {α : typevec (n+1)} :
  drop_fun (@typevec.id _ α) = id := rfl

@[simp]
lemma prod_map_id {α β : typevec n} :
  (@typevec.id _ α ⊗' @typevec.id _ β) = id :=
by { ext i : 2, induction i; simp only [typevec.prod.map,*,drop_fun_id],
     cases x, refl, refl }

@[simp]
lemma subtype_val_diag_sub {α : typevec n} :
  subtype_val (repeat_eq α) ⊚ diag_sub = prod.diag :=
by { clear_except, ext i, induction i; [refl, apply i_ih], }

@[simp]
lemma to_subtype_of_subtype {α : typevec n} (p : α ⟹ repeat n Prop) :
  @to_subtype n _ p ⊚ of_subtype _ = id :=
by { ext i : 2, dsimp [typevec.comp], induction i;
       simp [@to_subtype.equations._eqn_2 _ _ p,of_subtype,*],
     { refl },
       rw @to_subtype.equations._eqn_2 _ _ p i_a,
       change (λ (i : fin2 i_n.succ) (x : α i), p i x) with p,
       rw i_ih, refl  }

@[simp]
lemma to_subtype_of_subtype_assoc {α β : typevec n} (p : α ⟹ repeat n Prop)
  (f : β ⟹ subtype_ p) :
  @to_subtype n _ p ⊚ of_subtype _ ⊚ f = f :=
by rw [← comp_assoc,to_subtype_of_subtype]; simp

end typevec
