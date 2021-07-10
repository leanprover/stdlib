/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import logic.relator

/-!
# Quotient types

This module extends the core library's treatment of quotient types (`init.data.quot`).

## Tags

quotient
-/

variables {α : Sort*} {β : Sort*}

namespace setoid

lemma ext {α : Sort*} :
  ∀{s t : setoid α}, (∀a b, @setoid.r α s a b ↔ @setoid.r α t a b) → s = t
| ⟨r, _⟩ ⟨p, _⟩ eq :=
  have r = p, from funext $ assume a, funext $ assume b, propext $ eq a b,
  by subst this

end setoid

namespace quot
variables {ra : α → α → Prop} {rb : β → β → Prop} {φ : quot ra → quot rb → Sort*}
local notation `⟦`:max a `⟧` := quot.mk _ a

instance [inhabited α] : inhabited (quot ra) := ⟨⟦default _⟧⟩

/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrec_on₂ (qa : quot ra) (qb : quot rb) (f : Π a b, φ ⟦a⟧ ⟦b⟧)
  (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → f a₁ b == f a₂ b)
  (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → f a b₁ == f a b₂) : φ qa qb :=
quot.hrec_on qa (λ a, quot.hrec_on qb (f a) (λ b₁ b₂ pb, cb pb)) $ λ a₁ a₂ pa,
  quot.induction_on qb $ λ b,
    calc @quot.hrec_on _ _ (φ _) ⟦b⟧ (f a₁) (@cb _)
          == f a₁ b                                     : by simp [heq_self_iff_true]
      ... == f a₂ b                                     : ca pa
      ... == @quot.hrec_on _ _ (φ _) ⟦b⟧ (f a₂) (@cb _) : by simp [heq_self_iff_true]

/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `quot ra → quot rb`. -/
protected def map (f : α → β) (h : (ra ⇒ rb) f f) : quot ra → quot rb :=
quot.lift (λ x, ⟦f x⟧) $ assume x y (h₁ : ra x y), quot.sound $ h h₁

/-- If `ra` is a subrelation of `ra'`, then we have a natural map `quot ra → quot ra'`. -/
protected def map_right {ra' : α → α → Prop} (h : ∀a₁ a₂, ra a₁ a₂ → ra' a₁ a₂) :
  quot ra → quot ra' :=
quot.map id h

/-- weaken the relation of a quotient -/
def factor {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
  quot r → quot s :=
quot.lift (quot.mk s) (λ x y rxy, quot.sound (h x y rxy))

lemma factor_mk_eq {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
  factor r s h ∘ quot.mk _ = quot.mk _ := rfl

variables {γ : Sort*} {r : α → α → Prop} {s : β → β → Prop}

/-- **Alias** of `quot.lift_beta`. -/
lemma lift_mk (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) :
  quot.lift f h (quot.mk r a) = f a := quot.lift_beta f h a

@[simp]
lemma lift_on_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
  quot.lift_on (quot.mk r a) f h = f a := rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β`. -/
attribute [reducible, elab_as_eliminator]
protected def lift₂
  (f : α → β → γ)
  (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
  (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
  (q₁ : quot r) (q₂ : quot s) : γ :=
quot.lift (λ a, quot.lift (f a) (hr a))
(λ a₁ a₂ ha, funext (λ q, quot.induction_on q (λ b, hs a₁ a₂ b ha)))
q₁ q₂

@[simp]
lemma lift₂_mk (f : α → β → γ)
  (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
  (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (a : α) (b : β) :
  quot.lift₂ f hr hs (quot.mk r a) (quot.mk s b) = f a b := rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it. -/
attribute [reducible, elab_as_eliminator]
protected def lift_on₂ (p : quot r) (q : quot s) (f : α → β → γ)
  (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
  (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : γ := quot.lift₂ f hr hs p q

@[simp]
lemma lift_on₂_mk (a : α) (b : β) (f : α → β → γ)
  (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
  (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) :
  quot.lift_on₂ (quot.mk r a) (quot.mk s b) f hr hs = f a b := rfl

variables {t : γ → γ → Prop}

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` wih values in a quotient of
`γ`. -/
protected def map₂ (f : α → β → γ)
  (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
  (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b))
  (q₁ : quot r) (q₂ : quot s) : quot t :=
quot.lift₂ (λ a b, quot.mk t $ f a b) (λ a b₁ b₂ hb, quot.sound (hr a b₁ b₂ hb))
(λ a₁ a₂ b ha, quot.sound (hs a₁ a₂ b ha)) q₁ q₂

@[simp]
lemma map₂_mk (f : α → β → γ)
  (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
  (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b))
  (a : α) (b : β) : quot.map₂ f hr hs (quot.mk r a) (quot.mk s b) = quot.mk t (f a b) := rfl

attribute [elab_as_eliminator]
protected lemma induction_on₂
  {δ : quot r → quot s → Prop} (q₁ : quot r) (q₂ : quot s)
  (h : ∀ a b, δ (quot.mk r a) (quot.mk s b)) : δ q₁ q₂ :=
quot.ind (λ a₁, quot.ind (λ a₂, h a₁ a₂) q₂) q₁

attribute [elab_as_eliminator]
protected lemma induction_on₃
  {δ : quot r → quot s → quot t → Prop} (q₁ : quot r) (q₂ : quot s) (q₃ : quot t)
  (h : ∀ a b c, δ (quot.mk r a) (quot.mk s b) (quot.mk t c)) : δ q₁ q₂ q₃ :=
quot.ind (λ a₁, quot.ind (λ a₂, quot.ind (λ a₃, h a₁ a₂ a₃) q₃) q₂) q₁

end quot

namespace quotient
variables [sa : setoid α] [sb : setoid β]
variables {φ : quotient sa → quotient sb → Sort*}

instance [inhabited α] : inhabited (quotient sa) := ⟨⟦default _⟧⟩

/-- Induction on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrec_on₂ (qa : quotient sa) (qb : quotient sb) (f : Π a b, φ ⟦a⟧ ⟦b⟧)
  (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) : φ qa qb :=
quot.hrec_on₂ qa qb f
  (λ _ _ _ p, c _ _ _ _ p (setoid.refl _))
  (λ _ _ _ p, c _ _ _ _ (setoid.refl _) p)

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map (f : α → β) (h : ((≈) ⇒ (≈)) f f) : quotient sa → quotient sb :=
quot.map f h

@[simp] lemma map_mk (f : α → β) (h : ((≈) ⇒ (≈)) f f) (x : α) :
  quotient.map f h (⟦x⟧ : quotient sa) = (⟦f x⟧ : quotient sb) :=
rfl

variables {γ : Sort*} [sc : setoid γ]

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : quotient sa → quotient sb → quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ (f : α → β → γ) (h : ((≈) ⇒ (≈) ⇒ (≈)) f f) :
  quotient sa → quotient sb → quotient sc :=
quotient.lift₂ (λ x y, ⟦f x y⟧) (λ x₁ y₁ x₂ y₂ h₁ h₂, quot.sound $ h h₁ h₂)

end quotient

lemma quot.eq {α : Type*} {r : α → α → Prop} {x y : α} :
  quot.mk r x = quot.mk r y ↔ eqv_gen r x y :=
⟨quot.exact r, quot.eqv_gen_sound⟩

@[simp] theorem quotient.eq [r : setoid α] {x y : α} : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
⟨quotient.exact, quotient.sound⟩

theorem forall_quotient_iff {α : Type*} [r : setoid α] {p : quotient r → Prop} :
  (∀a:quotient r, p a) ↔ (∀a:α, p ⟦a⟧) :=
⟨assume h x, h _, assume h a, a.induction_on h⟩

@[simp] lemma quotient.lift_mk [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b)
  (x : α) :
  quotient.lift f h (quotient.mk x) = f x := rfl

@[simp] lemma quotient.lift_on_mk [s : setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b)
  (x : α) :
  quotient.lift_on (quotient.mk x) f h = f x := rfl

@[simp] theorem quotient.lift_on₂_mk {α : Sort*} {β : Sort*} [setoid α] (f : α → α → β)
  (h : ∀ (a₁ a₂ b₁ b₂ : α), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (x y : α) :
  quotient.lift_on₂ (quotient.mk x) (quotient.mk y) f h = f x y := rfl

/-- `quot.mk r` is a surjective function. -/
lemma surjective_quot_mk (r : α → α → Prop) : function.surjective (quot.mk r) :=
quot.exists_rep

/-- `quotient.mk` is a surjective function. -/
lemma surjective_quotient_mk (α : Sort*) [s : setoid α] :
  function.surjective (quotient.mk : α → quotient s) :=
quot.exists_rep

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def quot.out {r : α → α → Prop} (q : quot r) : α :=
classical.some (quot.exists_rep q)

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
meta def quot.unquot {r : α → α → Prop} : quot r → α := unchecked_cast

@[simp] theorem quot.out_eq {r : α → α → Prop} (q : quot r) : quot.mk r q.out = q :=
classical.some_spec (quot.exists_rep q)

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def quotient.out [s : setoid α] : quotient s → α := quot.out

@[simp] theorem quotient.out_eq [s : setoid α] (q : quotient s) : ⟦q.out⟧ = q := q.out_eq

theorem quotient.mk_out [s : setoid α] (a : α) : ⟦a⟧.out ≈ a :=
quotient.exact (quotient.out_eq _)

lemma quotient.mk_eq_iff_out [s : setoid α] {x : α} {y : quotient s} :
  ⟦x⟧ = y ↔ x ≈ quotient.out y :=
begin
  refine iff.trans _ quotient.eq,
  rw quotient.out_eq y,
end

lemma quotient.eq_mk_iff_out [s : setoid α] {x : quotient s} {y : α} :
  x = ⟦y⟧ ↔ quotient.out x ≈ y  :=
begin
  refine iff.trans _ quotient.eq,
  rw quotient.out_eq x,
end

instance pi_setoid {ι : Sort*} {α : ι → Sort*} [∀ i, setoid (α i)] : setoid (Π i, α i) :=
{ r := λ a b, ∀ i, a i ≈ b i,
  iseqv := ⟨
    λ a i, setoid.refl _,
    λ a b h i, setoid.symm (h _),
    λ a b c h₁ h₂ i, setoid.trans (h₁ _) (h₂ _)⟩ }

/-- Given a function `f : Π i, quotient (S i)`, returns the class of functions `Π i, α i` sending
each `i` to an element of the class `f i`. -/
noncomputable def quotient.choice {ι : Type*} {α : ι → Type*} [S : Π i, setoid (α i)]
  (f : Π i, quotient (S i)) : @quotient (Π i, α i) (by apply_instance) :=
⟦λ i, (f i).out⟧

theorem quotient.choice_eq {ι : Type*} {α : ι → Type*} [Π i, setoid (α i)]
  (f : Π i, α i) : quotient.choice (λ i, ⟦f i⟧) = ⟦f⟧ :=
quotient.sound $ λ i, quotient.mk_out _

lemma nonempty_quotient_iff (s : setoid α) : nonempty (quotient s) ↔ nonempty α :=
⟨assume ⟨a⟩, quotient.induction_on a nonempty.intro, assume ⟨a⟩, ⟨⟦a⟧⟩⟩

/-- `trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `nonempty α`, but unlike `nonempty α`, `trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def {u} trunc (α : Sort u) : Sort u := @quot α (λ _ _, true)

theorem true_equivalence : @equivalence α (λ _ _, true) :=
⟨λ _, trivial, λ _ _ _, trivial, λ _ _ _ _ _, trivial⟩

namespace trunc

/-- Constructor for `trunc α` -/
def mk (a : α) : trunc α := quot.mk _ a

instance [inhabited α] : inhabited (trunc α) := ⟨mk (default _)⟩

/-- Any constant function lifts to a function out of the truncation -/
def lift (f : α → β) (c : ∀ a b : α, f a = f b) : trunc α → β :=
quot.lift f (λ a b _, c a b)

theorem ind {β : trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : trunc α, β q := quot.ind

protected theorem lift_mk (f : α → β) (c) (a : α) : lift f c (mk a) = f a := rfl

/-- Lift a constant function on `q : trunc α`. -/
@[reducible, elab_as_eliminator]
protected def lift_on (q : trunc α) (f : α → β)
  (c : ∀ a b : α, f a = f b) : β := lift f c q

@[elab_as_eliminator]
protected theorem induction_on {β : trunc α → Prop} (q : trunc α)
  (h : ∀ a, β (mk a)) : β q := ind h q

theorem exists_rep (q : trunc α) : ∃ a : α, mk a = q := quot.exists_rep q

attribute [elab_as_eliminator]
protected theorem induction_on₂ {C : trunc α → trunc β → Prop} (q₁ : trunc α) (q₂ : trunc β)
  (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
trunc.induction_on q₁ $ λ a₁, trunc.induction_on q₂ (h a₁)

protected theorem eq (a b : trunc α) : a = b :=
trunc.induction_on₂ a b (λ x y, quot.sound trivial)

instance : subsingleton (trunc α) := ⟨trunc.eq⟩

/-- The `bind` operator for the `trunc` monad. -/
def bind (q : trunc α) (f : α → trunc β) : trunc β :=
trunc.lift_on q f (λ a b, trunc.eq _ _)

/-- A function `f : α → β` defines a function `map f : trunc α → trunc β`. -/
def map (f : α → β) (q : trunc α) : trunc β := bind q (trunc.mk ∘ f)

instance : monad trunc :=
{ pure := @trunc.mk,
  bind := @trunc.bind }

instance : is_lawful_monad trunc :=
{ id_map := λ α q, trunc.eq _ _,
  pure_bind := λ α β q f, rfl,
  bind_assoc := λ α β γ x f g, trunc.eq _ _ }

variable {C : trunc α → Sort*}

/-- Recursion/induction principle for `trunc`. -/
@[reducible, elab_as_eliminator]
protected def rec
   (f : Π a, C (mk a)) (h : ∀ (a b : α), (eq.rec (f a) (trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
   (q : trunc α) : C q :=
quot.rec f (λ a b _, h a b) q

/-- A version of `trunc.rec` taking `q : trunc α` as the first argument. -/
@[reducible, elab_as_eliminator]
protected def rec_on (q : trunc α) (f : Π a, C (mk a))
  (h : ∀ (a b : α), (eq.rec (f a) (trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
trunc.rec f h q

/-- A version of `trunc.rec_on` assuming the codomain is a `subsingleton`. -/
@[reducible, elab_as_eliminator]
protected def rec_on_subsingleton
   [∀ a, subsingleton (C (mk a))] (q : trunc α) (f : Π a, C (mk a)) : C q :=
trunc.rec f (λ a b, subsingleton.elim _ (f b)) q

/-- Noncomputably extract a representative of `trunc α` (using the axiom of choice). -/
noncomputable def out : trunc α → α := quot.out

@[simp] theorem out_eq (q : trunc α) : mk q.out = q := trunc.eq _ _

protected theorem nonempty (q : trunc α) : nonempty α :=
nonempty_of_exists q.exists_rep

end trunc

namespace quotient
variables {γ : Sort*} {φ : Sort*}
  {s₁ : setoid α} {s₂ : setoid β} {s₃ : setoid γ}

/-! Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules. -/

/-- A version of `quotient.mk` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
protected def mk' (a : α) : quotient s₁ := quot.mk s₁.1 a

/-- `quotient.mk'` is a surjective function. -/
lemma surjective_quotient_mk' : function.surjective (quotient.mk' : α → quotient s₁) :=
quot.exists_rep

/-- A version of `quotient.lift_on` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_eliminator, reducible]
protected def lift_on' (q : quotient s₁) (f : α → φ)
  (h : ∀ a b, @setoid.r α s₁ a b → f a = f b) : φ := quotient.lift_on q f h

@[simp]
protected lemma lift_on'_mk' (f : α → φ) (h) (x : α) :
  quotient.lift_on' (@quotient.mk' _ s₁ x) f h = f x := rfl

/-- A version of `quotient.lift_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_eliminator, reducible]
protected def lift_on₂' (q₁ : quotient s₁) (q₂ : quotient s₂) (f : α → β → γ)
  (h : ∀ a₁ a₂ b₁ b₂, @setoid.r α s₁ a₁ b₁ → @setoid.r β s₂ a₂ b₂ → f a₁ a₂ = f b₁ b₂) : γ :=
quotient.lift_on₂ q₁ q₂ f h

@[simp]
protected lemma lift_on₂'_mk' (f : α → β → γ) (h) (a : α) (b : β) :
  quotient.lift_on₂' (@quotient.mk' _ s₁ a) (@quotient.mk' _ s₂ b) f h = f a b := rfl

/-- A version of `quotient.ind` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_eliminator]
protected lemma ind' {p : quotient s₁ → Prop}
  (h : ∀ a, p (quotient.mk' a)) (q : quotient s₁) : p q :=
quotient.ind h q

/-- A version of `quotient.ind₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_eliminator]
protected lemma ind₂' {p : quotient s₁ → quotient s₂ → Prop}
  (h : ∀ a₁ a₂, p (quotient.mk' a₁) (quotient.mk' a₂))
  (q₁ : quotient s₁) (q₂ : quotient s₂) : p q₁ q₂ :=
quotient.ind₂ h q₁ q₂

/-- A version of `quotient.induction_on` taking `{s : setoid α}` as an implicit argument instead
of an instance argument. -/
@[elab_as_eliminator]
protected lemma induction_on' {p : quotient s₁ → Prop} (q : quotient s₁)
  (h : ∀ a, p (quotient.mk' a)) : p q := quotient.induction_on q h

/-- A version of `quotient.induction_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit
arguments instead of instance arguments. -/
@[elab_as_eliminator]
protected lemma induction_on₂' {p : quotient s₁ → quotient s₂ → Prop} (q₁ : quotient s₁)
  (q₂ : quotient s₂) (h : ∀ a₁ a₂, p (quotient.mk' a₁) (quotient.mk' a₂)) : p q₁ q₂ :=
quotient.induction_on₂ q₁ q₂ h

/-- A version of `quotient.induction_on₃` taking `{s₁ : setoid α} {s₂ : setoid β} {s₃ : setoid γ}`
as implicit arguments instead of instance arguments. -/
@[elab_as_eliminator]
protected lemma induction_on₃' {p : quotient s₁ → quotient s₂ → quotient s₃ → Prop}
  (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃)
  (h : ∀ a₁ a₂ a₃, p (quotient.mk' a₁) (quotient.mk' a₂) (quotient.mk' a₃)) : p q₁ q₂ q₃ :=
quotient.induction_on₃ q₁ q₂ q₃ h

/-- A version of `quotient.rec_on_subsingleton` taking `{s₁ : setoid α}` as an implicit argument
instead of an instance argument. -/
@[elab_as_eliminator]
protected def rec_on_subsingleton' {φ : quotient s₁ → Sort*}
  [h : ∀ a, subsingleton (φ ⟦a⟧)] (q : quotient s₁) (f : Π a, φ (quotient.mk' a)) : φ q :=
quotient.rec_on_subsingleton q f

/-- A version of `quotient.rec_on_subsingleton₂` taking `{s₁ : setoid α} {s₂ : setoid α}`
as implicit arguments instead of instance arguments. -/
attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton₂'
   {φ : quotient s₁ → quotient s₂ → Sort*} [h : ∀ a b, subsingleton (φ ⟦a⟧ ⟦b⟧)]
   (q₁ : quotient s₁) (q₂ : quotient s₂) (f : Π a₁ a₂, φ (quotient.mk' a₁) (quotient.mk' a₂)) :
   φ q₁ q₂ :=
quotient.rec_on_subsingleton₂ q₁ q₂ f

/-- Recursion on a `quotient` argument `a`, result type depends on `⟦a⟧`. -/
protected def hrec_on' {φ : quotient s₁ → Sort*} (qa : quotient s₁) (f : Π a, φ (quotient.mk' a))
  (c : ∀ a₁ a₂, a₁ ≈ a₂ → f a₁ == f a₂) : φ qa :=
quot.hrec_on qa f c

@[simp] lemma hrec_on'_mk' {φ : quotient s₁ → Sort*} (f : Π a, φ (quotient.mk' a))
  (c : ∀ a₁ a₂, a₁ ≈ a₂ → f a₁ == f a₂) (x : α) :
  (quotient.mk' x).hrec_on' f c = f x :=
rfl

/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrec_on₂' {φ : quotient s₁ → quotient s₂ → Sort*} (qa : quotient s₁)
  (qb : quotient s₂) (f : ∀ a b, φ (quotient.mk' a) (quotient.mk' b))
  (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) : φ qa qb :=
quotient.hrec_on₂ qa qb f c

@[simp] lemma hrec_on₂'_mk' {φ : quotient s₁ → quotient s₂ → Sort*}
  (f : ∀ a b, φ (quotient.mk' a) (quotient.mk' b))
  (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) (x : α) (qb : quotient s₂) :
  (quotient.mk' x).hrec_on₂' qb f c = qb.hrec_on' (f x) (λ b₁ b₂, c _ _ _ _ (setoid.refl _)) :=
rfl

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map' (f : α → β) (h : ((≈) ⇒ (≈)) f f) :
  quotient s₁ → quotient s₂ :=
quot.map f h

@[simp] lemma map'_mk' (f : α → β) (h) (x : α) :
  (quotient.mk' x : quotient s₁).map' f h = (quotient.mk' (f x) : quotient s₂) :=
rfl

/-- A version of `quotient.map₂` using curly braces and unification. -/
protected def map₂' (f : α → β → γ) (h : ((≈) ⇒ (≈) ⇒ (≈)) f f) :
  quotient s₁ → quotient s₂ → quotient s₃ :=
quotient.map₂ f h

@[simp] lemma map₂'_mk' (f : α → β → γ) (h) (x : α) :
  (quotient.mk' x : quotient s₁).map₂' f h =
    (quotient.map' (f x) (h (setoid.refl x)) : quotient s₂ → quotient s₃) :=
rfl

lemma exact' {a b : α} :
  (quotient.mk' a : quotient s₁) = quotient.mk' b → @setoid.r _ s₁ a b :=
quotient.exact

lemma sound' {a b : α} : @setoid.r _ s₁ a b → @quotient.mk' α s₁ a = quotient.mk' b :=
quotient.sound

@[simp]
protected lemma eq' {a b : α} : @quotient.mk' α s₁ a = quotient.mk' b ↔ @setoid.r _ s₁ a b :=
quotient.eq

/-- A version of `quotient.out` taking `{s₁ : setoid α}` as an implicit argument instead of an
instance argument. -/
noncomputable def out' (a : quotient s₁) : α := quotient.out a

@[simp] theorem out_eq' (q : quotient s₁) : quotient.mk' q.out' = q := q.out_eq

theorem mk_out' (a : α) : @setoid.r α s₁ (quotient.mk' a : quotient s₁).out' a :=
quotient.exact (quotient.out_eq _)

end quotient
