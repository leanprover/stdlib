/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
import data.rel

/-- `roption α` is the type of "partial values" of type `α`. It
  is similar to `option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
structure {u} roption (α : Type u) : Type u :=
(dom : Prop)
(get : dom → α)

namespace roption
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Convert an `roption α` with a decidable domain to an option -/
def to_option (o : roption α) [decidable o.dom] : option α :=
if h : dom o then some (o.get h) else none

/-- `roption` extensionality -/
theorem ext' : ∀ {o p : roption α}
  (H1 : o.dom ↔ p.dom)
  (H2 : ∀h₁ h₂, o.get h₁ = p.get h₂), o = p
| ⟨od, o⟩ ⟨pd, p⟩ H1 H2 := have t : od = pd, from propext H1,
  by cases t; rw [show o = p, from funext $ λp, H2 p p]

/-- `roption` eta expansion -/
@[simp] theorem eta : Π (o : roption α), (⟨o.dom, λ h, o.get h⟩ : roption α) = o
| ⟨h, f⟩ := rfl

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
protected def mem (a : α) (o : roption α) : Prop := ∃ h, o.get h = a

instance : has_mem α (roption α) := ⟨roption.mem⟩

theorem mem_eq (a : α) (o : roption α) : (a ∈ o) = (∃ h, o.get h = a) :=
rfl

theorem dom_iff_mem : ∀ {o : roption α}, o.dom ↔ ∃y, y ∈ o
| ⟨p, f⟩ := ⟨λh, ⟨f h, h, rfl⟩, λ⟨_, h, rfl⟩, h⟩

theorem get_mem {o : roption α} (h) : get o h ∈ o := ⟨_, rfl⟩

/-- `roption` extensionality -/
@[ext]
theorem ext {o p : roption α} (H : ∀ a, a ∈ o ↔ a ∈ p) : o = p :=
ext' ⟨λ h, ((H _).1 ⟨h, rfl⟩).fst,
     λ h, ((H _).2 ⟨h, rfl⟩).fst⟩ $
λ a b, ((H _).2 ⟨_, rfl⟩).snd

/-- The `none` value in `roption` has a `false` domain and an empty function. -/
def none : roption α := ⟨false, false.rec _⟩

instance : inhabited (roption α) := ⟨none⟩

@[simp] theorem not_mem_none (a : α) : a ∉ @none α := λ h, h.fst

/-- The `some a` value in `roption` has a `true` domain and the
  function returns `a`. -/
def some (a : α) : roption α := ⟨true, λ_, a⟩

theorem mem_unique : ∀ {a b : α} {o : roption α}, a ∈ o → b ∈ o → a = b
| _ _ ⟨p, f⟩ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ := rfl

theorem mem.left_unique : relator.left_unique ((∈) : α → roption α → Prop) :=
⟨λ a o b, mem_unique⟩

theorem get_eq_of_mem {o : roption α} {a} (h : a ∈ o) (h') : get o h' = a :=
mem_unique ⟨_, rfl⟩ h

@[simp] theorem get_some {a : α} (ha : (some a).dom) : get (some a) ha = a := rfl

theorem mem_some (a : α) : a ∈ some a := ⟨trivial, rfl⟩

@[simp] theorem mem_some_iff {a b} : b ∈ (some a : roption α) ↔ b = a :=
⟨λ⟨h, e⟩, e.symm, λ e, ⟨trivial, e.symm⟩⟩

theorem eq_some_iff {a : α} {o : roption α} : o = some a ↔ a ∈ o :=
⟨λ e, e.symm ▸ mem_some _,
 λ ⟨h, e⟩, e ▸ ext' (iff_true_intro h) (λ _ _, rfl)⟩

theorem eq_none_iff {o : roption α} : o = none ↔ ∀ a, a ∉ o :=
⟨λ e, e.symm ▸ not_mem_none,
 λ h, ext (by simpa [not_mem_none])⟩

theorem eq_none_iff' {o : roption α} : o = none ↔ ¬ o.dom :=
⟨λ e, e.symm ▸ id, λ h, eq_none_iff.2 (λ a h', h h'.fst)⟩

lemma some_ne_none (x : α) : some x ≠ none :=
by { intro h, change none.dom, rw [← h], trivial }

lemma ne_none_iff {o : roption α} : o ≠ none ↔ ∃x, o = some x :=
begin
  split,
  { rw [ne, eq_none_iff], intro h, push_neg at h, cases h with x hx, use x, rwa [eq_some_iff] },
  { rintro ⟨x, rfl⟩, apply some_ne_none }
end

lemma eq_none_or_eq_some (o : roption α) : o = none ∨ ∃ x, o = some x :=
begin
  classical,
  by_cases h : o.dom,
  { rw dom_iff_mem at h, right,
    apply exists_imp_exists _ h,
    simp [eq_some_iff] },
  { rw eq_none_iff', exact or.inl h },
end

@[simp] lemma some_inj {a b : α} : roption.some a = some b ↔ a = b :=
function.injective.eq_iff (λ a b h, congr_fun (eq_of_heq (roption.mk.inj h).2) trivial)

@[simp] lemma some_get {a : roption α} (ha : a.dom) :
  roption.some (roption.get a ha) = a :=
eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)

lemma get_eq_iff_eq_some {a : roption α} {ha : a.dom} {b : α} :
  a.get ha = b ↔ a = some b :=
⟨λ h, by simp [h.symm], λ h, by simp [h]⟩

lemma get_eq_get_of_eq (a : roption α) (ha : a.dom) {b : roption α} (h : a = b) :
  a.get ha = b.get (h ▸ ha) :=
by { congr, exact h }

instance none_decidable : decidable (@none α).dom := decidable.false
instance some_decidable (a : α) : decidable (some a).dom := decidable.true

def get_or_else (a : roption α) [decidable a.dom] (d : α) :=
if ha : a.dom then a.get ha else d

@[simp] lemma get_or_else_none (d : α) : get_or_else none d = d :=
dif_neg id

@[simp] lemma get_or_else_some (a : α) (d : α) : get_or_else (some a) d = a :=
dif_pos trivial

@[simp] theorem mem_to_option {o : roption α} [decidable o.dom] {a : α} :
  a ∈ to_option o ↔ a ∈ o :=
begin
  unfold to_option,
  by_cases h : o.dom; simp [h],
  { exact ⟨λ h, ⟨_, h⟩, λ ⟨_, h⟩, h⟩ },
  { exact mt Exists.fst h }
end

/-- Convert an `option α` into an `roption α` -/
def of_option : option α → roption α
| option.none     := none
| (option.some a) := some a

@[simp] theorem mem_of_option {a : α} : ∀ {o : option α}, a ∈ of_option o ↔ a ∈ o
| option.none     := ⟨λ h, h.fst.elim, λ h, option.no_confusion h⟩
| (option.some b) := ⟨λ h, congr_arg option.some h.snd,
  λ h, ⟨trivial, option.some.inj h⟩⟩

@[simp] theorem of_option_dom {α} : ∀ (o : option α), (of_option o).dom ↔ o.is_some
| option.none     := by simp [of_option, none]
| (option.some a) := by simp [of_option]

theorem of_option_eq_get {α} (o : option α) : of_option o = ⟨_, @option.get _ o⟩ :=
roption.ext' (of_option_dom o) $ λ h₁ h₂, by cases o; [cases h₁, refl]

instance : has_coe (option α) (roption α) := ⟨of_option⟩

@[simp] theorem mem_coe {a : α} {o : option α} :
  a ∈ (o : roption α) ↔ a ∈ o := mem_of_option

@[simp] theorem coe_none : (@option.none α : roption α) = none := rfl
@[simp] theorem coe_some (a : α) : (option.some a : roption α) = some a := rfl

@[elab_as_eliminator] protected lemma induction_on {P : roption α → Prop}
  (a : roption α) (hnone : P none) (hsome : ∀ a : α, P (some a)) : P a :=
(classical.em a.dom).elim
  (λ h, roption.some_get h ▸ hsome _)
  (λ h, (eq_none_iff'.2 h).symm ▸ hnone)

instance of_option_decidable : ∀ o : option α, decidable (of_option o).dom
| option.none     := roption.none_decidable
| (option.some a) := roption.some_decidable a

@[simp] theorem to_of_option (o : option α) : to_option (of_option o) = o :=
by cases o; refl

@[simp] theorem of_to_option (o : roption α) [decidable o.dom] : of_option (to_option o) = o :=
ext $ λ a, mem_of_option.trans mem_to_option

noncomputable def equiv_option : roption α ≃ option α :=
by haveI := classical.dec; exact
⟨λ o, to_option o, of_option, λ o, of_to_option o,
 λ o, eq.trans (by dsimp; congr) (to_of_option o)⟩

instance : order_bot (roption α) :=
{ le := λ x y, ∀ i, i ∈ x → i ∈ y,
  le_refl := λ x y, id,
  le_trans := λ x y z f g i, g _ ∘ f _,
  le_antisymm := λ x y f g, roption.ext $ λ z, ⟨f _, g _⟩,
  bot := none,
  bot_le := by { introv x, rintro ⟨⟨_⟩,_⟩, } }

instance : preorder (roption α) :=
by apply_instance

lemma le_total_of_le_of_le {x y : roption α} (z : roption α) (hx : x ≤ z) (hy : y ≤ z) :
  x ≤ y ∨ y ≤ x :=
begin
  rcases roption.eq_none_or_eq_some x with h | ⟨b, h₀⟩,
  { rw h, left, apply order_bot.bot_le _ },
  right, intros b' h₁,
  rw roption.eq_some_iff at h₀,
  replace hx := hx _ h₀, replace hy := hy _ h₁,
  replace hx := roption.mem_unique hx hy, subst hx,
  exact h₀
end

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
def assert (p : Prop) (f : p → roption α) : roption α :=
⟨∃h : p, (f h).dom, λha, (f ha.fst).get ha.snd⟩

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
protected def bind (f : roption α) (g : α → roption β) : roption β :=
assert (dom f) (λb, g (f.get b))

/-- The map operation for `roption` just maps the value and maintains the same domain. -/
def map (f : α → β) (o : roption α) : roption β :=
⟨o.dom, f ∘ o.get⟩

theorem mem_map (f : α → β) {o : roption α} :
  ∀ {a}, a ∈ o → f a ∈ map f o
| _ ⟨h, rfl⟩ := ⟨_, rfl⟩

@[simp] theorem mem_map_iff (f : α → β) {o : roption α} {b} :
  b ∈ map f o ↔ ∃ a ∈ o, f a = b :=
⟨match b with _, ⟨h, rfl⟩ := ⟨_, ⟨_, rfl⟩, rfl⟩ end,
 λ ⟨a, h₁, h₂⟩, h₂ ▸ mem_map f h₁⟩

@[simp] theorem map_none (f : α → β) :
  map f none = none := eq_none_iff.2 $ λ a, by simp

@[simp] theorem map_some (f : α → β) (a : α) : map f (some a) = some (f a) :=
eq_some_iff.2 $ mem_map f $ mem_some _

theorem mem_assert {p : Prop} {f : p → roption α}
  : ∀ {a} (h : p), a ∈ f h → a ∈ assert p f
| _ x ⟨h, rfl⟩ := ⟨⟨x, h⟩, rfl⟩

@[simp] theorem mem_assert_iff {p : Prop} {f : p → roption α} {a} :
  a ∈ assert p f ↔ ∃ h : p, a ∈ f h :=
⟨match a with _, ⟨h, rfl⟩ := ⟨_, ⟨_, rfl⟩⟩ end,
 λ ⟨a, h⟩, mem_assert _ h⟩

lemma assert_pos {p : Prop} {f : p → roption α} (h : p) :
  assert p f = f h :=
begin
  dsimp [assert],
  cases h' : f h,
  simp only [h', h, true_and, iff_self, exists_prop_of_true, eq_iff_iff],
  apply function.hfunext,
  { simp only [h,h',exists_prop_of_true] },
  { cc }
end

lemma assert_neg {p : Prop} {f : p → roption α} (h : ¬ p) :
  assert p f = none :=
begin
  dsimp [assert,none], congr,
  { simp only [h, not_false_iff, exists_prop_of_false] },
  { apply function.hfunext,
    { simp only [h, not_false_iff, exists_prop_of_false] },
    cc },
end

theorem mem_bind {f : roption α} {g : α → roption β} :
  ∀ {a b}, a ∈ f → b ∈ g a → b ∈ f.bind g
| _ _ ⟨h, rfl⟩ ⟨h₂, rfl⟩ := ⟨⟨h, h₂⟩, rfl⟩

@[simp] theorem mem_bind_iff {f : roption α} {g : α → roption β} {b} :
  b ∈ f.bind g ↔ ∃ a ∈ f, b ∈ g a :=
⟨match b with _, ⟨⟨h₁, h₂⟩, rfl⟩ := ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ end,
 λ ⟨a, h₁, h₂⟩, mem_bind h₁ h₂⟩

@[simp] theorem bind_none (f : α → roption β) :
  none.bind f = none := eq_none_iff.2 $ λ a, by simp

@[simp] theorem bind_some (a : α) (f : α → roption β) :
  (some a).bind f = f a := ext $ by simp

theorem bind_some_eq_map (f : α → β) (x : roption α) :
  x.bind (some ∘ f) = map f x :=
ext $ by simp [eq_comm]

theorem bind_assoc {γ} (f : roption α) (g : α → roption β) (k : β → roption γ) :
  (f.bind g).bind k = f.bind (λ x, (g x).bind k) :=
ext $ λ a, by simp; exact
 ⟨λ ⟨_, ⟨_, h₁, h₂⟩, h₃⟩, ⟨_, h₁, _, h₂, h₃⟩,
  λ ⟨_, h₁, _, h₂, h₃⟩, ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp] theorem bind_map {γ} (f : α → β) (x) (g : β → roption γ) :
  (map f x).bind g = x.bind (λ y, g (f y)) :=
by rw [← bind_some_eq_map, bind_assoc]; simp

@[simp] theorem map_bind {γ} (f : α → roption β) (x : roption α) (g : β → γ) :
  map g (x.bind f) = x.bind (λ y, map g (f y)) :=
by rw [← bind_some_eq_map, bind_assoc]; simp [bind_some_eq_map]

theorem map_map (g : β → γ) (f : α → β) (o : roption α) :
  map g (map f o) = map (g ∘ f) o :=
by rw [← bind_some_eq_map, bind_map, bind_some_eq_map]

instance : monad roption :=
{ pure := @some,
  map := @map,
  bind := @roption.bind }

instance : is_lawful_monad roption :=
{ bind_pure_comp_eq_map := @bind_some_eq_map,
  id_map := λ β f, by cases f; refl,
  pure_bind := @bind_some,
  bind_assoc := @bind_assoc }

theorem map_id' {f : α → α} (H : ∀ (x : α), f x = x) (o) : map f o = o :=
by rw [show f = id, from funext H]; exact id_map o

@[simp] theorem bind_some_right (x : roption α) : x.bind some = x :=
by rw [bind_some_eq_map]; simp [map_id']

@[simp] theorem pure_eq_some (a : α) : pure a = some a := rfl
@[simp] theorem ret_eq_some (a : α) : return a = some a := rfl

@[simp] theorem map_eq_map {α β} (f : α → β) (o : roption α) :
  f <$> o = map f o := rfl

@[simp] theorem bind_eq_bind {α β} (f : roption α) (g : α → roption β) :
  f >>= g = f.bind g := rfl

lemma bind_le {α} (x : roption α) (f : α → roption β) (y : roption β) :
  x >>= f ≤ y ↔ (∀ a, a ∈ x → f a ≤ y) :=
begin
  split; intro h,
  { intros a h' b, replace h := h b,
    simp only [and_imp, exists_prop, bind_eq_bind, mem_bind_iff, exists_imp_distrib] at h,
    apply h _ h' },
  { intros b h',
    simp only [exists_prop, bind_eq_bind, mem_bind_iff] at h',
    rcases h' with ⟨a,h₀,h₁⟩, apply h _ h₀ _ h₁ },
end

instance : monad_fail roption :=
{ fail := λ_ _, none, ..roption.monad }

/- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/
def restrict (p : Prop) : ∀ (o : roption α), (p → o.dom) → roption α
| ⟨d, f⟩ H := ⟨p, λh, f (H h)⟩

@[simp]
theorem mem_restrict (p : Prop) (o : roption α) (h : p → o.dom) (a : α) :
  a ∈ restrict p o h ↔ p ∧ a ∈ o :=
begin
  cases o, dsimp [restrict, mem_eq], split,
  { rintro ⟨h₀, h₁⟩, exact ⟨h₀, ⟨_, h₁⟩⟩ },
  rintro ⟨h₀, h₁, h₂⟩, exact ⟨h₀, h₂⟩
end

/-- `unwrap o` gets the value at `o`, ignoring the condition.
  (This function is unsound.) -/
meta def unwrap (o : roption α) : α := o.get undefined

theorem assert_defined {p : Prop} {f : p → roption α} :
  ∀ (h : p), (f h).dom → (assert p f).dom := exists.intro

theorem bind_defined {f : roption α} {g : α → roption β} :
  ∀ (h : f.dom), (g (f.get h)).dom → (f.bind g).dom := assert_defined

@[simp] theorem bind_dom {f : roption α} {g : α → roption β} :
  (f.bind g).dom ↔ ∃ h : f.dom, (g (f.get h)).dom := iff.rfl

end roption

/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → roption β`. -/
def pfun (α : Type*) (β : Type*) := α → roption β

infixr ` →. `:25 := pfun

namespace pfun
variables {α : Type*} {β : Type*} {γ : Type*}

instance : inhabited (α →. β) := ⟨λ a, roption.none⟩

/-- The domain of a partial function -/
def dom (f : α →. β) : set α := {a | (f a).dom}

theorem mem_dom (f : α →. β) (x : α) : x ∈ dom f ↔ ∃ y, y ∈ f x :=
by simp [dom, roption.dom_iff_mem]

theorem dom_eq (f : α →. β) : dom f = {x | ∃ y, y ∈ f x} :=
set.ext (mem_dom f)

/-- Evaluate a partial function -/
def fn (f : α →. β) (x) (h : dom f x) : β := (f x).get h

/-- Evaluate a partial function to return an `option` -/
def eval_opt (f : α →. β) [D : decidable_pred (∈ dom f)] (x : α) : option β :=
@roption.to_option _ _ (D x)

/-- Partial function extensionality -/
theorem ext' {f g : α →. β}
  (H1 : ∀ a, a ∈ dom f ↔ a ∈ dom g)
  (H2 : ∀ a p q, f.fn a p = g.fn a q) : f = g :=
funext $ λ a, roption.ext' (H1 a) (H2 a)

theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
funext $ λ a, roption.ext (H a)

/-- Turn a partial function into a function out of a subtype -/
def as_subtype (f : α →. β) (s : f.dom) : β := f.fn s s.2

/-- The set of partial functions `α →. β` is equivalent to
the set of pairs `(p : α → Prop, f : subtype p → β)`. -/
def equiv_subtype : (α →. β) ≃ (Σ p : α → Prop, subtype p → β) :=
⟨λ f, ⟨λ a, (f a).dom, as_subtype f⟩,
 λ f x, ⟨f.1 x, λ h, f.2 ⟨x, h⟩⟩,
 λ f, funext $ λ a, roption.eta _,
 λ ⟨p, f⟩, by dsimp; congr; funext a; cases a; refl⟩

theorem as_subtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.dom) :
  f.as_subtype ⟨x, domx⟩ = y :=
roption.mem_unique (roption.get_mem _) fxy

/-- Turn a total function into a partial function -/
protected def lift (f : α → β) : α →. β := λ a, roption.some (f a)

instance : has_coe (α → β) (α →. β) := ⟨pfun.lift⟩

@[simp] theorem lift_eq_coe (f : α → β) : pfun.lift f = f := rfl

@[simp] theorem coe_val (f : α → β) (a : α) :
  (f : α →. β) a = roption.some (f a) := rfl

/-- The graph of a partial function is the set of pairs
  `(x, f x)` where `x` is in the domain of `f`. -/
def graph (f : α →. β) : set (α × β) := {p | p.2 ∈ f p.1}

def graph' (f : α →. β) : rel α β := λ x y, y ∈ f x

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def ran (f : α →. β) : set β := {b | ∃a, b ∈ f a}

/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : set α} (H : p ⊆ f.dom) : α →. β :=
λ x, roption.restrict (x ∈ p) (f x) (@H x)

@[simp]
theorem mem_restrict {f : α →. β} {s : set α} (h : s ⊆ f.dom) (a : α) (b : β) :
  b ∈ restrict f h a ↔ a ∈ s ∧ b ∈ f a :=
by simp [restrict]

def res (f : α → β) (s : set α) : α →. β :=
restrict (pfun.lift f) (set.subset_univ s)

theorem mem_res (f : α → β) (s : set α) (a : α) (b : β) :
  b ∈ res f s a ↔ (a ∈ s ∧ f a = b) :=
by simp [res, @eq_comm _ b]

theorem res_univ (f : α → β) : pfun.res f set.univ = f :=
rfl

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.dom ↔ ∃y, (x, y) ∈ f.graph :=
roption.dom_iff_mem

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
show (∃ (h : true), f a = b) ↔ f a = b, by simp

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := λ_, roption.some x

/-- The monad `bind` function, pointwise `roption.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ :=
λa, roption.bind (f a) (λb, g b a)

/-- The monad `map` function, pointwise `roption.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ :=
λa, roption.map f (g a)

instance : monad (pfun α) :=
{ pure := @pfun.pure _,
  bind := @pfun.bind _,
  map := @pfun.map _ }

instance : is_lawful_monad (pfun α) :=
{ bind_pure_comp_eq_map := λ β γ f x, funext $ λ a, roption.bind_some_eq_map _ _,
  id_map := λ β f, by funext a; dsimp [functor.map, pfun.map]; cases f a; refl,
  pure_bind := λ β γ x f, funext $ λ a, roption.bind_some.{u_1 u_2} _ (f x),
  bind_assoc := λ β γ δ f g k,
    funext $ λ a, roption.bind_assoc (f a) (λ b, g b a) (λ b, k b a) }

theorem pure_defined (p : set α) (x : β) : p ⊆ (@pfun.pure α _ x).dom := set.subset_univ p

theorem bind_defined {α β γ} (p : set α) {f : α →. β} {g : β → α →. γ}
  (H1 : p ⊆ f.dom) (H2 : ∀x, p ⊆ (g x).dom) : p ⊆ (f >>= g).dom :=
λa ha, (⟨H1 ha, H2 _ ha⟩ : (f >>= g).dom a)

def fix (f : α →. β ⊕ α) : α →. β := λ a,
roption.assert (acc (λ x y, sum.inr x ∈ f y) a) $ λ h,
@well_founded.fix_F _ (λ x y, sum.inr x ∈ f y) _
  (λ a IH, roption.assert (f a).dom $ λ hf,
    by cases e : (f a).get hf with b a';
      [exact roption.some b, exact IH _ ⟨hf, e⟩])
  a h

theorem dom_of_mem_fix {f : α →. β ⊕ α} {a : α} {b : β}
  (h : b ∈ fix f a) : (f a).dom :=
let ⟨h₁, h₂⟩ := roption.mem_assert_iff.1 h in
by rw well_founded.fix_F_eq at h₂; exact h₂.fst.fst

theorem mem_fix_iff {f : α →. β ⊕ α} {a : α} {b : β} :
  b ∈ fix f a ↔ sum.inl b ∈ f a ∨ ∃ a', sum.inr a' ∈ f a ∧ b ∈ fix f a' :=
⟨λ h, let ⟨h₁, h₂⟩ := roption.mem_assert_iff.1 h in
  begin
    rw well_founded.fix_F_eq at h₂,
    simp at h₂,
    cases h₂ with h₂ h₃,
    cases e : (f a).get h₂ with b' a'; simp [e] at h₃,
    { subst b', refine or.inl ⟨h₂, e⟩ },
    { exact or.inr ⟨a', ⟨_, e⟩, roption.mem_assert _ h₃⟩ }
  end,
λ h, begin
  simp [fix],
  rcases h with ⟨h₁, h₂⟩ | ⟨a', h, h₃⟩,
  { refine ⟨⟨_, λ y h', _⟩, _⟩,
    { injection roption.mem_unique ⟨h₁, h₂⟩ h' },
    { rw well_founded.fix_F_eq, simp [h₁, h₂] } },
  { simp [fix] at h₃, cases h₃ with h₃ h₄,
    refine ⟨⟨_, λ y h', _⟩, _⟩,
    { injection roption.mem_unique h h' with e,
      exact e ▸ h₃ },
    { cases h with h₁ h₂,
      rw well_founded.fix_F_eq, simp [h₁, h₂, h₄] } }
end⟩

@[elab_as_eliminator] def fix_induction
  {f : α →. β ⊕ α} {b : β} {C : α → Sort*} {a : α} (h : b ∈ fix f a)
  (H : ∀ a, b ∈ fix f a →
    (∀ a', b ∈ fix f a' → sum.inr a' ∈ f a → C a') → C a) : C a :=
begin
  replace h := roption.mem_assert_iff.1 h,
  have := h.snd, revert this,
  induction h.fst with a ha IH, intro h₂,
  refine H a (roption.mem_assert_iff.2 ⟨⟨_, ha⟩, h₂⟩)
    (λ a' ha' fa', _),
  have := (roption.mem_assert_iff.1 ha').snd,
  exact IH _ fa' ⟨ha _ fa', this⟩ this
end

end pfun

namespace pfun

variables {α : Type*} {β : Type*} (f : α →. β)

def image (s : set α) : set β := rel.image f.graph' s

lemma image_def (s : set α) : image f s = {y | ∃ x ∈ s, y ∈ f x} := rfl

lemma mem_image (y : β) (s : set α) : y ∈ image f s ↔ ∃ x ∈ s, y ∈ f x :=
iff.rfl

lemma image_mono {s t : set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
rel.image_mono _ h

lemma image_inter (s t : set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
rel.image_inter _ s t

lemma image_union (s t : set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
rel.image_union _ s t

def preimage (s : set β) : set α := rel.preimage (λ x y, y ∈ f x) s

lemma preimage_def (s : set β) : preimage f s = {x | ∃ y ∈ s, y ∈ f x} := rfl

lemma mem_preimage (s : set β) (x : α) : x ∈ preimage f s ↔ ∃ y ∈ s, y ∈ f x :=
iff.rfl

lemma preimage_subset_dom (s : set β) : f.preimage s ⊆ f.dom :=
assume x ⟨y, ys, fxy⟩, roption.dom_iff_mem.mpr ⟨y, fxy⟩

lemma preimage_mono {s t : set β} (h : s ⊆ t) : f.preimage s ⊆ f.preimage t :=
rel.preimage_mono _ h

lemma preimage_inter (s t : set β) : f.preimage (s ∩ t) ⊆ f.preimage s ∩ f.preimage t :=
rel.preimage_inter _ s t

lemma preimage_union (s t : set β) : f.preimage (s ∪ t) = f.preimage s ∪ f.preimage t :=
rel.preimage_union _ s t

lemma preimage_univ : f.preimage set.univ = f.dom :=
by ext; simp [mem_preimage, mem_dom]

def core (s : set β) : set α := rel.core f.graph' s

lemma core_def (s : set β) : core f s = {x | ∀ y, y ∈ f x → y ∈ s} := rfl

lemma mem_core (x : α) (s : set β) : x ∈ core f s ↔ (∀ y, y ∈ f x → y ∈ s) :=
iff.rfl

lemma compl_dom_subset_core (s : set β) : f.domᶜ ⊆ f.core s :=
assume x hx y fxy,
absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx

lemma core_mono {s t : set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
rel.core_mono _ h

lemma core_inter (s t : set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
rel.core_inter _ s t

lemma mem_core_res (f : α → β) (s : set α) (t : set β) (x : α) :
  x ∈ core (res f s) t ↔ (x ∈ s → f x ∈ t) :=
by simp [mem_core, mem_res]

section
open_locale classical

lemma core_res (f : α → β) (s : set α) (t : set β) : core (res f s) t = sᶜ ∪ f ⁻¹' t :=
by { ext, rw mem_core_res, by_cases h : x ∈ s; simp [h] }

end

lemma core_restrict (f : α → β) (s : set β) : core (f : α →. β) s = set.preimage f s :=
by ext x; simp [core_def]

lemma preimage_subset_core (f : α →. β) (s : set β) : f.preimage s ⊆ f.core s :=
assume x ⟨y, ys, fxy⟩ y' fxy',
have y = y', from roption.mem_unique fxy fxy',
this ▸ ys

lemma preimage_eq (f : α →. β) (s : set β) : f.preimage s = f.core s ∩ f.dom :=
set.eq_of_subset_of_subset
  (set.subset_inter (preimage_subset_core f s) (preimage_subset_dom f s))
  (assume x ⟨xcore, xdom⟩,
    let y := (f x).get xdom in
    have ys : y ∈ s, from xcore _ (roption.get_mem _),
    show x ∈ preimage f s, from  ⟨(f x).get xdom, ys, roption.get_mem _⟩)

lemma core_eq (f : α →. β) (s : set β) : f.core s = f.preimage s ∪ f.domᶜ :=
by rw [preimage_eq, set.union_distrib_right, set.union_comm (dom f), set.compl_union_self,
        set.inter_univ, set.union_eq_self_of_subset_right (compl_dom_subset_core f s)]

lemma preimage_as_subtype (f : α →. β) (s : set β) :
  f.as_subtype ⁻¹' s = subtype.val ⁻¹' pfun.preimage f s :=
begin
  ext x,
  simp only [set.mem_preimage, set.mem_set_of_eq, pfun.as_subtype, pfun.mem_preimage],
  show pfun.fn f (x.val) _ ∈ s ↔ ∃ y ∈ s, y ∈ f (x.val),
  exact iff.intro
    (assume h, ⟨_, h, roption.get_mem _⟩)
    (assume ⟨y, ys, fxy⟩,
      have f.fn x.val x.property ∈ f x.val := roption.get_mem _,
      roption.mem_unique fxy this ▸ ys)
end

end pfun
