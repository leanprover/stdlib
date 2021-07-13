/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.basic
import logic.is_empty

/-!
# Option of a type

This file develops the basic theory of option types.

If `α` is a type, then `option α` can be understood as the type with one more element than `α`.
`option α` has terms `some a`, where `a : α`, and `none`, which is the added element.
This is useful in multiple ways:
* It is the prototype of addition of terms to a type. See for example `with_bot α` which uses
  `none` as an element smaller than all others.
* It can be used to define failsafe partial functions, which return `some the_result_we_expect`
  if we can find `the_result_we_expect`, and `none` if there is no meaningful result. This forces
  any subsequent use of the partial function to explicitly deal with the exceptions that make it
  return `none`.
* `option` is a monad. We love monads.

`roption` is an alternative to `option` that can be seen as the type of `true`/`false` values
along with a term `a : α` if the value is `true`.

## Implementation notes

`option` is currently defined in core Lean, but this will change in Lean 4.
-/

namespace option
variables {α : Type*} {β : Type*} {γ : Type*}

lemma coe_def : (coe : α → option α) = some := rfl

lemma some_ne_none (x : α) : some x ≠ none := λ h, option.no_confusion h

protected lemma «forall» {p : option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
⟨λ h, ⟨h _, λ x, h _⟩, λ h x, option.cases_on x h.1 h.2⟩

protected lemma «exists» {p : option α → Prop} : (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
⟨λ ⟨x, hx⟩, (option.cases_on x or.inl $ λ x hx, or.inr ⟨x, hx⟩) hx,
  λ h, h.elim (λ h, ⟨_, h⟩) (λ ⟨x, hx⟩, ⟨_, hx⟩)⟩

@[simp] theorem get_mem : ∀ {o : option α} (h : is_some o), option.get h ∈ o
| (some a) _ := rfl

theorem get_of_mem {a : α} : ∀ {o : option α} (h : is_some o), a ∈ o → option.get h = a
| _ _ rfl := rfl

@[simp] lemma not_mem_none (a : α) : a ∉ (none : option α) :=
λ h, option.no_confusion h

@[simp] lemma some_get : ∀ {x : option α} (h : is_some x), some (option.get h) = x
| (some x) hx := rfl

@[simp] lemma get_some (x : α) (h : is_some (some x)) : option.get h = x := rfl

@[simp] lemma get_or_else_some (x y : α) : option.get_or_else (some x) y = x := rfl

@[simp] lemma get_or_else_none (x : α) : option.get_or_else none x = x := rfl

@[simp] lemma get_or_else_coe (x y : α) : option.get_or_else ↑x y = x := rfl

lemma get_or_else_of_ne_none {x : option α} (hx : x ≠ none) (y : α) : some (x.get_or_else y) = x :=
by cases x; [contradiction, rw get_or_else_some]

theorem mem_unique {o : option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
option.some.inj $ ha.symm.trans hb

theorem mem.left_unique : relator.left_unique ((∈) : α → option α → Prop) :=
⟨λ a o b, mem_unique⟩

theorem some_injective (α : Type*) : function.injective (@some α) :=
λ _ _, some_inj.mp

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : function.injective f) : function.injective (option.map f)
| none      none      H := rfl
| (some a₁) (some a₂) H := by rw Hf (option.some.inj H)

@[ext] theorem ext : ∀ {o₁ o₂ : option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
| none     none     H := rfl
| (some a) o        H := ((H _).1 rfl).symm
| o        (some b) H := (H _).2 rfl

theorem eq_none_iff_forall_not_mem {o : option α} :
  o = none ↔ (∀ a, a ∉ o) :=
⟨λ e a h, by rw e at h; cases h, λ h, ext $ by simpa⟩

@[simp] theorem none_bind {α β} (f : α → option β) : none >>= f = none := rfl

@[simp] theorem some_bind {α β} (a : α) (f : α → option β) : some a >>= f = f a := rfl

@[simp] theorem none_bind' (f : α → option β) : none.bind f = none := rfl

@[simp] theorem some_bind' (a : α) (f : α → option β) : (some a).bind f = f a := rfl

@[simp] theorem bind_some : ∀ x : option α, x >>= some = x :=
@bind_pure α option _ _

@[simp] theorem bind_eq_some {α β} {x : option α} {f : α → option β} {b : β} :
  x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] theorem bind_eq_some' {x : option α} {f : α → option β} {b : β} :
  x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] theorem bind_eq_none' {o : option α} {f : α → option β} :
  o.bind f = none ↔ (∀ b a, a ∈ o → b ∉ f a) :=
by simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some']

@[simp] theorem bind_eq_none {α β} {o : option α} {f : α → option β} :
  o >>= f = none ↔ (∀ b a, a ∈ o → b ∉ f a) :=
bind_eq_none'

lemma bind_comm {α β γ} {f : α → β → option γ} (a : option α) (b : option β) :
  a.bind (λx, b.bind (f x)) = b.bind (λy, a.bind (λx, f x y)) :=
by cases a; cases b; refl

lemma bind_assoc (x : option α) (f : α → option β) (g : β → option γ) :
  (x.bind f).bind g = x.bind (λ y, (f y).bind g) := by cases x; refl

lemma join_eq_some {x : option (option α)} {a : α} : x.join = some a ↔ x = some (some a) := by simp

lemma join_ne_none {x : option (option α)} : x.join ≠ none ↔ ∃ z, x = some (some z) := by simp

lemma join_ne_none' {x : option (option α)} : ¬(x.join = none) ↔ ∃ z, x = some (some z) := by simp

lemma join_eq_none {o : option (option α)} : o.join = none ↔ o = none ∨ o = some none :=
by rcases o with _|_|_; simp

lemma bind_id_eq_join {x : option (option α)} : x >>= id = x.join := by simp

lemma join_eq_join : mjoin = @join α :=
funext (λ x, by rw [mjoin, bind_id_eq_join])

lemma bind_eq_bind {α β : Type*} {f : α → option β} {x : option α} :
  x >>= f = x.bind f := rfl

@[simp] lemma map_eq_map {α β} {f : α → β} :
  (<$>) f = option.map f := rfl

theorem map_none {α β} {f : α → β} : f <$> none = none := rfl

theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) := rfl

@[simp] theorem map_none' {f : α → β} : option.map f none = none := rfl

@[simp] theorem map_some' {a : α} {f : α → β} : option.map f (some a) = some (f a) := rfl

theorem map_eq_some {α β} {x : option α} {f : α → β} {b : β} :
  f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

@[simp] theorem map_eq_some' {x : option α} {f : α → β} {b : β} :
  x.map f = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

lemma map_eq_none {α β} {x : option α} {f : α → β} :
  f <$> x = none ↔ x = none :=
by { cases x; simp only [map_none, map_some, eq_self_iff_true] }

@[simp] lemma map_eq_none' {x : option α} {f : α → β} :
  x.map f = none ↔ x = none :=
by { cases x; simp only [map_none', map_some', eq_self_iff_true] }

lemma map_congr {f g : α → β} {x : option α} (h : ∀ a ∈ x, f a = g a) :
  option.map f x = option.map g x :=
by { cases x; simp only [map_none', map_some', h, mem_def] }

@[simp] theorem map_id' : option.map (@id α) = id := map_id

@[simp] lemma map_map (h : β → γ) (g : α → β) (x : option α) :
  option.map h (option.map g x) = option.map (h ∘ g) x :=
by { cases x; simp only [map_none', map_some'] }

lemma comp_map (h : β → γ) (g : α → β) (x : option α) :
  option.map (h ∘ g) x = option.map h (option.map g x) := (map_map _ _ _).symm

@[simp] lemma map_comp_map (f : α → β) (g : β → γ) :
  option.map g ∘ option.map f = option.map (g ∘ f) :=
by { ext x, rw comp_map }

lemma mem_map_of_mem {α β : Type*} {a : α} {x : option α} (g : α → β) (h : a ∈ x) : g a ∈ x.map g :=
mem_def.mpr ((mem_def.mp h).symm ▸ map_some')

lemma bind_map_comm {α β} {x : option (option α) } {f : α → β} :
  x >>= option.map f = x.map (option.map f) >>= id :=
by { cases x; simp }

lemma join_map_eq_map_join {f : α → β} {x : option (option α)} :
  (x.map (option.map f)).join = x.join.map f :=
by { rcases x with _ | _ | x; simp }

lemma join_join {x : option (option (option α))} :
  x.join.join = (x.map join).join :=
by { rcases x with _ | _ | _ | x; simp }

lemma mem_of_mem_join {a : α} {x : option (option α)} (h : a ∈ x.join) : some a ∈ x :=
mem_def.mpr ((mem_def.mp h).symm ▸ join_eq_some.mp h)

section pmap

variables {p : α → Prop} (f : Π (a : α), p a → β) (x : option α)

@[simp] lemma pbind_eq_bind (f : α → option β) (x : option α) :
  x.pbind (λ a _, f a) = x.bind f :=
by { cases x; simp only [pbind, none_bind', some_bind'] }

lemma map_bind {α β γ} (f : β → γ) (x : option α) (g : α → option β) :
  option.map f (x >>= g) = (x >>= λ a, option.map f (g a)) :=
by simp_rw [←map_eq_map, ←bind_pure_comp_eq_map,is_lawful_monad.bind_assoc]

lemma map_bind' (f : β → γ) (x : option α) (g : α → option β) :
  option.map f (x.bind g) = x.bind (λ a, option.map f (g a)) :=
by { cases x; simp }

lemma map_pbind (f : β → γ) (x : option α) (g : Π a, a ∈ x → option β) :
  option.map f (x.pbind g) = (x.pbind (λ a H, option.map f (g a H))) :=
by { cases x; simp only [pbind, map_none'] }

lemma pbind_map (f : α → β) (x : option α) (g : Π (b : β), b ∈ x.map f → option γ) :
  pbind (option.map f x) g = x.pbind (λ a h, g (f a) (mem_map_of_mem _ h)) :=
by { cases x; refl }

@[simp] lemma pmap_none (f : Π (a : α), p a → β) {H} : pmap f (@none α) H = none := rfl

@[simp] lemma pmap_some (f : Π (a : α), p a → β) {x : α} (h : p x) :
  pmap f (some x) = λ _, some (f x h) := rfl

lemma mem_pmem {a : α} (h : ∀ a ∈ x, p a) (ha : a ∈ x) :
  f a (h a ha) ∈ pmap f x h :=
by { rw mem_def at ha ⊢, subst ha, refl }

lemma pmap_map (g : γ → α) (x : option γ) (H) :
  pmap f (x.map g) H = pmap (λ a h, f (g a) h) x (λ a h, H _ (mem_map_of_mem _ h)) :=
by { cases x; simp only [map_none', map_some', pmap] }

lemma map_pmap (g : β → γ) (f : Π a, p a → β) (x H) :
  option.map g (pmap f x H) = pmap (λ a h, g (f a h)) x H :=
by { cases x; simp only [map_none', map_some', pmap] }

@[simp] lemma pmap_eq_map (p : α → Prop) (f : α → β) (x H) :
  @pmap _ _ p (λ a _, f a) x H = option.map f x :=
by { cases x; simp only [map_none', map_some', pmap] }

lemma pmap_bind {α β γ} {x : option α} {g : α → option β} {p : β → Prop} {f : Π b, p b → γ}
  (H) (H' : ∀ (a : α) b ∈ g a, b ∈ x >>= g) :
  pmap f (x >>= g) H = (x >>= λa, pmap f (g a) (λ b h, H _ (H' a _ h))) :=
by { cases x; simp only [pmap, none_bind, some_bind] }

lemma bind_pmap {α β γ} {p : α → Prop} (f : Π a, p a → β) (x : option α) (g : β → option γ) (H) :
  (pmap f x H) >>= g = x.pbind (λ a h, g (f a (H _ h))) :=
by { cases x; simp only [pmap, none_bind, some_bind, pbind] }

variables {f x}

lemma pbind_eq_none {f : Π (a : α), a ∈ x → option β}
  (h' : ∀ a ∈ x, f a H = none → x = none) :
  x.pbind f = none ↔ x = none :=
begin
  cases x,
  { simp },
  { simp only [pbind, iff_false],
    intro h,
    cases h' x rfl h }
end

lemma pbind_eq_some {f : Π (a : α), a ∈ x → option β} {y : β} :
  x.pbind f = some y ↔ ∃ (z ∈ x), f z H = some y :=
begin
  cases x,
  { simp },
  { simp only [pbind],
    split,
    { intro h,
      use x,
      simpa only [mem_def, exists_prop_of_true] using h },
    { rintro ⟨z, H, hz⟩,
      simp only [mem_def] at H,
      simpa only [H] using hz } }
end

@[simp] lemma pmap_eq_none_iff {h} :
  pmap f x h = none ↔ x = none :=
by { cases x; simp }

@[simp] lemma pmap_eq_some_iff {hf} {y : β} :
  pmap f x hf = some y ↔ ∃ (a : α) (H : x = some a), f a (hf a H) = y :=
begin
  cases x,
  { simp only [not_mem_none, exists_false, pmap, not_false_iff, exists_prop_of_false] },
  { split,
    { intro h,
      simp only [pmap] at h,
      exact ⟨x, rfl, h⟩ },
    { rintro ⟨a, H, rfl⟩,
      simp only [mem_def] at H,
      simp only [H, pmap] } }
end

@[simp] lemma join_pmap_eq_pmap_join {f : Π a, p a → β} {x : option (option α)} (H) :
  (pmap (pmap f) x H).join = pmap f x.join (λ a h, H (some a) (mem_of_mem_join h) _ rfl) :=
by { rcases x with _ | _ | x; simp }

end pmap

@[simp] theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) := rfl

@[simp] theorem some_orelse' (a : α) (x : option α) : (some a).orelse x = some a := rfl

@[simp] theorem some_orelse (a : α) (x : option α) : (some a <|> x) = some a := rfl

@[simp] theorem none_orelse' (x : option α) : none.orelse x = x :=
by cases x; refl

@[simp] theorem none_orelse (x : option α) : (none <|> x) = x := none_orelse' x

@[simp] theorem orelse_none' (x : option α) : x.orelse none = x :=
by cases x; refl

@[simp] theorem orelse_none (x : option α) : (x <|> none) = x := orelse_none' x

@[simp] theorem is_some_none : @is_some α none = ff := rfl

@[simp] theorem is_some_some {a : α} : is_some (some a) = tt := rfl

theorem is_some_iff_exists {x : option α} : is_some x ↔ ∃ a, x = some a :=
by cases x; simp [is_some]; exact ⟨_, rfl⟩

@[simp] theorem is_none_none : @is_none α none = tt := rfl

@[simp] theorem is_none_some {a : α} : is_none (some a) = ff := rfl

@[simp] theorem not_is_some {a : option α} : is_some a = ff ↔ a.is_none = tt :=
by cases a; simp

lemma eq_some_iff_get_eq {o : option α} {a : α} :
  o = some a ↔ ∃ h : o.is_some, option.get h = a :=
by cases o; simp

lemma not_is_some_iff_eq_none {o : option α} :  ¬o.is_some ↔ o = none :=
by cases o; simp

lemma ne_none_iff_is_some {o : option α} : o ≠ none ↔ o.is_some :=
by cases o; simp

lemma ne_none_iff_exists {o : option α} : o ≠ none ↔ ∃ (x : α), some x = o :=
by {cases o; simp}

lemma ne_none_iff_exists' {o : option α} : o ≠ none ↔ ∃ (x : α), o = some x :=
ne_none_iff_exists.trans $ exists_congr $ λ _, eq_comm

lemma bex_ne_none {p : option α → Prop} :
  (∃ x ≠ none, p x) ↔ ∃ x, p (some x) :=
⟨λ ⟨x, hx, hp⟩, ⟨get $ ne_none_iff_is_some.1 hx, by rwa [some_get]⟩,
  λ ⟨x, hx⟩, ⟨some x, some_ne_none x, hx⟩⟩

lemma ball_ne_none {p : option α → Prop} :
  (∀ x ≠ none, p x) ↔ ∀ x, p (some x) :=
⟨λ h x, h (some x) (some_ne_none x),
  λ h x hx, by simpa only [some_get] using h (get $ ne_none_iff_is_some.1 hx)⟩

theorem iget_mem [inhabited α] : ∀ {o : option α}, is_some o → o.iget ∈ o
| (some a) _ := rfl

theorem iget_of_mem [inhabited α] {a : α} : ∀ {o : option α}, a ∈ o → o.iget = a
| _ rfl := rfl

@[simp] theorem guard_eq_some {p : α → Prop} [decidable_pred p] {a b : α} :
  guard p a = some b ↔ a = b ∧ p a :=
by by_cases p a; simp [option.guard, h]; intro; contradiction

@[simp] theorem guard_eq_some' {p : Prop} [decidable p] :
  ∀ u, _root_.guard p = some u ↔ p
| () := by by_cases p; simp [guard, h, pure]; intro; contradiction

theorem lift_or_get_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
  ∀ o₁ o₂, lift_or_get f o₁ o₂ = o₁ ∨ lift_or_get f o₁ o₂ = o₂
| none     none     := or.inl rfl
| (some a) none     := or.inl rfl
| none     (some b) := or.inr rfl
| (some a) (some b) := by simpa [lift_or_get] using h a b

@[simp] lemma lift_or_get_none_left {f} {b : option α} : lift_or_get f none b = b :=
by cases b; refl

@[simp] lemma lift_or_get_none_right {f} {a : option α} : lift_or_get f a none = a :=
by cases a; refl

@[simp] lemma lift_or_get_some_some {f} {a b : α} :
  lift_or_get f (some a) (some b) = f a b := rfl

/-- Given an element of `a : option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def cases_on' : option α → β → (α → β) → β
| none     n s := n
| (some a) n s := s a

@[simp] lemma cases_on'_none (x : β) (f : α → β) : cases_on' none x f = x := rfl

@[simp] lemma cases_on'_some (x : β) (f : α → β) (a : α) : cases_on' (some a) x f = f a := rfl

@[simp] lemma cases_on'_coe (x : β) (f : α → β) (a : α) : cases_on' (a : option α) x f = f a := rfl

@[simp] lemma cases_on'_none_coe (f : option α → β) (o : option α) :
  cases_on' o (f none) (f ∘ coe) = f o :=
by cases o; refl

@[simp] lemma get_or_else_map (f : α → β) (x : α) (o : option α) :
  get_or_else (option.map f o) (f x) = f (get_or_else o x) :=
by cases o; refl

section
open_locale classical

/-- An arbitrary `some a` with `a : α` if `α` is nonempty, and otherwise `none`. -/
noncomputable def choice (α : Type*) : option α :=
if h : nonempty α then
  some h.some
else
  none

lemma choice_eq {α : Type*} [subsingleton α] (a : α) : choice α = some a :=
begin
  dsimp [choice],
  rw dif_pos (⟨a⟩ : nonempty α),
  congr,
end

lemma choice_eq_none (α : Type*) [is_empty α] : choice α = none :=
dif_neg (not_nonempty_iff_imp_false.mpr is_empty_elim)

lemma choice_is_some_iff_nonempty {α : Type*} : (choice α).is_some ↔ nonempty α :=
begin
  fsplit,
  { intro h, exact ⟨option.get h⟩, },
  { rintro ⟨a⟩,
    dsimp [choice],
    rw dif_pos,
    fsplit,
    exact ⟨a⟩, },
end

end

end option
