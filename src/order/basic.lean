/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.subtype
import data.prod

/-!
# Basic definitions about `≤` and `<`

## Definitions

### Predicates on functions

- `monotone f`: a function between two types equipped with `≤` is monotone
  if `a ≤ b` implies `f a ≤ f b`.
- `strict_mono f` : a function between two types equipped with `<` is strictly monotone
  if `a < b` implies `f a < f b`.
- `order_dual α` : a type tag reversing the meaning of all inequalities.

### Transfering orders

- `order.preimage`, `preorder.lift`: transfer a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`: transfer a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra classes

- `no_top_order`, `no_bot_order`: an order without a maximal/minimal element.
- `densely_ordered`: an order with no gaps, i.e. for any two elements `a<b` there exists
  `c`, `a<c<b`.

## Main theorems

- `monotone_of_monotone_nat`: if `f : ℕ → α` and `f n ≤ f (n + 1)` for all `n`, then
  `f` is monotone;
- `strict_mono.nat`: if `f : ℕ → α` and `f n < f (n + 1)` for all `n`, then f is strictly monotone.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## See also
- `algebra.order` for basic lemmas about orders, and projection notation for orders

## Tags

preorder, order, partial order, linear order, monotone, strictly monotone
-/

open function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

attribute [simp] le_refl

@[simp] lemma lt_self_iff_false [preorder α] (a : α) : a < a ↔ false :=
by simp [lt_irrefl a]

attribute [ext] has_le

@[ext]
lemma preorder.to_has_le_injective {α : Type*} :
  function.injective (@preorder.to_has_le α) :=
λ A B h, begin
  cases A, cases B,
  injection h with h_le,
  have : A_lt = B_lt,
  { funext a b,
    dsimp [(≤)] at A_lt_iff_le_not_le B_lt_iff_le_not_le h_le,
    simp [A_lt_iff_le_not_le, B_lt_iff_le_not_le, h_le], },
  congr',
end

@[ext]
lemma partial_order.to_preorder_injective {α : Type*} :
  function.injective (@partial_order.to_preorder α) :=
λ A B h, by { cases A, cases B, injection h, congr' }

@[ext]
lemma linear_order.to_partial_order_injective {α : Type*} :
  function.injective (@linear_order.to_partial_order α) :=
λ A B h, by { cases A, cases B, injection h, congr' }

theorem preorder.ext {α} {A B : preorder α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

theorem partial_order.ext {α} {A B : partial_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

theorem linear_order.ext {α} {A B : linear_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

/-- Given a relation `R` on `β` and a function `f : α → β`,
  the preimage relation on `α` is defined by `x ≤ y ↔ f x ≤ f y`.
  It is the unique relation on `α` making `f` a `rel_embedding`
  (assuming `f` is injective). -/
@[simp] def order.preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) := s (f x) (f y)

infix ` ⁻¹'o `:80 := order.preimage

/-- The preimage of a decidable order is decidable. -/
instance order.preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : decidable_rel s] :
  decidable_rel (f ⁻¹'o s) :=
λ x y, H _ _

section monotone
variables [preorder α] [preorder β] [preorder γ]

/-- A function between preorders is monotone if
  `a ≤ b` implies `f a ≤ f b`. -/
def monotone (f : α → β) := ∀⦃a b⦄, a ≤ b → f a ≤ f b

theorem monotone_id : @monotone α α _ _ id := assume x y h, h

theorem monotone_const {b : β} : monotone (λ(a:α), b) := assume x y h, le_refl b

protected theorem monotone.comp {g : β → γ} {f : α → β} (m_g : monotone g) (m_f : monotone f) :
  monotone (g ∘ f) :=
assume a b h, m_g (m_f h)

protected theorem monotone.iterate {f : α → α} (hf : monotone f) (n : ℕ) : monotone (f^[n]) :=
nat.rec_on n monotone_id (λ n ihn, ihn.comp hf)

lemma monotone_of_monotone_nat {f : ℕ → α} (hf : ∀n, f n ≤ f (n + 1)) :
  monotone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, assumption, exact hf _ }
end

lemma monotone.reflect_lt {α β} [linear_order α] [preorder β] {f : α → β} (hf : monotone f)
  {x x' : α} (h : f x < f x') : x < x' :=
by { rw [← not_le], intro h', apply not_le_of_lt h, exact hf h' }

/-- If `f` is a monotone function from `ℕ` to a preorder such that `y` lies between `f x` and
  `f (x + 1)`, then `y` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_nat {α} [preorder α] {f : ℕ → α} (hf : monotone f)
  (x x' : ℕ) {y : α} (h1 : f x < y) (h2 : y < f (x + 1)) : f x' ≠ y :=
by { rintro rfl, apply (hf.reflect_lt h1).not_le, exact nat.le_of_lt_succ (hf.reflect_lt h2) }

/-- If `f` is a monotone function from `ℤ` to a preorder such that `y` lies between `f x` and
  `f (x + 1)`, then `y` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_int {α} [preorder α] {f : ℤ → α} (hf : monotone f)
  (x x' : ℤ) {y : α} (h1 : f x < y) (h2 : y < f (x + 1)) : f x' ≠ y :=
by { rintro rfl, apply (hf.reflect_lt h1).not_le, exact int.le_of_lt_add_one (hf.reflect_lt h2) }

end monotone

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def strict_mono [has_lt α] [has_lt β] (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f a < f b

lemma strict_mono_id [has_lt α] : strict_mono (id : α → α) := λ a b, id

lemma strict_mono_of_strict_mono_nat [preorder α] {f : ℕ → α} (hf : ∀n, f n < f (n + 1)) :
  strict_mono f | n m h :=
begin
  induction h,
  { exact hf _ },
  { transitivity, assumption, exact hf _ }
end

/-- A function `f` is strictly monotone increasing on `t` if `x < y` for `x,y ∈ t` implies
`f x < f y`. -/
def strict_mono_incr_on [has_lt α] [has_lt β] (f : α → β) (t : set α) : Prop :=
∀ ⦃x⦄ (hx : x ∈ t) ⦃y⦄ (hy : y ∈ t), x < y → f x < f y

/-- A function `f` is strictly monotone decreasing on `t` if `x < y` for `x,y ∈ t` implies
`f y < f x`. -/
def strict_mono_decr_on [has_lt α] [has_lt β] (f : α → β) (t : set α) : Prop :=
∀ ⦃x⦄ (hx : x ∈ t) ⦃y⦄ (hy : y ∈ t), x < y → f y < f x

/-- Type tag for a set with dual order: `≤` means `≥` and `<` means `>`. -/
def order_dual (α : Type*) := α

namespace order_dual
instance (α : Type*) [h : nonempty α] : nonempty (order_dual α) := h
instance (α : Type*) [h : subsingleton α] : subsingleton (order_dual α) := h
instance (α : Type*) [has_le α] : has_le (order_dual α) := ⟨λx y:α, y ≤ x⟩
instance (α : Type*) [has_lt α] : has_lt (order_dual α) := ⟨λx y:α, y < x⟩
instance (α : Type*) [has_zero α] : has_zero (order_dual α) := ⟨(0 : α)⟩

-- `dual_le` and `dual_lt` should not be simp lemmas:
-- they cause a loop since `α` and `order_dual α` are definitionally equal

lemma dual_le [has_le α] {a b : α} :
  @has_le.le (order_dual α) _ a b ↔ @has_le.le α _ b a := iff.rfl

lemma dual_lt [has_lt α] {a b : α} :
  @has_lt.lt (order_dual α) _ a b ↔ @has_lt.lt α _ b a := iff.rfl

lemma dual_compares [has_lt α] {a b : α} {o : ordering} :
  @ordering.compares (order_dual α) _ o a b ↔ @ordering.compares α _ o b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

instance (α : Type*) [preorder α] : preorder (order_dual α) :=
{ le_refl  := le_refl,
  le_trans := assume a b c hab hbc, hbc.trans hab,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  .. order_dual.has_le α,
  .. order_dual.has_lt α }

instance (α : Type*) [partial_order α] : partial_order (order_dual α) :=
{ le_antisymm := assume a b hab hba, @le_antisymm α _ a b hba hab, .. order_dual.preorder α }

instance (α : Type*) [linear_order α] : linear_order (order_dual α) :=
{ le_total := assume a b:α, le_total b a,
  decidable_le := show decidable_rel (λa b:α, b ≤ a), by apply_instance,
  decidable_lt := show decidable_rel (λa b:α, b < a), by apply_instance,
  .. order_dual.partial_order α }

instance : Π [inhabited α], inhabited (order_dual α) := id

theorem preorder.dual_dual (α : Type*) [H : preorder α] :
  order_dual.preorder (order_dual α) = H :=
preorder.ext $ λ _ _, iff.rfl

theorem partial_order.dual_dual (α : Type*) [H : partial_order α] :
  order_dual.partial_order (order_dual α) = H :=
partial_order.ext $ λ _ _, iff.rfl

theorem linear_order.dual_dual (α : Type*) [H : linear_order α] :
  order_dual.linear_order (order_dual α) = H :=
linear_order.ext $ λ _ _, iff.rfl

theorem cmp_le_flip {α} [has_le α] [@decidable_rel α (≤)] (x y : α) :
  @cmp_le (order_dual α) _ _ x y = cmp_le y x := rfl

end order_dual

namespace strict_mono_incr_on

section dual

variables [preorder α] [preorder β] {f : α → β} {s : set α}

protected lemma dual (H : strict_mono_incr_on f s) :
  @strict_mono_incr_on (order_dual α) (order_dual β) _ _ f s :=
λ x hx y hy, H hy hx

protected lemma dual_right (H : strict_mono_incr_on f s) :
  @strict_mono_decr_on α (order_dual β) _ _ f s :=
H

end dual

variables [linear_order α] [preorder β] {f : α → β} {s : set α} {x y : α}

lemma le_iff_le (H : strict_mono_incr_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x ≤ f y ↔ x ≤ y :=
⟨λ h, le_of_not_gt $ λ h', not_le_of_lt (H hy hx h') h,
 λ h, h.lt_or_eq_dec.elim (λ h', le_of_lt (H hx hy h')) (λ h', h' ▸ le_refl _)⟩

lemma lt_iff_lt (H : strict_mono_incr_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x < f y ↔ x < y :=
by simp only [H.le_iff_le, hx, hy, lt_iff_le_not_le]

protected theorem compares (H : strict_mono_incr_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  ∀ {o}, ordering.compares o (f x) (f y) ↔ ordering.compares o x y
| ordering.lt := H.lt_iff_lt hx hy
| ordering.eq := ⟨λ h, le_antisymm ((H.le_iff_le hx hy).1 h.le) ((H.le_iff_le hy hx).1 h.symm.le),
                   congr_arg _⟩
| ordering.gt := H.lt_iff_lt hy hx

end strict_mono_incr_on

namespace strict_mono_decr_on

section dual

variables [preorder α] [preorder β] {f : α → β} {s : set α}

protected lemma dual (H : strict_mono_decr_on f s) :
  @strict_mono_decr_on (order_dual α) (order_dual β) _ _ f s :=
λ x hx y hy, H hy hx

protected lemma dual_right (H : strict_mono_decr_on f s) :
  @strict_mono_incr_on α (order_dual β) _ _ f s :=
H

end dual

variables [linear_order α] [preorder β] {f : α → β} {s : set α} {x y : α}

lemma le_iff_le (H : strict_mono_decr_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x ≤ f y ↔ y ≤ x :=
H.dual_right.le_iff_le hy hx

lemma lt_iff_lt (H : strict_mono_decr_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x < f y ↔ y < x :=
H.dual_right.lt_iff_lt hy hx

protected theorem compares (H : strict_mono_decr_on f s) (hx : x ∈ s) (hy : y ∈ s) {o : ordering} :
  ordering.compares o (f x) (f y) ↔ ordering.compares o y x :=
order_dual.dual_compares.trans $ H.dual_right.compares hy hx

end strict_mono_decr_on

namespace strict_mono
open ordering function

protected lemma strict_mono_incr_on [has_lt α] [has_lt β] {f : α → β} (hf : strict_mono f)
  (s : set α) :
  strict_mono_incr_on f s :=
λ x hx y hy hxy, hf hxy

lemma comp [has_lt α] [has_lt β] [has_lt γ] {g : β → γ} {f : α → β}
  (hg : strict_mono g) (hf : strict_mono f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

protected theorem iterate [has_lt α] {f : α → α} (hf : strict_mono f) (n : ℕ) :
  strict_mono (f^[n]) :=
nat.rec_on n strict_mono_id (λ n ihn, ihn.comp hf)

lemma id_le {φ : ℕ → ℕ} (h : strict_mono φ) : ∀ n, n ≤ φ n :=
λ n, nat.rec_on n (nat.zero_le _)
  (λ n hn, nat.succ_le_of_lt (lt_of_le_of_lt hn $ h $ nat.lt_succ_self n))

protected lemma ite' [preorder α] [has_lt β] {f g : α → β} (hf : strict_mono f) (hg : strict_mono g)
  {p : α → Prop} [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
  strict_mono (λ x, if p x then f x else g x) :=
begin
  intros x y h,
  by_cases hy : p y,
  { have hx : p x := hp h hy,
    simpa [hx, hy] using hf h },
  { by_cases hx : p x,
    { simpa [hx, hy] using hfg hx hy h },
    { simpa [hx, hy] using hg h} }
end

protected lemma ite [preorder α] [preorder β] {f g : α → β} (hf : strict_mono f)
  (hg : strict_mono g) {p : α → Prop} [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ x, f x ≤ g x) :
  strict_mono (λ x, if p x then f x else g x) :=
hf.ite' hg hp $ λ x y hx hy h, (hf h).trans_le (hfg y)

section
variables [linear_order α] [preorder β] {f : α → β}

lemma lt_iff_lt (H : strict_mono f) {a b} : f a < f b ↔ a < b :=
(H.strict_mono_incr_on set.univ).lt_iff_lt trivial trivial

protected theorem compares (H : strict_mono f) {a b} {o} :
  compares o (f a) (f b) ↔ compares o a b :=
(H.strict_mono_incr_on set.univ).compares trivial trivial

lemma injective (H : strict_mono f) : injective f :=
λ x y h, show compares eq x y, from H.compares.1 h

lemma le_iff_le (H : strict_mono f) {a b} : f a ≤ f b ↔ a ≤ b :=
(H.strict_mono_incr_on set.univ).le_iff_le trivial trivial

lemma top_preimage_top (H : strict_mono f) {a} (h_top : ∀ p, p ≤ f a) (x : α) : x ≤ a :=
H.le_iff_le.mp (h_top (f x))

lemma bot_preimage_bot (H : strict_mono f) {a} (h_bot : ∀ p, f a ≤ p) (x : α) : a ≤ x :=
H.le_iff_le.mp (h_bot (f x))

end

protected lemma nat {β} [preorder β] {f : ℕ → β} (h : ∀n, f n < f (n+1)) : strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply h, exact ih.trans (h _) }

-- `preorder α` isn't strong enough: if the preorder on α is an equivalence relation,
-- then `strict_mono f` is vacuously true.
lemma monotone [partial_order α] [preorder β] {f : α → β} (H : strict_mono f) : monotone f :=
λ a b h, (lt_or_eq_of_le h).rec (le_of_lt ∘ (@H _ _)) (by rintro rfl; refl)

end strict_mono

section
open function

lemma injective_of_lt_imp_ne [linear_order α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
  injective f :=
begin
  intros x y k,
  contrapose k,
  rw [←ne.def, ne_iff_lt_or_gt] at k,
  cases k,
  { apply h _ _ k },
  { rw eq_comm,
    apply h _ _ k }
end

lemma strict_mono_of_monotone_of_injective [partial_order α] [partial_order β] {f : α → β}
  (h₁ : monotone f) (h₂ : injective f) : strict_mono f :=
λ a b h,
begin
  rw lt_iff_le_and_ne at ⊢ h,
  exact ⟨h₁ h.1, λ e, h.2 (h₂ e)⟩
end

lemma monotone.strict_mono_iff_injective [linear_order α] [partial_order β] {f : α → β}
  (h : monotone f) : strict_mono f ↔ injective f :=
⟨λ h, h.injective, strict_mono_of_monotone_of_injective h⟩

lemma strict_mono_of_le_iff_le [preorder α] [preorder β] {f : α → β}
  (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : strict_mono f :=
λ a b, by simp [lt_iff_le_not_le, h] {contextual := tt}

end

/-! ### Order instances on the function space -/

instance pi.preorder {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] : preorder (Πi, α i) :=
{ le       := λx y, ∀i, x i ≤ y i,
  le_refl  := assume a i, le_refl (a i),
  le_trans := assume a b c h₁ h₂ i, le_trans (h₁ i) (h₂ i) }

lemma pi.le_def {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] {x y : Π i, α i} :
  x ≤ y ↔ ∀ i, x i ≤ y i :=
iff.rfl

lemma pi.lt_def {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] {x y : Π i, α i} :
  x < y ↔ x ≤ y ∧ ∃ i, x i < y i :=
by simp [lt_iff_le_not_le, pi.le_def] {contextual := tt}

lemma le_update_iff {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a : α i} :
  x ≤ function.update y i a ↔ x i ≤ a ∧ ∀ j ≠ i, x j ≤ y j :=
function.forall_update_iff _ (λ j z, x j ≤ z)

lemma update_le_iff {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a : α i} :
  function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ j ≠ i, x j ≤ y j :=
function.forall_update_iff _ (λ j z, z ≤ y j)

lemma update_le_update_iff {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a b : α i} :
  function.update x i a ≤ function.update y i b ↔ a ≤ b ∧ ∀ j ≠ i, x j ≤ y j :=
by simp [update_le_iff] {contextual := tt}

instance pi.partial_order {ι : Type u} {α : ι → Type v} [∀i, partial_order (α i)] :
  partial_order (Πi, α i) :=
{ le_antisymm := λf g h1 h2, funext (λb, le_antisymm (h1 b) (h2 b)),
  ..pi.preorder }

theorem comp_le_comp_left_of_monotone [preorder α] [preorder β]
  {f : β → α} {g h : γ → β} (m_f : monotone f) (le_gh : g ≤ h) :
  has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
assume x, m_f (le_gh x)

section monotone
variables [preorder α] [preorder γ]

protected theorem monotone.order_dual {f : α → γ} (hf : monotone f) :
  @monotone (order_dual α) (order_dual γ) _ _ f :=
λ x y hxy, hf hxy

theorem monotone_lam {f : α → β → γ} (m : ∀b, monotone (λa, f a b)) : monotone f :=
assume a a' h b, m b h

theorem monotone_app (f : β → α → γ) (b : β) (m : monotone (λa b, f b a)) : monotone (f b) :=
assume a a' h, m h b

end monotone

theorem strict_mono.order_dual [has_lt α] [has_lt β] {f : α → β} (hf : strict_mono f) :
  @strict_mono (order_dual α) (order_dual β) _ _ f :=
λ x y hxy, hf hxy

/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible] def preorder.lift {α β} [preorder β] (f : α → β) : preorder α :=
{ le := λx y, f x ≤ f y,
  le_refl := λ a, le_refl _,
  le_trans := λ a b c, le_trans,
  lt := λx y, f x < f y,
  lt_iff_le_not_le := λ a b, lt_iff_le_not_le }

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def partial_order.lift {α β} [partial_order β] (f : α → β) (inj : injective f) :
  partial_order α :=
{ le_antisymm := λ a b h₁ h₂, inj (le_antisymm h₁ h₂), .. preorder.lift f }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def linear_order.lift {α β} [linear_order β] (f : α → β) (inj : injective f) :
  linear_order α :=
{ le_total := λx y, le_total (f x) (f y),
  decidable_le := λ x y, (infer_instance : decidable (f x ≤ f y)),
  decidable_lt := λ x y, (infer_instance : decidable (f x < f y)),
  decidable_eq := λ x y, decidable_of_iff _ inj.eq_iff,
  .. partial_order.lift f inj }

instance subtype.preorder {α} [preorder α] (p : α → Prop) : preorder (subtype p) :=
preorder.lift subtype.val

@[simp] lemma subtype.mk_le_mk {α} [preorder α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
iff.rfl

@[simp] lemma subtype.mk_lt_mk {α} [preorder α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : subtype p) < ⟨y, hy⟩ ↔ x < y :=
iff.rfl

@[simp, norm_cast] lemma subtype.coe_le_coe {α} [preorder α] {p : α → Prop} {x y : subtype p} :
  (x : α) ≤ y ↔ x ≤ y :=
iff.rfl

@[simp, norm_cast] lemma subtype.coe_lt_coe {α} [preorder α] {p : α → Prop} {x y : subtype p} :
  (x : α) < y ↔ x < y :=
iff.rfl

instance subtype.partial_order {α} [partial_order α] (p : α → Prop) :
  partial_order (subtype p) :=
partial_order.lift subtype.val subtype.val_injective

instance subtype.linear_order {α} [linear_order α] (p : α → Prop) : linear_order (subtype p) :=
linear_order.lift subtype.val subtype.val_injective

lemma subtype.mono_coe [preorder α] (t : set α) : monotone (coe : (subtype t) → α) :=
λ x y, id

lemma subtype.strict_mono_coe [preorder α] (t : set α) : strict_mono (coe : (subtype t) → α) :=
λ x y, id

instance prod.has_le (α : Type u) (β : Type v) [has_le α] [has_le β] : has_le (α × β) :=
⟨λp q, p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

instance prod.preorder (α : Type u) (β : Type v) [preorder α] [preorder β] : preorder (α × β) :=
{ le_refl  := assume ⟨a, b⟩, ⟨le_refl a, le_refl b⟩,
  le_trans := assume ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩,
    ⟨le_trans hac hce, le_trans hbd hdf⟩,
  .. prod.has_le α β }

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `lex α β = α × β`.) -/
instance prod.partial_order (α : Type u) (β : Type v) [partial_order α] [partial_order β] :
  partial_order (α × β) :=
{ le_antisymm := assume ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ ⟨hca, hdb⟩,
    prod.ext (le_antisymm hac hca) (le_antisymm hbd hdb),
  .. prod.preorder α β }

/-!
### Additional order classes
-/

/-- order without a top element; somtimes called cofinal -/
class no_top_order (α : Type u) [preorder α] : Prop :=
(no_top : ∀a:α, ∃a', a < a')

lemma no_top [preorder α] [no_top_order α] : ∀a:α, ∃a', a < a' :=
no_top_order.no_top

instance nonempty_gt {α : Type u} [preorder α] [no_top_order α] (a : α) :
  nonempty {x // a < x} :=
nonempty_subtype.2 (no_top a)

/-- order without a bottom element; somtimes called coinitial or dense -/
class no_bot_order (α : Type u) [preorder α] : Prop :=
(no_bot : ∀a:α, ∃a', a' < a)

lemma no_bot [preorder α] [no_bot_order α] : ∀a:α, ∃a', a' < a :=
no_bot_order.no_bot

instance order_dual.no_top_order (α : Type u) [preorder α] [no_bot_order α] :
  no_top_order (order_dual α) :=
⟨λ a, @no_bot α _ _ a⟩

instance order_dual.no_bot_order (α : Type u) [preorder α] [no_top_order α] :
  no_bot_order (order_dual α) :=
⟨λ a, @no_top α _ _ a⟩

instance nonempty_lt {α : Type u} [preorder α] [no_bot_order α] (a : α) :
  nonempty {x // x < a} :=
nonempty_subtype.2 (no_bot a)

/-- An order is dense if there is an element between any pair of distinct elements. -/
class densely_ordered (α : Type u) [preorder α] : Prop :=
(dense : ∀a₁ a₂:α, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂)

lemma exists_between [preorder α] [densely_ordered α] : ∀{a₁ a₂:α}, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂ :=
densely_ordered.dense

instance order_dual.densely_ordered (α : Type u) [preorder α] [densely_ordered α] :
  densely_ordered (order_dual α) :=
⟨λ a₁ a₂ ha, (@exists_between α _ _ _ _ ha).imp $ λ a, and.symm⟩

lemma le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀a₃>a₂, a₁ ≤ a₃) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := exists_between ha in
  lt_irrefl a $ lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma eq_of_le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃>a₂, a₁ ≤ a₃) : a₁ = a₂ :=
le_antisymm (le_of_forall_le_of_dense h₂) h₁

lemma le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀a₃<a₁, a₃ ≤ a₂) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := exists_between ha in
  lt_irrefl a $ lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma eq_of_le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃<a₁, a₃ ≤ a₂) : a₁ = a₂ :=
le_antisymm (le_of_forall_ge_of_dense h₂) h₁

lemma dense_or_discrete [linear_order α] (a₁ a₂ : α) :
  (∃a, a₁ < a ∧ a < a₂) ∨ ((∀a>a₁, a₂ ≤ a) ∧ (∀a<a₂, a ≤ a₁)) :=
or_iff_not_imp_left.2 $ assume h,
  ⟨assume a ha₁, le_of_not_gt $ assume ha₂, h ⟨a, ha₁, ha₂⟩,
    assume a ha₂, le_of_not_gt $ assume ha₁, h ⟨a, ha₁, ha₂⟩⟩

variables {s : β → β → Prop} {t : γ → γ → Prop}

/-- Type synonym to create an instance of `linear_order` from a
`partial_order` and `[is_total α (≤)]` -/
def as_linear_order (α : Type u) := α

instance {α} [inhabited α] : inhabited (as_linear_order α) :=
⟨ (default α : α) ⟩

noncomputable instance as_linear_order.linear_order {α} [partial_order α] [is_total α (≤)] :
  linear_order (as_linear_order α) :=
{ le_total := @total_of α (≤) _,
  decidable_le := classical.dec_rel _,
  .. (_ : partial_order α) }
