/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.set.basic
open function

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
- `partial_order.lift`, `linear_order.lift`, `decidable_linear_order.lift`:
  transfer a partial (resp., linear, decidable linear) order on `β` to a partial
  (resp., linear, decidable linear) order on `α` using an injective function `f`.

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

## Tags

preorder, order, partial order, linear order, monotone, strictly monotone
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem ge_of_eq [preorder α] {a b : α} : a = b → a ≥ b :=
λ h, h ▸ le_refl a

theorem preorder.ext {α} {A B : preorder α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  resetI, cases A, cases B, congr,
  { funext x y, exact propext (H x y) },
  { funext x y,
    dsimp [(≤)] at A_lt_iff_le_not_le B_lt_iff_le_not_le H,
    simp [A_lt_iff_le_not_le, B_lt_iff_le_not_le, H] },
end

theorem partial_order.ext {α} {A B : partial_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by haveI this := preorder.ext H;
   cases A; cases B; injection this; congr'

theorem linear_order.ext {α} {A B : linear_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by haveI this := partial_order.ext H;
   cases A; cases B; injection this; congr'

/-- Given an order `R` on `β` and a function `f : α → β`,
  the preimage order on `α` is defined by `x ≤ y ↔ f x ≤ f y`.
  It is the unique order on `α` making `f` an order embedding
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

lemma reflect_lt {α β} [linear_order α] [preorder β] {f : α → β} (hf : monotone f)
  {x x' : α} (h : f x < f x') : x < x' :=
by { rw [← not_le], intro h', apply not_le_of_lt h, exact hf h' }

end monotone

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def strict_mono [has_lt α] [has_lt β] (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f a < f b

lemma strict_mono_id [has_lt α] : strict_mono (id : α → α) := λ a b, id

namespace strict_mono
open ordering function

lemma comp [has_lt α] [has_lt β] [has_lt γ] {g : β → γ} {f : α → β}
  (hg : strict_mono g) (hf : strict_mono f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

protected theorem iterate [has_lt α] {f : α → α} (hf : strict_mono f) (n : ℕ) :
  strict_mono (f^[n]) :=
nat.rec_on n strict_mono_id (λ n ihn, ihn.comp hf)

lemma id_le {φ : ℕ → ℕ} (h : strict_mono φ) : ∀ n, n ≤ φ n :=
λ n, nat.rec_on n (nat.zero_le _) (λ n hn, nat.succ_le_of_lt (lt_of_le_of_lt hn $ h $ nat.lt_succ_self n))

section
variables [linear_order α] [preorder β] {f : α → β}

lemma lt_iff_lt (H : strict_mono f) {a b} :
  f a < f b ↔ a < b :=
⟨λ h, ((lt_trichotomy b a)
  .resolve_left $ λ h', lt_asymm h $ H h')
  .resolve_left $ λ e, ne_of_gt h $ congr_arg _ e, @H _ _⟩

lemma injective (H : strict_mono f) : injective f
| a b e := ((lt_trichotomy a b)
  .resolve_left $ λ h, ne_of_lt (H h) e)
  .resolve_right $ λ h, ne_of_gt (H h) e

theorem compares (H : strict_mono f) {a b} :
  ∀ {o}, compares o (f a) (f b) ↔ compares o a b
| lt := H.lt_iff_lt
| eq := ⟨λ h, H.injective h, congr_arg _⟩
| gt := H.lt_iff_lt

lemma le_iff_le (H : strict_mono f) {a b} :
  f a ≤ f b ↔ a ≤ b :=
⟨λ h, le_of_not_gt $ λ h', not_le_of_lt (H h') h,
 λ h, (lt_or_eq_of_le h).elim (λ h', le_of_lt (H h')) (λ h', h' ▸ le_refl _)⟩
end

protected lemma nat {β} [preorder β] {f : ℕ → β} (h : ∀n, f n < f (n+1)) : strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply h, exact lt.trans ih (h _) }

-- `preorder α` isn't strong enough: if the preorder on α is an equivalence relation,
-- then `strict_mono f` is vacuously true.
lemma monotone [partial_order α] [preorder β] {f : α → β} (H : strict_mono f) : monotone f :=
λ a b h, (lt_or_eq_of_le h).rec (le_of_lt ∘ (@H _ _)) (by rintro rfl; refl)

end strict_mono

section
open function
variables [partial_order α] [partial_order β] {f : α → β}

lemma strict_mono_of_monotone_of_injective (h₁ : monotone f) (h₂ : injective f) :
  strict_mono f :=
λ a b h,
begin
  rw lt_iff_le_and_ne at ⊢ h,
  exact ⟨h₁ h.1, λ e, h.2 (h₂ e)⟩
end

end

/-- Type tag for a set with dual order: `≤` means `≥` and `<` means `>`. -/
def order_dual (α : Type*) := α

namespace order_dual
instance (α : Type*) [h : nonempty α] : nonempty (order_dual α) := h
instance (α : Type*) [has_le α] : has_le (order_dual α) := ⟨λx y:α, y ≤ x⟩
instance (α : Type*) [has_lt α] : has_lt (order_dual α) := ⟨λx y:α, y < x⟩

-- `dual_le` and `dual_lt` should not be simp lemmas:
-- they cause a loop since `α` and `order_dual α` are definitionally equal

lemma dual_le [has_le α] {a b : α} :
  @has_le.le (order_dual α) _ a b ↔ @has_le.le α _ b a := iff.rfl

lemma dual_lt [has_lt α] {a b : α} :
  @has_lt.lt (order_dual α) _ a b ↔ @has_lt.lt α _ b a := iff.rfl

instance (α : Type*) [preorder α] : preorder (order_dual α) :=
{ le_refl  := le_refl,
  le_trans := assume a b c hab hbc, le_trans hbc hab,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  .. order_dual.has_le α,
  .. order_dual.has_lt α }

instance (α : Type*) [partial_order α] : partial_order (order_dual α) :=
{ le_antisymm := assume a b hab hba, @le_antisymm α _ a b hba hab, .. order_dual.preorder α }

instance (α : Type*) [linear_order α] : linear_order (order_dual α) :=
{ le_total := assume a b:α, le_total b a, .. order_dual.partial_order α }

instance (α : Type*) [decidable_linear_order α] : decidable_linear_order (order_dual α) :=
{ decidable_le := show decidable_rel (λa b:α, b ≤ a), by apply_instance,
  decidable_lt := show decidable_rel (λa b:α, b < a), by apply_instance,
  .. order_dual.linear_order α }

instance : Π [inhabited α], inhabited (order_dual α) := id

end order_dual

/- order instances on the function space -/

instance pi.preorder {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] : preorder (Πi, α i) :=
{ le       := λx y, ∀i, x i ≤ y i,
  le_refl  := assume a i, le_refl (a i),
  le_trans := assume a b c h₁ h₂ i, le_trans (h₁ i) (h₂ i) }

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

/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`. -/
def preorder.lift {α β} [preorder β] (f : α → β) : preorder α :=
{ le := λx y, f x ≤ f y,
  le_refl := λ a, le_refl _,
  le_trans := λ a b c, le_trans,
  lt := λx y, f x < f y,
  lt_iff_le_not_le := λ a b, lt_iff_le_not_le }

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. -/
def partial_order.lift {α β} [partial_order β] (f : α → β) (inj : injective f) :
  partial_order α :=
{ le_antisymm := λ a b h₁ h₂, inj (le_antisymm h₁ h₂), .. preorder.lift f }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. -/
def linear_order.lift {α β} [linear_order β] (f : α → β) (inj : injective f) :
  linear_order α :=
{ le_total := λx y, le_total (f x) (f y), .. partial_order.lift f inj }

/-- Transfer a `decidable_linear_order` on `β` to a `decidable_linear_order` on `α` using
an injective function `f : α → β`. -/
def decidable_linear_order.lift {α β} [decidable_linear_order β] (f : α → β) (inj : injective f) :
  decidable_linear_order α :=
{ decidable_le := λ x y, show decidable (f x ≤ f y), by apply_instance,
  decidable_lt := λ x y, show decidable (f x < f y), by apply_instance,
  decidable_eq := λ x y, decidable_of_iff _ ⟨@inj x y, congr_arg f⟩,
  .. linear_order.lift f inj }

instance subtype.preorder {α} [preorder α] (p : α → Prop) : preorder (subtype p) :=
preorder.lift subtype.val

instance subtype.partial_order {α} [partial_order α] (p : α → Prop) :
  partial_order (subtype p) :=
partial_order.lift subtype.val subtype.val_injective

instance subtype.linear_order {α} [linear_order α] (p : α → Prop) : linear_order (subtype p) :=
linear_order.lift subtype.val subtype.val_injective

instance subtype.decidable_linear_order {α} [decidable_linear_order α] (p : α → Prop) :
  decidable_linear_order (subtype p) :=
decidable_linear_order.lift subtype.val subtype.val_injective

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

/-- An order is dense if there is an element between any pair of distinct elements. -/
class densely_ordered (α : Type u) [preorder α] : Prop :=
(dense : ∀a₁ a₂:α, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂)

lemma dense [preorder α] [densely_ordered α] : ∀{a₁ a₂:α}, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂ :=
densely_ordered.dense

instance order_dual.densely_ordered (α : Type u) [preorder α] [densely_ordered α] :
  densely_ordered (order_dual α) :=
⟨λ a₁ a₂ ha, (@dense α _ _ _ _ ha).imp $ λ a, and.symm⟩

lemma le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀a₃>a₂, a₁ ≤ a₃) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := dense ha in
  lt_irrefl a $ lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma eq_of_le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃>a₂, a₁ ≤ a₃) : a₁ = a₂ :=
le_antisymm (le_of_forall_le_of_dense h₂) h₁

lemma le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀a₃<a₁, a₂ ≥ a₃) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := dense ha in
  lt_irrefl a $ lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma eq_of_le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃<a₁, a₂ ≥ a₃) : a₁ = a₂ :=
le_antisymm (le_of_forall_ge_of_dense h₂) h₁

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma dense_or_discrete [linear_order α] (a₁ a₂ : α) :
  (∃a, a₁ < a ∧ a < a₂) ∨ ((∀a>a₁, a ≥ a₂) ∧ (∀a<a₂, a ≤ a₁)) :=
classical.or_iff_not_imp_left.2 $ assume h,
  ⟨assume a ha₁, le_of_not_gt $ assume ha₂, h ⟨a, ha₁, ha₂⟩,
    assume a ha₂, le_of_not_gt $ assume ha₁, h ⟨a, ha₁, ha₂⟩⟩

variables {s : β → β → Prop} {t : γ → γ → Prop}

/-- Any `linear_order` is a noncomputable `decidable_linear_order`. This is not marked
as an instance to avoid a loop. -/
noncomputable def classical.DLO (α) [LO : linear_order α] : decidable_linear_order α :=
{ decidable_le := classical.dec_rel _, ..LO }

variable (r)
local infix ` ≼ ` : 50 := r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def directed {ι : Sort v} (f : ι → α) := ∀x y, ∃z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def directed_on (s : set α) := ∀ (x ∈ s) (y ∈ s), ∃z ∈ s, x ≼ z ∧ y ≼ z

theorem directed_on_iff_directed {s} : @directed_on α r s ↔ directed r (coe : s → α) :=
by simp [directed, directed_on]; refine ball_congr (λ x hx, by simp; refl)

theorem directed_on_image {s} {f : β → α} :
  directed_on r (f '' s) ↔ directed_on (f ⁻¹'o r) s :=
by simp only [directed_on, set.ball_image_iff, set.bex_image_iff, order.preimage]

theorem directed_on.mono {s : set α} (h : directed_on r s)
  {r' : α → α → Prop} (H : ∀ {a b}, r a b → r' a b) :
  directed_on r' s :=
λ x hx y hy, let ⟨z, zs, xz, yz⟩ := h x hx y hy in ⟨z, zs, H xz, H yz⟩

theorem directed_comp {ι} (f : ι → β) (g : β → α) :
  directed r (g ∘ f) ↔ directed (g ⁻¹'o r) f := iff.rfl

variable {r}

theorem directed.mono {s : α → α → Prop} {ι} {f : ι → α}
  (H : ∀ a b, r a b → s a b) (h : directed r f) : directed s f :=
λ a b, let ⟨c, h₁, h₂⟩ := h a b in ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
  (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y)) (hf : directed r f) :
  directed rb (g ∘ f) :=
(directed_comp rb f g).2 $ hf.mono hg

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A `preorder` is a `directed_order` if for any two elements `i`, `j`
there is an element `k` such that `i ≤ k` and `j ≤ k`. -/
class directed_order (α : Type u) extends preorder α :=
(directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k)
end prio
