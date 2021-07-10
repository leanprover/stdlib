/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.equiv.nat
import order.rel_iso
import order.directed

/-!
# Encodable types

This file defines encodable (constructively countable) types as a typeclass.
This is used to provide explicit encode/decode functions from and to `ℕ`, with the information that
those functions are inverses of each other.
The difference with `denumerable` is that finite types are encodable. For infinite types,
`encodable` and `denumerable` agree.

## Main declarations

* `encodable α`: States that there exists an explicit encoding function `encode : α → ℕ` with a
  partial inverse `decode : ℕ → option α`.
* `decode₂`: Version of `decode` that is equal to `none` outside of the range of `encode`. Useful as
  we do not require this in the definition of `decode`.
* `ulower α`: Any encodable type has an equivalent type living in the lowest universe, namely a
  subtype of `ℕ`. `ulower α` finds it.

## Implementation notes

The point of asking for an explicit partial inverse `decode : ℕ → option α` to `encode : α → ℕ` is
to make the range of `encode` decidable even when the finiteness of `α` is not.
-/

open option list nat function

/-- Constructively countable type. Made from an explicit injection `encode : α → ℕ` and a partial
inverse `decode : ℕ → option α`. Note that finite types *are* countable. See `denumerable` if you
wish to enforce infiniteness. -/
class encodable (α : Type*) :=
(encode : α → ℕ)
(decode [] : ℕ → option α)
(encodek : ∀ a, decode (encode a) = some a)

attribute [simp] encodable.encodek

namespace encodable
variables {α : Type*} {β : Type*}
universe u

theorem encode_injective [encodable α] : function.injective (@encode α _)
| x y e := option.some.inj $ by rw [← encodek, e, encodek]

lemma surjective_decode_iget (α : Type*) [encodable α] [inhabited α] :
  surjective (λ n, (encodable.decode α n).iget) :=
λ x, ⟨encodable.encode x, by simp_rw [encodable.encodek]⟩

/-- An encodable type has decidable equality. Not set as an instance because this is usually not the
best way to infer decidability. -/
def decidable_eq_of_encodable (α) [encodable α] : decidable_eq α
| a b := decidable_of_iff _ encode_injective.eq_iff

/-- If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable as well. -/
def of_left_injection [encodable α]
  (f : β → α) (finv : α → option β) (linv : ∀ b, finv (f b) = some b) : encodable β :=
⟨λ b, encode (f b),
 λ n, (decode α n).bind finv,
 λ b, by simp [encodable.encodek, linv]⟩

/-- If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well. -/
def of_left_inverse [encodable α]
  (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) : encodable β :=
of_left_injection f (some ∘ finv) (λ b, congr_arg some (linv b))

/-- Encodability is preserved by equivalence. -/
def of_equiv (α) [encodable α] (e : β ≃ α) : encodable β :=
of_left_inverse e e.symm e.left_inv

@[simp] theorem encode_of_equiv {α β} [encodable α] (e : β ≃ α) (b : β) :
  @encode _ (of_equiv _ e) b = encode (e b) := rfl

@[simp] theorem decode_of_equiv {α β} [encodable α] (e : β ≃ α) (n : ℕ) :
  @decode _ (of_equiv _ e) n = (decode α n).map e.symm := rfl

instance nat : encodable ℕ :=
⟨id, some, λ a, rfl⟩

@[simp] theorem encode_nat (n : ℕ) : encode n = n := rfl
@[simp] theorem decode_nat (n : ℕ) : decode ℕ n = some n := rfl

instance empty : encodable empty :=
⟨λ a, a.rec _, λ n, none, λ a, a.rec _⟩

instance unit : encodable punit :=
⟨λ_, zero, λ n, nat.cases_on n (some punit.star) (λ _, none), λ _, by simp⟩

@[simp] theorem encode_star : encode punit.star = 0 := rfl

@[simp] theorem decode_unit_zero : decode punit 0 = some punit.star := rfl
@[simp] theorem decode_unit_succ (n) : decode punit (succ n) = none := rfl

/-- If `α` is encodable, then so is `option α`. -/
instance option {α : Type*} [h : encodable α] : encodable (option α) :=
⟨λ o, option.cases_on o nat.zero (λ a, succ (encode a)),
 λ n, nat.cases_on n (some none) (λ m, (decode α m).map some),
 λ o, by cases o; dsimp; simp [encodek, nat.succ_ne_zero]⟩

@[simp] theorem encode_none [encodable α] : encode (@none α) = 0 := rfl
@[simp] theorem encode_some [encodable α] (a : α) :
  encode (some a) = succ (encode a) := rfl

@[simp] theorem decode_option_zero [encodable α] : decode (option α) 0 = some none := rfl
@[simp] theorem decode_option_succ [encodable α] (n) :
  decode (option α) (succ n) = (decode α n).map some := rfl

/-- Failsafe variant of `decode`. `decode₂ α n` returns the preimage of `n` under `encode` if it
exists, and returns `none` if it doesn't. This requirement could be imposed directly on `decode` but
is not to help make the definition easier to use. -/
def decode₂ (α) [encodable α] (n : ℕ) : option α :=
(decode α n).bind (option.guard (λ a, encode a = n))

theorem mem_decode₂' [encodable α] {n : ℕ} {a : α} :
  a ∈ decode₂ α n ↔ a ∈ decode α n ∧ encode a = n :=
by simp [decode₂]; exact
⟨λ ⟨_, h₁, rfl, h₂⟩, ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨_, h₁, rfl, h₂⟩⟩

theorem mem_decode₂ [encodable α] {n : ℕ} {a : α} :
  a ∈ decode₂ α n ↔ encode a = n :=
mem_decode₂'.trans (and_iff_right_of_imp $ λ e, e ▸ encodek _)

theorem decode₂_ne_none_iff [encodable α] {n : ℕ} :
  decode₂ α n ≠ none ↔ n ∈ set.range (encode : α → ℕ) :=
by simp_rw [set.range, set.mem_set_of_eq, ne.def, option.eq_none_iff_forall_not_mem,
  encodable.mem_decode₂, not_forall, not_not]

theorem decode₂_is_partial_inv [encodable α] : is_partial_inv encode (decode₂ α) :=
λ a n, mem_decode₂
theorem decode₂_inj [encodable α] {n : ℕ} {a₁ a₂ : α}
  (h₁ : a₁ ∈ decode₂ α n) (h₂ : a₂ ∈ decode₂ α n) : a₁ = a₂ :=
encode_injective $ (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm

theorem encodek₂ [encodable α] (a : α) : decode₂ α (encode a) = some a :=
mem_decode₂.2 rfl

/-- The encoding function has decidable range. -/
def decidable_range_encode (α : Type*) [encodable α] : decidable_pred (∈ set.range (@encode α _)) :=
λ x, decidable_of_iff (option.is_some (decode₂ α x))
  ⟨λ h, ⟨option.get h, by rw [← decode₂_is_partial_inv (option.get h), option.some_get]⟩,
  λ ⟨n, hn⟩, by rw [← hn, encodek₂]; exact rfl⟩

/-- An encodable type is equivalent to the range of its encoding function. -/
def equiv_range_encode (α : Type*) [encodable α] : α ≃ set.range (@encode α _) :=
{ to_fun := λ a : α, ⟨encode a, set.mem_range_self _⟩,
  inv_fun := λ n, option.get (show is_some (decode₂ α n.1),
    by cases n.2 with x hx; rw [← hx, encodek₂]; exact rfl),
  left_inv := λ a, by dsimp;
    rw [← option.some_inj, option.some_get, encodek₂],
  right_inv := λ ⟨n, x, hx⟩, begin
    apply subtype.eq,
    dsimp,
    conv {to_rhs, rw ← hx},
    rw [encode_injective.eq_iff, ← option.some_inj, option.some_get, ← hx, encodek₂],
  end }

section sum
variables [encodable α] [encodable β]

/-- Explicit encoding function for the sum of two encodable types. -/
def encode_sum : α ⊕ β → ℕ
| (sum.inl a) := bit0 $ encode a
| (sum.inr b) := bit1 $ encode b

/-- Explicit decoding function for the sum of two encodable types. -/
def decode_sum (n : ℕ) : option (α ⊕ β) :=
match bodd_div2 n with
| (ff, m) := (decode α m).map sum.inl
| (tt, m) := (decode β m).map sum.inr
end

/-- If `α` and `β` are encodable, then so is their sum. -/
instance sum : encodable (α ⊕ β) :=
⟨encode_sum, decode_sum, λ s,
  by cases s; simp [encode_sum, decode_sum, encodek]; refl⟩

@[simp] theorem encode_inl (a : α) :
  @encode (α ⊕ β) _ (sum.inl a) = bit0 (encode a) := rfl
@[simp] theorem encode_inr (b : β) :
  @encode (α ⊕ β) _ (sum.inr b) = bit1 (encode b) := rfl
@[simp] theorem decode_sum_val (n : ℕ) :
  decode (α ⊕ β) n = decode_sum n := rfl

end sum

instance bool : encodable bool :=
of_equiv (unit ⊕ unit) equiv.bool_equiv_punit_sum_punit

@[simp] theorem encode_tt : encode tt = 1 := rfl
@[simp] theorem encode_ff : encode ff = 0 := rfl

@[simp] theorem decode_zero : decode bool 0 = some ff := rfl
@[simp] theorem decode_one : decode bool 1 = some tt := rfl

theorem decode_ge_two (n) (h : 2 ≤ n) : decode bool n = none :=
begin
  suffices : decode_sum n = none,
  { change (decode_sum n).map _ = none, rw this, refl },
  have : 1 ≤ div2 n,
  { rw [div2_val, nat.le_div_iff_mul_le],
    exacts [h, dec_trivial] },
  cases exists_eq_succ_of_ne_zero (ne_of_gt this) with m e,
  simp [decode_sum]; cases bodd n; simp [decode_sum]; rw e; refl
end

section sigma
variables {γ : α → Type*} [encodable α] [∀ a, encodable (γ a)]

/-- Explicit encoding function for `sigma γ` -/
def encode_sigma : sigma γ → ℕ
| ⟨a, b⟩ := mkpair (encode a) (encode b)

/-- Explicit decoding function for `sigma γ` -/
def decode_sigma (n : ℕ) : option (sigma γ) :=
let (n₁, n₂) := unpair n in
(decode α n₁).bind $ λ a, (decode (γ a) n₂).map $ sigma.mk a

instance sigma : encodable (sigma γ) :=
⟨encode_sigma, decode_sigma, λ ⟨a, b⟩,
  by simp [encode_sigma, decode_sigma, unpair_mkpair, encodek]⟩

@[simp] theorem decode_sigma_val (n : ℕ) : decode (sigma γ) n =
  (decode α n.unpair.1).bind (λ a, (decode (γ a) n.unpair.2).map $ sigma.mk a) :=
show decode_sigma._match_1 _ = _, by cases n.unpair; refl

@[simp] theorem encode_sigma_val (a b) : @encode (sigma γ) _ ⟨a, b⟩ =
  mkpair (encode a) (encode b) := rfl

end sigma

section prod
variables [encodable α] [encodable β]

/-- If `α` and `β` are encodable, then so is their product. -/
instance prod : encodable (α × β) :=
of_equiv _ (equiv.sigma_equiv_prod α β).symm

@[simp] theorem decode_prod_val (n : ℕ) : decode (α × β) n =
  (decode α n.unpair.1).bind (λ a, (decode β n.unpair.2).map $ prod.mk a) :=
show (decode (sigma (λ _, β)) n).map (equiv.sigma_equiv_prod α β) = _,
by simp; cases decode α n.unpair.1; simp;
   cases decode β n.unpair.2; refl

@[simp] theorem encode_prod_val (a b) : @encode (α × β) _ (a, b) =
  mkpair (encode a) (encode b) := rfl

end prod

section subtype
open subtype decidable
variables {P : α → Prop} [encA : encodable α] [decP : decidable_pred P]
include encA

/-- Explicit encoding function for a decidable subtype of an encodable type -/
def encode_subtype : {a : α // P a} → ℕ
| ⟨v, h⟩ := encode v

include decP

/-- Explicit decoding function for a decidable subtype of an encodable type -/
def decode_subtype (v : ℕ) : option {a : α // P a} :=
(decode α v).bind $ λ a,
if h : P a then some ⟨a, h⟩ else none

/-- A decidable subtype of an encodable type is encodable. -/
instance subtype : encodable {a : α // P a} :=
⟨encode_subtype, decode_subtype,
 λ ⟨v, h⟩, by simp [encode_subtype, decode_subtype, encodek, h]⟩

lemma subtype.encode_eq (a : subtype P) : encode a = encode a.val :=
by cases a; refl

end subtype

instance fin (n) : encodable (fin n) :=
of_equiv _ (equiv.fin_equiv_subtype _)

instance int : encodable ℤ :=
of_equiv _ equiv.int_equiv_nat

instance pnat : encodable ℕ+ :=
of_equiv _ equiv.pnat_equiv_nat

/-- The lift of an encodable type is encodable. -/
instance ulift [encodable α] : encodable (ulift α) :=
of_equiv _ equiv.ulift

/-- The lift of an encodable type is encodable. -/
instance plift [encodable α] : encodable (plift α) :=
of_equiv _ equiv.plift

/-- If `β` is encodable and there is an injection `f : α → β`, then `α` is encodable as well. -/
noncomputable def of_inj [encodable β] (f : α → β) (hf : injective f) : encodable α :=
of_left_injection f (partial_inv f) (λ x, (partial_inv_of_injective hf _ _).2 rfl)

end encodable

section ulower
local attribute [instance, priority 100] encodable.decidable_range_encode

/-- `ulower α : Type` is an equivalent type in the lowest universe, given `encodable α`. -/
@[derive decidable_eq, derive encodable]
def ulower (α : Type*) [encodable α] : Type :=
set.range (encodable.encode : α → ℕ)

end ulower

namespace ulower
variables (α : Type*) [encodable α]

/-- The equivalence between the encodable type `α` and `ulower α : Type`. -/
def equiv : α ≃ ulower α :=
encodable.equiv_range_encode α

variables {α}

/-- Lowers an `a : α` into `ulower α`. -/
def down (a : α) : ulower α := equiv α a

instance [inhabited α] : inhabited (ulower α) := ⟨down (default _)⟩

/-- Lifts an `a : ulower α` into `α`. -/
def up (a : ulower α) : α := (equiv α).symm a

@[simp] lemma down_up {a : ulower α} : down a.up = a := equiv.right_inv _ _
@[simp] lemma up_down {a : α} : (down a).up = a := equiv.left_inv _ _

@[simp] lemma up_eq_up {a b : ulower α} : a.up = b.up ↔ a = b :=
equiv.apply_eq_iff_eq _

@[simp] lemma down_eq_down {a b : α} : down a = down b ↔ a = b :=
equiv.apply_eq_iff_eq _

@[ext] protected lemma ext {a b : ulower α} : a.up = b.up → a = b :=
up_eq_up.1

end ulower

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) :
  p (choose ex) :=
-/

namespace encodable
section find_a
variables {α : Type*} (p : α → Prop) [encodable α] [decidable_pred p]

private def good : option α → Prop
| (some a) := p a
| none     := false

private def decidable_good : decidable_pred (good p)
| n := by cases n; unfold good; apply_instance
local attribute [instance] decidable_good

open encodable
variable {p}

/-- Constructive choice function for a decidable subtype of an encodable type. -/
def choose_x (h : ∃ x, p x) : {a : α // p a} :=
have ∃ n, good p (decode α n), from
let ⟨w, pw⟩ := h in ⟨encode w, by simp [good, encodek, pw]⟩,
match _, nat.find_spec this : ∀ o, good p o → {a // p a} with
| some a, h := ⟨a, h⟩
end

/-- Constructive choice function for a decidable predicate over an encodable type. -/
def choose (h : ∃ x, p x) : α := (choose_x h).1

lemma choose_spec (h : ∃ x, p x) : p (choose h) := (choose_x h).2

end find_a

theorem axiom_of_choice {α : Type*} {β : α → Type*} {R : Π x, β x → Prop}
  [Π a, encodable (β a)] [∀ x y, decidable (R x y)]
  (H : ∀ x, ∃ y, R x y) : ∃ f : Π a, β a, ∀ x, R x (f x) :=
⟨λ x, choose (H x), λ x, choose_spec (H x)⟩

theorem skolem {α : Type*} {β : α → Type*} {P : Π x, β x → Prop}
  [c : Π a, encodable (β a)] [d : ∀ x y, decidable (P x y)] :
  (∀ x, ∃ y, P x y) ↔ ∃ f : Π a, β a, (∀ x, P x (f x)) :=
⟨axiom_of_choice, λ ⟨f, H⟩ x, ⟨_, H x⟩⟩

/-
There is a total ordering on the elements of an encodable type, induced by the map to ℕ.
-/

/-- The `encode` function, viewed as an embedding. -/
def encode' (α) [encodable α] : α ↪ ℕ :=
⟨encodable.encode, encodable.encode_injective⟩

instance {α} [encodable α] : is_trans _ (encode' α ⁻¹'o (≤)) :=
(rel_embedding.preimage _ _).is_trans
instance {α} [encodable α] : is_antisymm _ (encodable.encode' α ⁻¹'o (≤)) :=
(rel_embedding.preimage _ _).is_antisymm
instance {α} [encodable α] : is_total _ (encodable.encode' α ⁻¹'o (≤)) :=
(rel_embedding.preimage _ _).is_total

end encodable

namespace directed

open encodable

variables {α : Type*} {β : Type*} [encodable α] [inhabited α]

/-- Given a `directed r` function `f : α → β` defined on an encodable inhabited type,
construct a noncomputable sequence such that `r (f (x n)) (f (x (n + 1)))`
and `r (f a) (f (x (encode a + 1))`. -/
protected noncomputable def sequence {r : β → β → Prop} (f : α → β) (hf : directed r f) : ℕ → α
| 0       := default α
| (n + 1) :=
  let p := sequence n in
  match decode α n with
  | none     := classical.some (hf p p)
  | (some a) := classical.some (hf p a)
  end

lemma sequence_mono_nat {r : β → β → Prop} {f : α → β} (hf : directed r f) (n : ℕ) :
  r (f (hf.sequence f n)) (f (hf.sequence f (n+1))) :=
begin
  dsimp [directed.sequence],
  generalize eq : hf.sequence f n = p,
  cases h : decode α n with a,
  { exact (classical.some_spec (hf p p)).1 },
  { exact (classical.some_spec (hf p a)).1 }
end

lemma rel_sequence {r : β → β → Prop} {f : α → β} (hf : directed r f) (a : α) :
  r (f a) (f (hf.sequence f (encode a + 1))) :=
begin
  simp only [directed.sequence, encodek],
  exact (classical.some_spec (hf _ a)).2
end

variables [preorder β] {f : α → β} (hf : directed (≤) f)

lemma sequence_mono : monotone (f ∘ (hf.sequence f)) :=
monotone_of_monotone_nat $ hf.sequence_mono_nat

lemma le_sequence (a : α) : f a ≤ f (hf.sequence f (encode a + 1)) :=
hf.rel_sequence a

end directed

section quotient
open encodable quotient
variables {α : Type*} {s : setoid α} [@decidable_rel α (≈)] [encodable α]

/-- Representative of an equivalence class. This is a computable version of `quot.out` for a setoid
on an encodable type. -/
def quotient.rep (q : quotient s) : α :=
choose (exists_rep q)

theorem quotient.rep_spec (q : quotient s) : ⟦q.rep⟧ = q :=
choose_spec (exists_rep q)

/-- The quotient of an encodable space by a decidable equivalence relation is encodable. -/
def encodable_quotient : encodable (quotient s) :=
⟨λ q, encode q.rep,
 λ n, quotient.mk <$> decode α n,
 by rintros ⟨l⟩; rw encodek; exact congr_arg some ⟦l⟧.rep_spec⟩

end quotient
