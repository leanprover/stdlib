/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Finite types.
-/
import data.finset algebra.big_operators data.array.lemmas data.vector2
universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class fintype (α : Type*) :=
(elems : finset α)
(complete : ∀ x : α, x ∈ elems)

namespace finset
variable [fintype α]

/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : finset α := fintype.elems α

@[simp] theorem mem_univ (x : α) : x ∈ (univ : finset α) :=
fintype.complete x

@[simp] theorem mem_univ_val : ∀ x, x ∈ (univ : finset α).1 := mem_univ

theorem subset_univ (s : finset α) : s ⊆ univ := λ a _, mem_univ a

theorem eq_univ_iff_forall {s : finset α} : s = univ ↔ ∀ x, x ∈ s :=
by simp [ext]

end finset

open finset function

namespace fintype

instance decidable_pi_fintype {α} {β : α → Type*} [fintype α] [∀a, decidable_eq (β a)] :
  decidable_eq (Πa, β a) :=
assume f g, decidable_of_iff (∀ a ∈ fintype.elems α, f a = g a)
  (by simp [function.funext_iff, fintype.complete])

instance decidable_forall_fintype [fintype α] {p : α → Prop} [decidable_pred p] :
  decidable (∀ a, p a) :=
decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)

instance decidable_exists_fintype [fintype α] {p : α → Prop} [decidable_pred p] :
  decidable (∃ a, p a) :=
decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)

instance decidable_eq_equiv_fintype [fintype α] [decidable_eq β] :
  decidable_eq (α ≃ β) :=
λ a b, decidable_of_iff (a.1 = b.1) ⟨λ h, equiv.ext _ _ (congr_fun h), congr_arg _⟩

/-- Construct a proof of `fintype α` from a universal multiset -/
def of_multiset [decidable_eq α] (s : multiset α)
  (H : ∀ x : α, x ∈ s) : fintype α :=
⟨s.to_finset, by simpa using H⟩

/-- Construct a proof of `fintype α` from a universal list -/
def of_list [decidable_eq α] (l : list α)
  (H : ∀ x : α, x ∈ l) : fintype α :=
⟨l.to_finset, by simpa using H⟩

theorem exists_univ_list (α) [fintype α] :
  ∃ l : list α, l.nodup ∧ ∀ x : α, x ∈ l :=
let ⟨l, e⟩ := quotient.exists_rep (@univ α _).1 in
by have := and.intro univ.2 mem_univ_val;
   exact ⟨_, by rwa ← e at this⟩

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [fintype α] : ℕ := (@univ α _).card

/-- There is (computably) a bijection between `α` and `fin n` where
  `n = card α`. Since it is not unique, and depends on which permutation
  of the universe list is used, the bijection is wrapped in `trunc` to
  preserve computability.  -/
def equiv_fin (α) [fintype α] [decidable_eq α] : trunc (α ≃ fin (card α)) :=
by unfold card finset.card; exact
quot.rec_on_subsingleton (@univ α _).1
  (λ l (h : ∀ x:α, x ∈ l) (nd : l.nodup), trunc.mk
   ⟨λ a, ⟨_, list.index_of_lt_length.2 (h a)⟩,
    λ i, l.nth_le i.1 i.2,
    λ a, by simp,
    λ ⟨i, h⟩, fin.eq_of_veq $ list.nodup_iff_nth_le_inj.1 nd _ _
      (list.index_of_lt_length.2 (list.nth_le_mem _ _ _)) h $ by simp⟩)
  mem_univ_val univ.2

theorem exists_equiv_fin (α) [fintype α] : ∃ n, nonempty (α ≃ fin n) :=
by haveI := classical.dec_eq α; exact ⟨card α, nonempty_of_trunc (equiv_fin α)⟩

instance (α : Type*) : subsingleton (fintype α) :=
⟨λ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩, by congr; simp [finset.ext, h₁, h₂]⟩

protected def subtype {p : α → Prop} (s : finset α)
  (H : ∀ x : α, x ∈ s ↔ p x) : fintype {x // p x} :=
⟨⟨multiset.pmap subtype.mk s.1 (λ x, (H x).1),
  multiset.nodup_pmap (λ a _ b _, congr_arg subtype.val) s.2⟩,
λ ⟨x, px⟩, multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

theorem subtype_card {p : α → Prop} (s : finset α)
  (H : ∀ x : α, x ∈ s ↔ p x) :
  @card {x // p x} (fintype.subtype s H) = s.card :=
multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : finset α)
  (H : ∀ x : α, x ∈ s ↔ p x) [fintype {x // p x}] :
  card {x // p x} = s.card :=
by rw ← subtype_card s H; congr

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def of_bijective [fintype α] (f : α → β) (H : function.bijective f) : fintype β :=
⟨univ.map ⟨f, H.1⟩,
λ b, let ⟨a, e⟩ := H.2 b in e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def of_surjective [fintype α] [decidable_eq β] (f : α → β) (H : function.surjective f) : fintype β :=
⟨univ.image f, λ b, let ⟨a, e⟩ := H b in e ▸ mem_image_of_mem _ (mem_univ _)⟩

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def of_equiv (α : Type*) [fintype α] (f : α ≃ β) : fintype β := of_bijective _ f.bijective

theorem of_equiv_card [fintype α] (f : α ≃ β) :
  @card β (of_equiv α f) = card α :=
multiset.card_map _ _

theorem card_congr {α β} [fintype α] [fintype β] (f : α ≃ β) : card α = card β :=
by rw ← of_equiv_card f; congr

theorem card_eq {α β} [F : fintype α] [G : fintype β] : card α = card β ↔ nonempty (α ≃ β) :=
⟨λ e, match F, G, e with ⟨⟨s, nd⟩, h⟩, ⟨⟨s', nd'⟩, h'⟩, e' := begin
  change multiset.card s = multiset.card s' at e',
  revert nd nd' h h' e',
  refine quotient.induction_on₂ s s' (λ l₁ l₂
    (nd₁ : l₁.nodup) (nd₂ : l₂.nodup)
    (h₁ : ∀ x, x ∈ l₁) (h₂ : ∀ x, x ∈ l₂)
    (e' : l₁.length = l₂.length), _),
  haveI := classical.dec_eq α,
  refine ⟨equiv.of_bijective ⟨_, _⟩⟩,
  { refine λ a, l₂.nth_le (l₁.index_of a) _,
    rw ← e', exact list.index_of_lt_length.2 (h₁ a) },
  { intros a b h, simpa [h₁] using congr_arg l₁.nth
      (list.nodup_iff_nth_le_inj.1 nd₂ _ _ _ _ h) },
  { have := classical.dec_eq β,
    refine λ b, ⟨l₁.nth_le (l₂.index_of b) _, _⟩,
    { rw e', exact list.index_of_lt_length.2 (h₂ b) },
    { simp [nd₁] } }
end end, λ ⟨f⟩, card_congr f⟩

end fintype

instance (n : ℕ) : fintype (fin n) :=
⟨⟨list.pmap fin.mk (list.range n) (λ a, list.mem_range.1),
  list.nodup_pmap (λ a _ b _, congr_arg fin.val) (list.nodup_range _)⟩,
λ ⟨m, h⟩, list.mem_pmap.2 ⟨m, list.mem_range.2 h, rfl⟩⟩

@[simp] theorem fintype.card_fin (n : ℕ) : fintype.card (fin n) = n :=
by rw [fin.fintype]; simp [fintype.card, card, univ]

instance : fintype empty := ⟨∅, empty.rec _⟩

@[simp] theorem fintype.univ_empty : @univ empty _ = ∅ := rfl

@[simp] theorem fintype.card_empty : fintype.card empty = 0 := rfl

instance : fintype unit := ⟨⟨()::0, by simp⟩, λ ⟨⟩, by simp⟩

@[simp] theorem fintype.univ_unit : @univ unit _ = {()} := rfl

@[simp] theorem fintype.card_unit : fintype.card unit = 1 := rfl

instance : fintype bool := ⟨⟨tt::ff::0, by simp⟩, λ x, by cases x; simp⟩

@[simp] theorem fintype.univ_bool : @univ bool _ = {ff, tt} := rfl

@[simp] theorem fintype.card_bool : fintype.card bool = 2 := rfl

def finset.insert_none (s : finset α) : finset (option α) :=
⟨none :: s.1.map some, multiset.nodup_cons.2
  ⟨by simp, multiset.nodup_map (λ a b, option.some.inj) s.2⟩⟩

@[simp] theorem finset.mem_insert_none {s : finset α} : ∀ {o : option α},
  o ∈ s.insert_none ↔ ∀ a ∈ o, a ∈ s
| none     := iff_of_true (multiset.mem_cons_self _ _) (λ a h, by cases h)
| (some a) := multiset.mem_cons.trans $ by simp; refl

theorem finset.some_mem_insert_none {s : finset α} {a : α} :
  some a ∈ s.insert_none ↔ a ∈ s := by simp

instance {α : Type*} [fintype α] : fintype (option α) :=
⟨univ.insert_none, λ a, by simp⟩

@[simp] theorem fintype.card_option {α : Type*} [fintype α] :
  fintype.card (option α) = fintype.card α + 1 :=
(multiset.card_cons _ _).trans (by rw multiset.card_map; refl)

instance {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] : fintype (sigma β) :=
⟨univ.sigma (λ _, univ), λ ⟨a, b⟩, by simp⟩

@[simp] theorem fintype.card_sigma {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] :
  fintype.card (sigma β) = univ.sum (λ a, fintype.card (β a)) :=
card_sigma _ _

instance (α β : Type*) [fintype α] [fintype β] : fintype (α × β) :=
⟨univ.product univ, λ ⟨a, b⟩, by simp⟩

@[simp] theorem fintype.card_prod (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α × β) = fintype.card α * fintype.card β :=
card_product _ _

def fintype.fintype_prod_left {α β} [decidable_eq α] [fintype (α × β)] [nonempty β] : fintype α :=
⟨(fintype.elems (α × β)).image prod.fst,
  assume a, let ⟨b⟩ := ‹nonempty β› in by simp; exact ⟨b, fintype.complete _⟩⟩

def fintype.fintype_prod_right {α β} [decidable_eq β] [fintype (α × β)] [nonempty α] : fintype β :=
⟨(fintype.elems (α × β)).image prod.snd,
  assume b, let ⟨a⟩ := ‹nonempty α› in by simp; exact ⟨a, fintype.complete _⟩⟩

instance (α : Type*) [fintype α] : fintype (ulift α) :=
fintype.of_equiv _ equiv.ulift.symm

@[simp] theorem fintype.card_ulift (α : Type*) [fintype α] :
  fintype.card (ulift α) = fintype.card α :=
fintype.of_equiv_card _

instance (α : Type u) (β : Type v) [fintype α] [fintype β] : fintype (α ⊕ β) :=
@fintype.of_equiv _ _ (@sigma.fintype _
    (λ b, cond b (ulift α) (ulift.{(max u v) v} β)) _
    (λ b, by cases b; apply ulift.fintype))
  ((equiv.sum_equiv_sigma_bool _ _).symm.trans
    (equiv.sum_congr equiv.ulift equiv.ulift))

@[simp] theorem fintype.card_sum (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α ⊕ β) = fintype.card α + fintype.card β :=
by rw [sum.fintype, fintype.of_equiv_card]; simp

lemma fintype.card_le_of_injective [fintype α] [fintype β] (f : α → β)
  (hf : function.injective f) : fintype.card α ≤ fintype.card β :=
by haveI := classical.prop_decidable; exact
finset.card_le_card_of_inj_on f (λ _ _, finset.mem_univ _) (λ _ _ _ _ h, hf h)

lemma fintype.card_eq_one_iff [fintype α] : fintype.card α = 1 ↔ (∃ x : α, ∀ y, y = x) :=
by rw [← fintype.card_unit, fintype.card_eq];
exact ⟨λ ⟨a⟩, ⟨a.symm unit.star, λ y, a.bijective.1 (subsingleton.elim _ _)⟩,
λ ⟨x, hx⟩, ⟨⟨λ _, unit.star, λ _, x, λ _, (hx _).trans (hx _).symm,
    λ _, subsingleton.elim _ _⟩⟩⟩

lemma fintype.card_eq_zero_iff [fintype α] : fintype.card α = 0 ↔ (α → false) :=
⟨λ h a, have e : α ≃ empty := classical.choice (fintype.card_eq.1 (by simp [h])), (e a).elim,
λ h, have e : α ≃ empty := ⟨λ a, (h a).elim, λ a, a.elim, λ a, (h a).elim, λ a, a.elim⟩,
  by simp [fintype.card_congr e]⟩

lemma fintype.card_pos_iff [fintype α] : 0 < fintype.card α ↔ nonempty α :=
⟨λ h, classical.by_contradiction (λ h₁,
  have fintype.card α = 0 := fintype.card_eq_zero_iff.2 (λ a, h₁ ⟨a⟩),
  lt_irrefl 0 $ by rwa this at h),
λ ⟨a⟩, nat.pos_of_ne_zero (mt fintype.card_eq_zero_iff.1 (λ h, h a))⟩

lemma fintype.card_le_one_iff [fintype α] : fintype.card α ≤ 1 ↔ (∀ a b : α, a = b) :=
let n := fintype.card α in
have hn : n = fintype.card α := rfl,
match n, hn with
| 0 := λ ha, ⟨λ h, λ a, (fintype.card_eq_zero_iff.1 ha.symm a).elim, λ _, ha ▸ nat.le_succ _⟩
| 1 := λ ha, ⟨λ h, λ a b, let ⟨x, hx⟩ := fintype.card_eq_one_iff.1 ha.symm in
  by rw [hx a, hx b],
    λ _, ha ▸ le_refl _⟩
| (n+2) := λ ha, ⟨λ h, by rw ← ha at h; exact absurd h dec_trivial,
  (λ h, fintype.card_unit ▸ fintype.card_le_of_injective (λ _, ())
    (λ _ _ _, h _ _))⟩
end

lemma fintype.injective_iff_surjective [fintype α] {f : α → α} : injective f ↔ surjective f :=
by haveI := classical.prop_decidable; exact
have ∀ {f : α → α}, injective f → surjective f,
from λ f hinj x,
  have h₁ : image f univ = univ := eq_of_subset_of_card_le (subset_univ _)
    ((card_image_of_injective univ hinj).symm ▸ le_refl _),
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ _,
  exists_of_bex (mem_image.1 h₂),
⟨this, λ hsurj, injective_of_has_left_inverse ⟨surj_inv hsurj,
    left_inverse_of_surjective_of_right_inverse (this (injective_surj_inv hsurj))
      (right_inverse_surj_inv hsurj)⟩⟩

lemma fintype.injective_iff_surjective_of_equiv [fintype α] {f : α → β} (e : α ≃ β) :
  injective f ↔ surjective f :=
have injective (e.symm ∘ f) ↔ surjective (e.symm ∘ f), from fintype.injective_iff_surjective,
⟨λ hinj, by simpa [function.comp] using
  surjective_comp e.bijective.2 (this.1 (injective_comp e.symm.bijective.1 hinj)),
λ hsurj, by simpa [function.comp] using
  injective_comp e.bijective.1 (this.2 (surjective_comp e.symm.bijective.2 hsurj))⟩

instance list.subtype.fintype [decidable_eq α] (l : list α) : fintype {x // x ∈ l} :=
fintype.of_list l.attach l.mem_attach

instance multiset.subtype.fintype [decidable_eq α] (s : multiset α) : fintype {x // x ∈ s} :=
fintype.of_multiset s.attach s.mem_attach

instance finset.subtype.fintype (s : finset α) : fintype {x // x ∈ s} :=
⟨s.attach, s.mem_attach⟩

instance finset_coe.fintype (s : finset α) : fintype (↑s : set α) :=
finset.subtype.fintype s

instance plift.fintype (p : Prop) [decidable p] : fintype (plift p) :=
⟨if h : p then finset.singleton ⟨h⟩ else ∅, λ ⟨h⟩, by simp [h]⟩

instance Prop.fintype : fintype Prop :=
⟨⟨true::false::0, by simp [true_ne_false]⟩,
 classical.cases (by simp) (by simp)⟩

def set_fintype {α} [fintype α] (s : set α) [decidable_pred s] : fintype s :=
fintype.subtype (univ.filter (∈ s)) (by simp)

instance pi.fintype {α : Type*} {β : α → Type*}
  [fintype α] [decidable_eq α] [∀a, fintype (β a)] : fintype (Πa, β a) :=
@fintype.of_equiv _ _
  ⟨univ.pi $ λa:α, @univ (β a) _,
    λ f, finset.mem_pi.2 $ λ a ha, mem_univ _⟩
  ⟨λ f a, f a (mem_univ _), λ f a _, f a, λ f, rfl, λ f, rfl⟩

@[simp] lemma fintype.card_pi {β : α → Type*} [fintype α] [decidable_eq α]
  [f : Π a, fintype (β a)] : fintype.card (Π a, β a) = univ.prod (λ a, fintype.card (β a)) :=
by letI f' : fintype (Πa∈univ, β a) :=
  ⟨(univ.pi $ λa, univ), assume f, finset.mem_pi.2 $ assume a ha, mem_univ _⟩;
exact calc fintype.card (Π a, β a) = fintype.card (Π a ∈ univ, β a) : fintype.card_congr
  ⟨λ f a ha, f a, λ f a, f a (mem_univ a), λ _, rfl, λ _, rfl⟩
... = univ.prod (λ a, fintype.card (β a)) : finset.card_pi _ _

@[simp] lemma fintype.card_fun [fintype α] [decidable_eq α] [fintype β] :
  fintype.card (α → β) = fintype.card β ^ fintype.card α :=
by rw [fintype.card_pi, finset.prod_const, nat.pow_eq_pow]; refl

instance d_array.fintype {n : ℕ} {α : fin n → Type*}
  [∀n, fintype (α n)] : fintype (d_array n α) :=
fintype.of_equiv _ (equiv.d_array_equiv_fin _).symm

instance array.fintype {n : ℕ} {α : Type*} [fintype α] : fintype (array n α) :=
d_array.fintype

instance vector.fintype {α : Type*} [fintype α] {n : ℕ} : fintype (vector α n) :=
fintype.of_equiv _ (equiv.vector_equiv_fin _ _).symm

instance quotient.fintype [fintype α] (s : setoid α)
  [decidable_rel ((≈) : α → α → Prop)] : fintype (quotient s) :=
fintype.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

instance finset.fintype [fintype α] : fintype (finset α) :=
⟨univ.powerset, λ x, finset.mem_powerset.2 (finset.subset_univ _)⟩

instance subtype.fintype [fintype α] (p : α → Prop) [decidable_pred p] : fintype {x // p x} :=
set_fintype _

instance set.fintype [fintype α] [decidable_eq α] : fintype (set α) :=
pi.fintype

def quotient.fin_choice_aux {ι : Type*} [decidable_eq ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)] :
  ∀ (l : list ι), (∀ i ∈ l, quotient (S i)) → @quotient (Π i ∈ l, α i) (by apply_instance)
| []     f := ⟦λ i, false.elim⟧
| (i::l) f := begin
  refine quotient.lift_on₂ (f i (list.mem_cons_self _ _))
    (quotient.fin_choice_aux l (λ j h, f j (list.mem_cons_of_mem _ h)))
    _ _,
  exact λ a l, ⟦λ j h,
    if e : j = i then by rw e; exact a else
    l _ (h.resolve_left e)⟧,
  refine λ a₁ l₁ a₂ l₂ h₁ h₂, quotient.sound (λ j h, _),
  by_cases e : j = i; simp [e],
  { subst j, exact h₁ },
  { exact h₂ _ _ }
end

theorem quotient.fin_choice_aux_eq {ι : Type*} [decidable_eq ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)] :
  ∀ (l : list ι) (f : ∀ i ∈ l, α i), quotient.fin_choice_aux l (λ i h, ⟦f i h⟧) = ⟦f⟧
| []     f := quotient.sound (λ i h, h.elim)
| (i::l) f := begin
  simp [quotient.fin_choice_aux, quotient.fin_choice_aux_eq l],
  refine quotient.sound (λ j h, _),
  by_cases e : j = i; simp [e],
  subst j, refl
end

def quotient.fin_choice {ι : Type*} [fintype ι] [decidable_eq ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)]
  (f : ∀ i, quotient (S i)) : @quotient (Π i, α i) (by apply_instance) :=
quotient.lift_on (@quotient.rec_on _ _ (λ l : multiset ι,
    @quotient (Π i ∈ l, α i) (by apply_instance))
    finset.univ.1
    (λ l, quotient.fin_choice_aux l (λ i _, f i))
    (λ a b h, begin
      have := λ a, quotient.fin_choice_aux_eq a (λ i h, quotient.out (f i)),
      simp [quotient.out_eq] at this,
      simp [this],
      let g := λ a:multiset ι, ⟦λ (i : ι) (h : i ∈ a), quotient.out (f i)⟧,
      refine eq_of_heq ((eq_rec_heq _ _).trans (_ : g a == g b)),
      congr' 1, exact quotient.sound h,
    end))
  (λ f, ⟦λ i, f i (finset.mem_univ _)⟧)
  (λ a b h, quotient.sound $ λ i, h _ _)


theorem quotient.fin_choice_eq {ι : Type*} [fintype ι] [decidable_eq ι]
  {α : ι → Type*} [∀ i, setoid (α i)]
  (f : ∀ i, α i) : quotient.fin_choice (λ i, ⟦f i⟧) = ⟦f⟧ :=
begin
  let q, swap, change quotient.lift_on q _ _ = _,
  have : q = ⟦λ i h, f i⟧,
  { dsimp [q],
    exact quotient.induction_on
      (@finset.univ ι _).1 (λ l, quotient.fin_choice_aux_eq _ _) },
  simp [this], exact setoid.refl _
end