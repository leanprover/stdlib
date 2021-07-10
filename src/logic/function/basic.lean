/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import logic.basic
import data.option.defs

/-!
# Miscellaneous function constructions and lemmas
-/

universes u v w

namespace function

section
variables {α β γ : Sort*} {f : α → β}

/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `function.eval x : (Π x, β x) → β x`. -/
@[reducible] def eval {β : α → Sort*} (x : α) (f : Π x, β x) : β x := f x

@[simp] lemma eval_apply {β : α → Sort*} (x : α) (f : Π x, β x) : eval x f = f x := rfl

lemma comp_apply {α : Sort u} {β : Sort v} {φ : Sort w} (f : β → φ) (g : α → β) (a : α) :
  (f ∘ g) a = f (g a) := rfl

lemma const_def {y : β} : (λ x : α, y) = const α y := rfl

@[simp] lemma const_apply {y : β} {x : α} : const α y x = y := rfl

@[simp] lemma const_comp {f : α → β} {c : γ} : const β c ∘ f = const α c := rfl

@[simp] lemma comp_const {f : β → γ} {b : β} : f ∘ const α b = const α (f b) := rfl

lemma id_def : @id α = λ x, x := rfl

lemma hfunext {α α': Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : Πa, β a} {f' : Πa, β' a}
  (hα : α = α') (h : ∀a a', a == a' → f a == f' a') : f == f' :=
begin
  subst hα,
  have : ∀a, f a == f' a,
  { intro a, exact h a a (heq.refl a) },
  have : β = β',
  { funext a, exact type_eq_of_heq (this a) },
  subst this,
  apply heq_of_eq,
  funext a,
  exact eq_of_heq (this a)
end

lemma funext_iff {β : α → Sort*} {f₁ f₂ : Π (x : α), β x} : f₁ = f₂ ↔ (∀a, f₁ a = f₂ a) :=
iff.intro (assume h a, h ▸ rfl) funext

protected lemma bijective.injective {f : α → β} (hf : bijective f) : injective f := hf.1
protected lemma bijective.surjective {f : α → β} (hf : bijective f) : surjective f := hf.2

theorem injective.eq_iff (I : injective f) {a b : α} :
  f a = f b ↔ a = b :=
⟨@I _ _, congr_arg f⟩

theorem injective.eq_iff' (I : injective f) {a b : α} {c : β} (h : f b = c) :
  f a = c ↔ a = b :=
h ▸ I.eq_iff

lemma injective.ne (hf : injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
mt (assume h, hf h)

lemma injective.ne_iff (hf : injective f) {x y : α} : f x ≠ f y ↔ x ≠ y :=
⟨mt $ congr_arg f, hf.ne⟩

lemma injective.ne_iff' (hf : injective f) {x y : α} {z : β} (h : f y = z) :
  f x ≠ z ↔ x ≠ y :=
h ▸ hf.ne_iff

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
def injective.decidable_eq [decidable_eq β] (I : injective f) : decidable_eq α :=
λ a b, decidable_of_iff _ I.eq_iff

lemma injective.of_comp {g : γ → α} (I : injective (f ∘ g)) : injective g :=
λ x y h, I $ show f (g x) = f (g y), from congr_arg f h

lemma injective.of_comp_iff {f : α → β} (hf : injective f) (g : γ → α) :
  injective (f ∘ g) ↔ injective g :=
⟨injective.of_comp, hf.comp⟩

lemma injective.of_comp_iff' (f : α → β) {g : γ → α} (hg : bijective g) :
  injective (f ∘ g) ↔ injective f :=
⟨ λ h x y, let ⟨x', hx⟩ := hg.surjective x, ⟨y', hy⟩ := hg.surjective y in
    hx ▸ hy ▸ λ hf, h hf ▸ rfl,
  λ h, h.comp hg.injective⟩

lemma injective_of_subsingleton [subsingleton α] (f : α → β) :
  injective f :=
λ a b ab, subsingleton.elim _ _

lemma injective.dite (p : α → Prop) [decidable_pred p]
  {f : {a : α // p a} → β} {f' : {a : α // ¬ p a} → β}
  (hf : injective f) (hf' : injective f')
  (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
  function.injective (λ x, if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) :=
λ x₁ x₂ h, begin
  dsimp only at h,
  by_cases h₁ : p x₁; by_cases h₂ : p x₂,
  { rw [dif_pos h₁, dif_pos h₂] at h, injection (hf h), },
  { rw [dif_pos h₁, dif_neg h₂] at h, exact (im_disj h).elim, },
  { rw [dif_neg h₁, dif_pos h₂] at h, exact (im_disj h.symm).elim, },
  { rw [dif_neg h₁, dif_neg h₂] at h, injection (hf' h), },
end

lemma surjective.of_comp {g : γ → α} (S : surjective (f ∘ g)) : surjective f :=
λ y, let ⟨x, h⟩ := S y in ⟨g x, h⟩

lemma surjective.of_comp_iff (f : α → β) {g : γ → α} (hg : surjective g) :
  surjective (f ∘ g) ↔ surjective f :=
⟨surjective.of_comp, λ h, h.comp hg⟩

lemma surjective.of_comp_iff' {f : α → β} (hf : bijective f) (g : γ → α) :
  surjective (f ∘ g) ↔ surjective g :=
⟨λ h x, let ⟨x', hx'⟩ := h (f x) in ⟨x', hf.injective hx'⟩, hf.surjective.comp⟩

instance decidable_eq_pfun (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, decidable_eq (α hp)] : decidable_eq (Π hp, α hp)
| f g := decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

theorem surjective.forall {f : α → β} (hf : surjective f) {p : β → Prop} :
  (∀ y, p y) ↔ ∀ x, p (f x) :=
⟨λ h x, h (f x), λ h y, let ⟨x, hx⟩ := hf y in hx ▸ h x⟩

theorem surjective.forall₂ {f : α → β} (hf : surjective f) {p : β → β → Prop} :
  (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
hf.forall.trans $ forall_congr $ λ x, hf.forall

theorem surjective.forall₃ {f : α → β} (hf : surjective f) {p : β → β → β → Prop} :
  (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.forall.trans $ forall_congr $ λ x, hf.forall₂

theorem surjective.exists {f : α → β} (hf : surjective f) {p : β → Prop} :
  (∃ y, p y) ↔ ∃ x, p (f x) :=
⟨λ ⟨y, hy⟩, let ⟨x, hx⟩ := hf y in ⟨x, hx.symm ▸ hy⟩, λ ⟨x, hx⟩, ⟨f x, hx⟩⟩

theorem surjective.exists₂ {f : α → β} (hf : surjective f) {p : β → β → Prop} :
  (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
hf.exists.trans $ exists_congr $ λ x, hf.exists

theorem surjective.exists₃ {f : α → β} (hf : surjective f) {p : β → β → β → Prop} :
  (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.exists.trans $ exists_congr $ λ x, hf.exists₂

lemma bijective_iff_exists_unique (f : α → β) : bijective f ↔
  ∀ b : β, ∃! (a : α), f a = b :=
⟨ λ hf b, let ⟨a, ha⟩ := hf.surjective b in ⟨a, ha, λ a' ha', hf.injective (ha'.trans ha.symm)⟩,
  λ he, ⟨
    λ a a' h, unique_of_exists_unique (he (f a')) h rfl,
    λ b, exists_of_exists_unique (he b) ⟩⟩

/-- Shorthand for using projection notation with `function.bijective_iff_exists_unique`. -/
lemma bijective.exists_unique {f : α → β} (hf : bijective f) (b : β) : ∃! (a : α), f a = b :=
(bijective_iff_exists_unique f).mp hf b

lemma bijective.of_comp_iff (f : α → β) {g : γ → α} (hg : bijective g) :
  bijective (f ∘ g) ↔ bijective f :=
and_congr (injective.of_comp_iff' _ hg) (surjective.of_comp_iff _ hg.surjective)

lemma bijective.of_comp_iff' {f : α → β} (hf : bijective f) (g : γ → α) :
  function.bijective (f ∘ g) ↔ function.bijective g :=
and_congr (injective.of_comp_iff hf.injective _) (surjective.of_comp_iff' hf _)

/-- **Cantor's diagonal argument** implies that there are no surjective functions from `α`
to `set α`. -/
theorem cantor_surjective {α} (f : α → set α) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 $ iff_of_eq (congr_fun e D)

/-- **Cantor's diagonal argument** implies that there are no injective functions from `set α`
to `α`. -/
theorem cantor_injective {α : Type*} (f : (set α) → α) :
  ¬ function.injective f | i :=
cantor_surjective (λ a b, ∀ U, a = f U → U b) $
right_inverse.surjective (λ U, funext $ λ a, propext ⟨λ h, h U rfl, λ h' U' e, i e ▸ h'⟩)

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def is_partial_inv {α β} (f : α → β) (g : β → option α) : Prop :=
∀ x y, g y = some x ↔ f x = y

theorem is_partial_inv_left {α β} {f : α → β} {g} (H : is_partial_inv f g) (x) : g (f x) = some x :=
(H _ _).2 rfl

theorem injective_of_partial_inv {α β} {f : α → β} {g} (H : is_partial_inv f g) : injective f :=
λ a b h, option.some.inj $ ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

theorem injective_of_partial_inv_right {α β} {f : α → β} {g} (H : is_partial_inv f g)
 (x y b) (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

theorem left_inverse.comp_eq_id {f : α → β} {g : β → α} (h : left_inverse f g) : f ∘ g = id :=
funext h

theorem left_inverse_iff_comp {f : α → β} {g : β → α} : left_inverse f g ↔ f ∘ g = id :=
⟨left_inverse.comp_eq_id, congr_fun⟩

theorem right_inverse.comp_eq_id {f : α → β} {g : β → α} (h : right_inverse f g) : g ∘ f = id :=
funext h

theorem right_inverse_iff_comp {f : α → β} {g : β → α} : right_inverse f g ↔ g ∘ f = id :=
⟨right_inverse.comp_eq_id, congr_fun⟩

theorem left_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : left_inverse f g) (hh : left_inverse h i) : left_inverse (h ∘ f) (g ∘ i) :=
assume a, show h (f (g (i a))) = a, by rw [hf (i a), hh a]

theorem right_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : right_inverse f g) (hh : right_inverse h i) : right_inverse (h ∘ f) (g ∘ i) :=
left_inverse.comp hh hf

theorem left_inverse.right_inverse {f : α → β} {g : β → α} (h : left_inverse g f) :
  right_inverse f g := h

theorem right_inverse.left_inverse {f : α → β} {g : β → α} (h : right_inverse g f) :
  left_inverse f g := h

theorem left_inverse.surjective {f : α → β} {g : β → α} (h : left_inverse f g) :
  surjective f :=
h.right_inverse.surjective

theorem right_inverse.injective {f : α → β} {g : β → α} (h : right_inverse f g) :
  injective f :=
h.left_inverse.injective

theorem left_inverse.eq_right_inverse {f : α → β} {g₁ g₂ : β → α} (h₁ : left_inverse g₁ f)
  (h₂ : right_inverse g₂ f) :
  g₁ = g₂ :=
calc g₁ = g₁ ∘ f ∘ g₂ : by rw [h₂.comp_eq_id, comp.right_id]
    ... = g₂          : by rw [← comp.assoc, h₁.comp_eq_id, comp.left_id]

local attribute [instance, priority 10] classical.prop_decidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partial_inv {α β} (f : α → β) (b : β) : option α :=
if h : ∃ a, f a = b then some (classical.some h) else none

theorem partial_inv_of_injective {α β} {f : α → β} (I : injective f) :
  is_partial_inv f (partial_inv f) | a b :=
⟨λ h, if h' : ∃ a, f a = b then begin
    rw [partial_inv, dif_pos h'] at h,
    injection h with h, subst h,
    apply classical.some_spec h'
  end else by rw [partial_inv, dif_neg h'] at h; contradiction,
 λ e, e ▸ have h : ∃ a', f a' = f a, from ⟨_, rfl⟩,
   (dif_pos h).trans (congr_arg _ (I $ classical.some_spec h))⟩

theorem partial_inv_left {α β} {f : α → β} (I : injective f) : ∀ x, partial_inv f (f x) = some x :=
is_partial_inv_left (partial_inv_of_injective I)

end

section inv_fun
variables {α : Type u} [n : nonempty α] {β : Sort v} {f : α → β} {s : set α} {a : α} {b : β}
include n
local attribute [instance, priority 10] classical.prop_decidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `function.injective.inv_of_mem_range`. -/
noncomputable def inv_fun_on (f : α → β) (s : set α) (b : β) : α :=
if h : ∃a, a ∈ s ∧ f a = b then classical.some h else classical.choice n

theorem inv_fun_on_pos (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b :=
by rw [bex_def] at h; rw [inv_fun_on, dif_pos h]; exact classical.some_spec h

theorem inv_fun_on_mem (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s := (inv_fun_on_pos h).left

theorem inv_fun_on_eq (h : ∃a∈s, f a = b) : f (inv_fun_on f s b) = b := (inv_fun_on_pos h).right

theorem inv_fun_on_eq' (h : ∀ (x ∈ s) (y ∈ s), f x = f y → x = y) (ha : a ∈ s) :
  inv_fun_on f s (f a) = a :=
have ∃a'∈s, f a' = f a, from ⟨a, ha, rfl⟩,
h _ (inv_fun_on_mem this) _ ha (inv_fun_on_eq this)

theorem inv_fun_on_neg (h : ¬ ∃a∈s, f a = b) : inv_fun_on f s b = classical.choice n :=
by rw [bex_def] at h; rw [inv_fun_on, dif_neg h]

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
noncomputable def inv_fun (f : α → β) : β → α := inv_fun_on f set.univ

theorem inv_fun_eq (h : ∃a, f a = b) : f (inv_fun f b) = b :=
inv_fun_on_eq $ let ⟨a, ha⟩ := h in ⟨a, trivial, ha⟩

lemma inv_fun_neg (h : ¬ ∃ a, f a = b) : inv_fun f b = classical.choice n :=
by refine inv_fun_on_neg (mt _ h); exact assume ⟨a, _, ha⟩, ⟨a, ha⟩

theorem inv_fun_eq_of_injective_of_right_inverse {g : β → α}
  (hf : injective f) (hg : right_inverse g f) : inv_fun f = g :=
funext $ assume b,
hf begin rw [hg b], exact inv_fun_eq ⟨g b, hg b⟩ end

lemma right_inverse_inv_fun (hf : surjective f) : right_inverse (inv_fun f) f :=
assume b, inv_fun_eq $ hf b

lemma left_inverse_inv_fun (hf : injective f) : left_inverse (inv_fun f) f :=
assume b,
have f (inv_fun f (f b)) = f b,
  from inv_fun_eq ⟨b, rfl⟩,
hf this

lemma inv_fun_surjective (hf : injective f) : surjective (inv_fun f) :=
(left_inverse_inv_fun hf).surjective

lemma inv_fun_comp (hf : injective f) : inv_fun f ∘ f = id := funext $ left_inverse_inv_fun hf

end inv_fun

section inv_fun
variables {α : Type u} [i : nonempty α] {β : Sort v} {f : α → β}
include i

lemma injective.has_left_inverse (hf : injective f) : has_left_inverse f :=
⟨inv_fun f, left_inverse_inv_fun hf⟩

lemma injective_iff_has_left_inverse : injective f ↔ has_left_inverse f :=
⟨injective.has_left_inverse, has_left_inverse.injective⟩

end inv_fun

section surj_inv
variables {α : Sort u} {β : Sort v} {f : α → β}

/-- The inverse of a surjective function. (Unlike `inv_fun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surj_inv {f : α → β} (h : surjective f) (b : β) : α := classical.some (h b)

lemma surj_inv_eq (h : surjective f) (b) : f (surj_inv h b) = b := classical.some_spec (h b)

lemma right_inverse_surj_inv (hf : surjective f) : right_inverse (surj_inv hf) f :=
surj_inv_eq hf

lemma left_inverse_surj_inv (hf : bijective f) : left_inverse (surj_inv hf.2) f :=
right_inverse_of_injective_of_left_inverse hf.1 (right_inverse_surj_inv hf.2)

lemma surjective.has_right_inverse (hf : surjective f) : has_right_inverse f :=
⟨_, right_inverse_surj_inv hf⟩

lemma surjective_iff_has_right_inverse : surjective f ↔ has_right_inverse f :=
⟨surjective.has_right_inverse, has_right_inverse.surjective⟩

lemma bijective_iff_has_inverse : bijective f ↔ ∃ g, left_inverse g f ∧ right_inverse g f :=
⟨λ hf, ⟨_, left_inverse_surj_inv hf, right_inverse_surj_inv hf.2⟩,
 λ ⟨g, gl, gr⟩, ⟨gl.injective,  gr.surjective⟩⟩

lemma injective_surj_inv (h : surjective f) : injective (surj_inv h) :=
(right_inverse_surj_inv h).injective

lemma surjective_to_subsingleton [na : nonempty α] [subsingleton β] (f : α → β) :
  surjective f :=
λ y, let ⟨a⟩ := na in ⟨a, subsingleton.elim _ _⟩

end surj_inv

section update
variables {α : Sort u} {β : α → Sort v} {α' : Sort w} [decidable_eq α] [decidable_eq α']

/-- Replacing the value of a function at a given point by a given value. -/
def update (f : Πa, β a) (a' : α) (v : β a') (a : α) : β a :=
if h : a = a' then eq.rec v h.symm else f a

/-- On non-dependent functions, `function.update` can be expressed as an `ite` -/
lemma update_apply {β : Sort*} (f : α → β) (a' : α) (b : β) (a : α) :
  update f a' b a = if a = a' then b else f a :=
begin
  dunfold update,
  congr,
  funext,
  rw eq_rec_constant,
end

@[simp] lemma update_same (a : α) (v : β a) (f : Πa, β a) : update f a v a = v :=
dif_pos rfl

lemma update_injective (f : Πa, β a) (a' : α) : injective (update f a') :=
λ v v' h, have _ := congr_fun h a', by rwa [update_same, update_same] at this

@[simp] lemma update_noteq {a a' : α} (h : a ≠ a') (v : β a') (f : Πa, β a) :
  update f a' v a = f a :=
dif_neg h

lemma forall_update_iff (f : Π a, β a) {a : α} {b : β a} (p : Π a, β a → Prop) :
  (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x ≠ a, p x (f x) :=
calc (∀ x, p x (update f a b x)) ↔ ∀ x, (x = a ∨ x ≠ a) → p x (update f a b x) :
  by simp only [ne.def, classical.em, forall_prop_of_true]
... ↔ p a b ∧ ∀ x ≠ a, p x (f x) :
  by simp [or_imp_distrib, forall_and_distrib] { contextual := tt }

lemma update_eq_iff {a : α} {b : β a} {f g : Π a, β a} :
  update f a b = g ↔ b = g a ∧ ∀ x ≠ a, f x = g x :=
funext_iff.trans $ forall_update_iff _ (λ x y, y = g x)

lemma eq_update_iff {a : α} {b : β a} {f g : Π a, β a} :
  g = update f a b ↔ g a = b ∧ ∀ x ≠ a, g x = f x :=
funext_iff.trans $ forall_update_iff _ (λ x y, g x = y)

@[simp] lemma update_eq_self (a : α) (f : Πa, β a) : update f a (f a) = f :=
update_eq_iff.2 ⟨rfl, λ _ _, rfl⟩

lemma update_comp_eq_of_forall_ne' {α'} (g : Π a, β a) {f : α' → α} {i : α} (a : β i)
  (h : ∀ x, f x ≠ i) :
  (λ j, (update g i a) (f j)) = (λ j, g (f j)) :=
funext $ λ x, update_noteq (h _) _ _

/-- Non-dependent version of `function.update_comp_eq_of_forall_ne'` -/
lemma update_comp_eq_of_forall_ne {α β : Sort*} (g : α' → β) {f : α → α'} {i : α'} (a : β)
  (h : ∀ x, f x ≠ i) :
  (update g i a) ∘ f = g ∘ f :=
update_comp_eq_of_forall_ne' g a h

lemma update_comp_eq_of_injective' (g : Π a, β a) {f : α' → α} (hf : function.injective f)
  (i : α') (a : β (f i)) :
  (λ j, update g (f i) a (f j)) = update (λ i, g (f i)) i a :=
eq_update_iff.2 ⟨update_same _ _ _, λ j hj, update_noteq (hf.ne hj) _ _⟩

/-- Non-dependent version of `function.update_comp_eq_of_injective'` -/
lemma update_comp_eq_of_injective {β : Sort*} (g : α' → β) {f : α → α'}
  (hf : function.injective f) (i : α) (a : β) :
  (function.update g (f i) a) ∘ f = function.update (g ∘ f) i a :=
update_comp_eq_of_injective' g hf i a

lemma apply_update {ι : Sort*} [decidable_eq ι] {α β : ι → Sort*}
  (f : Π i, α i → β i) (g : Π i, α i) (i : ι) (v : α i) (j : ι) :
  f j (update g i v j) = update (λ k, f k (g k)) i (f i v) j :=
begin
  by_cases h : j = i,
  { subst j, simp },
  { simp [h] }
end

lemma comp_update {α' : Sort*} {β : Sort*} (f : α' → β) (g : α → α') (i : α) (v : α') :
  f ∘ (update g i v) = update (f ∘ g) i (f v) :=
funext $ apply_update _ _ _ _

theorem update_comm {α} [decidable_eq α] {β : α → Sort*}
  {a b : α} (h : a ≠ b) (v : β a) (w : β b) (f : Πa, β a) :
  update (update f a v) b w = update (update f b w) a v :=
begin
  funext c, simp only [update],
  by_cases h₁ : c = b; by_cases h₂ : c = a; try {simp [h₁, h₂]},
  cases h (h₂.symm.trans h₁),
end

@[simp] theorem update_idem {α} [decidable_eq α] {β : α → Sort*}
  {a : α} (v w : β a) (f : Πa, β a) : update (update f a v) a w = update f a w :=
by {funext b, by_cases b = a; simp [update, h]}

end update

section extend

noncomputable theory
local attribute [instance, priority 10] classical.prop_decidable

variables {α β γ : Type*} {f : α → β}

/-- `extend f g e'` extends a function `g : α → γ`
along a function `f : α → β` to a function `β → γ`,
by using the values of `g` on the range of `f`
and the values of an auxiliary function `e' : β → γ` elsewhere.

Mostly useful when `f` is injective. -/
def extend (f : α → β) (g : α → γ) (e' : β → γ) : β → γ :=
λ b, if h : ∃ a, f a = b then g (classical.some h) else e' b

lemma extend_def (f : α → β) (g : α → γ) (e' : β → γ) (b : β) [decidable (∃ a, f a = b)] :
  extend f g e' b = if h : ∃ a, f a = b then g (classical.some h) else e' b :=
by { unfold extend, congr }

@[simp] lemma extend_apply (hf : injective f) (g : α → γ) (e' : β → γ) (a : α) :
  extend f g e' (f a) = g a :=
begin
  simp only [extend_def, dif_pos, exists_apply_eq_apply],
  exact congr_arg g (hf $ classical.some_spec (exists_apply_eq_apply f a))
end

@[simp] lemma extend_comp (hf : injective f) (g : α → γ) (e' : β → γ) :
  extend f g e' ∘ f = g :=
funext $ λ a, extend_apply hf g e' a

end extend

lemma uncurry_def {α β γ} (f : α → β → γ) : uncurry f = (λp, f p.1 p.2) :=
rfl

@[simp] lemma uncurry_apply_pair {α β γ} (f : α → β → γ) (x : α) (y : β) :
  uncurry f (x, y) = f x y :=
rfl

@[simp] lemma curry_apply {α β γ} (f : α × β → γ) (x : α) (y : β) :
  curry f x y = f (x, y) :=
rfl

section bicomp
variables {α β γ δ ε : Type*}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
f (g a) (h b)

/-- Compose an unary function `f` with a binary function `g`. -/
def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
f (g a b)

-- Suggested local notation:
local notation f `∘₂` g := bicompr f g

lemma uncurry_bicompr (f : α → β → γ) (g : γ → δ) :
  uncurry (g ∘₂ f) = (g ∘ uncurry f) := rfl

lemma uncurry_bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) :
  uncurry (bicompl f g h) = (uncurry f) ∘ (prod.map g h) :=
rfl

end bicomp

section uncurry

variables {α β γ δ : Type*}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class has_uncurry (α : Type*) (β : out_param Type*) (γ : out_param Type*) := (uncurry : α → (β → γ))

/-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
`f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
for bundled maps.-/
add_decl_doc has_uncurry.uncurry

notation `↿`:max x:max := has_uncurry.uncurry x

instance has_uncurry_base : has_uncurry (α → β) α β := ⟨id⟩

instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ :=
⟨λ f p, ↿(f p.1) p.2⟩

end uncurry

/-- A function is involutive, if `f ∘ f = id`. -/
def involutive {α} (f : α → α) : Prop := ∀ x, f (f x) = x

lemma involutive_iff_iter_2_eq_id {α} {f : α → α} : involutive f ↔ (f^[2] = id) :=
funext_iff.symm

namespace involutive
variables {α : Sort u} {f : α → α} (h : involutive f)
include h

@[simp]
lemma comp_self : f ∘ f = id := funext h

protected lemma left_inverse : left_inverse f f := h
protected lemma right_inverse : right_inverse f f := h

protected lemma injective : injective f := h.left_inverse.injective
protected lemma surjective : surjective f := λ x, ⟨f x, h x⟩
protected lemma bijective : bijective f := ⟨h.injective, h.surjective⟩

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
protected lemma ite_not (P : Prop) [decidable P] (x : α) :
  f (ite P x (f x)) = ite (¬ P) x (f x) :=
by rw [apply_ite f, h, ite_not]

/-- An involution commutes across an equality. Compare to `function.injective.eq_iff`. -/
protected lemma eq_iff {x y : α} : f x = y ↔ x = f y :=
h.injective.eq_iff' (h y)

end involutive

/-- The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
@[reducible] def injective2 {α β γ} (f : α → β → γ) : Prop :=
∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace injective2
variables {α β γ : Type*} (f : α → β → γ)

protected lemma left (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ (h : f a₁ b₁ = f a₂ b₂) : a₁ = a₂ :=
(hf h).1

protected lemma right (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ (h : f a₁ b₁ = f a₂ b₂) : b₁ = b₂ :=
(hf h).2

lemma eq_iff (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
⟨λ h, hf h, λ⟨h1, h2⟩, congr_arg2 f h1 h2⟩

end injective2

section sometimes
local attribute [instance, priority 10] classical.prop_decidable

/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
noncomputable def sometimes {α β} [nonempty β] (f : α → β) : β :=
if h : nonempty α then f (classical.choice h) else classical.choice ‹_›

theorem sometimes_eq {p : Prop} {α} [nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
dif_pos ⟨a⟩

theorem sometimes_spec {p : Prop} {α} [nonempty α]
  (P : α → Prop) (f : p → α) (a : p) (h : P (f a)) : P (sometimes f) :=
by rwa sometimes_eq

end sometimes

end function

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def set.piecewise {α : Type u} {β : α → Sort v} (s : set α) (f g : Πi, β i)
  [∀j, decidable (j ∈ s)] :
  Πi, β i :=
λi, if i ∈ s then f i else g i

/-! ### Bijectivity of `eq.rec`, `eq.mp`, `eq.mpr`, and `cast` -/

lemma eq_rec_on_bijective {α : Sort*} {C : α → Sort*} :
  ∀ {a a' : α} (h : a = a'), function.bijective (@eq.rec_on _ _ C _ h)
| _ _ rfl := ⟨λ x y, id, λ x, ⟨x, rfl⟩⟩

lemma eq_mp_bijective {α β : Sort*} (h : α = β) : function.bijective (eq.mp h) :=
eq_rec_on_bijective h

lemma eq_mpr_bijective {α β : Sort*} (h : α = β) : function.bijective (eq.mpr h) :=
eq_rec_on_bijective h.symm

lemma cast_bijective {α β : Sort*} (h : α = β) : function.bijective (cast h) :=
eq_rec_on_bijective h

/-! Note these lemmas apply to `Type*` not `Sort*`, as the latter interferes with `simp`, and
is trivial anyway.-/

@[simp]
lemma eq_rec_inj {α : Sort*} {a a' : α} (h : a = a') {C : α → Type*} (x y : C a) :
  (eq.rec x h : C a') = eq.rec y h ↔ x = y :=
(eq_rec_on_bijective h).injective.eq_iff

@[simp]
lemma cast_inj {α β : Type*} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = y :=
(cast_bijective h).injective.eq_iff

/-- A set of functions "separates points"
if for each pair of distinct points there is a function taking different values on them. -/
def set.separates_points {α β : Type*} (A : set (α → β)) : Prop :=
∀ ⦃x y : α⦄, x ≠ y → ∃ f ∈ A, (f x : β) ≠ f y

lemma is_symm_op.flip_eq {α β} (op) [is_symm_op α β op] : flip op = op :=
funext $ λ a, funext $ λ b, (is_symm_op.symm_op a b).symm
