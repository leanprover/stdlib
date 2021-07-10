/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import data.set.basic
import logic.function.conjugate

/-!
# Functions over sets

## Main definitions

### Predicate

* `set.eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `set.maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `set.inj_on f s` : restriction of `f` to `s` is injective;
* `set.surj_on f s t` : every point in `s` has a preimage in `s`;
* `set.bij_on f s t` : `f` is a bijection between `s` and `t`;
* `set.left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `set.right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `set.inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `set.left_inv_on f' f s` and `set.right_inv_on f' f t`.

### Functions

* `set.restrict f s` : restrict the domain of `f` to the set `s`;
* `set.cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `set.maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/
universes u v w x y

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open function

namespace set

/-! ### Restrict -/

/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict (f : α → β) (s : set α) : s → β := λ x, f x

lemma restrict_eq (f : α → β) (s : set α) : s.restrict f = f ∘ coe := rfl

@[simp] lemma restrict_apply (f : α → β) (s : set α) (x : s) : restrict f s x = f x := rfl

@[simp] lemma range_restrict (f : α → β) (s : set α) : set.range (restrict f s) = f '' s :=
(range_comp _ _).trans $ congr_arg (('') f) subtype.range_coe

lemma image_restrict (f : α → β) (s t : set α) : s.restrict f '' (coe ⁻¹' t) = f '' (t ∩ s) :=
by rw [restrict, image_comp, image_preimage_eq_inter_range, subtype.range_coe]

/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def cod_restrict (f : α → β) (s : set β) (h : ∀ x, f x ∈ s) : α → s :=
λ x, ⟨f x, h x⟩

@[simp] lemma coe_cod_restrict_apply (f : α → β) (s : set β) (h : ∀ x, f x ∈ s) (x : α) :
  (cod_restrict f s h x : β) = f x :=
rfl

variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {p : set γ} {f f₁ f₂ f₃ : α → β} {g : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β}

/-! ### Equality on a set -/

/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
@[reducible] def eq_on (f₁ f₂ : α → β) (s : set α) : Prop :=
∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

@[simp] lemma eq_on_empty (f₁ f₂ : α → β) : eq_on f₁ f₂ ∅ := λ x, false.elim

@[symm] lemma eq_on.symm (h : eq_on f₁ f₂ s) : eq_on f₂ f₁ s :=
λ x hx, (h hx).symm

lemma eq_on_comm : eq_on f₁ f₂ s ↔ eq_on f₂ f₁ s :=
⟨eq_on.symm, eq_on.symm⟩

@[refl] lemma eq_on_refl (f : α → β) (s : set α) : eq_on f f s :=
λ _ _, rfl

@[trans] lemma eq_on.trans (h₁ : eq_on f₁ f₂ s) (h₂ : eq_on f₂ f₃ s) : eq_on f₁ f₃ s :=
λ x hx, (h₁ hx).trans (h₂ hx)

theorem eq_on.image_eq (heq : eq_on f₁ f₂ s) : f₁ '' s = f₂ '' s :=
image_congr heq

theorem eq_on.inter_preimage_eq (heq : eq_on f₁ f₂ s) (t : set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t :=
ext $ λ x, and.congr_right_iff.2 $ λ hx, by rw [mem_preimage, mem_preimage, heq hx]

lemma eq_on.mono (hs : s₁ ⊆ s₂) (hf : eq_on f₁ f₂ s₂) : eq_on f₁ f₂ s₁ :=
λ x hx, hf (hs hx)

lemma comp_eq_of_eq_on_range {ι : Sort*} {f : ι → α} {g₁ g₂ : α → β} (h : eq_on g₁ g₂ (range f)) :
  g₁ ∘ f = g₂ ∘ f :=
funext $ λ x, h $ mem_range_self _

/-! ### maps to -/

/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
@[reducible] def maps_to (f : α → β) (s : set α) (t : set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t

/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def maps_to.restrict (f : α → β) (s : set α) (t : set β) (h : maps_to f s t) :
  s → t :=
subtype.map f h

@[simp] lemma maps_to.coe_restrict_apply (h : maps_to f s t) (x : s) :
  (h.restrict f s t x : β) = f x := rfl

lemma maps_to_iff_exists_map_subtype : maps_to f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
⟨λ h, ⟨h.restrict f s t, λ _, rfl⟩,
  λ ⟨g, hg⟩ x hx, by { erw [hg ⟨x, hx⟩], apply subtype.coe_prop }⟩

theorem maps_to' : maps_to f s t ↔ f '' s ⊆ t :=
image_subset_iff.symm

theorem maps_to_empty (f : α → β) (t : set β) : maps_to f ∅ t := empty_subset _

theorem maps_to.image_subset (h : maps_to f s t) : f '' s ⊆ t :=
maps_to'.1 h

theorem maps_to.congr (h₁ : maps_to f₁ s t) (h : eq_on f₁ f₂ s) :
  maps_to f₂ s t :=
λ x hx, h hx ▸ h₁ hx

theorem eq_on.maps_to_iff (H : eq_on f₁ f₂ s) : maps_to f₁ s t ↔ maps_to f₂ s t :=
⟨λ h, h.congr H, λ h, h.congr H.symm⟩

theorem maps_to.comp (h₁ : maps_to g t p) (h₂ : maps_to f s t) : maps_to (g ∘ f) s p :=
λ x h, h₁ (h₂ h)

theorem maps_to_id (s : set α) : maps_to id s s := λ x, id

theorem maps_to.iterate {f : α → α} {s : set α} (h : maps_to f s s) :
  ∀ n, maps_to (f^[n]) s s
| 0 := λ _, id
| (n+1) := (maps_to.iterate n).comp h

theorem maps_to.iterate_restrict {f : α → α} {s : set α} (h : maps_to f s s) (n : ℕ) :
  (h.restrict f s s^[n]) = (h.iterate n).restrict _ _ _ :=
begin
  funext x,
  rw [subtype.ext_iff, maps_to.coe_restrict_apply],
  induction n with n ihn generalizing x,
  { refl },
  { simp [nat.iterate, ihn] }
end

theorem maps_to.mono (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) (hf : maps_to f s₁ t₁) :
  maps_to f s₂ t₂ :=
λ x hx, ht (hf $ hs hx)

theorem maps_to.union_union (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) :
  maps_to f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
λ x hx, hx.elim (λ hx, or.inl $ h₁ hx) (λ hx, or.inr $ h₂ hx)

theorem maps_to.union (h₁ : maps_to f s₁ t) (h₂ : maps_to f s₂ t) :
  maps_to f (s₁ ∪ s₂) t :=
union_self t ▸ h₁.union_union h₂

@[simp] theorem maps_to_union : maps_to f (s₁ ∪ s₂) t ↔ maps_to f s₁ t ∧ maps_to f s₂ t :=
⟨λ h, ⟨h.mono (subset_union_left s₁ s₂) (subset.refl t),
  h.mono (subset_union_right s₁ s₂) (subset.refl t)⟩, λ h, h.1.union h.2⟩

theorem maps_to.inter (h₁ : maps_to f s t₁) (h₂ : maps_to f s t₂) :
  maps_to f s (t₁ ∩ t₂) :=
λ x hx, ⟨h₁ hx, h₂ hx⟩

theorem maps_to.inter_inter (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) :
  maps_to f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
λ x hx, ⟨h₁ hx.1, h₂ hx.2⟩

@[simp] theorem maps_to_inter : maps_to f s (t₁ ∩ t₂) ↔ maps_to f s t₁ ∧ maps_to f s t₂ :=
⟨λ h, ⟨h.mono (subset.refl s) (inter_subset_left t₁ t₂),
  h.mono (subset.refl s) (inter_subset_right t₁ t₂)⟩, λ h, h.1.inter h.2⟩

theorem maps_to_univ (f : α → β) (s : set α) : maps_to f s univ := λ x h, trivial

theorem maps_to_image (f : α → β) (s : set α) : maps_to f s (f '' s) := by rw maps_to'

theorem maps_to_preimage (f : α → β) (t : set β) : maps_to f (f ⁻¹' t) t := subset.refl _

theorem maps_to_range (f : α → β) (s : set α) : maps_to f s (range f) :=
(maps_to_image f s).mono (subset.refl s) (image_subset_range _ _)

@[simp] lemma maps_image_to (f : α → β) (g : γ → α) (s : set γ) (t : set β) :
  maps_to f (g '' s) t ↔ maps_to (f ∘ g) s t :=
⟨λ h c hc, h ⟨c, hc, rfl⟩, λ h d ⟨c, hc⟩, hc.2 ▸ h hc.1⟩

@[simp] lemma maps_univ_to (f : α → β) (s : set β) :
  maps_to f univ s ↔ ∀ a, f a ∈ s :=
⟨λ h a, h (mem_univ _), λ h x _, h x⟩

@[simp] lemma maps_range_to (f : α → β) (g : γ → α) (s : set β) :
  maps_to f (range g) s ↔ maps_to (f ∘ g) univ s :=
by rw [←image_univ, maps_image_to]

theorem surjective_maps_to_image_restrict (f : α → β) (s : set α) :
  surjective ((maps_to_image f s).restrict f s (f '' s)) :=
λ ⟨y, x, hs, hxy⟩, ⟨⟨x, hs⟩, subtype.ext hxy⟩

theorem maps_to.mem_iff (h : maps_to f s t) (hc : maps_to f sᶜ tᶜ) {x} : f x ∈ t ↔ x ∈ s :=
⟨λ ht, by_contra $ λ hs, hc hs ht, λ hx, h hx⟩

/-! ### Injectivity on a set -/

/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
@[reducible] def inj_on (f : α → β) (s : set α) : Prop :=
∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

theorem inj_on_empty (f : α → β) : inj_on f ∅ :=
λ _ h₁, false.elim h₁

theorem inj_on.eq_iff {x y} (h : inj_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y ↔ x = y :=
⟨h hx hy, λ h, h ▸ rfl⟩

theorem inj_on.congr (h₁ : inj_on f₁ s) (h : eq_on f₁ f₂ s) :
  inj_on f₂ s :=
λ x hx y hy, h hx ▸ h hy ▸ h₁ hx hy

theorem eq_on.inj_on_iff (H : eq_on f₁ f₂ s) : inj_on f₁ s ↔ inj_on f₂ s :=
⟨λ h, h.congr H, λ h, h.congr H.symm⟩

theorem inj_on.mono (h : s₁ ⊆ s₂) (ht : inj_on f s₂) : inj_on f s₁ :=
λ x hx y hy H, ht (h hx) (h hy) H

theorem inj_on_insert {f : α → β} {s : set α} {a : α} (has : a ∉ s) :
  set.inj_on f (insert a s) ↔ set.inj_on f s ∧ f a ∉ f '' s :=
⟨λ hf, ⟨hf.mono $ subset_insert a s,
  λ ⟨x, hxs, hx⟩, has $ mem_of_eq_of_mem (hf (or.inl rfl) (or.inr hxs) hx.symm) hxs⟩,
λ ⟨h1, h2⟩ x hx y hy hfxy, or.cases_on hx
  (λ hxa : x = a, or.cases_on hy
    (λ hya : y = a, hxa.trans hya.symm)
    (λ hys : y ∈ s, h2.elim ⟨y, hys, hxa ▸ hfxy.symm⟩))
  (λ hxs : x ∈ s, or.cases_on hy
    (λ hya : y = a, h2.elim ⟨x, hxs, hya ▸ hfxy⟩)
    (λ hys : y ∈ s, h1 hxs hys hfxy))⟩

lemma injective_iff_inj_on_univ : injective f ↔ inj_on f univ :=
⟨λ h x hx y hy hxy, h hxy, λ h _ _ heq, h trivial trivial heq⟩

lemma inj_on_of_injective (h : injective f) (s : set α) : inj_on f s :=
λ x hx y hy hxy, h hxy

alias inj_on_of_injective ← function.injective.inj_on

theorem inj_on.comp (hg : inj_on g t) (hf: inj_on f s) (h : maps_to f s t) :
  inj_on (g ∘ f) s :=
λ x hx y hy heq, hf hx hy $ hg (h hx) (h hy) heq

lemma inj_on_iff_injective : inj_on f s ↔ injective (restrict f s) :=
⟨λ H a b h, subtype.eq $ H a.2 b.2 h,
 λ H a as b bs h, congr_arg subtype.val $ @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

lemma inj_on_preimage {B : set (set β)} (hB : B ⊆ 𝒫 (range f)) :
  inj_on (preimage f) B :=
λ s hs t ht hst, (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

lemma inj_on.mem_of_mem_image {x} (hf : inj_on f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) :
  x ∈ s₁ :=
let ⟨x', h', eq⟩ := h₁ in hf (hs h') h eq ▸ h'

lemma inj_on.mem_image_iff {x} (hf : inj_on f s) (hs : s₁ ⊆ s) (hx : x ∈ s) :
  f x ∈ f '' s₁ ↔ x ∈ s₁ :=
⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩

lemma inj_on.preimage_image_inter (hf : inj_on f s) (hs : s₁ ⊆ s) :
  f ⁻¹' (f '' s₁) ∩ s = s₁ :=
ext $ λ x, ⟨λ ⟨h₁, h₂⟩, hf.mem_of_mem_image hs h₂ h₁, λ h, ⟨mem_image_of_mem _ h, hs h⟩⟩

/-! ### Surjectivity on a set -/

/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
@[reducible] def surj_on (f : α → β) (s : set α) (t : set β) : Prop := t ⊆ f '' s

theorem surj_on.subset_range (h : surj_on f s t) : t ⊆ range f :=
subset.trans h $ image_subset_range f s

lemma surj_on_iff_exists_map_subtype :
  surj_on f s t ↔ ∃ (t' : set β) (g : s → t'), t ⊆ t' ∧ surjective g ∧ ∀ x : s, f x = g x :=
⟨λ h, ⟨_, (maps_to_image f s).restrict f s _, h, surjective_maps_to_image_restrict _ _, λ _, rfl⟩,
  λ ⟨t', g, htt', hg, hfg⟩ y hy, let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩ in
    ⟨x, x.2, by rw [hfg, hx, subtype.coe_mk]⟩⟩

theorem surj_on_empty (f : α → β) (s : set α) : surj_on f s ∅ := empty_subset _

theorem surj_on_image (f : α → β) (s : set α) : surj_on f s (f '' s) := subset.rfl

theorem surj_on.comap_nonempty (h : surj_on f s t) (ht : t.nonempty) : s.nonempty :=
(ht.mono h).of_image

theorem surj_on.congr (h : surj_on f₁ s t) (H : eq_on f₁ f₂ s) : surj_on f₂ s t :=
by rwa [surj_on, ← H.image_eq]

theorem eq_on.surj_on_iff (h : eq_on f₁ f₂ s) : surj_on f₁ s t ↔ surj_on f₂ s t :=
⟨λ H, H.congr h, λ H, H.congr h.symm⟩

theorem surj_on.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : surj_on f s₁ t₂) : surj_on f s₂ t₁ :=
subset.trans ht $ subset.trans hf $ image_subset _ hs

theorem surj_on.union (h₁ : surj_on f s t₁) (h₂ : surj_on f s t₂) : surj_on f s (t₁ ∪ t₂) :=
λ x hx, hx.elim (λ hx, h₁ hx) (λ hx, h₂ hx)

theorem surj_on.union_union (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) :
  surj_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
(h₁.mono (subset_union_left _ _) (subset.refl _)).union
  (h₂.mono (subset_union_right _ _) (subset.refl _))

theorem surj_on.inter_inter (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
  surj_on f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
begin
  intros y hy,
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩,
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩,
  have : x₁ = x₂, from h (or.inl hx₁) (or.inr hx₂) heq.symm,
  subst x₂,
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩
end

theorem surj_on.inter (h₁ : surj_on f s₁ t) (h₂ : surj_on f s₂ t) (h : inj_on f (s₁ ∪ s₂)) :
  surj_on f (s₁ ∩ s₂) t :=
inter_self t ▸ h₁.inter_inter h₂ h

theorem surj_on.comp (hg : surj_on g t p) (hf : surj_on f s t) : surj_on (g ∘ f) s p :=
subset.trans hg $ subset.trans (image_subset g hf) $ (image_comp g f s) ▸ subset.refl _

lemma surjective_iff_surj_on_univ : surjective f ↔ surj_on f univ univ :=
by simp [surjective, surj_on, subset_def]

lemma surj_on_iff_surjective : surj_on f s univ ↔ surjective (restrict f s) :=
⟨λ H b, let ⟨a, as, e⟩ := @H b trivial in ⟨⟨a, as⟩, e⟩,
 λ H b _, let ⟨⟨a, as⟩, e⟩ := H b in ⟨a, as, e⟩⟩

lemma surj_on.image_eq_of_maps_to (h₁ : surj_on f s t) (h₂ : maps_to f s t) :
  f '' s = t :=
eq_of_subset_of_subset h₂.image_subset h₁

lemma surj_on.maps_to_compl (h : surj_on f s t) (h' : injective f) : maps_to f sᶜ tᶜ :=
λ x hs ht, let ⟨x', hx', heq⟩ := h ht in hs $ h' heq ▸ hx'

lemma maps_to.surj_on_compl (h : maps_to f s t) (h' : surjective f) : surj_on f sᶜ tᶜ :=
h'.forall.2 $ λ x ht, mem_image_of_mem _ $ λ hs, ht (h hs)

/-! ### Bijectivity -/

/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
@[reducible] def bij_on (f : α → β) (s : set α) (t : set β) : Prop :=
maps_to f s t ∧ inj_on f s ∧ surj_on f s t

lemma bij_on.maps_to (h : bij_on f s t) : maps_to f s t := h.left

lemma bij_on.inj_on (h : bij_on f s t) : inj_on f s := h.right.left

lemma bij_on.surj_on (h : bij_on f s t) : surj_on f s t := h.right.right

lemma bij_on.mk (h₁ : maps_to f s t) (h₂ : inj_on f s) (h₃ : surj_on f s t) :
      bij_on f s t :=
⟨h₁, h₂, h₃⟩

lemma bij_on_empty (f : α → β) : bij_on f ∅ ∅ :=
⟨maps_to_empty f ∅, inj_on_empty f, surj_on_empty f ∅⟩

lemma bij_on.inter (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
  bij_on f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
⟨h₁.maps_to.inter_inter h₂.maps_to, h₁.inj_on.mono $ inter_subset_left _ _,
  h₁.surj_on.inter_inter h₂.surj_on h⟩

lemma bij_on.union (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
  bij_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
⟨h₁.maps_to.union_union h₂.maps_to, h, h₁.surj_on.union_union h₂.surj_on⟩

theorem bij_on.subset_range (h : bij_on f s t) : t ⊆ range f :=
h.surj_on.subset_range

lemma inj_on.bij_on_image (h : inj_on f s) : bij_on f s (f '' s) :=
bij_on.mk (maps_to_image f s) h (subset.refl _)

theorem bij_on.congr (h₁ : bij_on f₁ s t) (h : eq_on f₁ f₂ s) :
  bij_on f₂ s t :=
bij_on.mk (h₁.maps_to.congr h) (h₁.inj_on.congr h) (h₁.surj_on.congr h)

theorem eq_on.bij_on_iff (H : eq_on f₁ f₂ s) : bij_on f₁ s t ↔ bij_on f₂ s t :=
⟨λ h, h.congr H, λ h, h.congr H.symm⟩

lemma bij_on.image_eq (h : bij_on f s t) :
  f '' s = t :=
h.surj_on.image_eq_of_maps_to h.maps_to

theorem bij_on.comp (hg : bij_on g t p) (hf : bij_on f s t) : bij_on (g ∘ f) s p :=
bij_on.mk (hg.maps_to.comp hf.maps_to) (hg.inj_on.comp hf.inj_on hf.maps_to)
  (hg.surj_on.comp hf.surj_on)

theorem bij_on.bijective (h : bij_on f s t) :
  bijective (t.cod_restrict (s.restrict f) $ λ x, h.maps_to x.val_prop) :=
⟨λ x y h', subtype.ext $ h.inj_on x.2 y.2 $ subtype.ext_iff.1 h',
  λ ⟨y, hy⟩, let ⟨x, hx, hxy⟩ := h.surj_on hy in ⟨⟨x, hx⟩, subtype.eq hxy⟩⟩

lemma bijective_iff_bij_on_univ : bijective f ↔ bij_on f univ univ :=
iff.intro
(λ h, let ⟨inj, surj⟩ := h in
⟨maps_to_univ f _, inj.inj_on _, iff.mp surjective_iff_surj_on_univ surj⟩)
(λ h, let ⟨map, inj, surj⟩ := h in
⟨iff.mpr injective_iff_inj_on_univ inj, iff.mpr surjective_iff_surj_on_univ surj⟩)

lemma bij_on.compl (hst : bij_on f s t) (hf : bijective f) : bij_on f sᶜ tᶜ :=
⟨hst.surj_on.maps_to_compl hf.1, hf.1.inj_on _, hst.maps_to.surj_on_compl hf.2⟩

/-! ### left inverse -/

/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
@[reducible] def left_inv_on (f' : β → α) (f : α → β) (s : set α) : Prop :=
∀ ⦃x⦄, x ∈ s → f' (f x) = x

lemma left_inv_on.eq_on (h : left_inv_on f' f s) : eq_on (f' ∘ f) id s := h

lemma left_inv_on.eq (h : left_inv_on f' f s) {x} (hx : x ∈ s) : f' (f x) = x := h hx

lemma left_inv_on.congr_left (h₁ : left_inv_on f₁' f s)
  {t : set β} (h₁' : maps_to f s t) (heq : eq_on f₁' f₂' t) : left_inv_on f₂' f s :=
λ x hx, heq (h₁' hx) ▸ h₁ hx

theorem left_inv_on.congr_right (h₁ : left_inv_on f₁' f₁ s) (heq : eq_on f₁ f₂ s) :
  left_inv_on f₁' f₂ s :=
λ x hx, heq hx ▸ h₁ hx

theorem left_inv_on.inj_on (h : left_inv_on f₁' f s) : inj_on f s :=
λ x₁ h₁ x₂ h₂ heq,
calc
  x₁    = f₁' (f x₁) : eq.symm $ h h₁
  ...   = f₁' (f x₂) : congr_arg f₁' heq
  ...   = x₂         : h h₂

theorem left_inv_on.surj_on (h : left_inv_on f' f s) (hf : maps_to f s t) : surj_on f' t s :=
λ x hx, ⟨f x, hf hx, h hx⟩

theorem left_inv_on.maps_to (h : left_inv_on f' f s) (hf : surj_on f s t) : maps_to f' t s :=
λ y hy, let ⟨x, hs, hx⟩ := hf hy in by rwa [← hx, h hs]

theorem left_inv_on.comp
  (hf' : left_inv_on f' f s) (hg' : left_inv_on g' g t) (hf : maps_to f s t) :
  left_inv_on (f' ∘ g') (g ∘ f) s :=
λ x h,
calc
  (f' ∘ g') ((g ∘ f) x) = f' (f x) : congr_arg f' (hg' (hf h))
  ...                   = x        : hf' h

theorem left_inv_on.mono (hf : left_inv_on f' f s) (ht : s₁ ⊆ s) : left_inv_on f' f s₁ :=
λ x hx, hf (ht hx)

theorem left_inv_on.image_inter' (hf : left_inv_on f' f s) :
  f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s :=
begin
  apply subset.antisymm,
  { rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩, exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩ },
  { rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩, exact mem_image_of_mem _ ⟨by rwa ← hf h, h⟩ }
end

theorem left_inv_on.image_inter (hf : left_inv_on f' f s) :
  f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s :=
begin
  rw hf.image_inter',
  refine subset.antisymm _ (inter_subset_inter_left _ (preimage_mono $ inter_subset_left _ _)),
  rintro _ ⟨h₁, x, hx, rfl⟩, exact ⟨⟨h₁, by rwa hf hx⟩, mem_image_of_mem _ hx⟩
end

theorem left_inv_on.image_image (hf : left_inv_on f' f s) :
  f' '' (f '' s) = s :=
by rw [image_image, image_congr hf, image_id']

theorem left_inv_on.image_image' (hf : left_inv_on f' f s) (hs : s₁ ⊆ s) :
  f' '' (f '' s₁) = s₁ :=
(hf.mono hs).image_image

/-! ### Right inverse -/

/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible] def right_inv_on (f' : β → α) (f : α → β) (t : set β) : Prop :=
left_inv_on f f' t

lemma right_inv_on.eq_on (h : right_inv_on f' f t) : eq_on (f ∘ f') id t := h

lemma right_inv_on.eq (h : right_inv_on f' f t) {y} (hy : y ∈ t) : f (f' y) = y := h hy

lemma left_inv_on.right_inv_on_image (h : left_inv_on f' f s) : right_inv_on f' f (f '' s) :=
λ y ⟨x, hx, eq⟩, eq ▸ congr_arg f $ h.eq hx

theorem right_inv_on.congr_left (h₁ : right_inv_on f₁' f t) (heq : eq_on f₁' f₂' t) :
  right_inv_on f₂' f t :=
h₁.congr_right heq

theorem right_inv_on.congr_right (h₁ : right_inv_on f' f₁ t) (hg : maps_to f' t s)
  (heq : eq_on f₁ f₂ s) : right_inv_on f' f₂ t :=
left_inv_on.congr_left h₁ hg heq

theorem right_inv_on.surj_on (hf : right_inv_on f' f t) (hf' : maps_to f' t s) :
  surj_on f s t :=
hf.surj_on hf'

theorem right_inv_on.maps_to (h : right_inv_on f' f t) (hf : surj_on f' t s) : maps_to f s t :=
h.maps_to hf

theorem right_inv_on.comp (hf : right_inv_on f' f t) (hg : right_inv_on g' g p)
  (g'pt : maps_to g' p t) : right_inv_on (f' ∘ g') (g ∘ f) p :=
hg.comp hf g'pt

theorem right_inv_on.mono (hf : right_inv_on f' f t) (ht : t₁ ⊆ t) : right_inv_on f' f t₁ :=
hf.mono ht

theorem inj_on.right_inv_on_of_left_inv_on (hf : inj_on f s) (hf' : left_inv_on f f' t)
    (h₁ : maps_to f s t) (h₂ : maps_to f' t s) :
  right_inv_on f f' s :=
λ x h, hf (h₂ $ h₁ h) h (hf' (h₁ h))

theorem eq_on_of_left_inv_on_of_right_inv_on (h₁ : left_inv_on f₁' f s) (h₂ : right_inv_on f₂' f t)
  (h : maps_to f₂' t s) : eq_on f₁' f₂' t :=
λ y hy,
calc f₁' y = (f₁' ∘ f ∘ f₂') y : congr_arg f₁' (h₂ hy).symm
      ...  = f₂' y              : h₁ (h hy)

theorem surj_on.left_inv_on_of_right_inv_on (hf : surj_on f s t) (hf' : right_inv_on f f' s) :
  left_inv_on f f' t :=
λ y hy, let ⟨x, hx, heq⟩ := hf hy in by rw [← heq, hf' hx]

/-! ### Two-side inverses -/

/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
@[reducible] def inv_on (g : β → α) (f : α → β) (s : set α) (t : set β) : Prop :=
left_inv_on g f s ∧ right_inv_on g f t

lemma inv_on.symm (h : inv_on f' f s t) : inv_on f f' t s := ⟨h.right, h.left⟩

lemma inv_on.mono (h : inv_on f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : inv_on f' f s₁ t₁ :=
⟨h.1.mono hs, h.2.mono ht⟩

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem inv_on.bij_on (h : inv_on f' f s t) (hf : maps_to f s t) (hf' : maps_to f' t s) :
  bij_on f s t :=
⟨hf, h.left.inj_on, h.right.surj_on hf'⟩

/-! ### `inv_fun_on` is a left/right inverse -/

theorem inj_on.left_inv_on_inv_fun_on [nonempty α] (h : inj_on f s) :
  left_inv_on (inv_fun_on f s) f s :=
λ x hx, inv_fun_on_eq' h hx

lemma inj_on.inv_fun_on_image [nonempty α] (h : inj_on f s₂) (ht : s₁ ⊆ s₂) :
  (inv_fun_on f s₂) '' (f '' s₁) = s₁ :=
h.left_inv_on_inv_fun_on.image_image' ht

theorem surj_on.right_inv_on_inv_fun_on [nonempty α] (h : surj_on f s t) :
  right_inv_on (inv_fun_on f s) f t :=
λ y hy, inv_fun_on_eq $ mem_image_iff_bex.1 $ h hy

theorem bij_on.inv_on_inv_fun_on [nonempty α] (h : bij_on f s t) :
  inv_on (inv_fun_on f s) f s t :=
⟨h.inj_on.left_inv_on_inv_fun_on, h.surj_on.right_inv_on_inv_fun_on⟩

theorem surj_on.inv_on_inv_fun_on [nonempty α] (h : surj_on f s t) :
  inv_on (inv_fun_on f s) f (inv_fun_on f s '' t) t :=
begin
  refine ⟨_, h.right_inv_on_inv_fun_on⟩,
  rintros _ ⟨y, hy, rfl⟩,
  rw [h.right_inv_on_inv_fun_on hy]
end

theorem surj_on.maps_to_inv_fun_on [nonempty α] (h : surj_on f s t) :
  maps_to (inv_fun_on f s) t s :=
λ y hy, mem_preimage.2 $ inv_fun_on_mem $ mem_image_iff_bex.1 $ h hy

theorem surj_on.bij_on_subset [nonempty α] (h : surj_on f s t) :
  bij_on f (inv_fun_on f s '' t) t :=
begin
  refine h.inv_on_inv_fun_on.bij_on _ (maps_to_image _ _),
  rintros _ ⟨y, hy, rfl⟩,
  rwa [h.right_inv_on_inv_fun_on hy]
end

theorem surj_on_iff_exists_bij_on_subset :
  surj_on f s t ↔ ∃ s' ⊆ s, bij_on f s' t :=
begin
  split,
  { rcases eq_empty_or_nonempty t with rfl|ht,
    { exact λ _, ⟨∅, empty_subset _, bij_on_empty f⟩ },
    { assume h,
      haveI : nonempty α := ⟨classical.some (h.comap_nonempty ht)⟩,
      exact ⟨_, h.maps_to_inv_fun_on.image_subset, h.bij_on_subset⟩ }},
  { rintros ⟨s', hs', hfs'⟩,
    exact hfs'.surj_on.mono hs' (subset.refl _) }
end

lemma preimage_inv_fun_of_mem [n : nonempty α] {f : α → β} (hf : injective f) {s : set α}
  (h : classical.choice n ∈ s) : inv_fun f ⁻¹' s = f '' s ∪ (range f)ᶜ :=
begin
  ext x,
  rcases em (x ∈ range f) with ⟨a, rfl⟩|hx,
  { simp [left_inverse_inv_fun hf _, mem_image_of_injective hf] },
  { simp [mem_preimage, inv_fun_neg hx, h, hx] }
end

lemma preimage_inv_fun_of_not_mem [n : nonempty α] {f : α → β} (hf : injective f)
  {s : set α} (h : classical.choice n ∉ s) : inv_fun f ⁻¹' s = f '' s :=
begin
  ext x,
  rcases em (x ∈ range f) with ⟨a, rfl⟩|hx,
  { rw [mem_preimage, left_inverse_inv_fun hf, mem_image_of_injective hf] },
  { have : x ∉ f '' s, from λ h', hx (image_subset_range _ _ h'),
    simp only [mem_preimage, inv_fun_neg hx, h, this] },
end

end set

/-! ### Piecewise defined function -/

namespace set

variables {δ : α → Sort y} (s : set α) (f g : Πi, δ i)

@[simp] lemma piecewise_empty [∀i : α, decidable (i ∈ (∅ : set α))] : piecewise ∅ f g = g :=
by { ext i, simp [piecewise] }

@[simp] lemma piecewise_univ [∀i : α, decidable (i ∈ (set.univ : set α))] :
  piecewise set.univ f g = f :=
by { ext i, simp [piecewise] }

@[simp] lemma piecewise_insert_self {j : α} [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g j = f j :=
by simp [piecewise]

variable [∀j, decidable (j ∈ s)]

instance compl.decidable_mem (j : α) : decidable (j ∈ sᶜ) := not.decidable

lemma piecewise_insert [decidable_eq α] (j : α) [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g = function.update (s.piecewise f g) j (f j) :=
begin
  simp [piecewise],
  ext i,
  by_cases h : i = j,
  { rw h, simp },
  { by_cases h' : i ∈ s; simp [h, h'] }
end

@[simp, priority 990]
lemma piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i := if_pos hi

@[simp, priority 990]
lemma piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i := if_neg hi

lemma piecewise_singleton (x : α) [Π y, decidable (y ∈ ({x} : set α))] [decidable_eq α]
  (f g : α → β) : piecewise {x} f g = function.update g x (f x) :=
by { ext y, by_cases hy : y = x, { subst y, simp }, { simp [hy] } }

lemma piecewise_eq_on (f g : α → β) : eq_on (s.piecewise f g) f s :=
λ _, piecewise_eq_of_mem _ _ _

lemma piecewise_eq_on_compl (f g : α → β) : eq_on (s.piecewise f g) g sᶜ :=
λ _, piecewise_eq_of_not_mem _ _ _

lemma piecewise_le {δ : α → Type*} [Π i, preorder (δ i)] {s : set α} [Π j, decidable (j ∈ s)]
  {f₁ f₂ g : Π i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g i) (h₂ : ∀ i ∉ s, f₂ i ≤ g i) :
  s.piecewise f₁ f₂ ≤ g :=
λ i, if h : i ∈ s then by simp * else by simp *

lemma le_piecewise {δ : α → Type*} [Π i, preorder (δ i)] {s : set α} [Π j, decidable (j ∈ s)]
  {f₁ f₂ g : Π i, δ i} (h₁ : ∀ i ∈ s, g i ≤ f₁ i) (h₂ : ∀ i ∉ s, g i ≤ f₂ i) :
  g ≤ s.piecewise f₁ f₂ :=
@piecewise_le α (λ i, order_dual (δ i)) _ s _ _ _ _ h₁ h₂

lemma piecewise_le_piecewise {δ : α → Type*} [Π i, preorder (δ i)] {s : set α}
  [Π j, decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : Π i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g₁ i)
  (h₂ : ∀ i ∉ s, f₂ i ≤ g₂ i) :
  s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ :=
by apply piecewise_le; intros; simp *

@[simp, priority 990]
lemma piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g i = s.piecewise f g i :=
by simp [piecewise, h]

@[simp] lemma piecewise_compl [∀ i, decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
funext $ λ x, if hx : x ∈ s then by simp [hx] else by simp [hx]

@[simp] lemma piecewise_range_comp {ι : Sort*} (f : ι → α) [Π j, decidable (j ∈ range f)]
  (g₁ g₂ : α → β) :
  (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
comp_eq_of_eq_on_range $ piecewise_eq_on _ _ _

theorem maps_to.piecewise_ite {s s₁ s₂ : set α} {t t₁ t₂ : set β} {f₁ f₂ : α → β}
  [∀ i, decidable (i ∈ s)]
  (h₁ : maps_to f₁ (s₁ ∩ s) (t₁ ∩ t)) (h₂ : maps_to f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) :
  maps_to (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) :=
begin
  refine (h₁.congr _).union_union (h₂.congr _),
  exacts [(piecewise_eq_on s f₁ f₂).symm.mono (inter_subset_right _ _),
    (piecewise_eq_on_compl s f₁ f₂).symm.mono (inter_subset_right _ _)]
end

theorem eq_on_piecewise {f f' g : α → β} {t} :
  eq_on (s.piecewise f f') g t ↔ eq_on f g (t ∩ s) ∧ eq_on f' g (t ∩ sᶜ) :=
begin
  simp only [eq_on, ← forall_and_distrib],
  refine forall_congr (λ a, _), by_cases a ∈ s; simp *
end

theorem eq_on.piecewise_ite' {f f' g : α → β} {t t'} (h : eq_on f g (t ∩ s))
  (h' : eq_on f' g (t' ∩ sᶜ)) :
  eq_on (s.piecewise f f') g (s.ite t t') :=
by simp [eq_on_piecewise, *]

theorem eq_on.piecewise_ite {f f' g : α → β} {t t'} (h : eq_on f g t)
  (h' : eq_on f' g t') :
  eq_on (s.piecewise f f') g (s.ite t t') :=
(h.mono (inter_subset_left _ _)).piecewise_ite' s (h'.mono (inter_subset_left _ _))

lemma piecewise_preimage (f g : α → β) (t) :
  s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
ext $ λ x, by by_cases x ∈ s; simp [*, set.ite]

lemma apply_piecewise {δ' : α → Sort*} (h : Π i, δ i → δ' i) {x : α} :
  h x (s.piecewise f g x) = s.piecewise (λ x, h x (f x)) (λ x, h x (g x)) x :=
by by_cases hx : x ∈ s; simp [hx]

lemma apply_piecewise₂ {δ' δ'' : α → Sort*} (f' g' : Π i, δ' i) (h : Π i, δ i → δ' i → δ'' i)
  {x : α} :
  h x (s.piecewise f g x) (s.piecewise f' g' x) =
    s.piecewise (λ x, h x (f x) (f' x)) (λ x, h x (g x) (g' x)) x :=
by by_cases hx : x ∈ s; simp [hx]

lemma piecewise_op {δ' : α → Sort*} (h : Π i, δ i → δ' i) :
  s.piecewise (λ x, h x (f x)) (λ x, h x (g x)) = λ x, h x (s.piecewise f g x) :=
funext $ λ x, (apply_piecewise _ _ _ _).symm

lemma piecewise_op₂ {δ' δ'' : α → Sort*} (f' g' : Π i, δ' i) (h : Π i, δ i → δ' i → δ'' i) :
  s.piecewise (λ x, h x (f x) (f' x)) (λ x, h x (g x) (g' x)) =
    λ x, h x (s.piecewise f g x) (s.piecewise f' g' x) :=
funext $ λ x, (apply_piecewise₂ _ _ _ _ _ _).symm

@[simp] lemma piecewise_same : s.piecewise f f = f :=
by { ext x, by_cases hx : x ∈ s; simp [hx] }

lemma range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ :=
begin
  ext y, split,
  { rintro ⟨x, rfl⟩, by_cases h : x ∈ s;[left, right]; use x; simp [h] },
  { rintro (⟨x, hx, rfl⟩|⟨x, hx, rfl⟩); use x; simp * at * }
end

lemma piecewise_mem_pi {δ : α → Type*} {t : set α} {t' : Π i, set (δ i)}
  {f g} (hf : f ∈ pi t t') (hg : g ∈ pi t t') :
  s.piecewise f g ∈ pi t t' :=
by { intros i ht, by_cases hs : i ∈ s; simp [hf i ht, hg i ht, hs] }

@[simp] lemma pi_piecewise {ι : Type*} {α : ι → Type*} (s s' : set ι)
  (t t' : Π i, set (α i)) [Π x, decidable (x ∈ s')] :
  pi s (s'.piecewise t t') = pi (s ∩ s') t ∩ pi (s \ s') t' :=
begin
  ext x,
  simp only [mem_pi, mem_inter_eq, ← forall_and_distrib],
  refine forall_congr (λ i, _),
  by_cases hi : i ∈ s'; simp *
end

lemma univ_pi_piecewise {ι : Type*} {α : ι → Type*} (s : set ι)
  (t : Π i, set (α i)) [Π x, decidable (x ∈ s)] :
  pi univ (s.piecewise t (λ _, univ)) = pi s t :=
by simp

end set

lemma strict_mono_incr_on.inj_on [linear_order α] [preorder β] {f : α → β} {s : set α}
  (H : strict_mono_incr_on f s) :
  s.inj_on f :=
λ x hx y hy hxy, show ordering.eq.compares x y, from (H.compares hx hy).1 hxy

lemma strict_mono_decr_on.inj_on [linear_order α] [preorder β] {f : α → β} {s : set α}
  (H : strict_mono_decr_on f s) :
  s.inj_on f :=
@strict_mono_incr_on.inj_on α (order_dual β) _ _ f s H

lemma strict_mono_incr_on.comp [preorder α] [preorder β] [preorder γ]
  {g : β → γ} {f : α → β} {s : set α} {t : set β} (hg : strict_mono_incr_on g t)
  (hf : strict_mono_incr_on f s) (hs : set.maps_to f s t) :
  strict_mono_incr_on (g ∘ f) s :=
λ x hx y hy hxy, hg (hs hx) (hs hy) $ hf hx hy hxy

lemma strict_mono.comp_strict_mono_incr_on [preorder α] [preorder β] [preorder γ]
  {g : β → γ} {f : α → β} {s : set α} (hg : strict_mono g)
  (hf : strict_mono_incr_on f s) :
  strict_mono_incr_on (g ∘ f) s :=
λ x hx y hy hxy, hg $ hf hx hy hxy

lemma strict_mono.cod_restrict [preorder α] [preorder β] {f : α → β} (hf : strict_mono f)
  {s : set β} (hs : ∀ x, f x ∈ s) :
  strict_mono (set.cod_restrict f s hs) :=
hf

namespace function

open set

variables {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : set α}

lemma injective.comp_inj_on (hg : injective g) (hf : s.inj_on f) : s.inj_on (g ∘ f) :=
(hg.inj_on univ).comp hf (maps_to_univ _ _)

lemma surjective.surj_on (hf : surjective f) (s : set β) :
  surj_on f univ s :=
(surjective_iff_surj_on_univ.1 hf).mono (subset.refl _) (subset_univ _)

lemma left_inverse.left_inv_on {g : β → α} (h : left_inverse f g) (s : set β) :
  left_inv_on f g s :=
λ x hx, h x

lemma right_inverse.right_inv_on {g : β → α} (h : right_inverse f g) (s : set α) :
  right_inv_on f g s :=
λ x hx, h x

lemma left_inverse.right_inv_on_range {g : β → α} (h : left_inverse f g) :
  right_inv_on f g (range g) :=
forall_range_iff.2 $ λ i, congr_arg g (h i)

namespace semiconj

lemma maps_to_image (h : semiconj f fa fb) (ha : maps_to fa s t) :
  maps_to fb (f '' s) (f '' t) :=
λ y ⟨x, hx, hy⟩, hy ▸ ⟨fa x, ha hx, h x⟩

lemma maps_to_range (h : semiconj f fa fb) : maps_to fb (range f) (range f) :=
λ y ⟨x, hy⟩, hy ▸ ⟨fa x, h x⟩

lemma surj_on_image (h : semiconj f fa fb) (ha : surj_on fa s t) :
  surj_on fb (f '' s) (f '' t) :=
begin
  rintros y ⟨x, hxt, rfl⟩,
  rcases ha hxt with ⟨x, hxs, rfl⟩,
  rw [h x],
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)
end

lemma surj_on_range (h : semiconj f fa fb) (ha : surjective fa) :
  surj_on fb (range f) (range f) :=
by { rw ← image_univ, exact h.surj_on_image (ha.surj_on univ) }

lemma inj_on_image (h : semiconj f fa fb) (ha : inj_on fa s) (hf : inj_on f (fa '' s)) :
  inj_on fb (f '' s) :=
begin
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H,
  simp only [← h.eq] at H,
  exact congr_arg f (ha hx hy $ hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)
end

lemma inj_on_range (h : semiconj f fa fb) (ha : injective fa) (hf : inj_on f (range fa)) :
  inj_on fb (range f) :=
by { rw ← image_univ at *, exact h.inj_on_image (ha.inj_on univ) hf }

lemma bij_on_image (h : semiconj f fa fb) (ha : bij_on fa s t) (hf : inj_on f t) :
  bij_on fb (f '' s) (f '' t) :=
⟨h.maps_to_image ha.maps_to, h.inj_on_image ha.inj_on (ha.image_eq.symm ▸ hf),
  h.surj_on_image ha.surj_on⟩

lemma bij_on_range (h : semiconj f fa fb) (ha : bijective fa) (hf : injective f) :
  bij_on fb (range f) (range f) :=
begin
  rw [← image_univ],
  exact h.bij_on_image (bijective_iff_bij_on_univ.1 ha) (hf.inj_on univ)
end

lemma maps_to_preimage (h : semiconj f fa fb) {s t : set β} (hb : maps_to fb s t) :
  maps_to fa (f ⁻¹' s) (f ⁻¹' t) :=
λ x hx, by simp only [mem_preimage, h x, hb hx]

lemma inj_on_preimage (h : semiconj f fa fb) {s : set β} (hb : inj_on fb s)
  (hf : inj_on f (f ⁻¹' s)) :
  inj_on fa (f ⁻¹' s) :=
begin
  intros x hx y hy H,
  have := congr_arg f H,
  rw [h.eq, h.eq] at this,
  exact hf hx hy (hb hx hy this)
end

end semiconj

lemma update_comp_eq_of_not_mem_range' {α β : Sort*} {γ : β → Sort*} [decidable_eq β]
  (g : Π b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ set.range f) :
  (λ j, (function.update g i a) (f j)) = (λ j, g (f j)) :=
update_comp_eq_of_forall_ne' _ _ $ λ x hx, h ⟨x, hx⟩

/-- Non-dependent version of `function.update_comp_eq_of_not_mem_range'` -/
lemma update_comp_eq_of_not_mem_range {α β γ : Sort*} [decidable_eq β]
  (g : β → γ) {f : α → β} {i : β} (a : γ) (h : i ∉ set.range f) :
  (function.update g i a) ∘ f = g ∘ f :=
update_comp_eq_of_not_mem_range' g a h

end function
