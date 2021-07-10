/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
import analysis.normed_space.basic
import topology.local_homeomorph

/-!
# Asymptotics

We introduce these relations:

* `is_O_with c f g l` : "f is big O of g along l with constant c";
* `is_O f g l` : "f is big O of g along l";
* `is_o f g l` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `is_O f g l ↔ is_O (λ x, ∥f x∥) (λ x, ∥g x∥) l`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `is_o f g l ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/

open filter set
open_locale topological_space big_operators classical filter nnreal

namespace asymptotics

variables {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*}
  {E' : Type*} {F' : Type*} {G' : Type*} {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variables [has_norm E] [has_norm F] [has_norm G] [normed_group E'] [normed_group F']
  [normed_group G'] [normed_ring R] [normed_ring R'] [normed_field 𝕜] [normed_field 𝕜']
  {c c' : ℝ} {f : α → E} {g : α → F} {k : α → G} {f' : α → E'} {g' : α → F'} {k' : α → G'}
  {l l' : filter α}

section defs

/-! ### Definitions -/

/-- This version of the Landau notation `is_O_with C f g l` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by `C * ∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
@[irreducible]
def is_O_with (c : ℝ) (f : α → E) (g : α → F) (l : filter α) : Prop :=
∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥

/-- Definition of `is_O_with`. We record it in a lemma as we will set `is_O_with` to be irreducible
at the end of this file. -/
lemma is_O_with_iff {c : ℝ} {f : α → E} {g : α → F} {l : filter α} :
  is_O_with c f g l ↔ ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥ := by rw is_O_with

alias is_O_with_iff ↔ asymptotics.is_O_with.bound asymptotics.is_O_with.of_bound

/-- The Landau notation `is_O f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by a constant multiple of `∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
@[irreducible]
def is_O (f : α → E) (g : α → F) (l : filter α) : Prop := ∃ c : ℝ, is_O_with c f g l

/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
lemma is_O_iff_is_O_with {f : α → E} {g : α → F} {l : filter α} :
  is_O f g l ↔ ∃ c : ℝ, is_O_with c f g l := by rw is_O

/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
lemma is_O_iff {f : α → E} {g : α → F} {l : filter α} :
  is_O f g l ↔ ∃ c : ℝ, ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥ := by simp [is_O, is_O_with]

lemma is_O.of_bound (c : ℝ) {f : α → E} {g : α → F} {l : filter α}
  (h : ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥) : is_O f g l := is_O_iff.2 ⟨c, h⟩

lemma is_O.bound {f : α → E} {g : α → F} {l : filter α} :
  is_O f g l → ∃ c : ℝ, ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥ := is_O_iff.1

/-- The Landau notation `is_o f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by an arbitrarily small constant
multiple of `∥g∥`. In other words, `∥f∥ / ∥g∥` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
@[irreducible]
def is_o (f : α → E) (g : α → F) (l : filter α) : Prop := ∀ ⦃c : ℝ⦄, 0 < c → is_O_with c f g l

/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
lemma is_o_iff_forall_is_O_with {f : α → E} {g : α → F} {l : filter α} :
  is_o f g l ↔ ∀ ⦃c : ℝ⦄, 0 < c → is_O_with c f g l := by rw is_o

alias is_o_iff_forall_is_O_with ↔ asymptotics.is_o.forall_is_O_with asymptotics.is_o.of_is_O_with

/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
lemma is_o_iff {f : α → E} {g : α → F} {l : filter α} :
  is_o f g l ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥ :=
by simp only [is_o, is_O_with]

alias is_o_iff ↔ asymptotics.is_o.bound asymptotics.is_o.of_bound

lemma is_o.def {f : α → E} {g : α → F} {l : filter α} (h : is_o f g l) {c : ℝ} (hc : 0 < c) :
  ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥ :=
is_o_iff.1 h hc

lemma is_o.def' {f : α → E} {g : α → F} {l : filter α} (h : is_o f g l) {c : ℝ} (hc : 0 < c) :
  is_O_with c f g l :=
is_O_with_iff.2 $ is_o_iff.1 h hc

end defs

/-! ### Conversions -/

theorem is_O_with.is_O (h : is_O_with c f g l) : is_O f g l := by rw is_O; exact ⟨c, h⟩

theorem is_o.is_O_with (hgf : is_o f g l) : is_O_with 1 f g l := hgf.def' zero_lt_one

theorem is_o.is_O (hgf : is_o f g l) : is_O f g l := hgf.is_O_with.is_O

lemma is_O.is_O_with {f : α → E} {g : α → F} {l : filter α} :
  is_O f g l → ∃ c : ℝ, is_O_with c f g l := is_O_iff_is_O_with.1

theorem is_O_with.weaken (h : is_O_with c f g' l) (hc : c ≤ c') : is_O_with c' f g' l :=
is_O_with.of_bound $ mem_sets_of_superset h.bound $ λ x hx,
calc ∥f x∥ ≤ c * ∥g' x∥ : hx
... ≤ _ : mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem is_O_with.exists_pos (h : is_O_with c f g' l) :
  ∃ c' (H : 0 < c'), is_O_with c' f g' l :=
⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken $ le_max_left c 1⟩

theorem is_O.exists_pos (h : is_O f g' l) : ∃ c (H : 0 < c), is_O_with c f g' l :=
let ⟨c, hc⟩ := h.is_O_with in hc.exists_pos

theorem is_O_with.exists_nonneg (h : is_O_with c f g' l) :
  ∃ c' (H : 0 ≤ c'), is_O_with c' f g' l :=
let ⟨c, cpos, hc⟩ := h.exists_pos in ⟨c, le_of_lt cpos, hc⟩

theorem is_O.exists_nonneg (h : is_O f g' l) :
  ∃ c (H : 0 ≤ c), is_O_with c f g' l :=
let ⟨c, hc⟩ := h.is_O_with in hc.exists_nonneg

/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
lemma is_O_iff_eventually_is_O_with : is_O f g' l ↔ ∀ᶠ c in at_top, is_O_with c f g' l :=
is_O_iff_is_O_with.trans
  ⟨λ ⟨c, hc⟩, mem_at_top_sets.2 ⟨c, λ c' hc', hc.weaken hc'⟩, λ h, h.exists⟩

/-- `f = O(g)` if and only if `∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥` for all sufficiently large `c`. -/
lemma is_O_iff_eventually : is_O f g' l ↔ ∀ᶠ c in at_top, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g' x∥ :=
is_O_iff_eventually_is_O_with.trans $ by simp only [is_O_with]

/-! ### Subsingleton -/

@[nontriviality] lemma is_o_of_subsingleton [subsingleton E'] : is_o f' g' l :=
is_o.of_bound $ λ c hc, by simp [subsingleton.elim (f' _) 0, mul_nonneg hc.le]

@[nontriviality] lemma is_O_of_subsingleton [subsingleton E'] : is_O f' g' l :=
is_o_of_subsingleton.is_O

/-! ### Congruence -/

theorem is_O_with_congr {c₁ c₂} {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
  (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
  is_O_with c₁ f₁ g₁ l ↔ is_O_with c₂ f₂ g₂ l :=
begin
  unfold is_O_with,
  subst c₂,
  apply filter.eventually_congr,
  filter_upwards [hf, hg],
  assume x e₁ e₂,
  rw [e₁, e₂]
end

theorem is_O_with.congr' {c₁ c₂} {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
  (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
  is_O_with c₁ f₁ g₁ l → is_O_with c₂ f₂ g₂ l :=
(is_O_with_congr hc hf hg).mp

theorem is_O_with.congr {c₁ c₂} {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
  (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
  is_O_with c₁ f₁ g₁ l → is_O_with c₂ f₂ g₂ l :=
λ h, h.congr' hc (univ_mem_sets' hf) (univ_mem_sets' hg)

theorem is_O_with.congr_left {f₁ f₂ : α → E} {l : filter α} (hf : ∀ x, f₁ x = f₂ x) :
  is_O_with c f₁ g l → is_O_with c f₂ g l :=
is_O_with.congr rfl hf (λ _, rfl)

theorem is_O_with.congr_right {g₁ g₂ : α → F} {l : filter α} (hg : ∀ x, g₁ x = g₂ x) :
  is_O_with c f g₁ l → is_O_with c f g₂ l :=
is_O_with.congr rfl (λ _, rfl) hg

theorem is_O_with.congr_const {c₁ c₂} {l : filter α} (hc : c₁ = c₂) :
  is_O_with c₁ f g l → is_O_with c₂ f g l :=
is_O_with.congr hc (λ _, rfl) (λ _, rfl)

theorem is_O_congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
    (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
  is_O f₁ g₁ l ↔ is_O f₂ g₂ l :=
by { unfold is_O, exact exists_congr (λ c, is_O_with_congr rfl hf hg) }

theorem is_O.congr' {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
    (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
  is_O f₁ g₁ l → is_O f₂ g₂ l :=
(is_O_congr hf hg).mp

theorem is_O.congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
    (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
  is_O f₁ g₁ l → is_O f₂ g₂ l :=
λ h, h.congr' (univ_mem_sets' hf) (univ_mem_sets' hg)

theorem is_O.congr_left {f₁ f₂ : α → E} {l : filter α} (hf : ∀ x, f₁ x = f₂ x) :
  is_O f₁ g l → is_O f₂ g l :=
is_O.congr hf (λ _, rfl)

theorem is_O.congr_right {g₁ g₂ : α → E} {l : filter α} (hg : ∀ x, g₁ x = g₂ x) :
  is_O f g₁ l → is_O f g₂ l :=
is_O.congr (λ _, rfl) hg

theorem is_o_congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
    (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
  is_o f₁ g₁ l ↔ is_o f₂ g₂ l :=
by { unfold is_o, exact ball_congr (λ c hc, is_O_with_congr (eq.refl c) hf hg) }

theorem is_o.congr' {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
    (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
  is_o f₁ g₁ l → is_o f₂ g₂ l :=
(is_o_congr hf hg).mp

theorem is_o.congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : filter α}
    (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
  is_o f₁ g₁ l → is_o f₂ g₂ l :=
λ h, h.congr' (univ_mem_sets' hf) (univ_mem_sets' hg)

theorem is_o.congr_left {f₁ f₂ : α → E} {l : filter α} (hf : ∀ x, f₁ x = f₂ x) :
  is_o f₁ g l → is_o f₂ g l :=
is_o.congr hf (λ _, rfl)

theorem is_o.congr_right {g₁ g₂ : α → E} {l : filter α} (hg : ∀ x, g₁ x = g₂ x) :
  is_o f g₁ l → is_o f g₂ l :=
is_o.congr (λ _, rfl) hg

/-! ### Filter operations and transitivity -/

theorem is_O_with.comp_tendsto (hcfg : is_O_with c f g l)
  {k : β → α} {l' : filter β} (hk : tendsto k l' l):
  is_O_with c (f ∘ k) (g ∘ k) l' :=
is_O_with.of_bound $ hk hcfg.bound

theorem is_O.comp_tendsto (hfg : is_O f g l) {k : β → α} {l' : filter β} (hk : tendsto k l' l) :
  is_O (f ∘ k) (g ∘ k) l' :=
is_O_iff_is_O_with.2 $ hfg.is_O_with.imp (λ c h, h.comp_tendsto hk)

theorem is_o.comp_tendsto (hfg : is_o f g l) {k : β → α} {l' : filter β} (hk : tendsto k l' l) :
  is_o (f ∘ k) (g ∘ k) l' :=
is_o.of_is_O_with $ λ c cpos, (hfg.forall_is_O_with cpos).comp_tendsto hk

@[simp] theorem is_O_with_map {k : β → α} {l : filter β} :
  is_O_with c f g (map k l) ↔ is_O_with c (f ∘ k) (g ∘ k) l :=
by { unfold is_O_with, exact mem_map }

@[simp] theorem is_O_map {k : β → α} {l : filter β} :
  is_O f g (map k l) ↔ is_O (f ∘ k) (g ∘ k) l :=
by simp only [is_O, is_O_with_map]

@[simp] theorem is_o_map {k : β → α} {l : filter β} :
  is_o f g (map k l) ↔ is_o (f ∘ k) (g ∘ k) l :=
by simp only [is_o, is_O_with_map]

theorem is_O_with.mono (h : is_O_with c f g l') (hl : l ≤ l') : is_O_with c f g l :=
is_O_with.of_bound $ hl h.bound

theorem is_O.mono (h : is_O f g l') (hl : l ≤ l') : is_O f g l :=
is_O_iff_is_O_with.2 $ h.is_O_with.imp (λ c h, h.mono hl)

theorem is_o.mono (h : is_o f g l') (hl : l ≤ l') : is_o f g l :=
is_o.of_is_O_with $ λ c cpos, (h.forall_is_O_with cpos).mono hl

theorem is_O_with.trans (hfg : is_O_with c f g l) (hgk : is_O_with c' g k l) (hc : 0 ≤ c) :
  is_O_with (c * c') f k l :=
begin
  unfold is_O_with at *,
  filter_upwards [hfg, hgk],
  assume x hx hx',
  calc ∥f x∥ ≤ c * ∥g x∥ : hx
  ... ≤ c * (c' * ∥k x∥) : mul_le_mul_of_nonneg_left hx' hc
  ... = c * c' * ∥k x∥ : (mul_assoc _ _ _).symm
end

theorem is_O.trans (hfg : is_O f g' l) (hgk : is_O g' k l) : is_O f k l :=
let ⟨c, cnonneg, hc⟩ := hfg.exists_nonneg, ⟨c', hc'⟩ := hgk.is_O_with in
(hc.trans hc' cnonneg).is_O

theorem is_o.trans_is_O_with (hfg : is_o f g l) (hgk : is_O_with c g k l) (hc : 0 < c) :
  is_o f k l :=
begin
  unfold is_o at *,
  intros c' c'pos,
  have : 0 < c' / c, from div_pos c'pos hc,
  exact ((hfg this).trans hgk (le_of_lt this)).congr_const (div_mul_cancel _ (ne_of_gt hc))
end

theorem is_o.trans_is_O (hfg : is_o f g l) (hgk : is_O g k' l) : is_o f k' l :=
let ⟨c, cpos, hc⟩ := hgk.exists_pos in hfg.trans_is_O_with hc cpos

theorem is_O_with.trans_is_o (hfg : is_O_with c f g l) (hgk : is_o g k l) (hc : 0 < c) :
  is_o f k l :=
begin
  unfold is_o at *,
  intros c' c'pos,
  have : 0 < c' / c, from div_pos c'pos hc,
  exact (hfg.trans (hgk this) (le_of_lt hc)).congr_const (mul_div_cancel' _ (ne_of_gt hc))
end

theorem is_O.trans_is_o (hfg : is_O f g' l) (hgk : is_o g' k l) : is_o f k l :=
let ⟨c, cpos, hc⟩ := hfg.exists_pos in hc.trans_is_o hgk cpos

theorem is_o.trans (hfg : is_o f g l) (hgk : is_o g k' l) : is_o f k' l :=
hfg.trans_is_O hgk.is_O

theorem is_o.trans' (hfg : is_o f g' l) (hgk : is_o g' k l) : is_o f k l :=
hfg.is_O.trans_is_o hgk

section

variable (l)

theorem is_O_with_of_le' (hfg : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : is_O_with c f g l :=
is_O_with.of_bound $ univ_mem_sets' hfg

theorem is_O_with_of_le (hfg : ∀ x, ∥f x∥ ≤ ∥g x∥) : is_O_with 1 f g l :=
is_O_with_of_le' l $ λ x, by { rw one_mul, exact hfg x }

theorem is_O_of_le' (hfg : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : is_O f g l :=
(is_O_with_of_le' l hfg).is_O

theorem is_O_of_le (hfg : ∀ x, ∥f x∥ ≤ ∥g x∥) : is_O f g l :=
(is_O_with_of_le l hfg).is_O

end

theorem is_O_with_refl (f : α → E) (l : filter α) : is_O_with 1 f f l :=
is_O_with_of_le l $ λ _, le_refl _

theorem is_O_refl (f : α → E) (l : filter α) : is_O f f l := (is_O_with_refl f l).is_O

theorem is_O_with.trans_le (hfg : is_O_with c f g l) (hgk : ∀ x, ∥g x∥ ≤ ∥k x∥) (hc : 0 ≤ c) :
  is_O_with c f k l :=
(hfg.trans (is_O_with_of_le l hgk) hc).congr_const $ mul_one c

theorem is_O.trans_le (hfg : is_O f g' l) (hgk : ∀ x, ∥g' x∥ ≤ ∥k x∥) :
  is_O f k l :=
hfg.trans (is_O_of_le l hgk)

theorem is_o.trans_le (hfg : is_o f g l) (hgk : ∀ x, ∥g x∥ ≤ ∥k x∥) :
  is_o f k l :=
hfg.trans_is_O_with (is_O_with_of_le _ hgk) zero_lt_one

section bot

variables (c f g)

@[simp] theorem is_O_with_bot : is_O_with c f g ⊥ := is_O_with.of_bound $ trivial

@[simp] theorem is_O_bot : is_O f g ⊥ := (is_O_with_bot 1 f g).is_O

@[simp] theorem is_o_bot : is_o f g ⊥ := is_o.of_is_O_with $ λ c _, is_O_with_bot c f g

end bot

theorem is_O_with.join (h : is_O_with c f g l) (h' : is_O_with c f g l') :
  is_O_with c f g (l ⊔ l') :=
is_O_with.of_bound $ mem_sup_sets.2 ⟨h.bound, h'.bound⟩

theorem is_O_with.join' (h : is_O_with c f g' l) (h' : is_O_with c' f g' l') :
  is_O_with (max c c') f g' (l ⊔ l') :=
is_O_with.of_bound $
mem_sup_sets.2 ⟨(h.weaken $ le_max_left c c').bound, (h'.weaken $ le_max_right c c').bound⟩

theorem is_O.join (h : is_O f g' l) (h' : is_O f g' l') : is_O f g' (l ⊔ l') :=
let ⟨c, hc⟩ := h.is_O_with, ⟨c', hc'⟩ := h'.is_O_with in (hc.join' hc').is_O

theorem is_o.join (h : is_o f g l) (h' : is_o f g l') :
  is_o f g (l ⊔ l') :=
is_o.of_is_O_with $
λ c cpos, (h.forall_is_O_with cpos).join (h'.forall_is_O_with cpos)

/-! ### Simplification : norm -/

@[simp] theorem is_O_with_norm_right : is_O_with c f (λ x, ∥g' x∥) l ↔ is_O_with c f g' l :=
by simp only [is_O_with, norm_norm]

alias is_O_with_norm_right ↔ asymptotics.is_O_with.of_norm_right asymptotics.is_O_with.norm_right

@[simp] theorem is_O_norm_right : is_O f (λ x, ∥g' x∥) l ↔ is_O f g' l :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_norm_right) }

alias is_O_norm_right ↔ asymptotics.is_O.of_norm_right asymptotics.is_O.norm_right

@[simp] theorem is_o_norm_right : is_o f (λ x, ∥g' x∥) l ↔ is_o f g' l :=
by { unfold is_o, exact forall_congr (λ _, forall_congr $ λ _, is_O_with_norm_right) }

alias is_o_norm_right ↔ asymptotics.is_o.of_norm_right asymptotics.is_o.norm_right

@[simp] theorem is_O_with_norm_left : is_O_with c (λ x, ∥f' x∥) g l ↔ is_O_with c f' g l :=
by simp only [is_O_with, norm_norm]

alias is_O_with_norm_left ↔ asymptotics.is_O_with.of_norm_left asymptotics.is_O_with.norm_left

@[simp] theorem is_O_norm_left : is_O (λ x, ∥f' x∥) g l ↔ is_O f' g l :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_norm_left) }

alias is_O_norm_left ↔ asymptotics.is_O.of_norm_left asymptotics.is_O.norm_left

@[simp] theorem is_o_norm_left : is_o (λ x, ∥f' x∥) g l ↔ is_o f' g l :=
by { unfold is_o,  exact forall_congr (λ _, forall_congr $ λ _, is_O_with_norm_left) }

alias is_o_norm_left ↔ asymptotics.is_o.of_norm_left asymptotics.is_o.norm_left

theorem is_O_with_norm_norm :
  is_O_with c (λ x, ∥f' x∥) (λ x, ∥g' x∥) l ↔ is_O_with c f' g' l :=
is_O_with_norm_left.trans is_O_with_norm_right

alias is_O_with_norm_norm ↔ asymptotics.is_O_with.of_norm_norm asymptotics.is_O_with.norm_norm

theorem is_O_norm_norm :
  is_O (λ x, ∥f' x∥) (λ x, ∥g' x∥) l ↔ is_O f' g' l :=
is_O_norm_left.trans is_O_norm_right

alias is_O_norm_norm ↔ asymptotics.is_O.of_norm_norm asymptotics.is_O.norm_norm

theorem is_o_norm_norm :
  is_o (λ x, ∥f' x∥) (λ x, ∥g' x∥) l ↔ is_o f' g' l :=
is_o_norm_left.trans is_o_norm_right

alias is_o_norm_norm ↔ asymptotics.is_o.of_norm_norm asymptotics.is_o.norm_norm

/-! ### Simplification: negate -/

@[simp] theorem is_O_with_neg_right : is_O_with c f (λ x, -(g' x)) l ↔ is_O_with c f g' l :=
by simp only [is_O_with, norm_neg]

alias is_O_with_neg_right ↔ asymptotics.is_O_with.of_neg_right asymptotics.is_O_with.neg_right

@[simp] theorem is_O_neg_right : is_O f (λ x, -(g' x)) l ↔ is_O f g' l :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_neg_right) }

alias is_O_neg_right ↔ asymptotics.is_O.of_neg_right asymptotics.is_O.neg_right

@[simp] theorem is_o_neg_right : is_o f (λ x, -(g' x)) l ↔ is_o f g' l :=
by { unfold is_o, exact forall_congr (λ _, (forall_congr (λ _, is_O_with_neg_right))) }

alias is_o_neg_right ↔ asymptotics.is_o.of_neg_right asymptotics.is_o.neg_right

@[simp] theorem is_O_with_neg_left : is_O_with c (λ x, -(f' x)) g l ↔ is_O_with c f' g l :=
by simp only [is_O_with, norm_neg]

alias is_O_with_neg_left ↔ asymptotics.is_O_with.of_neg_left asymptotics.is_O_with.neg_left

@[simp] theorem is_O_neg_left : is_O (λ x, -(f' x)) g l ↔ is_O f' g l :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_neg_left) }

alias is_O_neg_left ↔ asymptotics.is_O.of_neg_left asymptotics.is_O.neg_left

@[simp] theorem is_o_neg_left : is_o (λ x, -(f' x)) g l ↔ is_o f' g l :=
by { unfold is_o, exact forall_congr (λ _, (forall_congr (λ _, is_O_with_neg_left))) }

alias is_o_neg_left ↔ asymptotics.is_o.of_neg_right asymptotics.is_o.neg_left

/-! ### Product of functions (right) -/

lemma is_O_with_fst_prod : is_O_with 1 f' (λ x, (f' x, g' x)) l :=
is_O_with_of_le l $ λ x, le_max_left _ _

lemma is_O_with_snd_prod : is_O_with 1 g' (λ x, (f' x, g' x)) l :=
is_O_with_of_le l $ λ x, le_max_right _ _

lemma is_O_fst_prod : is_O f' (λ x, (f' x, g' x)) l := is_O_with_fst_prod.is_O

lemma is_O_snd_prod : is_O g' (λ x, (f' x, g' x)) l := is_O_with_snd_prod.is_O

lemma is_O_fst_prod' {f' : α → E' × F'} : is_O (λ x, (f' x).1) f' l :=
by simpa [is_O, is_O_with] using is_O_fst_prod

lemma is_O_snd_prod' {f' : α → E' × F'} : is_O (λ x, (f' x).2) f' l :=
by simpa [is_O, is_O_with] using is_O_snd_prod

section

variables (f' k')

lemma is_O_with.prod_rightl (h : is_O_with c f g' l) (hc : 0 ≤ c) :
  is_O_with c f (λ x, (g' x, k' x)) l :=
(h.trans is_O_with_fst_prod hc).congr_const (mul_one c)

lemma is_O.prod_rightl (h : is_O f g' l) : is_O f (λx, (g' x, k' x)) l :=
let ⟨c, cnonneg, hc⟩ := h.exists_nonneg in (hc.prod_rightl k' cnonneg).is_O

lemma is_o.prod_rightl (h : is_o f g' l) : is_o f (λ x, (g' x, k' x)) l :=
is_o.of_is_O_with $
λ c cpos, (h.forall_is_O_with cpos).prod_rightl k' (le_of_lt cpos)

lemma is_O_with.prod_rightr (h : is_O_with c f g' l) (hc : 0 ≤ c) :
  is_O_with c f (λ x, (f' x, g' x)) l :=
(h.trans is_O_with_snd_prod hc).congr_const (mul_one c)

lemma is_O.prod_rightr (h : is_O f g' l) : is_O f (λx, (f' x, g' x)) l :=
let ⟨c, cnonneg, hc⟩ := h.exists_nonneg in (hc.prod_rightr f' cnonneg).is_O

lemma is_o.prod_rightr (h : is_o f g' l) : is_o f (λx, (f' x, g' x)) l :=
is_o.of_is_O_with $
λ c cpos, (h.forall_is_O_with cpos).prod_rightr f' (le_of_lt cpos)

end

lemma is_O_with.prod_left_same (hf : is_O_with c f' k' l) (hg : is_O_with c g' k' l) :
  is_O_with c (λ x, (f' x, g' x)) k' l :=
by rw is_O_with_iff at *; filter_upwards [hf, hg] λ x, max_le

lemma is_O_with.prod_left (hf : is_O_with c f' k' l) (hg : is_O_with c' g' k' l) :
  is_O_with (max c c') (λ x, (f' x, g' x)) k' l :=
(hf.weaken $ le_max_left c c').prod_left_same (hg.weaken $ le_max_right c c')

lemma is_O_with.prod_left_fst (h : is_O_with c (λ x, (f' x, g' x)) k' l) :
  is_O_with c f' k' l :=
(is_O_with_fst_prod.trans h zero_le_one).congr_const $ one_mul c

lemma is_O_with.prod_left_snd (h : is_O_with c (λ x, (f' x, g' x)) k' l) :
  is_O_with c g' k' l :=
(is_O_with_snd_prod.trans h zero_le_one).congr_const $ one_mul c

lemma is_O_with_prod_left :
   is_O_with c (λ x, (f' x, g' x)) k' l ↔ is_O_with c f' k' l ∧ is_O_with c g' k' l :=
⟨λ h, ⟨h.prod_left_fst, h.prod_left_snd⟩, λ h, h.1.prod_left_same h.2⟩

lemma is_O.prod_left (hf : is_O f' k' l) (hg : is_O g' k' l) : is_O (λ x, (f' x, g' x)) k' l :=
let ⟨c, hf⟩ := hf.is_O_with, ⟨c', hg⟩ := hg.is_O_with in (hf.prod_left hg).is_O

lemma is_O.prod_left_fst (h : is_O (λ x, (f' x, g' x)) k' l) : is_O f' k' l :=
is_O_fst_prod.trans h

lemma is_O.prod_left_snd (h : is_O (λ x, (f' x, g' x)) k' l) : is_O g' k' l :=
is_O_snd_prod.trans h

@[simp] lemma is_O_prod_left :
  is_O (λ x, (f' x, g' x)) k' l ↔ is_O f' k' l ∧ is_O g' k' l :=
⟨λ h, ⟨h.prod_left_fst, h.prod_left_snd⟩, λ h, h.1.prod_left h.2⟩

lemma is_o.prod_left (hf : is_o f' k' l) (hg : is_o g' k' l) : is_o (λ x, (f' x, g' x)) k' l :=
is_o.of_is_O_with $
λ c hc, (hf.forall_is_O_with hc).prod_left_same (hg.forall_is_O_with hc)

lemma is_o.prod_left_fst (h : is_o (λ x, (f' x, g' x)) k' l) : is_o f' k' l :=
is_O_fst_prod.trans_is_o h

lemma is_o.prod_left_snd (h : is_o (λ x, (f' x, g' x)) k' l) : is_o g' k' l :=
is_O_snd_prod.trans_is_o h

@[simp] lemma is_o_prod_left :
  is_o (λ x, (f' x, g' x)) k' l ↔ is_o f' k' l ∧ is_o g' k' l :=
⟨λ h, ⟨h.prod_left_fst, h.prod_left_snd⟩, λ h, h.1.prod_left h.2⟩

lemma is_O_with.eq_zero_imp (h : is_O_with c f' g' l) : ∀ᶠ x in l, g' x = 0 → f' x = 0 :=
eventually.mono h.bound $ λ x hx hg, norm_le_zero_iff.1 $ by simpa [hg] using hx

lemma is_O.eq_zero_imp (h : is_O f' g' l) : ∀ᶠ x in l, g' x = 0 → f' x = 0 :=
let ⟨C, hC⟩ := h.is_O_with in hC.eq_zero_imp

/-! ### Addition and subtraction -/

section add_sub

variables {c₁ c₂ : ℝ} {f₁ f₂ : α → E'}

theorem is_O_with.add (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_O_with c₂ f₂ g l) :
  is_O_with (c₁ + c₂) (λ x, f₁ x + f₂ x) g l :=
by rw is_O_with at *; filter_upwards [h₁, h₂] λ x hx₁ hx₂,
calc ∥f₁ x + f₂ x∥ ≤ c₁ * ∥g x∥ + c₂ * ∥g x∥ : norm_add_le_of_le hx₁ hx₂
               ... = (c₁ + c₂) * ∥g x∥       : (add_mul _ _ _).symm

theorem is_O.add (h₁ : is_O f₁ g l) (h₂ : is_O f₂ g l) : is_O (λ x, f₁ x + f₂ x) g l :=
let ⟨c₁, hc₁⟩ := h₁.is_O_with, ⟨c₂, hc₂⟩ := h₂.is_O_with in (hc₁.add hc₂).is_O

theorem is_o.add (h₁ : is_o f₁ g l) (h₂ : is_o f₂ g l) : is_o (λ x, f₁ x + f₂ x) g l :=
is_o.of_is_O_with $ λ c cpos, ((h₁.forall_is_O_with $ half_pos cpos).add
  (h₂.forall_is_O_with $ half_pos cpos)).congr_const (add_halves c)

theorem is_o.add_add {g₁ g₂ : α → F'} (h₁ : is_o f₁ g₁ l) (h₂ : is_o f₂ g₂ l) :
  is_o (λ x, f₁ x + f₂ x) (λ x, ∥g₁ x∥ + ∥g₂ x∥) l :=
by refine (h₁.trans_le $ λ x, _).add (h₂.trans_le _);
  simp [real.norm_eq_abs, abs_of_nonneg, add_nonneg]

theorem is_O.add_is_o (h₁ : is_O f₁ g l) (h₂ : is_o f₂ g l) : is_O (λ x, f₁ x + f₂ x) g l :=
h₁.add h₂.is_O

theorem is_o.add_is_O (h₁ : is_o f₁ g l) (h₂ : is_O f₂ g l) : is_O (λ x, f₁ x + f₂ x) g l :=
h₁.is_O.add h₂

theorem is_O_with.add_is_o (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_o f₂ g l) (hc : c₁ < c₂) :
  is_O_with c₂ (λx, f₁ x + f₂ x) g l :=
(h₁.add (h₂.forall_is_O_with (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)

theorem is_o.add_is_O_with (h₁ : is_o f₁ g l) (h₂ : is_O_with c₁ f₂ g l) (hc : c₁ < c₂) :
  is_O_with c₂ (λx, f₁ x + f₂ x) g l :=
(h₂.add_is_o h₁ hc).congr_left $ λ _, add_comm _ _

theorem is_O_with.sub (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_O_with c₂ f₂ g l) :
  is_O_with (c₁ + c₂) (λ x, f₁ x - f₂ x) g l :=
by simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem is_O_with.sub_is_o (h₁ : is_O_with c₁ f₁ g l) (h₂ : is_o f₂ g l) (hc : c₁ < c₂) :
  is_O_with c₂ (λ x, f₁ x - f₂ x) g l :=
by simpa only [sub_eq_add_neg] using h₁.add_is_o h₂.neg_left hc

theorem is_O.sub (h₁ : is_O f₁ g l) (h₂ : is_O f₂ g l) : is_O (λ x, f₁ x - f₂ x) g l :=
by simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem is_o.sub (h₁ : is_o f₁ g l) (h₂ : is_o f₂ g l) : is_o (λ x, f₁ x - f₂ x) g l :=
by simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/

section is_oO_as_rel

variables {f₁ f₂ f₃ : α → E'}

theorem is_O_with.symm (h : is_O_with c (λ x, f₁ x - f₂ x) g l) :
  is_O_with c (λ x, f₂ x - f₁ x) g l :=
h.neg_left.congr_left $ λ x, neg_sub _ _

theorem is_O_with_comm :
  is_O_with c (λ x, f₁ x - f₂ x) g l ↔ is_O_with c (λ x, f₂ x - f₁ x) g l :=
⟨is_O_with.symm, is_O_with.symm⟩

theorem is_O.symm (h : is_O (λ x, f₁ x - f₂ x) g l) : is_O (λ x, f₂ x - f₁ x) g l :=
h.neg_left.congr_left $ λ x, neg_sub _ _

theorem is_O_comm : is_O (λ x, f₁ x - f₂ x) g l ↔ is_O (λ x, f₂ x - f₁ x) g l :=
⟨is_O.symm, is_O.symm⟩

theorem is_o.symm (h : is_o (λ x, f₁ x - f₂ x) g l) : is_o (λ x, f₂ x - f₁ x) g l :=
by simpa only [neg_sub] using h.neg_left

theorem is_o_comm : is_o (λ x, f₁ x - f₂ x) g l ↔ is_o (λ x, f₂ x - f₁ x) g l :=
⟨is_o.symm, is_o.symm⟩

theorem is_O_with.triangle (h₁ : is_O_with c (λ x, f₁ x - f₂ x) g l)
  (h₂ : is_O_with c' (λ x, f₂ x - f₃ x) g l) :
  is_O_with (c + c') (λ x, f₁ x - f₃ x) g l :=
(h₁.add h₂).congr_left $ λ x, sub_add_sub_cancel _ _ _

theorem is_O.triangle (h₁ : is_O (λ x, f₁ x - f₂ x) g l) (h₂ : is_O (λ x, f₂ x - f₃ x) g l) :
  is_O (λ x, f₁ x - f₃ x) g l :=
(h₁.add h₂).congr_left $ λ x, sub_add_sub_cancel _ _ _

theorem is_o.triangle (h₁ : is_o (λ x, f₁ x - f₂ x) g l) (h₂ : is_o (λ x, f₂ x - f₃ x) g l) :
  is_o (λ x, f₁ x - f₃ x) g l :=
(h₁.add h₂).congr_left $ λ x, sub_add_sub_cancel _ _ _

theorem is_O.congr_of_sub (h : is_O (λ x, f₁ x - f₂ x) g l) :
  is_O f₁ g l ↔ is_O f₂ g l :=
⟨λ h', (h'.sub h).congr_left (λ x, sub_sub_cancel _ _),
 λ h', (h.add h').congr_left (λ x, sub_add_cancel _ _)⟩

theorem is_o.congr_of_sub (h : is_o (λ x, f₁ x - f₂ x) g l) :
  is_o f₁ g l ↔ is_o f₂ g l :=
⟨λ h', (h'.sub h).congr_left (λ x, sub_sub_cancel _ _),
 λ h', (h.add h').congr_left (λ x, sub_add_cancel _ _)⟩

end is_oO_as_rel

/-! ### Zero, one, and other constants -/

section zero_const

variables (g g' l)

theorem is_o_zero : is_o (λ x, (0 : E')) g' l :=
is_o.of_bound $ λ c hc, univ_mem_sets' $ λ x,
by simpa using mul_nonneg (le_of_lt hc) (norm_nonneg $ g' x)

theorem is_O_with_zero (hc : 0 ≤ c) : is_O_with c (λ x, (0 : E')) g' l :=
is_O_with.of_bound $ univ_mem_sets' $ λ x, by simpa using mul_nonneg hc (norm_nonneg $ g' x)

theorem is_O_with_zero' : is_O_with 0 (λ x, (0 : E')) g l :=
is_O_with.of_bound $ univ_mem_sets' $ λ x, by simp

theorem is_O_zero : is_O (λ x, (0 : E')) g l :=
is_O_iff_is_O_with.2 ⟨0, is_O_with_zero' _ _⟩

theorem is_O_refl_left : is_O (λ x, f' x - f' x) g' l :=
(is_O_zero g' l).congr_left $ λ x, (sub_self _).symm

theorem is_o_refl_left : is_o (λ x, f' x - f' x) g' l :=
(is_o_zero g' l).congr_left $ λ x, (sub_self _).symm

variables {g g' l}

@[simp] theorem is_O_with_zero_right_iff :
  is_O_with c f' (λ x, (0 : F')) l ↔ ∀ᶠ x in l, f' x = 0 :=
by simp only [is_O_with, exists_prop, true_and, norm_zero, mul_zero, norm_le_zero_iff]

@[simp] theorem is_O_zero_right_iff : is_O f' (λ x, (0 : F')) l ↔ ∀ᶠ x in l, f' x = 0 :=
⟨λ h, let ⟨c, hc⟩ := h.is_O_with in is_O_with_zero_right_iff.1 hc,
  λ h, (is_O_with_zero_right_iff.2 h : is_O_with 1 _ _ _).is_O⟩

@[simp] theorem is_o_zero_right_iff :
  is_o f' (λ x, (0 : F')) l ↔ ∀ᶠ x in l, f' x = 0 :=
⟨λ h, is_O_zero_right_iff.1 h.is_O,
  λ h, is_o.of_is_O_with $ λ c hc, is_O_with_zero_right_iff.2 h⟩

theorem is_O_with_const_const (c : E) {c' : F'} (hc' : c' ≠ 0) (l : filter α) :
  is_O_with (∥c∥ / ∥c'∥) (λ x : α, c) (λ x, c') l :=
begin
  unfold is_O_with,
  apply univ_mem_sets',
  intro x,
  rw [mem_set_of_eq, div_mul_cancel],
  rwa [ne.def, norm_eq_zero]
end

theorem is_O_const_const (c : E) {c' : F'} (hc' : c' ≠ 0) (l : filter α) :
  is_O (λ x : α, c) (λ x, c') l :=
(is_O_with_const_const c hc' l).is_O

end zero_const

@[simp] lemma is_O_with_top : is_O_with c f g ⊤ ↔ ∀ x, ∥f x∥ ≤ c * ∥g x∥ := by rw is_O_with; refl

@[simp] lemma is_O_top : is_O f g ⊤ ↔ ∃ C, ∀ x, ∥f x∥ ≤ C * ∥g x∥ := by rw is_O_iff; refl

@[simp] lemma is_o_top : is_o f' g' ⊤ ↔ ∀ x, f' x = 0 :=
begin
  refine ⟨_, λ h, (is_o_zero g' ⊤).congr (λ x, (h x).symm) (λ x, rfl)⟩,
  simp only [is_o_iff, eventually_top],
  refine λ h x, norm_le_zero_iff.1 _,
  have : tendsto (λ c : ℝ, c * ∥g' x∥) (𝓝[Ioi 0] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left inf_le_left,
  exact le_of_tendsto_of_tendsto tendsto_const_nhds this
    (eventually_nhds_within_iff.2 $ eventually_of_forall $ λ c hc, h hc x)
end

@[simp] lemma is_O_with_principal {s : set α} :
  is_O_with c f g (𝓟 s) ↔ ∀ x ∈ s, ∥f x∥ ≤ c * ∥g x∥ :=
by rw is_O_with; refl

lemma is_O_principal {s : set α} :
  is_O f g (𝓟 s) ↔ ∃ c, ∀ x ∈ s, ∥f x∥ ≤ c * ∥g x∥ :=
by rw is_O_iff; refl

theorem is_O_with_const_one (c : E) (l : filter α) : is_O_with ∥c∥ (λ x : α, c) (λ x, (1 : 𝕜)) l :=
begin
  refine (is_O_with_const_const c _ l).congr_const _,
  { rw [norm_one, div_one] },
  { exact one_ne_zero }
end

theorem is_O_const_one (c : E) (l : filter α) : is_O (λ x : α, c) (λ x, (1 : 𝕜)) l :=
(is_O_with_const_one c l).is_O

section

variable (𝕜)

theorem is_o_const_iff_is_o_one {c : F'} (hc : c ≠ 0) :
  is_o f (λ x, c) l ↔ is_o f (λ x, (1:𝕜)) l :=
⟨λ h, h.trans_is_O $ is_O_const_one c l, λ h, h.trans_is_O $ is_O_const_const _ hc _⟩

end

theorem is_o_const_iff {c : F'} (hc : c ≠ 0) :
  is_o f' (λ x, c) l ↔ tendsto f' l (𝓝 0) :=
(is_o_const_iff_is_o_one ℝ hc).trans
begin
  clear hc c,
  simp only [is_o, is_O_with, norm_one, mul_one, metric.nhds_basis_closed_ball.tendsto_right_iff,
    metric.mem_closed_ball, dist_zero_right]
end

theorem is_o_const_const_iff [ne_bot l] {d : E'} {c : F'} (hc : c ≠ 0) :
  is_o (λ x, d) (λ x, c) l ↔ d = 0 :=
begin
  rw is_o_const_iff hc,
  refine ⟨λ h, tendsto_nhds_unique tendsto_const_nhds h, _⟩,
  rintros rfl,
  exact tendsto_const_nhds,
end

lemma is_o_id_const {c : F'} (hc : c ≠ 0) :
  is_o (λ (x : E'), x) (λ x, c) (𝓝 0) :=
(is_o_const_iff hc).mpr (continuous_id.tendsto 0)

theorem is_O_const_of_tendsto {y : E'} (h : tendsto f' l (𝓝 y)) {c : F'} (hc : c ≠ 0) :
  is_O f' (λ x, c) l :=
begin
  refine is_O.trans _ (is_O_const_const (∥y∥ + 1) hc l),
  refine is_O.of_bound 1 _,
  simp only [is_O_with, one_mul],
  have : tendsto (λx, ∥f' x∥) l (𝓝 ∥y∥), from (continuous_norm.tendsto _).comp h,
  have Iy : ∥y∥ < ∥∥y∥ + 1∥, from lt_of_lt_of_le (lt_add_one _) (le_abs_self _),
  exact this (ge_mem_nhds Iy)
end

section

variable (𝕜)

theorem is_o_one_iff : is_o f' (λ x, (1 : 𝕜)) l ↔ tendsto f' l (𝓝 0) :=
is_o_const_iff one_ne_zero

theorem is_O_one_of_tendsto {y : E'} (h : tendsto f' l (𝓝 y)) :
  is_O f' (λ x, (1:𝕜)) l :=
is_O_const_of_tendsto h one_ne_zero

theorem is_O.trans_tendsto_nhds (hfg : is_O f g' l) {y : F'} (hg : tendsto g' l (𝓝 y)) :
  is_O f (λ x, (1:𝕜)) l :=
hfg.trans $ is_O_one_of_tendsto 𝕜 hg

end

theorem is_O.trans_tendsto (hfg : is_O f' g' l) (hg : tendsto g' l (𝓝 0)) :
  tendsto f' l (𝓝 0) :=
(is_o_one_iff ℝ).1 $ hfg.trans_is_o $ (is_o_one_iff ℝ).2 hg

theorem is_o.trans_tendsto (hfg : is_o f' g' l) (hg : tendsto g' l (𝓝 0)) :
  tendsto f' l (𝓝 0) :=
hfg.is_O.trans_tendsto hg

/-! ### Multiplication by a constant -/

theorem is_O_with_const_mul_self (c : R) (f : α → R) (l : filter α) :
  is_O_with ∥c∥ (λ x, c * f x) f l :=
is_O_with_of_le' _ $ λ x, norm_mul_le _ _

theorem is_O_const_mul_self (c : R) (f : α → R) (l : filter α) :
  is_O (λ x, c * f x) f l :=
(is_O_with_const_mul_self c f l).is_O

theorem is_O_with.const_mul_left {f : α → R} (h : is_O_with c f g l) (c' : R) :
  is_O_with (∥c'∥ * c) (λ x, c' * f x) g l :=
(is_O_with_const_mul_self c' f l).trans h (norm_nonneg c')

theorem is_O.const_mul_left {f : α → R} (h : is_O f g l) (c' : R) :
  is_O (λ x, c' * f x) g l :=
let ⟨c, hc⟩ := h.is_O_with in (hc.const_mul_left c').is_O

theorem is_O_with_self_const_mul' (u : units R) (f : α → R) (l : filter α) :
  is_O_with ∥(↑u⁻¹:R)∥ f (λ x, ↑u * f x) l :=
(is_O_with_const_mul_self ↑u⁻¹ _ l).congr_left $ λ x, u.inv_mul_cancel_left (f x)

theorem is_O_with_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : filter α) :
  is_O_with ∥c∥⁻¹ f (λ x, c * f x) l :=
(is_O_with_self_const_mul' (units.mk0 c hc) f l).congr_const $
  normed_field.norm_inv c

theorem is_O_self_const_mul' {c : R} (hc : is_unit c) (f : α → R) (l : filter α) :
  is_O f (λ x, c * f x) l :=
let ⟨u, hu⟩ := hc in hu ▸ (is_O_with_self_const_mul' u f l).is_O

theorem is_O_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : filter α) :
  is_O f (λ x, c * f x) l :=
is_O_self_const_mul' (is_unit.mk0 c hc) f l

theorem is_O_const_mul_left_iff' {f : α → R} {c : R} (hc : is_unit c) :
  is_O (λ x, c * f x) g l ↔ is_O f g l :=
⟨(is_O_self_const_mul' hc f l).trans, λ h, h.const_mul_left c⟩

theorem is_O_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  is_O (λ x, c * f x) g l ↔ is_O f g l :=
is_O_const_mul_left_iff' $ is_unit.mk0 c hc

theorem is_o.const_mul_left {f : α → R} (h : is_o f g l) (c : R) :
  is_o (λ x, c * f x) g l :=
(is_O_const_mul_self c f l).trans_is_o h

theorem is_o_const_mul_left_iff' {f : α → R} {c : R} (hc : is_unit c) :
  is_o (λ x, c * f x) g l ↔ is_o f g l :=
⟨(is_O_self_const_mul' hc f l).trans_is_o, λ h, h.const_mul_left c⟩

theorem is_o_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  is_o (λ x, c * f x) g l ↔ is_o f g l :=
is_o_const_mul_left_iff' $ is_unit.mk0 c hc

theorem is_O_with.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
  (h : is_O_with c' f (λ x, c * g x) l) :
  is_O_with (c' * ∥c∥) f g l :=
h.trans (is_O_with_const_mul_self c g l) hc'

theorem is_O.of_const_mul_right {g : α → R} {c : R}
  (h : is_O f (λ x, c * g x) l) :
  is_O f g l :=
let ⟨c, cnonneg, hc⟩ := h.exists_nonneg in (hc.of_const_mul_right cnonneg).is_O

theorem is_O_with.const_mul_right' {g : α → R} {u : units R} {c' : ℝ} (hc' : 0 ≤ c')
  (h : is_O_with c' f g l) :
  is_O_with (c' * ∥(↑u⁻¹:R)∥) f (λ x, ↑u * g x) l :=
h.trans (is_O_with_self_const_mul' _ _ _) hc'

theorem is_O_with.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0)
  {c' : ℝ} (hc' : 0 ≤ c') (h : is_O_with c' f g l) :
  is_O_with (c' * ∥c∥⁻¹) f (λ x, c * g x) l :=
h.trans (is_O_with_self_const_mul c hc g l) hc'

theorem is_O.const_mul_right' {g : α → R} {c : R} (hc : is_unit c) (h : is_O f g l) :
  is_O f (λ x, c * g x) l :=
h.trans (is_O_self_const_mul' hc g l)

theorem is_O.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : is_O f g l) :
  is_O f (λ x, c * g x) l :=
h.const_mul_right' $ is_unit.mk0 c hc

theorem is_O_const_mul_right_iff' {g : α → R} {c : R} (hc : is_unit c) :
  is_O f (λ x, c * g x) l ↔ is_O f g l :=
⟨λ h, h.of_const_mul_right, λ h, h.const_mul_right' hc⟩

theorem is_O_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  is_O f (λ x, c * g x) l ↔ is_O f g l :=
is_O_const_mul_right_iff' $ is_unit.mk0 c hc

theorem is_o.of_const_mul_right {g : α → R} {c : R} (h : is_o f (λ x, c * g x) l) :
  is_o f g l :=
h.trans_is_O (is_O_const_mul_self c g l)

theorem is_o.const_mul_right' {g : α → R} {c : R} (hc : is_unit c) (h : is_o f g l) :
  is_o f (λ x, c * g x) l :=
h.trans_is_O (is_O_self_const_mul' hc g l)

theorem is_o.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : is_o f g l) :
  is_o f (λ x, c * g x) l :=
h.const_mul_right' $ is_unit.mk0 c hc

theorem is_o_const_mul_right_iff' {g : α → R} {c : R} (hc : is_unit c) :
  is_o f (λ x, c * g x) l ↔ is_o f g l :=
⟨λ h, h.of_const_mul_right, λ h, h.const_mul_right' hc⟩

theorem is_o_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  is_o f (λ x, c * g x) l ↔ is_o f g l :=
is_o_const_mul_right_iff' $ is_unit.mk0 c hc

/-! ### Multiplication -/

theorem is_O_with.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ}
  (h₁ : is_O_with c₁ f₁ g₁ l) (h₂ : is_O_with c₂ f₂ g₂ l) :
  is_O_with (c₁ * c₂) (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
begin
  unfold is_O_with at *,
  filter_upwards [h₁, h₂],
  intros x hx₁ hx₂,
  apply le_trans (norm_mul_le _ _),
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1,
  rw normed_field.norm_mul,
  ac_refl
end

theorem is_O.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜}
  (h₁ : is_O f₁ g₁ l) (h₂ : is_O f₂ g₂ l) :
  is_O (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
let ⟨c, hc⟩ := h₁.is_O_with, ⟨c', hc'⟩ := h₂.is_O_with in (hc.mul hc').is_O

theorem is_O.mul_is_o {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜}
  (h₁ : is_O f₁ g₁ l) (h₂ : is_o f₂ g₂ l) :
  is_o (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
begin
  unfold is_o at *,
  intros c cpos,
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩,
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gt c'pos))
end

theorem is_o.mul_is_O {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜}
  (h₁ : is_o f₁ g₁ l) (h₂ : is_O f₂ g₂ l) :
  is_o (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
begin
  unfold is_o at *,
  intros c cpos,
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩,
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gt c'pos))
end

theorem is_o.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : is_o f₁ g₁ l) (h₂ : is_o f₂ g₂ l) :
  is_o (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
h₁.mul_is_O h₂.is_O

theorem is_O_with.pow' {f : α → R} {g : α → 𝕜} (h : is_O_with c f g l) :
  ∀ n : ℕ, is_O_with (nat.cases_on n ∥(1 : R)∥ (λ n, c ^ (n + 1))) (λ x, f x ^ n) (λ x, g x ^ n) l
| 0 := by simpa using is_O_with_const_const (1 : R) (@one_ne_zero 𝕜 _ _) l
| 1 := by simpa
| (n + 2) := by simpa [pow_succ] using h.mul (is_O_with.pow' (n + 1))

theorem is_O_with.pow [norm_one_class R] {f : α → R} {g : α → 𝕜} (h : is_O_with c f g l) :
  ∀ n : ℕ, is_O_with (c ^ n) (λ x, f x ^ n) (λ x, g x ^ n) l
| 0 := by simpa using h.pow' 0
| (n + 1) := h.pow' (n + 1)

theorem is_O.pow {f : α → R} {g : α → 𝕜} (h : is_O f g l) (n : ℕ) :
  is_O (λ x, f x ^ n) (λ x, g x ^ n) l :=
let ⟨C, hC⟩ := h.is_O_with in is_O_iff_is_O_with.2 ⟨_, hC.pow' n⟩

theorem is_o.pow {f : α → R} {g : α → 𝕜} (h : is_o f g l) {n : ℕ} (hn : 0 < n) :
  is_o (λ x, f x ^ n) (λ x, g x ^ n) l :=
begin
  cases n, exact hn.false.elim, clear hn,
  induction n with n ihn, { simpa only [pow_one] },
  convert h.mul ihn; simp [pow_succ]
end

/-! ### Scalar multiplication -/

section smul_const
variables [normed_space 𝕜 E']

theorem is_O_with.const_smul_left (h : is_O_with c f' g l) (c' : 𝕜) :
  is_O_with (∥c'∥ * c) (λ x, c' • f' x) g l :=
by refine ((h.norm_left.const_mul_left (∥c'∥)).congr _ _ (λ _, rfl)).of_norm_left;
    intros; simp only [norm_norm, norm_smul]

theorem is_O_const_smul_left_iff {c : 𝕜} (hc : c ≠ 0) :
  is_O (λ x, c • f' x) g l ↔ is_O f' g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_O_norm_left], simp only [norm_smul],
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left],
end

theorem is_o_const_smul_left (h : is_o f' g l) (c : 𝕜) :
  is_o (λ x, c • f' x) g l :=
begin
  refine ((h.norm_left.const_mul_left (∥c∥)).congr_left _).of_norm_left,
  exact λ x, (norm_smul _ _).symm
end

theorem is_o_const_smul_left_iff {c : 𝕜} (hc : c ≠ 0) :
  is_o (λ x, c • f' x) g l ↔ is_o f' g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_o_norm_left], simp only [norm_smul],
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]
end

theorem is_O_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
  is_O f (λ x, c • f' x) l ↔ is_O f f' l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_O_norm_right], simp only [norm_smul],
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]
end

theorem is_o_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
  is_o f (λ x, c • f' x) l ↔ is_o f f' l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_o_norm_right], simp only [norm_smul],
  rw [is_o_const_mul_right_iff cne0, is_o_norm_right]
end

end smul_const

section smul

variables [normed_space 𝕜 E'] [normed_space 𝕜 F']

theorem is_O_with.smul {k₁ k₂ : α → 𝕜} (h₁ : is_O_with c k₁ k₂ l) (h₂ : is_O_with c' f' g' l) :
  is_O_with (c * c') (λ x, k₁ x • f' x) (λ x, k₂ x • g' x) l :=
by refine ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_O.smul {k₁ k₂ : α → 𝕜} (h₁ : is_O k₁ k₂ l) (h₂ : is_O f' g' l) :
  is_O (λ x, k₁ x • f' x) (λ x, k₂ x • g' x) l :=
by refine ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_O.smul_is_o {k₁ k₂ : α → 𝕜} (h₁ : is_O k₁ k₂ l) (h₂ : is_o f' g' l) :
  is_o (λ x, k₁ x • f' x) (λ x, k₂ x • g' x) l :=
by refine ((h₁.norm_norm.mul_is_o h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_o.smul_is_O {k₁ k₂ : α → 𝕜} (h₁ : is_o k₁ k₂ l) (h₂ : is_O f' g' l) :
  is_o (λ x, k₁ x • f' x) (λ x, k₂ x • g' x) l :=
by refine ((h₁.norm_norm.mul_is_O h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_o.smul {k₁ k₂ : α → 𝕜} (h₁ : is_o k₁ k₂ l) (h₂ : is_o f' g' l) :
  is_o (λ x, k₁ x • f' x) (λ x, k₂ x • g' x) l :=
by refine ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

end smul

/-! ### Sum -/

section sum

variables {ι : Type*} {A : ι → α → E'} {C : ι → ℝ} {s : finset ι}

theorem is_O_with.sum (h : ∀ i ∈ s, is_O_with (C i) (A i) g l) :
  is_O_with (∑ i in s, C i) (λ x, ∑ i in s, A i x) g l :=
begin
  induction s using finset.induction_on with i s is IH,
  { simp only [is_O_with_zero', finset.sum_empty, forall_true_iff] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

theorem is_O.sum (h : ∀ i ∈ s, is_O (A i) g l) :
  is_O (λ x, ∑ i in s, A i x) g l :=
begin
  induction s using finset.induction_on with i s is IH,
  { simp only [is_O_zero, finset.sum_empty, forall_true_iff] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

theorem is_o.sum (h : ∀ i ∈ s, is_o (A i) g' l) :
  is_o (λ x, ∑ i in s, A i x) g' l :=
begin
  induction s using finset.induction_on with i s is IH,
  { simp only [is_o_zero, finset.sum_empty, forall_true_iff] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

end sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/

theorem is_o.tendsto_0 {f g : α → 𝕜} {l : filter α} (h : is_o f g l) :
  tendsto (λ x, f x / (g x)) l (𝓝 0) :=
have eq₁ : is_o (λ x, f x / g x) (λ x, g x / g x) l,
  by simpa only [div_eq_mul_inv] using h.mul_is_O (is_O_refl _ _),
have eq₂ : is_O (λ x, g x / g x) (λ x, (1 : 𝕜)) l,
  from is_O_of_le _ (λ x, by by_cases h : ∥g x∥ = 0; simp [h, zero_le_one]),
(is_o_one_iff 𝕜).mp (eq₁.trans_is_O eq₂)

theorem is_o_iff_tendsto' {f g : α → 𝕜} {l : filter α}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
  is_o f g l ↔ tendsto (λ x, f x / (g x)) l (𝓝 0) :=
iff.intro is_o.tendsto_0 $ λ h,
  (((is_o_one_iff _).mpr h).mul_is_O (is_O_refl g l)).congr'
    (hgf.mono $ λ x, div_mul_cancel_of_imp) (eventually_of_forall $ λ x, one_mul _)

theorem is_o_iff_tendsto {f g : α → 𝕜} {l : filter α}
    (hgf : ∀ x, g x = 0 → f x = 0) :
  is_o f g l ↔ tendsto (λ x, f x / (g x)) l (𝓝 0) :=
⟨λ h, h.tendsto_0, (is_o_iff_tendsto' (eventually_of_forall hgf)).2⟩

alias is_o_iff_tendsto' ↔ _ asymptotics.is_o_of_tendsto'
alias is_o_iff_tendsto ↔ _ asymptotics.is_o_of_tendsto

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/

section eventually_mul_div_cancel

variables {u v : α → 𝕜}

lemma is_O_with.eventually_mul_div_cancel (h : is_O_with c u v l) :
  (u / v) * v =ᶠ[l] u :=
eventually.mono h.bound (λ y hy, div_mul_cancel_of_imp $ λ hv, by simpa [hv] using hy)

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
lemma is_O.eventually_mul_div_cancel (h : is_O u v l) :  (u / v) * v =ᶠ[l] u :=
let ⟨c, hc⟩ := h.is_O_with in hc.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
lemma is_o.eventually_mul_div_cancel (h : is_o u v l) : (u / v) * v =ᶠ[l] u :=
(h.forall_is_O_with zero_lt_one).eventually_mul_div_cancel

end eventually_mul_div_cancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/

section exists_mul_eq

variables {u v : α → 𝕜}

/-- If `∥φ∥` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
lemma is_O_with_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c) (h : u =ᶠ[l] φ * v) :
  is_O_with c u v l :=
begin
  unfold is_O_with,
  refine h.symm.rw (λ x a, ∥a∥ ≤ c * ∥v x∥) (hφ.mono $ λ x hx, _),
  simp only [normed_field.norm_mul, pi.mul_apply],
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
end

lemma is_O_with_iff_exists_eq_mul (hc : 0 ≤ c) :
  is_O_with c u v l ↔ ∃ (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v :=
begin
  split,
  { intro h,
    use (λ x, u x / v x),
    refine ⟨eventually.mono h.bound (λ y hy, _), h.eventually_mul_div_cancel.symm⟩,
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy },
  { rintros ⟨φ, hφ, h⟩,
    exact is_O_with_of_eq_mul φ hφ h }
end

lemma is_O_with.exists_eq_mul (h : is_O_with c u v l) (hc : 0 ≤ c) :
  ∃ (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v :=
(is_O_with_iff_exists_eq_mul hc).mp h

lemma is_O_iff_exists_eq_mul :
  is_O u v l ↔ ∃ (φ : α → 𝕜) (hφ : l.is_bounded_under (≤) (norm ∘ φ)), u =ᶠ[l] φ * v :=
begin
  split,
  { rintros h,
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩,
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩,
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩ },
  { rintros ⟨φ, ⟨c, hφ⟩, huvφ⟩,
    exact is_O_iff_is_O_with.2 ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩ }
end

alias is_O_iff_exists_eq_mul ↔ asymptotics.is_O.exists_eq_mul _

lemma is_o_iff_exists_eq_mul :
  is_o u v l ↔ ∃ (φ : α → 𝕜) (hφ : tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v :=
begin
  split,
  { exact λ h, ⟨λ x, u x / v x, h.tendsto_0, h.eventually_mul_div_cancel.symm⟩ },
  { unfold is_o, rintros ⟨φ, hφ, huvφ⟩ c hpos,
    rw normed_group.tendsto_nhds_zero at hφ,
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mono $ λ x, le_of_lt)  huvφ }
end

alias is_o_iff_exists_eq_mul ↔ asymptotics.is_o.exists_eq_mul _

end exists_mul_eq

/-! ### Miscellanous lemmas -/

theorem div_is_bounded_under_of_is_O {α : Type*} {l : filter α}
  {f g : α → 𝕜} (h : is_O f g l) :
  is_bounded_under (≤) l (λ x, ∥f x / g x∥) :=
begin
  obtain ⟨c, hc⟩ := is_O_iff.mp h,
  refine ⟨max c 0, eventually_map.2 (filter.mem_sets_of_superset hc (λ x hx, _))⟩,
  simp only [mem_set_of_eq, normed_field.norm_div] at ⊢ hx,
  by_cases hgx : g x = 0,
  { rw [hgx, norm_zero, div_zero, le_max_iff],
    exact or.inr le_rfl },
  { exact le_max_iff.2 (or.inl ((div_le_iff (norm_pos_iff.2 hgx)).2 hx)) }
end

theorem is_O_iff_div_is_bounded_under {α : Type*} {l : filter α}
  {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
  is_O f g l ↔ is_bounded_under (≤) l (λ x, ∥f x / g x∥) :=
begin
  refine ⟨div_is_bounded_under_of_is_O, λ h, _⟩,
  obtain ⟨c, hc⟩ := h,
  rw filter.eventually_iff at hgf hc,
  simp only [mem_set_of_eq, mem_map, normed_field.norm_div] at hc,
  refine is_O_iff.2 ⟨c, filter.eventually_of_mem (inter_mem_sets hgf hc) (λ x hx, _)⟩,
  by_cases hgx : g x = 0,
  { simp [hx.1 hgx, hgx] },
  { refine (div_le_iff (norm_pos_iff.2 hgx)).mp hx.2 },
end

theorem is_O_of_div_tendsto_nhds {α : Type*} {l : filter α}
  {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0)
  (c : 𝕜) (H : filter.tendsto (f / g) l (𝓝 c)) :
  is_O f g l :=
(is_O_iff_div_is_bounded_under hgf).2 $ is_bounded_under_of_tendsto H

lemma is_o.tendsto_zero_of_tendsto {α E 𝕜 : Type*} [normed_group E] [normed_field 𝕜] {u : α → E}
  {v : α → 𝕜} {l : filter α} {y : 𝕜} (huv : is_o u v l) (hv : tendsto v l (𝓝 y)) :
  tendsto u l (𝓝 0) :=
begin
  suffices h : is_o u (λ x, (1 : 𝕜)) l,
  { rwa is_o_one_iff at h },
  exact huv.trans_is_O (is_O_one_of_tendsto 𝕜 hv),
end

theorem is_o_pow_pow {m n : ℕ} (h : m < n) :
  is_o (λ(x : 𝕜), x^n) (λx, x^m) (𝓝 0) :=
begin
  let p := n - m,
  have nmp : n = m + p := (nat.add_sub_cancel' (le_of_lt h)).symm,
  have : (λ(x : 𝕜), x^m) = (λx, x^m * 1), by simp only [mul_one],
  simp only [this, pow_add, nmp],
  refine is_O.mul_is_o (is_O_refl _ _) ((is_o_one_iff _).2 _),
  convert (continuous_pow p).tendsto (0 : 𝕜),
  exact (zero_pow (nat.sub_pos_of_lt h)).symm
end

theorem is_o_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
  is_o (λ(x : E'), ∥x∥^n) (λx, ∥x∥^m) (𝓝 (0 : E')) :=
(is_o_pow_pow h).comp_tendsto tendsto_norm_zero

theorem is_o_pow_id {n : ℕ} (h : 1 < n) :
  is_o (λ(x : 𝕜), x^n) (λx, x) (𝓝 0) :=
by { convert is_o_pow_pow h, simp only [pow_one] }

theorem is_o_norm_pow_id {n : ℕ} (h : 1 < n) :
  is_o (λ(x : E'), ∥x∥^n) (λx, x) (𝓝 0) :=
by simpa only [pow_one, is_o_norm_right] using @is_o_norm_pow_norm_pow E' _ _ _ h

theorem is_O_with.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : is_O_with c f₁ f₂ l) (hc : c < 1) :
  is_O_with (1 / (1 - c)) f₂ (λx, f₂ x - f₁ x) l :=
is_O_with.of_bound $ mem_sets_of_superset h.bound $ λ x hx,
begin
  simp only [mem_set_of_eq] at hx ⊢,
  rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff, mul_sub, mul_one, mul_comm],
  { exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _) },
  { exact sub_pos.2 hc }
end

theorem is_O_with.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : is_O_with c f₁ f₂ l) (hc : c < 1) :
  is_O_with (1 / (1 - c)) f₂ (λx, f₁ x + f₂ x) l :=
(h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (λ x, rfl)
  (λ x, by rw [neg_sub, sub_neg_eq_add])

theorem is_o.right_is_O_sub {f₁ f₂ : α → E'} (h : is_o f₁ f₂ l) :
  is_O f₂ (λx, f₂ x - f₁ x) l :=
((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).is_O

theorem is_o.right_is_O_add {f₁ f₂ : α → E'} (h : is_o f₁ f₂ l) :
  is_O f₂ (λx, f₁ x + f₂ x) l :=
((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).is_O

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`∥f x∥ ≤ C * ∥g x∥` whenever `g x ≠ 0`. -/
theorem bound_of_is_O_cofinite (h : is_O f g' cofinite) :
  ∃ C > 0, ∀ ⦃x⦄, g' x ≠ 0 → ∥f x∥ ≤ C * ∥g' x∥ :=
begin
  rcases h.exists_pos with ⟨C, C₀, hC⟩,
  rw [is_O_with, eventually_cofinite] at hC,
  rcases (hC.to_finset.image (λ x, ∥f x∥ / ∥g' x∥)).exists_le with ⟨C', hC'⟩,
  have : ∀ x, C * ∥g' x∥ < ∥f x∥ → ∥f x∥ / ∥g' x∥ ≤ C', by simpa using hC',
  refine ⟨max C C', lt_max_iff.2 (or.inl C₀), λ x h₀, _⟩,
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le],
  exact λ hx, (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)
end

theorem is_O_cofinite_iff (h : ∀ x, g' x = 0 → f' x = 0) :
  is_O f' g' cofinite ↔ ∃ C, ∀ x, ∥f' x∥ ≤ C * ∥g' x∥ :=
⟨λ h', let ⟨C, C₀, hC⟩ := bound_of_is_O_cofinite h' in
  ⟨C, λ x, if hx : g' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
  λ h, (is_O_top.2 h).mono le_top⟩

theorem bound_of_is_O_nat_at_top {f : ℕ → E} {g' : ℕ → E'} (h : is_O f g' at_top) :
  ∃ C > 0, ∀ ⦃x⦄, g' x ≠ 0 → ∥f x∥ ≤ C * ∥g' x∥ :=
bound_of_is_O_cofinite $ by rwa nat.cofinite_eq_at_top

theorem is_O_nat_at_top_iff {f : ℕ → E'} {g : ℕ → F'} (h : ∀ x, g x = 0 → f x = 0) :
  is_O f g at_top ↔ ∃ C, ∀ x, ∥f x∥ ≤ C * ∥g x∥ :=
by rw [← nat.cofinite_eq_at_top, is_O_cofinite_iff h]

theorem is_O_one_nat_at_top_iff {f : ℕ → E'} :
  is_O f (λ n, 1 : ℕ → ℝ) at_top ↔ ∃ C, ∀ n, ∥f n∥ ≤ C :=
iff.trans (is_O_nat_at_top_iff (λ n h, (one_ne_zero h).elim)) $
  by simp only [norm_one, mul_one]

theorem is_O_with_pi {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_group (E' i)]
  {f : α → Π i, E' i} {C : ℝ} (hC : 0 ≤ C) :
  is_O_with C f g' l ↔ ∀ i, is_O_with C (λ x, f x i) g' l :=
have ∀ x, 0 ≤ C * ∥g' x∥, from λ x, mul_nonneg hC (norm_nonneg _),
by simp only [is_O_with_iff, pi_norm_le_iff (this _), eventually_all]

@[simp] theorem is_O_pi {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_group (E' i)]
  {f : α → Π i, E' i} :
  is_O f g' l ↔ ∀ i, is_O (λ x, f x i) g' l :=
begin
  simp only [is_O_iff_eventually_is_O_with, ← eventually_all],
  exact eventually_congr (eventually_at_top.2 ⟨0, λ c, is_O_with_pi⟩)
end

@[simp] theorem is_o_pi {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_group (E' i)]
  {f : α → Π i, E' i} :
  is_o f g' l ↔ ∀ i, is_o (λ x, f x i) g' l :=
begin
  simp only [is_o, is_O_with_pi, le_of_lt] { contextual := tt },
  exact ⟨λ h i c hc, h hc i, λ h c hc i, h i hc⟩
end

end asymptotics

open asymptotics

lemma summable_of_is_O {ι E} [normed_group E] [complete_space E] {f : ι → E} (g : ι → ℝ)
  (hg : summable g) (h : is_O f g cofinite) : summable f :=
let ⟨C, hC⟩ := h.is_O_with in
summable_of_norm_bounded_eventually (λ x, C * ∥g x∥) (hg.abs.mul_left _) hC.bound

lemma summable_of_is_O_nat {E} [normed_group E] [complete_space E] {f : ℕ → E} (g : ℕ → ℝ)
  (hg : summable g) (h : is_O f g at_top) : summable f :=
summable_of_is_O g hg $ nat.cofinite_eq_at_top.symm ▸ h

namespace local_homeomorph

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

variables {E : Type*} [has_norm E] {F : Type*} [has_norm F]

/-- Transfer `is_O_with` over a `local_homeomorph`. -/
lemma is_O_with_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target)
  {f : β → E} {g : β → F} {C : ℝ} :
  is_O_with C f g (𝓝 b) ↔ is_O_with C (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
⟨λ h, h.comp_tendsto $
  by { convert e.continuous_at (e.map_target hb), exact (e.right_inv hb).symm },
  λ h, (h.comp_tendsto (e.continuous_at_symm hb)).congr' rfl
    ((e.eventually_right_inverse hb).mono $ λ x hx, congr_arg f hx)
    ((e.eventually_right_inverse hb).mono $ λ x hx, congr_arg g hx)⟩

/-- Transfer `is_O` over a `local_homeomorph`. -/
lemma is_O_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
  is_O f g (𝓝 b) ↔ is_O (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
by { unfold is_O, exact exists_congr (λ C, e.is_O_with_congr hb) }

/-- Transfer `is_o` over a `local_homeomorph`. -/
lemma is_o_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
  is_o f g (𝓝 b) ↔ is_o (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
by { unfold is_o, exact (forall_congr $ λ c, forall_congr $ λ hc, e.is_O_with_congr hb) }

end local_homeomorph

namespace homeomorph

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

variables {E : Type*} [has_norm E] {F : Type*} [has_norm F]

open asymptotics

/-- Transfer `is_O_with` over a `homeomorph`. -/
lemma is_O_with_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
  is_O_with C f g (𝓝 b) ↔ is_O_with C (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
e.to_local_homeomorph.is_O_with_congr trivial

/-- Transfer `is_O` over a `homeomorph`. -/
lemma is_O_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
  is_O f g (𝓝 b) ↔ is_O (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
by { unfold is_O, exact exists_congr (λ C, e.is_O_with_congr) }

/-- Transfer `is_o` over a `homeomorph`. -/
lemma is_o_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
  is_o f g (𝓝 b) ↔ is_o (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
by { unfold is_o, exact forall_congr (λ c, forall_congr (λ hc, e.is_O_with_congr)) }

end homeomorph
