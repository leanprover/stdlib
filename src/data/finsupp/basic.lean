/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import algebra.group.pi
import algebra.big_operators.order
import algebra.module.basic
import algebra.module.pi
import group_theory.submonoid.basic
import data.fintype.card
import data.finset.preimage
import data.multiset.antidiagonal
import data.indicator_function

/-!

# Type of functions with finite support

For any type `α` and a type `M` with zero, we define the type `finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `monoid_algebra R M` and `add_monoid_algebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `add_monoid_algebra`s, hence they use
  `finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `linear_independent`) is defined as a map
  `finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `multiset α ≃+ α →₀ ℕ`;
* `free_abelian_group α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `finsupp` elements.

Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `monoid_algebra`, `add_monoid_algebra`, and types based on these two have
non-pointwise multiplication.

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`. We also use the following convention
for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## TODO

* This file is currently ~2K lines long, so possibly it should be splitted into smaller chunks;

* Add the list of definitions and important lemmas to the module docstring.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## Notation

This file defines `α →₀ β` as notation for `finsupp α β`.

-/

noncomputable theory
open_locale classical big_operators

open finset

variables {α β γ ι M M' N P G H R S : Type*}

/-- `finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure finsupp (α : Type*) (M : Type*) [has_zero M] :=
(support            : finset α)
(to_fun             : α → M)
(mem_support_to_fun : ∀a, a ∈ support ↔ to_fun a ≠ 0)

infixr ` →₀ `:25 := finsupp

namespace finsupp

/-! ### Basic declarations about `finsupp` -/

section basic
variable [has_zero M]

instance : has_coe_to_fun (α →₀ M) := ⟨λ _, α → M, to_fun⟩

@[simp] lemma coe_mk (f : α → M) (s : finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) :
  ⇑(⟨s, f, h⟩ : α →₀ M) = f := rfl

instance : has_zero (α →₀ M) := ⟨⟨∅, (λ _, 0), λ _, ⟨false.elim, λ H, H rfl⟩⟩⟩

@[simp] lemma coe_zero : ⇑(0 : α →₀ M) = (λ _, (0:M)) := rfl
lemma zero_apply {a : α} : (0 : α →₀ M) a = 0 := rfl
@[simp] lemma support_zero : (0 : α →₀ M).support = ∅ := rfl

instance : inhabited (α →₀ M) := ⟨0⟩

@[simp] lemma mem_support_iff {f : α →₀ M} : ∀{a:α}, a ∈ f.support ↔ f a ≠ 0 :=
f.mem_support_to_fun

@[simp] lemma fun_support_eq (f : α →₀ M) : function.support f = f.support :=
set.ext $ λ x, mem_support_iff.symm

lemma not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
not_iff_comm.1 mem_support_iff.symm

lemma coe_fn_injective : @function.injective (α →₀ M) (α → M) coe_fn
| ⟨s, f, hf⟩ ⟨t, g, hg⟩ h :=
  begin
    change f = g at h, subst h,
    have : s = t, { ext a, exact (hf a).trans (hg a).symm },
    subst this
  end

@[ext] lemma ext {f g : α →₀ M} (h : ∀a, f a = g a) : f = g := coe_fn_injective (funext h)

lemma ext_iff {f g : α →₀ M} : f = g ↔ (∀a:α, f a = g a) :=
⟨by rintros rfl a; refl, ext⟩

lemma ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
⟨λ h, h ▸ ⟨rfl, λ _ _, rfl⟩, λ ⟨h₁, h₂⟩, ext $ λ a,
  if h : a ∈ f.support then h₂ a h else
    have hf : f a = 0, from not_mem_support_iff.1 h,
    have hg : g a = 0, by rwa [h₁, not_mem_support_iff] at h,
    by rw [hf, hg]⟩

@[simp] lemma support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 :=
⟨assume h, ext $ assume a, by_contradiction $ λ H, (finset.ext_iff.1 h a).1 $
  mem_support_iff.2 H, by rintro rfl; refl⟩

lemma support_nonempty_iff {f : α →₀ M} : f.support.nonempty ↔ f ≠ 0 :=
by simp only [finsupp.support_eq_empty, finset.nonempty_iff_ne_empty, ne.def]

lemma nonzero_iff_exists {f : α →₀ M} : f ≠ 0 ↔ ∃ a : α, f a ≠ 0 :=
by simp [finsupp.support_eq_empty.symm, finset.eq_empty_iff_forall_not_mem]

lemma card_support_eq_zero {f : α →₀ M} : card f.support = 0 ↔ f = 0 :=
by simp

instance finsupp.decidable_eq [decidable_eq α] [decidable_eq M] : decidable_eq (α →₀ M) :=
assume f g, decidable_of_iff (f.support = g.support ∧ (∀a∈f.support, f a = g a)) ext_iff'.symm

lemma finite_supp (f : α →₀ M) : set.finite {a | f a ≠ 0} :=
⟨fintype.of_finset f.support (λ _, mem_support_iff)⟩

lemma support_subset_iff {s : set α} {f : α →₀ M} :
  ↑f.support ⊆ s ↔ (∀a∉s, f a = 0) :=
by simp only [set.subset_def, mem_coe, mem_support_iff];
   exact forall_congr (assume a, not_imp_comm)

/-- Given `fintype α`, `equiv_fun_on_fintype` is the `equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
def equiv_fun_on_fintype [fintype α] : (α →₀ M) ≃ (α → M) :=
⟨λf a, f a, λf, mk (finset.univ.filter $ λa, f a ≠ 0) f (by simp only [true_and, finset.mem_univ,
  iff_self, finset.mem_filter, finset.filter_congr_decidable, forall_true_iff]),
  begin intro f, ext a, refl end,
  begin intro f, ext a, refl end⟩

end basic

/-! ### Declarations about `single` -/

section single
variables [has_zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function which has
  value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M :=
⟨if b = 0 then ∅ else {a}, λ a', if a = a' then b else 0, λ a', begin
  by_cases hb : b = 0; by_cases a = a';
    simp only [hb, h, if_pos, if_false, mem_singleton],
  { exact ⟨false.elim, λ H, H rfl⟩ },
  { exact ⟨false.elim, λ H, H rfl⟩ },
  { exact ⟨λ _, hb, λ _, rfl⟩ },
  { exact ⟨λ H _, h H.symm, λ H, (H rfl).elim⟩ }
end⟩

lemma single_apply : single a b a' = if a = a' then b else 0 :=
rfl

lemma single_eq_indicator : ⇑(single a b) = set.indicator {a} (λ _, b) :=
by { ext, simp [single_apply, set.indicator, @eq_comm _ a] }

@[simp] lemma single_eq_same : (single a b : α →₀ M) a = b :=
if_pos rfl

@[simp] lemma single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 :=
if_neg h

lemma single_eq_update : ⇑(single a b) = function.update 0 a b :=
by rw [single_eq_indicator, ← set.piecewise_eq_indicator, set.piecewise_singleton]

@[simp] lemma single_zero : (single a 0 : α →₀ M) = 0 :=
coe_fn_injective $ by simpa only [single_eq_update, coe_zero]
  using function.update_eq_self a (0 : α → M)

lemma single_of_single_apply (a a' : α) (b : M) :
  single a ((single a' b) a) = single a' (single a' b) a :=
begin
  rw [single_apply, single_apply],
  ext,
  split_ifs,
  { rw h, },
  { rw [zero_apply, single_apply, if_t_t], },
end

lemma support_single_ne_zero (hb : b ≠ 0) : (single a b).support = {a} :=
if_neg hb

lemma support_single_subset : (single a b).support ⊆ {a} :=
show ite _ _ _ ⊆ _, by split_ifs; [exact empty_subset _, exact subset.refl _]

lemma single_apply_mem (x) : single a b x ∈ ({0, b} : set M) :=
by rcases em (a = x) with (rfl|hx); [simp, simp [single_eq_of_ne hx]]

lemma range_single_subset : set.range (single a b) ⊆ {0, b} :=
set.range_subset_iff.2 single_apply_mem

lemma single_injective (a : α) : function.injective (single a : M → α →₀ M) :=
assume b₁ b₂ eq,
have (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a, by rw eq,
by rwa [single_eq_same, single_eq_same] at this

lemma single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ (x = a → b = 0) :=
by simp [single_eq_indicator]

lemma mem_support_single (a a' : α) (b : M) :
  a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 :=
by simp [single_apply_eq_zero, not_or_distrib]

lemma eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b :=
begin
  refine ⟨λ h, h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩,
  rintro ⟨h, rfl⟩,
  ext x,
  by_cases hx : a = x; simp only [hx, single_eq_same, single_eq_of_ne, ne.def, not_false_iff],
  exact not_mem_support_iff.1 (mt (λ hx, (mem_singleton.1 (h hx)).symm) hx)
end

lemma single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
  single a₁ b₁ = single a₂ b₂ ↔ ((a₁ = a₂ ∧ b₁ = b₂) ∨ (b₁ = 0 ∧ b₂ = 0)) :=
begin
  split,
  { assume eq,
    by_cases a₁ = a₂,
    { refine or.inl ⟨h, _⟩,
      rwa [h, (single_injective a₂).eq_iff] at eq },
    { rw [ext_iff] at eq,
      have h₁ := eq a₁,
      have h₂ := eq a₂,
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (ne.symm h)] at h₁ h₂,
      exact or.inr ⟨h₁, h₂.symm⟩ } },
  { rintros (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
    { refl },
    { rw [single_zero, single_zero] } }
end

lemma single_left_inj (h : b ≠ 0) :
  single a b = single a' b ↔ a = a' :=
⟨λ H, by simpa only [h, single_eq_single_iff,
  and_false, or_false, eq_self_iff_true, and_true] using H,
 λ H, by rw [H]⟩

@[simp] lemma single_eq_zero : single a b = 0 ↔ b = 0 :=
by simp [ext_iff, single_eq_indicator]

lemma single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ :=
by simp only [single_apply]; ac_refl

instance [nonempty α] [nontrivial M] : nontrivial (α →₀ M) :=
begin
  inhabit α,
  rcases exists_ne (0 : M) with ⟨x, hx⟩,
  exact nontrivial_of_ne (single (default α) x) 0 (mt single_eq_zero.1 hx)
end

lemma unique_single [unique α] (x : α →₀ M) : x = single (default α) (x (default α)) :=
ext $ unique.forall_iff.2 single_eq_same.symm

lemma unique_ext [unique α] {f g : α →₀ M} (h : f (default α) = g (default α)) : f = g :=
ext $ λ a, by rwa [unique.eq_default a]

lemma unique_ext_iff [unique α] {f g : α →₀ M} : f = g ↔  f (default α) = g (default α) :=
⟨λ h, h ▸ rfl, unique_ext⟩

@[simp] lemma unique_single_eq_iff [unique α] {b' : M} :
  single a b = single a' b' ↔ b = b' :=
by rw [unique_ext_iff, unique.eq_default a, unique.eq_default a', single_eq_same, single_eq_same]

lemma support_eq_singleton {f : α →₀ M} {a : α} :
  f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
⟨λ h, ⟨mem_support_iff.1 $ h.symm ▸ finset.mem_singleton_self a,
  eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩, λ h, h.2.symm ▸ support_single_ne_zero h.1⟩

lemma support_eq_singleton' {f : α →₀ M} {a : α} :
  f.support = {a} ↔ ∃ b ≠ 0, f = single a b :=
⟨λ h, let h := support_eq_singleton.1 h in ⟨_, h.1, h.2⟩,
  λ ⟨b, hb, hf⟩, hf.symm ▸ support_single_ne_zero hb⟩

lemma card_support_eq_one {f : α →₀ M} : card f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) :=
by simp only [card_eq_one, support_eq_singleton]

lemma card_support_eq_one' {f : α →₀ M} : card f.support = 1 ↔ ∃ a (b ≠ 0), f = single a b :=
by simp only [card_eq_one, support_eq_singleton']

end single

/-! ### Declarations about `on_finset` -/

section on_finset
variables [has_zero M]

/-- `on_finset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
  The function needs to be `0` outside of `s`. Use this when the set needs to be filtered anyways,
  otherwise a better set representation is often available. -/
def on_finset (s : finset α) (f : α → M) (hf : ∀a, f a ≠ 0 → a ∈ s) : α →₀ M :=
⟨s.filter (λa, f a ≠ 0), f, by simpa⟩

@[simp] lemma on_finset_apply {s : finset α} {f : α → M} {hf a} :
  (on_finset s f hf : α →₀ M) a = f a :=
rfl

@[simp] lemma support_on_finset_subset {s : finset α} {f : α → M} {hf} :
  (on_finset s f hf).support ⊆ s :=
filter_subset _ _

@[simp] lemma mem_support_on_finset
  {s : finset α} {f : α → M} (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) {a : α} :
  a ∈ (finsupp.on_finset s f hf).support ↔ f a ≠ 0 :=
by rw [finsupp.mem_support_iff, finsupp.on_finset_apply]

lemma support_on_finset
  {s : finset α} {f : α → M} (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) :
  (finsupp.on_finset s f hf).support = s.filter (λ a, f a ≠ 0) :=
rfl

end on_finset

/-! ### Declarations about `map_range` -/

section map_range
variables [has_zero M] [has_zero N]

/-- The composition of `f : M → N` and `g : α →₀ M` is
`map_range f hf g : α →₀ N`, well-defined when `f 0 = 0`. -/
def map_range (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
on_finset g.support (f ∘ g) $
  assume a, by rw [mem_support_iff, not_imp_not]; exact λ H, (congr_arg f H).trans hf

@[simp] lemma map_range_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} :
  map_range f hf g a = f (g a) :=
rfl

@[simp] lemma map_range_zero {f : M → N} {hf : f 0 = 0} : map_range f hf (0 : α →₀ M) = 0 :=
ext $ λ a, by simp only [hf, zero_apply, map_range_apply]

lemma support_map_range {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
  (map_range f hf g).support ⊆ g.support :=
support_on_finset_subset

@[simp] lemma map_range_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
  map_range f hf (single a b) = single a (f b) :=
ext $ λ a', show f (ite _ _ _) = ite _ _ _, by split_ifs; [refl, exact hf]

end map_range

/-! ### Declarations about `emb_domain` -/

section emb_domain
variables [has_zero M] [has_zero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `emb_domain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def emb_domain (f : α ↪ β) (v : α →₀ M) : β →₀ M :=
begin
  refine ⟨v.support.map f, λa₂,
    if h : a₂ ∈ v.support.map f then v (v.support.choose (λa₁, f a₁ = a₂) _) else 0, _⟩,
  { rcases finset.mem_map.1 h with ⟨a, ha, rfl⟩,
    exact exists_unique.intro a ⟨ha, rfl⟩ (assume b ⟨_, hb⟩, f.injective hb) },
  { assume a₂,
    split_ifs,
    { simp only [h, true_iff, ne.def],
      rw [← not_mem_support_iff, not_not],
      apply finset.choose_mem },
    { simp only [h, ne.def, ne_self_iff_false] } }
end

@[simp] lemma support_emb_domain (f : α ↪ β) (v : α →₀ M) :
  (emb_domain f v).support = v.support.map f :=
rfl

@[simp] lemma emb_domain_zero (f : α ↪ β) : (emb_domain f 0 : β →₀ M) = 0 :=
rfl

@[simp] lemma emb_domain_apply (f : α ↪ β) (v : α →₀ M) (a : α) :
  emb_domain f v (f a) = v a :=
begin
  change dite _ _ _ = _,
  split_ifs; rw [finset.mem_map' f] at h,
  { refine congr_arg (v : α → M) (f.inj' _),
    exact finset.choose_property (λa₁, f a₁ = f a) _ _ },
  { exact (not_mem_support_iff.1 h).symm }
end

lemma emb_domain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ set.range f) :
  emb_domain f v a = 0 :=
begin
  refine dif_neg (mt (assume h, _) h),
  rcases finset.mem_map.1 h with ⟨a, h, rfl⟩,
  exact set.mem_range_self a
end

lemma emb_domain_injective (f : α ↪ β) :
  function.injective (emb_domain f : (α →₀ M) → (β →₀ M)) :=
λ l₁ l₂ h, ext $ λ a, by simpa only [emb_domain_apply] using ext_iff.1 h (f a)

@[simp] lemma emb_domain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} :
  emb_domain f l₁ = emb_domain f l₂ ↔ l₁ = l₂ :=
(emb_domain_injective f).eq_iff

@[simp] lemma emb_domain_eq_zero {f : α ↪ β} {l : α →₀ M} :
  emb_domain f l = 0 ↔ l = 0 :=
(emb_domain_injective f).eq_iff' $ emb_domain_zero f

lemma emb_domain_map_range
  (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
  emb_domain f (map_range g hg p) = map_range g hg (emb_domain f p) :=
begin
  ext a,
  by_cases a ∈ set.range f,
  { rcases h with ⟨a', rfl⟩,
    rw [map_range_apply, emb_domain_apply, emb_domain_apply, map_range_apply] },
  { rw [map_range_apply, emb_domain_notin_range, emb_domain_notin_range, ← hg]; assumption }
end

lemma single_of_emb_domain_single
  (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
  (h : l.emb_domain f = single a b) :
  ∃ x, l = single x b ∧ f x = a :=
begin
  have h_map_support : finset.map f (l.support) = {a},
    by rw [←support_emb_domain, h, support_single_ne_zero hb]; refl,
  have ha : a ∈ finset.map f (l.support),
    by simp only [h_map_support, finset.mem_singleton],
  rcases finset.mem_map.1 ha with ⟨c, hc₁, hc₂⟩,
  use c,
  split,
  { ext d,
    rw [← emb_domain_apply f l, h],
    by_cases h_cases : c = d,
    { simp only [eq.symm h_cases, hc₂, single_eq_same] },
    { rw [single_apply, single_apply, if_neg, if_neg h_cases],
      by_contra hfd,
      exact h_cases (f.injective (hc₂.trans hfd)) } },
  { exact hc₂ }
end

end emb_domain

/-! ### Declarations about `zip_with` -/

section zip_with
variables [has_zero M] [has_zero N] [has_zero P]

/-- `zip_with f hf g₁ g₂` is the finitely supported function satisfying
  `zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, and it is well-defined when `f 0 0 = 0`. -/
def zip_with (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : (α →₀ P) :=
on_finset (g₁.support ∪ g₂.support) (λa, f (g₁ a) (g₂ a)) $ λ a H,
begin
  simp only [mem_union, mem_support_iff, ne], rw [← not_and_distrib],
  rintro ⟨h₁, h₂⟩, rw [h₁, h₂] at H, exact H hf
end

@[simp] lemma zip_with_apply
  {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
  zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
rfl

lemma support_zip_with {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} :
  (zip_with f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support :=
support_on_finset_subset

end zip_with

/-! ### Declarations about `erase` -/

section erase

variables [has_zero M]

/-- `erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to
  `0`. -/
def erase (a : α) (f : α →₀ M) : α →₀ M :=
⟨f.support.erase a, (λa', if a' = a then 0 else f a'),
  assume a', by rw [mem_erase, mem_support_iff]; split_ifs;
    [exact ⟨λ H _, H.1 h, λ H, (H rfl).elim⟩,
    exact and_iff_right h]⟩

@[simp] lemma support_erase {a : α} {f : α →₀ M} :
  (f.erase a).support = f.support.erase a :=
rfl

@[simp] lemma erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 :=
if_pos rfl

@[simp] lemma erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' :=
if_neg h

@[simp] lemma erase_single {a : α} {b : M} : (erase a (single a b)) = 0 :=
begin
  ext s, by_cases hs : s = a,
  { rw [hs, erase_same], refl },
  { rw [erase_ne hs], exact single_eq_of_ne (ne.symm hs) }
end

lemma erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : (erase a (single a' b)) = single a' b :=
begin
  ext s, by_cases hs : s = a,
  { rw [hs, erase_same, single_eq_of_ne (h.symm)] },
  { rw [erase_ne hs] }
end

@[simp] lemma erase_zero (a : α) : erase a (0 : α →₀ M) = 0 :=
by rw [← support_eq_empty, support_erase, support_zero, erase_empty]

end erase

/-!
### Declarations about `sum` and `prod`

In most of this section, the domain `β` is assumed to be an `add_monoid`.
-/

section sum_prod

-- [to_additive sum] for finsupp.prod doesn't work, the equation lemmas are not generated
/-- `sum f g` is the sum of `g a (f a)` over the support of `f`. -/
def sum [has_zero M] [add_comm_monoid N] (f : α →₀ M) (g : α → M → N) : N :=
∑ a in f.support, g a (f a)

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive]
def prod [has_zero M] [comm_monoid N] (f : α →₀ M) (g : α → M → N) : N :=
∏ a in f.support, g a (f a)

variables [has_zero M] [has_zero M'] [comm_monoid N]

@[to_additive]
lemma prod_of_support_subset (f : α →₀ M) {s : finset α}
  (hs : f.support ⊆ s) (g : α → M → N) (h : ∀ i ∈ s, g i 0 = 1) :
  f.prod g = ∏ x in s, g x (f x) :=
finset.prod_subset hs $ λ x hxs hx, h x hxs ▸ congr_arg (g x) $ not_mem_support_iff.1 hx

@[to_additive]
lemma prod_fintype [fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) :
  f.prod g = ∏ i, g i (f i) :=
f.prod_of_support_subset (subset_univ _) g (λ x _, h x)

@[simp, to_additive]
lemma prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) :
  (single a b).prod h = h a b :=
calc (single a b).prod h = ∏ x in {a}, h x (single a b x) :
  prod_of_support_subset _ support_single_subset h $ λ x hx, (mem_singleton.1 hx).symm ▸ h_zero
... = h a b : by simp

@[to_additive]
lemma prod_map_range_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N}
  (h0 : ∀a, h a 0 = 1) : (map_range f hf g).prod h = g.prod (λa b, h a (f b)) :=
finset.prod_subset support_map_range $ λ _ _ H,
  by rw [not_mem_support_iff.1 H, h0]

@[simp, to_additive]
lemma prod_zero_index {h : α → M → N} : (0 : α →₀ M).prod h = 1 := rfl

@[to_additive]
lemma prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
  f.prod (λ x v, g.prod (λ x' v', h x v x' v')) = g.prod (λ x' v', f.prod (λ x v, h x v x' v')) :=
finset.prod_comm

@[simp, to_additive]
lemma prod_ite_eq [decidable_eq α] (f : α →₀ M) (a : α) (b : α → M → N) :
  f.prod (λ x v, ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 :=
by { dsimp [finsupp.prod], rw f.support.prod_ite_eq, }

@[simp] lemma sum_ite_self_eq
  [decidable_eq α] {N : Type*} [add_comm_monoid N] (f : α →₀ N) (a : α) :
  f.sum (λ x v, ite (a = x) v 0) = f a :=
by { convert f.sum_ite_eq a (λ x, id), simp [ite_eq_right_iff.2 eq.symm] }

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[simp, to_additive "A restatement of `sum_ite_eq` with the equality test reversed."]
lemma prod_ite_eq' [decidable_eq α] (f : α →₀ M) (a : α) (b : α → M → N) :
  f.prod (λ x v, ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 :=
by { dsimp [finsupp.prod], rw f.support.prod_ite_eq', }

@[simp] lemma sum_ite_self_eq'
  [decidable_eq α] {N : Type*} [add_comm_monoid N] (f : α →₀ N) (a : α) :
  f.sum (λ x v, ite (x = a) v 0) = f a :=
by { convert f.sum_ite_eq' a (λ x, id), simp [ite_eq_right_iff.2 eq.symm] }

@[simp] lemma prod_pow [fintype α] (f : α →₀ ℕ) (g : α → N) :
  f.prod (λ a b, g a ^ b) = ∏ a, g a ^ (f a) :=
f.prod_fintype _ $ λ a, pow_zero _

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `on_finset` is the same as multiplying it over the original
`finset`. -/
@[to_additive "If `g` maps a second argument of 0 to 0, summing it over the
result of `on_finset` is the same as summing it over the original
`finset`."]
lemma on_finset_prod {s : finset α} {f : α → M} {g : α → M → N}
    (hf : ∀a, f a ≠ 0 → a ∈ s) (hg : ∀ a, g a 0 = 1) :
  (on_finset s f hf).prod g = ∏ a in s, g a (f a) :=
finset.prod_subset support_on_finset_subset $ by simp [*] { contextual := tt }

end sum_prod

/-!
### Additive monoid structure on `α →₀ M`
-/

section add_monoid

variables [add_monoid M]

instance : has_add (α →₀ M) := ⟨zip_with (+) (add_zero 0)⟩

@[simp] lemma coe_add (f g : α →₀ M) : ⇑(f + g) = f + g := rfl
lemma add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a := rfl

lemma support_add {g₁ g₂ : α →₀ M} : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
support_zip_with

lemma support_add_eq {g₁ g₂ : α →₀ M} (h : disjoint g₁.support g₂.support) :
  (g₁ + g₂).support = g₁.support ∪ g₂.support :=
le_antisymm support_zip_with $ assume a ha,
(finset.mem_union.1 ha).elim
  (assume ha, have a ∉ g₂.support, from disjoint_left.1 h ha,
    by simp only [mem_support_iff, not_not] at *;
    simpa only [add_apply, this, add_zero])
  (assume ha, have a ∉ g₁.support, from disjoint_right.1 h ha,
    by simp only [mem_support_iff, not_not] at *;
    simpa only [add_apply, this, zero_add])

@[simp] lemma single_add {a : α} {b₁ b₂ : M} : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
ext $ assume a',
begin
  by_cases h : a = a',
  { rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same] },
  { rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_add] }
end

instance : add_monoid (α →₀ M) :=
{ add_monoid .
  zero      := 0,
  add       := (+),
  add_assoc := assume ⟨s, f, hf⟩ ⟨t, g, hg⟩ ⟨u, h, hh⟩, ext $ assume a, add_assoc _ _ _,
  zero_add  := assume ⟨s, f, hf⟩, ext $ assume a, zero_add _,
  add_zero  := assume ⟨s, f, hf⟩, ext $ assume a, add_zero _ }

/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` for the stronger version as a linear map.
-/
@[simps] def single_add_hom (a : α) : M →+ α →₀ M :=
⟨single a, single_zero, λ _ _, single_add⟩

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` for the stronger version as a linear map. -/
@[simps apply]
def apply_add_hom (a : α) : (α →₀ M) →+ M := ⟨λ g, g a, zero_apply, λ _ _, add_apply _ _ _⟩

lemma single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f :=
ext $ λ a',
if h : a = a' then by subst h; simp only [add_apply, single_eq_same, erase_same, add_zero]
else by simp only [add_apply, single_eq_of_ne h, zero_add, erase_ne (ne.symm h)]

lemma erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f :=
ext $ λ a',
if h : a = a' then by subst h; simp only [add_apply, single_eq_same, erase_same, zero_add]
else by simp only [add_apply, single_eq_of_ne h, add_zero, erase_ne (ne.symm h)]

@[simp] lemma erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' :=
begin
  ext s, by_cases hs : s = a,
  { rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero] },
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply],
end

@[elab_as_eliminator]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (ha : ∀a b (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
  p f :=
suffices ∀s (f : α →₀ M), f.support = s → p f, from this _ _ rfl,
assume s, finset.induction_on s (λ f hf, by rwa [support_eq_empty.1 hf]) $
assume a s has ih f hf,
suffices p (single a (f a) + f.erase a), by rwa [single_add_erase] at this,
begin
  apply ha,
  { rw [support_erase, mem_erase], exact λ H, H.1 rfl },
  { rw [← mem_support_iff, hf], exact mem_insert_self _ _ },
  { apply ih _ _,
    rw [support_erase, hf, finset.erase_insert has] }
end

lemma induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (ha : ∀a b (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (f + single a b)) :
  p f :=
suffices ∀s (f : α →₀ M), f.support = s → p f, from this _ _ rfl,
assume s, finset.induction_on s (λ f hf, by rwa [support_eq_empty.1 hf]) $
assume a s has ih f hf,
suffices p (f.erase a + single a (f a)), by rwa [erase_add_single] at this,
begin
  apply ha,
  { rw [support_erase, mem_erase], exact λ H, H.1 rfl },
  { rw [← mem_support_iff, hf], exact mem_insert_self _ _ },
  { apply ih _ _,
    rw [support_erase, hf, finset.erase_insert has] }
end

lemma induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g)) (hsingle : ∀ a b, p (single a b)) :
  p f :=
induction₂ f h0 (λ a b f _ _ w, hadd _ _ w (hsingle _ _))

@[simp] lemma add_closure_Union_range_single :
  add_submonoid.closure (⋃ a : α, set.range (single a : M → α →₀ M)) = ⊤ :=
top_unique $ λ x hx, finsupp.induction x (add_submonoid.zero_mem _) $
  λ a b f ha hb hf, add_submonoid.add_mem _
    (add_submonoid.subset_closure $ set.mem_Union.2 ⟨a, set.mem_range_self _⟩) hf

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal. -/
lemma add_hom_ext [add_monoid N] ⦃f g : (α →₀ M) →+ N⦄
  (H : ∀ x y, f (single x y) = g (single x y)) :
  f = g :=
begin
  refine add_monoid_hom.eq_of_eq_on_mdense add_closure_Union_range_single (λ f hf, _),
  simp only [set.mem_Union, set.mem_range] at hf,
  rcases hf with ⟨x, y, rfl⟩,
  apply H
end

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext] lemma add_hom_ext' [add_monoid N] ⦃f g : (α →₀ M) →+ N⦄
  (H : ∀ x, f.comp (single_add_hom x) = g.comp (single_add_hom x)) :
  f = g :=
add_hom_ext $ λ x, add_monoid_hom.congr_fun (H x)

@[ext] lemma mul_hom_ext' [monoid N] {f g : multiplicative (α →₀ M) →* N}
  (H : ∀ x, f.comp (single_add_hom x).to_multiplicative =
    g.comp (single_add_hom x).to_multiplicative) :
  f = g :=
suffices f.to_additive'' = g.to_additive'', by simpa using this,
by { ext x y, simpa using monoid_hom.ext_iff.1 (H x) (multiplicative.of_add y) }

lemma mul_hom_ext [monoid N] ⦃f g : multiplicative (α →₀ M) →* N⦄
  (H : ∀ x y, f (multiplicative.of_add $ single x y) = g (multiplicative.of_add $ single x y)) :
  f = g :=
by { ext x y, simp [H] }

lemma map_range_add [add_monoid N]
  {f : M → N} {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : α →₀ M) :
  map_range f hf (v₁ + v₂) = map_range f hf v₁ + map_range f hf v₂ :=
ext $ λ a, by simp only [hf', add_apply, map_range_apply]

end add_monoid

end finsupp

@[to_additive]
lemma mul_equiv.map_finsupp_prod [has_zero M] [comm_monoid N] [comm_monoid P]
  (h : N ≃* P) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
h.map_prod _ _

@[to_additive]
lemma monoid_hom.map_finsupp_prod [has_zero M] [comm_monoid N] [comm_monoid P]
  (h : N →* P) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
h.map_prod _ _

lemma ring_hom.map_finsupp_sum [has_zero M] [semiring R] [semiring S]
  (h : R →+* S) (f : α →₀ M) (g : α → M → R) : h (f.sum g) = f.sum (λ a b, h (g a b)) :=
h.map_sum _ _

lemma ring_hom.map_finsupp_prod [has_zero M] [comm_semiring R] [comm_semiring S]
  (h : R →+* S) (f : α →₀ M) (g : α → M → R) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
h.map_prod _ _

@[to_additive]
lemma monoid_hom.coe_finsupp_prod [has_zero β] [monoid N] [comm_monoid P]
  (f : α →₀ β) (g : α → β → N →* P) :
  ⇑(f.prod g) = f.prod (λ i fi, g i fi) :=
monoid_hom.coe_prod _ _

@[simp, to_additive]
lemma monoid_hom.finsupp_prod_apply [has_zero β] [monoid N] [comm_monoid P]
  (f : α →₀ β) (g : α → β → N →* P) (x : N) :
  f.prod g x = f.prod (λ i fi, g i fi x) :=
monoid_hom.finset_prod_apply _ _ _

namespace finsupp

section nat_sub
instance nat_sub : has_sub (α →₀ ℕ) := ⟨zip_with (λ m n, m - n) (nat.sub_zero 0)⟩

@[simp] lemma coe_nat_sub (g₁ g₂ : α →₀ ℕ) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl
lemma nat_sub_apply (g₁ g₂ : α →₀ ℕ) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

@[simp] lemma single_sub {a : α} {n₁ n₂ : ℕ} : single a (n₁ - n₂) = single a n₁ - single a n₂ :=
begin
  ext f,
  by_cases h : (a = f),
  { rw [h, nat_sub_apply, single_eq_same, single_eq_same, single_eq_same] },
  rw [nat_sub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h]
end

-- These next two lemmas are used in developing
-- the partial derivative on `mv_polynomial`.

lemma sub_single_one_add {a : α} {u u' : α →₀ ℕ} (h : u a ≠ 0) :
  u - single a 1 + u' = u + u' - single a 1 :=
begin
  ext b,
  rw [add_apply, nat_sub_apply, nat_sub_apply, add_apply],
  by_cases h : a = b,
  { rw [←h, single_eq_same], cases (u a), { contradiction }, { simp }, },
  { simp [h], }
end

lemma add_sub_single_one {a : α} {u u' : α →₀ ℕ} (h : u' a ≠ 0) :
  u + (u' - single a 1) = u + u' - single a 1 :=
begin
  ext b,
  rw [add_apply, nat_sub_apply, nat_sub_apply, add_apply],
  by_cases h : a = b,
  { rw [←h, single_eq_same], cases (u' a), { contradiction }, { simp }, },
  { simp [h], }
end

@[simp] lemma nat_zero_sub (f : α →₀ ℕ) : 0 - f = 0 := ext $ λ x, nat.zero_sub _

end nat_sub

instance [add_comm_monoid M] : add_comm_monoid (α →₀ M) :=
{ add_comm := assume ⟨s, f, _⟩ ⟨t, g, _⟩, ext $ assume a, add_comm _ _,
  .. finsupp.add_monoid }

instance [add_group G] : has_sub (α →₀ G) := ⟨zip_with has_sub.sub (sub_zero _)⟩

instance [add_group G] : add_group (α →₀ G) :=
{ neg            := map_range (has_neg.neg) neg_zero,
  sub            := has_sub.sub,
  sub_eq_add_neg := λ x y, ext (λ i, sub_eq_add_neg _ _),
  add_left_neg   := assume ⟨s, f, _⟩, ext $ assume x, add_left_neg _,
  .. finsupp.add_monoid }

instance [add_comm_group G] : add_comm_group (α →₀ G) :=
{ add_comm := add_comm, ..finsupp.add_group }

lemma single_multiset_sum [add_comm_monoid M] (s : multiset M) (a : α) :
  single a s.sum = (s.map (single a)).sum :=
multiset.induction_on s single_zero $ λ a s ih,
by rw [multiset.sum_cons, single_add, ih, multiset.map_cons, multiset.sum_cons]

lemma single_finset_sum [add_comm_monoid M] (s : finset ι) (f : ι → M) (a : α) :
  single a (∑ b in s, f b) = ∑ b in s, single a (f b) :=
begin
  transitivity,
  apply single_multiset_sum,
  rw [multiset.map_map],
  refl
end

lemma single_sum [has_zero M] [add_comm_monoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
  single a (s.sum f) = s.sum (λd c, single a (f d c)) :=
single_finset_sum _ _ _

@[to_additive]
lemma prod_neg_index [add_group G] [comm_monoid M] {g : α →₀ G} {h : α → G → M}
  (h0 : ∀a, h a 0 = 1) :
  (-g).prod h = g.prod (λa b, h a (- b)) :=
prod_map_range_index h0

@[simp] lemma coe_neg [add_group G] (g : α →₀ G) : ⇑(-g) = -g := rfl
lemma neg_apply [add_group G] (g : α →₀ G) (a : α) : (- g) a = - g a := rfl

@[simp] lemma coe_sub [add_group G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl
lemma sub_apply [add_group G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

@[simp] lemma support_neg [add_group G] {f : α →₀ G} : support (-f) = support f :=
finset.subset.antisymm
  support_map_range
  (calc support f = support (- (- f)) : congr_arg support (neg_neg _).symm
     ... ⊆ support (- f) : support_map_range)

@[simp] lemma sum_apply [has_zero M] [add_comm_monoid N]
  {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
  (f.sum g) a₂ = f.sum (λa₁ b, g a₁ b a₂) :=
(apply_add_hom a₂ : (β →₀ N) →+ _).map_sum _ _

lemma support_sum [has_zero M] [add_comm_monoid N]
  {f : α →₀ M} {g : α → M → (β →₀ N)} :
  (f.sum g).support ⊆ f.support.bUnion (λa, (g a (f a)).support) :=
have ∀ c, f.sum (λ a b, g a b c) ≠ 0 → (∃ a, f a ≠ 0 ∧ ¬ (g a (f a)) c = 0),
  from assume a₁ h,
  let ⟨a, ha, ne⟩ := finset.exists_ne_zero_of_sum_ne_zero h in
  ⟨a, mem_support_iff.mp ha, ne⟩,
by simpa only [finset.subset_iff, mem_support_iff, finset.mem_bUnion, sum_apply, exists_prop]

@[simp] lemma sum_zero [has_zero M] [add_comm_monoid N] {f : α →₀ M} :
  f.sum (λa b, (0 : N)) = 0 :=
finset.sum_const_zero

@[simp, to_additive]
lemma prod_mul  [has_zero M] [comm_monoid N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
  f.prod (λa b, h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ :=
finset.prod_mul_distrib

@[simp, to_additive]
lemma prod_inv [has_zero M] [comm_group G] {f : α →₀ M}
  {h : α → M → G} : f.prod (λa b, (h a b)⁻¹) = (f.prod h)⁻¹ :=
(((monoid_hom.id G)⁻¹).map_prod _ _).symm

@[simp] lemma sum_sub [has_zero M] [add_comm_group G] {f : α →₀ M}
  {h₁ h₂ : α → M → G} :
  f.sum (λa b, h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
finset.sum_sub_distrib

@[to_additive]
lemma prod_add_index [add_comm_monoid M] [comm_monoid N] {f g : α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  (f + g).prod h = f.prod h * g.prod h :=
have hf : f.prod h = ∏ a in f.support ∪ g.support, h a (f a),
  from f.prod_of_support_subset (subset_union_left _ _) _ $ λ a ha, h_zero a,
have hg : g.prod h = ∏ a in f.support ∪ g.support, h a (g a),
  from g.prod_of_support_subset (subset_union_right _ _) _ $ λ a ha, h_zero a,
have hfg : (f + g).prod h = ∏ a in f.support ∪ g.support, h a ((f + g) a),
  from (f + g).prod_of_support_subset support_add _ $ λ a ha, h_zero a,
by simp only [*, add_apply, prod_mul_distrib]

@[simp]
lemma sum_add_index' [add_comm_monoid M] [add_comm_monoid N] {f g : α →₀ M} (h : α → M →+ N) :
  (f + g).sum (λ x, h x) = f.sum (λ x, h x) + g.sum (λ x, h x) :=
sum_add_index (λ a, (h a).map_zero) (λ a, (h a).map_add)

@[simp]
lemma prod_add_index' [add_comm_monoid M] [comm_monoid N] {f g : α →₀ M}
  (h : α → multiplicative M →* N) :
  (f + g).prod (λ a b, h a (multiplicative.of_add b)) =
    f.prod (λ a b, h a (multiplicative.of_add b)) * g.prod (λ a b, h a (multiplicative.of_add b)) :=
prod_add_index (λ a, (h a).map_one) (by simp)

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def lift_add_hom [add_comm_monoid M] [add_comm_monoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) :=
{ to_fun := λ F,
  { to_fun := λ f, f.sum (λ x, F x),
    map_zero' := finset.sum_empty,
    map_add' := λ _ _, sum_add_index (λ x, (F x).map_zero) (λ x, (F x).map_add) },
  inv_fun := λ F x, F.comp $ single_add_hom x,
  left_inv := λ F, by { ext, simp },
  right_inv := λ F, by { ext, simp },
  map_add' := λ F G, by { ext, simp } }

@[simp] lemma lift_add_hom_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : α → M →+ N) (f : α →₀ M) :
  lift_add_hom F f = f.sum (λ x, F x) :=
rfl

@[simp] lemma lift_add_hom_symm_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : (α →₀ M) →+ N) (x : α) :
  lift_add_hom.symm F x = F.comp (single_add_hom x) :=
rfl

lemma lift_add_hom_symm_apply_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : (α →₀ M) →+ N) (x : α) (y : M) :
  lift_add_hom.symm F x y = F (single x y) :=
rfl

@[simp] lemma lift_add_hom_single_add_hom [add_comm_monoid M] :
  lift_add_hom (single_add_hom : α → M →+ α →₀ M) = add_monoid_hom.id _ :=
lift_add_hom.to_equiv.apply_eq_iff_eq_symm_apply.2 rfl

@[simp] lemma sum_single [add_comm_monoid M] (f : α →₀ M) :
  f.sum single = f :=
add_monoid_hom.congr_fun lift_add_hom_single_add_hom f

@[simp] lemma lift_add_hom_apply_single [add_comm_monoid M] [add_comm_monoid N]
  (f : α → M →+ N) (a : α) (b : M) :
  lift_add_hom f (single a b) = f a b :=
sum_single_index (f a).map_zero

@[simp] lemma lift_add_hom_comp_single [add_comm_monoid M] [add_comm_monoid N] (f : α → M →+ N)
  (a : α) :
  (lift_add_hom f).comp (single_add_hom a) = f a :=
add_monoid_hom.ext $ λ b, lift_add_hom_apply_single f a b

lemma comp_lift_add_hom [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
  (g : N →+ P) (f : α → M →+ N) :
  g.comp (lift_add_hom f) = lift_add_hom (λ a, g.comp (f a)) :=
lift_add_hom.symm_apply_eq.1 $ funext $ λ a,
  by rw [lift_add_hom_symm_apply, add_monoid_hom.comp_assoc, lift_add_hom_comp_single]

lemma sum_sub_index [add_comm_group β] [add_comm_group γ] {f g : α →₀ β}
  {h : α → β → γ} (h_sub : ∀a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) :
  (f - g).sum h = f.sum h - g.sum h :=
(lift_add_hom (λ a, add_monoid_hom.of_map_sub (h a) (h_sub a))).map_sub f g

@[to_additive]
lemma prod_emb_domain [has_zero M] [comm_monoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
  (v.emb_domain f).prod g = v.prod (λ a b, g (f a) b) :=
begin
  rw [prod, prod, support_emb_domain, finset.prod_map],
  simp_rw emb_domain_apply,
end

@[to_additive]
lemma prod_finset_sum_index [add_comm_monoid M] [comm_monoid N]
  {s : finset ι} {g : ι → α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  ∏ i in s, (g i).prod h = (∑ i in s, g i).prod h :=
finset.induction_on s rfl $ λ a s has ih,
by rw [prod_insert has, ih, sum_insert has, prod_add_index h_zero h_add]

@[to_additive]
lemma prod_sum_index
  [add_comm_monoid M] [add_comm_monoid N] [comm_monoid P]
  {f : α →₀ M} {g : α → M → β →₀ N}
  {h : β → N → P} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  (f.sum g).prod h = f.prod (λa b, (g a b).prod h) :=
(prod_finset_sum_index h_zero h_add).symm

lemma multiset_sum_sum_index
  [add_comm_monoid M] [add_comm_monoid N]
  (f : multiset (α →₀ M)) (h : α → M → N)
  (h₀ : ∀a, h a 0 = 0) (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
  (f.sum.sum h) = (f.map $ λg:α →₀ M, g.sum h).sum :=
multiset.induction_on f rfl $ assume a s ih,
by rw [multiset.sum_cons, multiset.map_cons, multiset.sum_cons, sum_add_index h₀ h₁, ih]

lemma multiset_map_sum [has_zero M] {f : α →₀ M} {m : β → γ} {h : α → M → multiset β} :
  multiset.map m (f.sum h) = f.sum (λa b, (h a b).map m) :=
(f.support.sum_hom _).symm

lemma multiset_sum_sum [has_zero M] [add_comm_monoid N] {f : α →₀ M} {h : α → M → multiset N} :
  multiset.sum (f.sum h) = f.sum (λa b, multiset.sum (h a b)) :=
(f.support.sum_hom multiset.sum).symm

section map_range
variables
  [add_comm_monoid M] [add_comm_monoid N] (f : M →+ N)

/--
Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
def map_range.add_monoid_hom : (α →₀ M) →+ (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_zero' := map_range_zero,
  map_add' := λ a b, map_range_add f.map_add _ _ }

lemma map_range_multiset_sum (m : multiset (α →₀ M)) :
  map_range f f.map_zero m.sum = (m.map $ λx, map_range f f.map_zero x).sum :=
(m.sum_hom (map_range.add_monoid_hom f)).symm

lemma map_range_finset_sum (s : finset ι) (g : ι → (α →₀ M))  :
  map_range f f.map_zero (∑ x in s, g x) = ∑ x in s, map_range f f.map_zero (g x) :=
by rw [finset.sum.equations._eqn_1, map_range_multiset_sum, multiset.map_map]; refl

end map_range

/-! ### Declarations about `map_domain` -/

section map_domain
variables [add_comm_monoid M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def map_domain (f : α → β) (v : α →₀ M) : β →₀ M :=
v.sum $ λa, single (f a)

lemma map_domain_apply {f : α → β} (hf : function.injective f) (x : α →₀ M) (a : α) :
  map_domain f x (f a) = x a :=
begin
  rw [map_domain, sum_apply, sum, finset.sum_eq_single a, single_eq_same],
  { assume b _ hba, exact single_eq_of_ne (hf.ne hba) },
  { assume h, rw [not_mem_support_iff.1 h, single_zero, zero_apply] }
end

@[simp] lemma map_domain_apply_equiv (f : α ≃ β) (x : α →₀ M) (b : β) :
  map_domain f x b = x (f.symm b) :=
by rw [← f.apply_symm_apply b, map_domain_apply f.injective, f.apply_symm_apply]

lemma map_domain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ set.range f) :
  map_domain f x a = 0 :=
begin
  rw [map_domain, sum_apply, sum],
  exact finset.sum_eq_zero
    (assume a' h', single_eq_of_ne $ assume eq, h $ eq ▸ set.mem_range_self _)
end

lemma map_domain_id : map_domain id v = v :=
sum_single _

lemma map_domain_comp {f : α → β} {g : β → γ} :
  map_domain (g ∘ f) v = map_domain g (map_domain f v) :=
begin
  refine ((sum_sum_index _ _).trans _).symm,
  { intros, exact single_zero },
  { intros, exact single_add },
  refine sum_congr rfl (λ _ _, sum_single_index _),
  { exact single_zero }
end

lemma map_domain_single {f : α → β} {a : α} {b : M} : map_domain f (single a b) = single (f a) b :=
sum_single_index single_zero

@[simp] lemma map_domain_zero {f : α → β} : map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
sum_zero_index

lemma map_domain_congr {f g : α → β} (h : ∀x∈v.support, f x = g x) :
  v.map_domain f = v.map_domain g :=
finset.sum_congr rfl $ λ _ H, by simp only [h _ H]

lemma map_domain_add {f : α → β} : map_domain f (v₁ + v₂) = map_domain f v₁ + map_domain f v₂ :=
sum_add_index (λ _, single_zero) (λ _ _ _, single_add)

lemma map_domain_finset_sum {f : α → β} {s : finset ι} {v : ι → α →₀ M} :
  map_domain f (∑ i in s, v i) = ∑ i in s, map_domain f (v i) :=
eq.symm $ sum_finset_sum_index (λ _, single_zero) (λ _ _ _, single_add)

lemma map_domain_sum [has_zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
  map_domain f (s.sum v) = s.sum (λa b, map_domain f (v a b)) :=
eq.symm $ sum_finset_sum_index (λ _, single_zero) (λ _ _ _, single_add)

lemma map_domain_support {f : α → β} {s : α →₀ M} :
  (s.map_domain f).support ⊆ s.support.image f :=
finset.subset.trans support_sum $
  finset.subset.trans (finset.bUnion_mono $ assume a ha, support_single_subset) $
  by rw [finset.bUnion_singleton]; exact subset.refl _

@[to_additive]
lemma prod_map_domain_index [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (h_zero : ∀b, h b 0 = 1) (h_add : ∀b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
  (map_domain f s).prod h = s.prod (λa m, h (f a) m) :=
(prod_sum_index h_zero h_add).trans $ prod_congr rfl $ λ _ _, prod_single_index (h_zero _)

/--
A version of `sum_map_domain_index` that takes a bundled `add_monoid_hom`,
rather than separate linearity hypotheses.
-/
-- Note that in `prod_map_domain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `monoid_hom`.
@[simp]
lemma sum_map_domain_index_add_monoid_hom [add_comm_monoid N] {f : α → β}
  {s : α →₀ M} (h : β → M →+ N) :
  (map_domain f s).sum (λ b m, h b m) = s.sum (λ a m, h (f a) m) :=
@sum_map_domain_index _ _ _ _ _ _ _ _
  (λ b m, h b m)
  (λ b, (h b).map_zero)
  (λ b m₁ m₂, (h b).map_add _ _)

lemma emb_domain_eq_map_domain (f : α ↪ β) (v : α →₀ M) :
  emb_domain f v = map_domain f v :=
begin
  ext a,
  by_cases a ∈ set.range f,
  { rcases h with ⟨a, rfl⟩,
    rw [map_domain_apply f.injective, emb_domain_apply] },
  { rw [map_domain_notin_range, emb_domain_notin_range]; assumption }
end

@[to_additive]
lemma prod_map_domain_index_inj [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (hf : function.injective f) :
  (s.map_domain f).prod h = s.prod (λa b, h (f a) b) :=
by rw [←function.embedding.coe_fn_mk f hf, ←emb_domain_eq_map_domain, prod_emb_domain]

lemma map_domain_injective {f : α → β} (hf : function.injective f) :
  function.injective (map_domain f : (α →₀ M) → (β →₀ M)) :=
begin
  assume v₁ v₂ eq, ext a,
  have : map_domain f v₁ (f a) = map_domain f v₂ (f a), { rw eq },
  rwa [map_domain_apply hf, map_domain_apply hf] at this,
end

end map_domain

/-! ### Declarations about `comap_domain` -/

section comap_domain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
def comap_domain [has_zero M] (f : α → β) (l : β →₀ M) (hf : set.inj_on f (f ⁻¹' ↑l.support)) :
  α →₀ M :=
{ support := l.support.preimage f hf,
  to_fun := (λ a, l (f a)),
  mem_support_to_fun :=
    begin
      intros a,
      simp only [finset.mem_def.symm, finset.mem_preimage],
      exact l.mem_support_to_fun (f a),
    end }

@[simp]
lemma comap_domain_apply [has_zero M] (f : α → β) (l : β →₀ M)
  (hf : set.inj_on f (f ⁻¹' ↑l.support)) (a : α) :
  comap_domain f l hf a = l (f a) :=
rfl

lemma sum_comap_domain [has_zero M] [add_comm_monoid N]
  (f : α → β) (l : β →₀ M) (g : β → M → N)
  (hf : set.bij_on f (f ⁻¹' ↑l.support) ↑l.support) :
  (comap_domain f l hf.inj_on).sum (g ∘ f) = l.sum g :=
begin
  simp only [sum, comap_domain_apply, (∘)],
  simp [comap_domain, finset.sum_preimage_of_bij f _ _ (λ x, g x (l x))],
end

lemma eq_zero_of_comap_domain_eq_zero [add_comm_monoid M]
  (f : α → β) (l : β →₀ M) (hf : set.bij_on f (f ⁻¹' ↑l.support) ↑l.support) :
   comap_domain f l hf.inj_on = 0 → l = 0 :=
begin
  rw [← support_eq_empty, ← support_eq_empty, comap_domain],
  simp only [finset.ext_iff, finset.not_mem_empty, iff_false, mem_preimage],
  assume h a ha,
  cases hf.2.2 ha with b hb,
  exact h b (hb.2.symm ▸ ha)
end

lemma map_domain_comap_domain [add_comm_monoid M] (f : α → β) (l : β →₀ M)
  (hf : function.injective f) (hl : ↑l.support ⊆ set.range f):
  map_domain f (comap_domain f l (hf.inj_on _)) = l :=
begin
  ext a,
  by_cases h_cases: a ∈ set.range f,
  { rcases set.mem_range.1 h_cases with ⟨b, hb⟩,
    rw [hb.symm, map_domain_apply hf, comap_domain_apply] },
  { rw map_domain_notin_range _ _ h_cases,
    by_contra h_contr,
    apply h_cases (hl $ finset.mem_coe.2 $ mem_support_iff.2 $ λ h, h_contr h.symm) }
end

end comap_domain

/-! ### Declarations about `filter` -/

section filter
section has_zero
variables [has_zero M] (p : α → Prop) (f : α →₀ M)

/-- `filter p f` is the function which is `f a` if `p a` is true and 0 otherwise. -/
def filter (p : α → Prop) (f : α →₀ M) : α →₀ M :=
{ to_fun := λ a, if p a then f a else 0,
  support := f.support.filter (λ a, p a),
  mem_support_to_fun := λ a, by split_ifs; { simp only [h, mem_filter, mem_support_iff], tauto } }

lemma filter_apply (a : α) : f.filter p a = if p a then f a else 0 := rfl

lemma filter_eq_indicator : ⇑(f.filter p) = set.indicator {x | p x} f := rfl

@[simp] lemma filter_apply_pos {a : α} (h : p a) : f.filter p a = f a :=
if_pos h

@[simp] lemma filter_apply_neg {a : α} (h : ¬ p a) : f.filter p a = 0 :=
if_neg h

@[simp] lemma support_filter : (f.filter p).support = f.support.filter p := rfl

lemma filter_zero : (0 : α →₀ M).filter p = 0 :=
by rw [← support_eq_empty, support_filter, support_zero, finset.filter_empty]

@[simp] lemma filter_single_of_pos
  {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
coe_fn_injective $ by simp [filter_eq_indicator, set.subset_def, mem_support_single, h]

@[simp] lemma filter_single_of_neg
  {a : α} {b : M} (h : ¬ p a) : (single a b).filter p = 0 :=
ext $ by simp [filter_eq_indicator, single_apply_eq_zero, @imp.swap (p _), h]

end has_zero

lemma filter_pos_add_filter_neg [add_monoid M] (f : α →₀ M) (p : α → Prop) :
  f.filter p + f.filter (λa, ¬ p a) = f :=
coe_fn_injective $ set.indicator_self_add_compl {x | p x} f

end filter

/-! ### Declarations about `frange` -/

section frange
variables [has_zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : finset M := finset.image f f.support

theorem mem_frange {f : α →₀ M} {y : M} :
  y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y :=
finset.mem_image.trans
⟨λ ⟨x, hx1, hx2⟩, ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩,
λ ⟨hy, x, hx⟩, ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_frange {f : α →₀ M} : (0:M) ∉ f.frange :=
λ H, (mem_frange.1 H).1 rfl

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} :=
λ r hr, let ⟨t, ht1, ht2⟩ := mem_frange.1 hr in ht2 ▸
  (by rw single_apply at ht2 ⊢; split_ifs at ht2 ⊢; [exact finset.mem_singleton_self _, cc])

end frange

/-! ### Declarations about `subtype_domain` -/

section subtype_domain


section zero

variables [has_zero M] {p : α → Prop}

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain (p : α → Prop) (f : α →₀ M) : (subtype p →₀ M) :=
⟨f.support.subtype p, f ∘ coe, λ a, by simp only [mem_subtype, mem_support_iff]⟩

@[simp] lemma support_subtype_domain {f : α →₀ M} :
  (subtype_domain p f).support = f.support.subtype p :=
rfl

@[simp] lemma subtype_domain_apply {a : subtype p} {v : α →₀ M} :
  (subtype_domain p v) a = v (a.val) :=
rfl

@[simp] lemma subtype_domain_zero : subtype_domain p (0 : α →₀ M) = 0 :=
rfl

lemma subtype_domain_eq_zero_iff' {f : α →₀ M} :
  f.subtype_domain p = 0 ↔ ∀ x, p x → f x = 0 :=
by simp_rw [← support_eq_empty, support_subtype_domain, subtype_eq_empty, not_mem_support_iff]

lemma subtype_domain_eq_zero_iff {f : α →₀ M} (hf : ∀ x ∈ f.support , p x) :
  f.subtype_domain p = 0 ↔ f = 0 :=
subtype_domain_eq_zero_iff'.trans ⟨λ H, ext $ λ x,
  if hx : p x then H x hx else not_mem_support_iff.1 $ mt (hf x) hx, λ H x _, by simp [H]⟩

@[to_additive]
lemma prod_subtype_domain_index [comm_monoid N] {v : α →₀ M}
  {h : α → M → N} (hp : ∀x∈v.support, p x) :
  (v.subtype_domain p).prod (λa b, h a b) = v.prod h :=
prod_bij (λp _, p.val)
  (λ _, mem_subtype.1)
  (λ _ _, rfl)
  (λ _ _ _ _, subtype.eq)
  (λ b hb, ⟨⟨b, hp b hb⟩, mem_subtype.2 hb, rfl⟩)

end zero

section monoid
variables [add_monoid M] {p : α → Prop} {v v' : α →₀ M}

@[simp] lemma subtype_domain_add {v v' : α →₀ M} :
  (v + v').subtype_domain p = v.subtype_domain p + v'.subtype_domain p :=
ext $ λ _, rfl

instance subtype_domain.is_add_monoid_hom :
  is_add_monoid_hom (subtype_domain p : (α →₀ M) → subtype p →₀ M) :=
{ map_add := λ _ _, subtype_domain_add, map_zero := subtype_domain_zero }

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filter_add_hom (p : α → Prop) : (α →₀ M) →+ (α →₀ M) :=
{ to_fun := filter p,
  map_zero' := filter_zero p,
  map_add' := λ f g, coe_fn_injective $ set.indicator_add {x | p x} f g }

@[simp] lemma filter_add {v v' : α →₀ M} : (v + v').filter p = v.filter p + v'.filter p :=
(filter_add_hom p).map_add v v'

end monoid

section comm_monoid
variables [add_comm_monoid M] {p : α → Prop}

lemma subtype_domain_sum {s : finset ι} {h : ι → α →₀ M} :
  (∑ c in s, h c).subtype_domain p = ∑ c in s, (h c).subtype_domain p :=
eq.symm (s.sum_hom _)

lemma subtype_domain_finsupp_sum [has_zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

lemma filter_sum (s : finset ι) (f : ι → α →₀ M) :
  (∑ a in s, f a).filter p = ∑ a in s, filter p (f a) :=
(filter_add_hom p : (α →₀ M) →+ _).map_sum f s

lemma filter_eq_sum (p : α → Prop) (f : α →₀ M) :
  f.filter p = ∑ i in f.support.filter p, single i (f i) :=
(f.filter p).sum_single.symm.trans $ finset.sum_congr rfl $
  λ x hx, by rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end comm_monoid

section group
variables [add_group G] {p : α → Prop} {v v' : α →₀ G}

@[simp] lemma subtype_domain_neg : (- v).subtype_domain p = - v.subtype_domain p :=
ext $ λ _, rfl

@[simp] lemma subtype_domain_sub :
  (v - v').subtype_domain p = v.subtype_domain p - v'.subtype_domain p :=
ext $ λ _, rfl

end group

end subtype_domain

/-! ### Declarations relating `finsupp` to `multiset` -/

section multiset

/-- Given `f : α →₀ ℕ`, `f.to_multiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `add_equiv`. -/
def to_multiset : (α →₀ ℕ) ≃+ multiset α :=
{ to_fun := λ f, f.sum (λa n, n •ℕ {a}),
  inv_fun := λ s, ⟨s.to_finset, λ a, s.count a, λ a, by simp⟩,
  left_inv := λ f, ext $ λ a,
    suffices (if f a = 0 then 0 else f a) = f a,
    by simpa [finsupp.sum, multiset.count_sum', multiset.count_cons],
    by split_ifs with h; [rw h, refl],
  right_inv := λ s, by simp [finsupp.sum],
  map_add' := λ f g, sum_add_index (λ a, zero_nsmul _) (λ a, add_nsmul _) }

lemma to_multiset_zero : (0 : α →₀ ℕ).to_multiset = 0 :=
rfl

lemma to_multiset_add (m n : α →₀ ℕ) :
  (m + n).to_multiset = m.to_multiset + n.to_multiset :=
to_multiset.map_add m n

lemma to_multiset_apply (f : α →₀ ℕ) : f.to_multiset = f.sum (λ a n, n •ℕ {a}) := rfl

@[simp] lemma to_multiset_single (a : α) (n : ℕ) : to_multiset (single a n) = n •ℕ {a} :=
by rw [to_multiset_apply, sum_single_index]; apply zero_nsmul

lemma card_to_multiset (f : α →₀ ℕ) : f.to_multiset.card = f.sum (λa, id) :=
by simp [to_multiset_apply, add_monoid_hom.map_finsupp_sum, function.id_def]

lemma to_multiset_map (f : α →₀ ℕ) (g : α → β) :
  f.to_multiset.map g = (f.map_domain g).to_multiset :=
begin
  refine f.induction _ _,
  { rw [to_multiset_zero, multiset.map_zero, map_domain_zero, to_multiset_zero] },
  { assume a n f _ _ ih,
    rw [to_multiset_add, multiset.map_add, ih, map_domain_add, map_domain_single,
      to_multiset_single, to_multiset_add, to_multiset_single,
      is_add_monoid_hom.map_nsmul (multiset.map g)],
    refl }
end

@[simp] lemma prod_to_multiset [comm_monoid M] (f : M →₀ ℕ) :
  f.to_multiset.prod = f.prod (λa n, a ^ n) :=
begin
  refine f.induction _ _,
  { rw [to_multiset_zero, multiset.prod_zero, finsupp.prod_zero_index] },
  { assume a n f _ _ ih,
    rw [to_multiset_add, multiset.prod_add, ih, to_multiset_single, finsupp.prod_add_index,
      finsupp.prod_single_index, multiset.prod_smul, multiset.singleton_eq_singleton,
      multiset.prod_singleton],
    { exact pow_zero a },
    { exact pow_zero },
    { exact pow_add  } }
end

@[simp] lemma to_finset_to_multiset (f : α →₀ ℕ) : f.to_multiset.to_finset = f.support :=
begin
  refine f.induction _ _,
  { rw [to_multiset_zero, multiset.to_finset_zero, support_zero] },
  { assume a n f ha hn ih,
    rw [to_multiset_add, multiset.to_finset_add, ih, to_multiset_single, support_add_eq,
      support_single_ne_zero hn, multiset.to_finset_nsmul _ _ hn,
      multiset.singleton_eq_singleton, multiset.to_finset_cons, multiset.to_finset_zero],
    refl,
    refine disjoint.mono_left support_single_subset _,
    rwa [finset.singleton_disjoint] }
end

@[simp] lemma count_to_multiset (f : α →₀ ℕ) (a : α) :
  f.to_multiset.count a = f a :=
calc f.to_multiset.count a = f.sum (λx n, (n •ℕ {x} : multiset α).count a) :
    (f.support.sum_hom $ multiset.count a).symm
  ... = f.sum (λx n, n * ({x} : multiset α).count a) : by simp only [multiset.count_smul]
  ... = f.sum (λx n, n * (x ::ₘ 0 : multiset α).count a) : rfl
  ... = f a * (a ::ₘ 0 : multiset α).count a : sum_eq_single _
    (λ a' _ H, by simp only [multiset.count_cons_of_ne (ne.symm H), multiset.count_zero, mul_zero])
    (λ H, by simp only [not_mem_support_iff.1 H, zero_mul])
  ... = f a : by simp only [multiset.count_singleton, mul_one]

lemma mem_support_multiset_sum [add_comm_monoid M]
  {s : multiset (α →₀ M)} (a : α) :
  a ∈ s.sum.support → ∃f∈s, a ∈ (f : α →₀ M).support :=
multiset.induction_on s false.elim
  begin
    assume f s ih ha,
    by_cases a ∈ f.support,
    { exact ⟨f, multiset.mem_cons_self _ _, h⟩ },
    { simp only [multiset.sum_cons, mem_support_iff, add_apply,
        not_mem_support_iff.1 h, zero_add] at ha,
      rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩,
      exact ⟨f', multiset.mem_cons_of_mem h₀, h₁⟩ }
  end

lemma mem_support_finset_sum [add_comm_monoid M]
  {s : finset ι} {h : ι → α →₀ M} (a : α) (ha : a ∈ (∑ c in s, h c).support) :
  ∃ c ∈ s, a ∈ (h c).support :=
let ⟨f, hf, hfa⟩ := mem_support_multiset_sum a ha in
let ⟨c, hc, eq⟩ := multiset.mem_map.1 hf in
⟨c, hc, eq.symm ▸ hfa⟩

@[simp] lemma mem_to_multiset (f : α →₀ ℕ) (i : α) :
  i ∈ f.to_multiset ↔ i ∈ f.support :=
by rw [← multiset.count_ne_zero, finsupp.count_to_multiset, finsupp.mem_support_iff]

end multiset

/-! ### Declarations about `curry` and `uncurry` -/

section curry_uncurry

variables [add_comm_monoid M] [add_comm_monoid N]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : (α × β) →₀ M) : α →₀ (β →₀ M) :=
f.sum $ λp c, single p.1 (single p.2 c)

lemma sum_curry_index (f : (α × β) →₀ M) (g : α → β → M → N)
  (hg₀ : ∀ a b, g a b 0 = 0) (hg₁ : ∀a b c₀ c₁, g a b (c₀ + c₁) = g a b c₀ + g a b c₁) :
  f.curry.sum (λa f, f.sum (g a)) = f.sum (λp c, g p.1 p.2 c) :=
begin
  rw [finsupp.curry],
  transitivity,
  { exact sum_sum_index (assume a, sum_zero_index)
      (assume a b₀ b₁, sum_add_index (assume a, hg₀ _ _) (assume c d₀ d₁, hg₁ _ _ _ _)) },
  congr, funext p c,
  transitivity,
  { exact sum_single_index sum_zero_index },
  exact sum_single_index (hg₀ _ _)
end

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ (β →₀ M)) : (α × β) →₀ M :=
f.sum $ λa g, g.sum $ λb c, single (a, b) c

/-- `finsupp_prod_equiv` defines the `equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsupp_prod_equiv : ((α × β) →₀ M) ≃ (α →₀ (β →₀ M)) :=
by refine ⟨finsupp.curry, finsupp.uncurry, λ f, _, λ f, _⟩; simp only [
  finsupp.curry, finsupp.uncurry, sum_sum_index, sum_zero_index, sum_add_index,
  sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff,
  forall_3_true_iff, prod.mk.eta, (single_sum _ _ _).symm, sum_single]

lemma filter_curry (f : α × β →₀ M) (p : α → Prop) :
  (f.filter (λa:α×β, p a.1)).curry = f.curry.filter p :=
begin
  rw [finsupp.curry, finsupp.curry, finsupp.sum, finsupp.sum, filter_sum, support_filter,
    sum_filter],
  refine finset.sum_congr rfl _,
  rintros ⟨a₁, a₂⟩ ha,
  dsimp only,
  split_ifs,
  { rw [filter_apply_pos, filter_single_of_pos]; exact h },
  { rwa [filter_single_of_neg] }
end

lemma support_curry (f : α × β →₀ M) : f.curry.support ⊆ f.support.image prod.fst :=
begin
  rw ← finset.bUnion_singleton,
  refine finset.subset.trans support_sum _,
  refine finset.bUnion_mono (assume a _, support_single_subset)
end

end curry_uncurry

section
variables [group G] [mul_action G α] [add_comm_monoid M]

/--
Scalar multiplication by a group element g,
given by precomposition with the action of g⁻¹ on the domain.
-/
def comap_has_scalar : has_scalar G (α →₀ M) :=
{ smul := λ g f, f.comap_domain (λ a, g⁻¹ • a)
  (λ a a' m m' h, by simpa [←mul_smul] using (congr_arg (λ a, g • a) h)) }

local attribute [instance] comap_has_scalar

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is multiplicative in g.
-/
def comap_mul_action : mul_action G (α →₀ M) :=
{ one_smul := λ f, by { ext, dsimp [(•)], simp, },
  mul_smul := λ g g' f, by { ext, dsimp [(•)], simp [mul_smul], }, }

local attribute [instance] comap_mul_action

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is additive in the second argument.
-/
def comap_distrib_mul_action :
  distrib_mul_action G (α →₀ M) :=
{ smul_zero := λ g, by { ext, dsimp [(•)], simp, },
  smul_add := λ g f f', by { ext, dsimp [(•)], simp, }, }

/--
Scalar multiplication by a group element on finitely supported functions on a group,
given by precomposition with the action of g⁻¹. -/
def comap_distrib_mul_action_self :
  distrib_mul_action G (G →₀ M) :=
@finsupp.comap_distrib_mul_action G M G _ (monoid.to_mul_action G) _

@[simp]
lemma comap_smul_single (g : G) (a : α) (b : M) :
  g • single a b = single (g • a) b :=
begin
  ext a',
  dsimp [(•)],
  by_cases h : g • a = a',
  { subst h, simp [←mul_smul], },
  { simp [single_eq_of_ne h], rw [single_eq_of_ne],
    rintro rfl, simpa [←mul_smul] using h, }
end

@[simp]
lemma comap_smul_apply (g : G) (f : α →₀ M) (a : α) :
  (g • f) a = f (g⁻¹ • a) := rfl

end

section
instance [semiring R] [add_comm_monoid M] [semimodule R M] : has_scalar R (α →₀ M) :=
⟨λa v, v.map_range ((•) a) (smul_zero _)⟩

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

@[simp] lemma coe_smul {_ : semiring R} [add_comm_monoid M] [semimodule R M]
  (b : R) (v : α →₀ M) : ⇑(b • v) = b • v := rfl
lemma smul_apply {_ : semiring R} [add_comm_monoid M] [semimodule R M]
  (b : R) (v : α →₀ M) (a : α) : (b • v) a = b • (v a) := rfl

variables (α M)

instance [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule R (α →₀ M) :=
{ smul      := (•),
  smul_add  := λ a x y, ext $ λ _, smul_add _ _ _,
  add_smul  := λ a x y, ext $ λ _, add_smul _ _ _,
  one_smul  := λ x, ext $ λ _, one_smul _ _,
  mul_smul  := λ r s x, ext $ λ _, mul_smul _ _ _,
  zero_smul := λ x, ext $ λ _, zero_smul _ _,
  smul_zero := λ x, ext $ λ _, smul_zero _ }

instance [semiring R] [semiring S] [add_comm_monoid M] [semimodule R M] [semimodule S M]
  [has_scalar R S] [is_scalar_tower R S M] :
  is_scalar_tower R S (α →₀ M) :=
{ smul_assoc := λ r s a, ext $ λ _, smul_assoc _ _ _ }

instance [semiring R] [semiring S] [add_comm_monoid M] [semimodule R M] [semimodule S M]
  [smul_comm_class R S M] :
  smul_comm_class R S (α →₀ M) :=
{ smul_comm := λ r s a, ext $ λ _, smul_comm _ _ _ }

variables {α M} {R}

lemma support_smul {_ : semiring R} [add_comm_monoid M] [semimodule R M] {b : R} {g : α →₀ M} :
  (b • g).support ⊆ g.support :=
λ a, by simp only [smul_apply, mem_support_iff, ne.def]; exact mt (λ h, h.symm ▸ smul_zero _)

section

variables {p : α → Prop}

@[simp] lemma filter_smul {_ : semiring R} [add_comm_monoid M] [semimodule R M]
  {b : R} {v : α →₀ M} : (b • v).filter p = b • v.filter p :=
coe_fn_injective $ set.indicator_smul {x | p x} b v

end

lemma map_domain_smul {_ : semiring R} [add_comm_monoid M] [semimodule R M]
   {f : α → β} (b : R) (v : α →₀ M) : map_domain f (b • v) = b • map_domain f v :=
begin
  change map_domain f (map_range _ _ _) = map_range _ _ _,
  apply finsupp.induction v, { simp only [map_domain_zero, map_range_zero] },
  intros a b v' hv₁ hv₂ IH,
  rw [map_range_add, map_domain_add, IH, map_domain_add, map_range_add,
    map_range_single, map_domain_single, map_domain_single, map_range_single];
  apply smul_add
end

@[simp] lemma smul_single {_ : semiring R} [add_comm_monoid M] [semimodule R M]
  (c : R) (a : α) (b : M) : c • finsupp.single a b = finsupp.single a (c • b) :=
map_range_single

@[simp] lemma smul_single' {_ : semiring R}
  (c : R) (a : α) (b : R) : c • finsupp.single a b = finsupp.single a (c * b) :=
smul_single _ _ _

lemma smul_single_one [semiring R] (a : α) (b : R) : b • single a 1 = single a b :=
by rw [smul_single, smul_eq_mul, mul_one]

end

lemma sum_smul_index [semiring R] [add_comm_monoid M] {g : α →₀ R} {b : R} {h : α → R → M}
  (h0 : ∀i, h i 0 = 0) : (b • g).sum h = g.sum (λi a, h i (b * a)) :=
finsupp.sum_map_range_index h0

lemma sum_smul_index' [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid N]
  {g : α →₀ M} {b : R} {h : α → M → N} (h0 : ∀i, h i 0 = 0) :
  (b • g).sum h = g.sum (λi c, h i (b • c)) :=
finsupp.sum_map_range_index h0

/-- A version of `finsupp.sum_smul_index'` for bundled additive maps. -/
lemma sum_smul_index_add_monoid_hom
  [semiring R] [add_comm_monoid M] [add_comm_monoid N] [semimodule R M]
  {g : α →₀ M} {b : R} {h : α → M →+ N} :
  (b • g).sum (λ a, h a) = g.sum (λ i c, h i (b • c)) :=
sum_map_range_index (λ i, (h i).map_zero)

instance [semiring R] [add_comm_monoid M] [semimodule R M] {ι : Type*}
  [no_zero_smul_divisors R M] : no_zero_smul_divisors R (ι →₀ M) :=
⟨λ c f h, or_iff_not_imp_left.mpr (λ hc, finsupp.ext
  (λ i, (smul_eq_zero.mp (finsupp.ext_iff.mp h i)).resolve_left hc))⟩

section
variables [semiring R] [semiring S]

lemma sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
  (s.sum f) * b = s.sum (λ a c, (f a c) * b) :=
by simp only [finsupp.sum, finset.sum_mul]

lemma mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
  b * (s.sum f) = s.sum (λ a c, b * (f a c)) :=
by simp only [finsupp.sum, finset.mul_sum]

instance unique_of_right [subsingleton R] : unique (α →₀ R) :=
{ uniq := λ l, ext $ λ i, subsingleton.elim _ _,
  .. finsupp.inhabited }

end

/-- Given an `add_comm_monoid M` and `s : set α`, `restrict_support_equiv s M` is the `equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
def restrict_support_equiv (s : set α) (M : Type*) [add_comm_monoid M] :
  {f : α →₀ M // ↑f.support ⊆ s } ≃ (s →₀ M):=
begin
  refine ⟨λf, subtype_domain (λx, x ∈ s) f.1, λ f, ⟨f.map_domain subtype.val, _⟩, _, _⟩,
  { refine set.subset.trans (finset.coe_subset.2 map_domain_support) _,
    rw [finset.coe_image, set.image_subset_iff],
    exact assume x hx, x.2 },
  { rintros ⟨f, hf⟩,
    apply subtype.eq,
    ext a,
    dsimp only,
    refine classical.by_cases (assume h : a ∈ set.range (subtype.val : s → α), _) (assume h, _),
    { rcases h with ⟨x, rfl⟩,
      rw [map_domain_apply subtype.val_injective, subtype_domain_apply] },
    { convert map_domain_notin_range _ _ h,
      rw [← not_mem_support_iff],
      refine mt _ h,
      exact assume ha, ⟨⟨a, hf ha⟩, rfl⟩ } },
  { assume f,
    ext ⟨a, ha⟩,
    dsimp only,
    rw [subtype_domain_apply, map_domain_apply subtype.val_injective] }
end

/-- Given `add_comm_monoid M` and `e : α ≃ β`, `dom_congr e` is the corresponding `equiv` between
`α →₀ M` and `β →₀ M`. -/
@[simps]
protected def dom_congr [add_comm_monoid M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) :=
{ to_fun := map_domain e,
  inv_fun := map_domain e.symm,
  left_inv := begin
    assume v,
    simp only [map_domain_comp.symm, (∘), equiv.symm_apply_apply],
    exact map_domain_id
  end,
  right_inv := begin
    assume v,
    simp only [map_domain_comp.symm, (∘), equiv.apply_symm_apply],
    exact map_domain_id
  end,
  map_add' := λ a b, map_domain_add, }

end finsupp

namespace finsupp

/-! ### Declarations about sigma types -/

section sigma

variables {αs : ι → Type*} [has_zero M] (l : (Σ i, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`. -/
def split (i : ι) : αs i →₀ M :=
l.comap_domain (sigma.mk i) (λ x1 x2 _ _ hx, heq_iff_eq.1 (sigma.mk.inj hx).2)

lemma split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ :=
begin
  dunfold split,
  rw comap_domain_apply
end

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def split_support : finset ι := l.support.image sigma.fst

lemma mem_split_support_iff_nonzero (i : ι) :
  i ∈ split_support l ↔ split l i ≠ 0 :=
begin
  rw [split_support, mem_image, ne.def, ← support_eq_empty, ← ne.def,
    ← finset.nonempty_iff_ne_empty, split, comap_domain, finset.nonempty],
  simp only [exists_prop, finset.mem_preimage, exists_and_distrib_right, exists_eq_right,
    mem_support_iff, sigma.exists, ne.def]
end

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def split_comp [has_zero N] (g : Π i, (αs i →₀ M) → N)
  (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N :=
{ support := split_support l,
  to_fun := λ i, g i (split l i),
  mem_support_to_fun :=
  begin
    intros i,
    rw [mem_split_support_iff_nonzero, not_iff_not, hg],
  end }

lemma sigma_support : l.support = l.split_support.sigma (λ i, (l.split i).support) :=
by simp only [finset.ext_iff, split_support, split, comap_domain, mem_image,
  mem_preimage, sigma.forall, mem_sigma]; tauto

lemma sigma_sum [add_comm_monoid N] (f : (Σ (i : ι), αs i) → M → N) :
  l.sum f = ∑ i in split_support l, (split l i).sum (λ (a : αs i) b, f ⟨i, a⟩ b) :=
by simp only [sum, sigma_support, sum_sigma, split_apply]

end sigma

end finsupp

/-! ### Declarations relating `multiset` to `finsupp` -/

namespace multiset

/-- Given a multiset `s`, `s.to_finsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
def to_finsupp : multiset α ≃+ (α →₀ ℕ) := finsupp.to_multiset.symm

@[simp] lemma to_finsupp_support (s : multiset α) :
  s.to_finsupp.support = s.to_finset :=
rfl

@[simp] lemma to_finsupp_apply (s : multiset α) (a : α) :
  to_finsupp s a = s.count a :=
rfl

lemma to_finsupp_zero : to_finsupp (0 : multiset α) = 0 := add_equiv.map_zero _

lemma to_finsupp_add (s t : multiset α) :
  to_finsupp (s + t) = to_finsupp s + to_finsupp t :=
to_finsupp.map_add s t

@[simp] lemma to_finsupp_singleton (a : α) : to_finsupp (a ::ₘ 0) = finsupp.single a 1 :=
finsupp.to_multiset.symm_apply_eq.2 $ by simp

@[simp] lemma to_finsupp_to_multiset (s : multiset α) :
  s.to_finsupp.to_multiset = s :=
finsupp.to_multiset.apply_symm_apply s

lemma to_finsupp_eq_iff {s : multiset α} {f : α →₀ ℕ} : s.to_finsupp = f ↔ s = f.to_multiset :=
finsupp.to_multiset.symm_apply_eq

end multiset

@[simp] lemma finsupp.to_multiset_to_finsupp (f : α →₀ ℕ) :
  f.to_multiset.to_finsupp = f :=
finsupp.to_multiset.symm_apply_apply f

/-! ### Declarations about order(ed) instances on `finsupp` -/

namespace finsupp

instance [preorder M] [has_zero M] : preorder (α →₀ M) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }

instance [partial_order M] [has_zero M] : partial_order (α →₀ M) :=
{ le_antisymm := λ f g hfg hgf, ext $ λ s, le_antisymm (hfg s) (hgf s),
  .. finsupp.preorder }

instance [ordered_cancel_add_comm_monoid M] : add_left_cancel_semigroup (α →₀ M) :=
{ add_left_cancel := λ a b c h, ext $ λ s,
  by { rw ext_iff at h, exact add_left_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_add_comm_monoid M] : add_right_cancel_semigroup (α →₀ M) :=
{ add_right_cancel := λ a b c h, ext $ λ s,
  by { rw ext_iff at h, exact add_right_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_add_comm_monoid M] : ordered_cancel_add_comm_monoid (α →₀ M) :=
{ add_le_add_left := λ a b h c s, add_le_add_left (h s) (c s),
  le_of_add_le_add_left := λ a b c h s, le_of_add_le_add_left (h s),
  .. finsupp.add_comm_monoid, .. finsupp.partial_order,
  .. finsupp.add_left_cancel_semigroup, .. finsupp.add_right_cancel_semigroup }

lemma le_def [preorder M] [has_zero M] {f g : α →₀ M} : f ≤ g ↔ ∀ x, f x ≤ g x := iff.rfl

lemma le_iff [canonically_ordered_add_monoid M] (f g : α →₀ M) :
  f ≤ g ↔ ∀ s ∈ f.support, f s ≤ g s :=
⟨λ h s hs, h s,
λ h s, if H : s ∈ f.support then h s H else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

@[simp] lemma add_eq_zero_iff [canonically_ordered_add_monoid M] (f g : α →₀ M) :
  f + g = 0 ↔ f = 0 ∧ g = 0 :=
by simp [ext_iff, forall_and_distrib]

/-- `finsupp.to_multiset` as an order isomorphism. -/
def order_iso_multiset : (α →₀ ℕ) ≃o multiset α :=
{ to_equiv := to_multiset.to_equiv,
  map_rel_iff' := λ f g, by simp [multiset.le_iff_count, le_def] }

@[simp] lemma coe_order_iso_multiset : ⇑(@order_iso_multiset α) = to_multiset := rfl

@[simp] lemma coe_order_iso_multiset_symm :
  ⇑(@order_iso_multiset α).symm = multiset.to_finsupp := rfl

lemma to_multiset_strict_mono : strict_mono (@to_multiset α) :=
order_iso_multiset.strict_mono

lemma sum_id_lt_of_lt (m n : α →₀ ℕ) (h : m < n) :
  m.sum (λ _, id) < n.sum (λ _, id) :=
begin
  rw [← card_to_multiset, ← card_to_multiset],
  apply multiset.card_lt_of_lt,
  exact to_multiset_strict_mono h
end

variable (α)

/-- The order on `σ →₀ ℕ` is well-founded.-/
lemma lt_wf : well_founded (@has_lt.lt (α →₀ ℕ) _) :=
subrelation.wf (sum_id_lt_of_lt) $ inv_image.wf _ nat.lt_wf

instance decidable_le : decidable_rel (@has_le.le (α →₀ ℕ) _) :=
λ m n, by rw le_iff; apply_instance

variable {α}

@[simp] lemma nat_add_sub_cancel (f g : α →₀ ℕ) : f + g - g = f :=
ext $ λ a, nat.add_sub_cancel _ _

@[simp] lemma nat_add_sub_cancel_left (f g : α →₀ ℕ) : f + g - f = g :=
ext $ λ a, nat.add_sub_cancel_left _ _

lemma nat_add_sub_of_le {f g : α →₀ ℕ} (h : f ≤ g) : f + (g - f) = g :=
ext $ λ a, nat.add_sub_of_le (h a)

lemma nat_sub_add_cancel {f g : α →₀ ℕ} (h : f ≤ g) : g - f + f = g :=
ext $ λ a, nat.sub_add_cancel (h a)

instance : canonically_ordered_add_monoid (α →₀ ℕ) :=
{ bot := 0,
  bot_le := λ f s, zero_le (f s),
  le_iff_exists_add := λ f g, ⟨λ H, ⟨g - f, (nat_add_sub_of_le H).symm⟩,
    λ ⟨c, hc⟩, hc.symm ▸ λ x, by simp⟩,
 .. (infer_instance : ordered_add_comm_monoid (α →₀ ℕ)) }

/-- The `finsupp` counterpart of `multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities of these pairs. -/
def antidiagonal (f : α →₀ ℕ) : ((α →₀ ℕ) × (α →₀ ℕ)) →₀ ℕ :=
(f.to_multiset.antidiagonal.map (prod.map multiset.to_finsupp multiset.to_finsupp)).to_finsupp

@[simp] lemma mem_antidiagonal_support {f : α →₀ ℕ} {p : (α →₀ ℕ) × (α →₀ ℕ)} :
  p ∈ (antidiagonal f).support ↔ p.1 + p.2 = f :=
begin
  rcases p with ⟨p₁, p₂⟩,
  simp [antidiagonal, ← and.assoc, ← finsupp.to_multiset.apply_eq_iff_eq]
end

lemma swap_mem_antidiagonal_support {n : α →₀ ℕ} {f : (α →₀ ℕ) × (α →₀ ℕ)} :
  f.swap ∈ (antidiagonal n).support ↔ f ∈ (antidiagonal n).support :=
by simp only [mem_antidiagonal_support, add_comm, prod.swap]

lemma antidiagonal_support_filter_fst_eq (f g : α →₀ ℕ) :
  (antidiagonal f).support.filter (λ p, p.1 = g) = if g ≤ f then {(g, f - g)} else ∅ :=
begin
  ext ⟨a, b⟩,
  suffices : a = g → (a + b = f ↔ g ≤ f ∧ b = f - g),
  { simpa [apply_ite ((∈) (a, b)), ← and.assoc, @and.right_comm _ (a = _), and.congr_left_iff] },
  rintro rfl, split,
  { rintro rfl, exact ⟨le_add_right le_rfl, (nat_add_sub_cancel_left _ _).symm⟩ },
  { rintro ⟨h, rfl⟩, exact nat_add_sub_of_le h }
end

lemma antidiagonal_support_filter_snd_eq (f g : α →₀ ℕ) :
  (antidiagonal f).support.filter (λ p, p.2 = g) = if g ≤ f then {(f - g, g)} else ∅ :=
begin
  ext ⟨a, b⟩,
  suffices : b = g → (a + b = f ↔ g ≤ f ∧ a = f - g),
  { simpa [apply_ite ((∈) (a, b)), ← and.assoc, and.congr_left_iff] },
  rintro rfl, split,
  { rintro rfl, exact ⟨le_add_left le_rfl, (nat_add_sub_cancel _ _).symm⟩ },
  { rintro ⟨h, rfl⟩, exact nat_sub_add_cancel h }
end

@[simp] lemma antidiagonal_zero : antidiagonal (0 : α →₀ ℕ) = single (0,0) 1 :=
by rw [← multiset.to_finsupp_singleton]; refl

@[to_additive]
lemma prod_antidiagonal_support_swap {M : Type*} [comm_monoid M] (n : α →₀ ℕ)
  (f : (α →₀ ℕ) → (α →₀ ℕ) → M) :
  ∏ p in (antidiagonal n).support, f p.1 p.2 = ∏ p in (antidiagonal n).support, f p.2 p.1 :=
finset.prod_bij (λ p hp, p.swap) (λ p, swap_mem_antidiagonal_support.2) (λ p hp, rfl)
  (λ p₁ p₂ _ _ h, prod.swap_injective h)
  (λ p hp, ⟨p.swap, swap_mem_antidiagonal_support.2 hp, p.swap_swap.symm⟩)

/-- The set `{m : α →₀ ℕ | m ≤ n}` as a `finset`. -/
def Iic_finset (n : α →₀ ℕ) : finset (α →₀ ℕ) :=
(antidiagonal n).support.image prod.fst

@[simp] lemma mem_Iic_finset {m n : α →₀ ℕ} : m ∈ Iic_finset n ↔ m ≤ n :=
by simp [Iic_finset, le_iff_exists_add, eq_comm]

@[simp] lemma coe_Iic_finset (n : α →₀ ℕ) : ↑(Iic_finset n) = set.Iic n :=
by { ext, simp }

/-- Let `n : α →₀ ℕ` be a finitely supported function.
The set of `m : α →₀ ℕ` that are coordinatewise less than or equal to `n`,
is a finite set. -/
lemma finite_le_nat (n : α →₀ ℕ) : set.finite {m | m ≤ n} :=
by simpa using (Iic_finset n).finite_to_set

/-- Let `n : α →₀ ℕ` be a finitely supported function.
The set of `m : α →₀ ℕ` that are coordinatewise less than or equal to `n`,
but not equal to `n` everywhere, is a finite set. -/
lemma finite_lt_nat (n : α →₀ ℕ) : set.finite {m | m < n} :=
(finite_le_nat n).subset $ λ m, le_of_lt

end finsupp

namespace multiset

lemma to_finsuppstrict_mono : strict_mono (@to_finsupp α) :=
finsupp.order_iso_multiset.symm.strict_mono

end multiset
