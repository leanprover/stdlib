/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import algebra.big_operators.pi
import algebra.module.pi
import algebra.module.prod
import algebra.module.submodule
import data.finsupp.basic

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps. If `p` and `q` are submodules of a module, `p ≤ q`
means that `p ⊆ q`.

Many of the relevant definitions, including `module`, `submodule`, and `linear_map`, are found in
`src/algebra/module`.

## Main definitions

* Many constructors for linear maps, including `prod` and `coprod`
* `submodule.span s` is defined to be the smallest submodule containing the set `s`.
* If `p` is a submodule of `M`, `submodule.quotient p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.
* The general linear group is defined to be the group of invertible linear maps from `M` to itself.

## Main statements

* The first and second isomorphism laws for modules are proved as `quot_ker_equiv_range` and
  `quotient_inf_equiv_sup_quotient`.

## Notations

* We continue to use the notation `M →ₗ[R] M₂` for the type of linear maps from `M` to `M₂` over the
  ring `R`.
* We introduce the notations `M ≃ₗ M₂` and `M ≃ₗ[R] M₂` for `linear_equiv M M₂`. In the first, the
  ring `R` is implicit.
* We introduce the notation `R ∙ v` for the span of a singleton, `submodule.span R {v}`.  This is
  `\.`, not the same as the scalar multiplication `•`/`\bub`.

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`prod`, `coprod`, arithmetic operations like `+`) instead of defining a function and proving
it is linear.

## Tags
linear algebra, vector space, module

-/

open function
open_locale big_operators

universes u v w x y z u' v' w' y'
variables {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variables {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}

namespace finsupp

lemma smul_sum {α : Type u} {β : Type v} {R : Type w} {M : Type y}
  [has_zero β] [semiring R] [add_comm_monoid M] [semimodule R M]
  {v : α →₀ β} {c : R} {h : α → β → M} :
  c • (v.sum h) = v.sum (λa b, c • h a b) :=
finset.smul_sum

end finsupp

section
open_locale classical

/-- decomposing `x : ι → R` as a sum along the canonical basis -/
lemma pi_eq_sum_univ {ι : Type u} [fintype ι] {R : Type v} [semiring R] (x : ι → R) :
  x = ∑ i, x i • (λj, if i = j then 1 else 0) :=
by { ext, simp }

end

/-! ### Properties of linear maps -/
namespace linear_map

section add_comm_monoid
variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]
variables (f g : M →ₗ[R] M₂)
include R

@[simp] theorem comp_id : f.comp id = f :=
linear_map.ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
linear_map.ext $ λ x, rfl

theorem comp_assoc (g : M₂ →ₗ[R] M₃) (h : M₃ →ₗ[R] M₄) : (h.comp g).comp f = h.comp (g.comp f) :=
rfl

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def dom_restrict (f : M →ₗ[R] M₂) (p : submodule R M) : p →ₗ[R] M₂ := f.comp p.subtype

@[simp] lemma dom_restrict_apply (f : M →ₗ[R] M₂) (p : submodule R M) (x : p) :
  f.dom_restrict p x = f x := rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (h : ∀c, f c ∈ p) : M₂ →ₗ[R] p :=
by refine {to_fun := λc, ⟨f c, h c⟩, ..}; intros; apply set_coe.ext; simp

@[simp] theorem cod_restrict_apply (p : submodule R M) (f : M₂ →ₗ[R] M) {h} (x : M₂) :
  (cod_restrict p f h x : M) = f x := rfl

@[simp] lemma comp_cod_restrict (p : submodule R M₂) (h : ∀b, f b ∈ p) (g : M₃ →ₗ[R] M) :
  (cod_restrict p f h).comp g = cod_restrict p (f.comp g) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (p : submodule R M₂) (h : ∀b, f b ∈ p) :
  p.subtype.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- Restrict domain and codomain of an endomorphism. -/
def restrict (f : M →ₗ[R] M) {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) : p →ₗ[R] p :=
(f.dom_restrict p).cod_restrict p $ submodule.forall.2 hf

lemma restrict_apply
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) (x : p) :
  f.restrict hf x = ⟨f x, hf x.1 x.2⟩ := rfl

lemma subtype_comp_restrict {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) :
  p.subtype.comp (f.restrict hf) = f.dom_restrict p := rfl

lemma restrict_eq_cod_restrict_dom_restrict
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) :
  f.restrict hf = (f.dom_restrict p).cod_restrict p (λ x, hf x.1 x.2) := rfl

lemma restrict_eq_dom_restrict_cod_restrict
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x, f x ∈ p) :
  f.restrict (λ x _, hf x) = (f.cod_restrict p hf).dom_restrict p := rfl

/-- The constant 0 map is linear. -/
instance : has_zero (M →ₗ[R] M₂) := ⟨⟨λ _, 0, by simp, by simp⟩⟩

instance : inhabited (M →ₗ[R] M₂) := ⟨0⟩

@[simp] lemma zero_apply (x : M) : (0 : M →ₗ[R] M₂) x = 0 := rfl

@[simp] lemma default_def : default (M →ₗ[R] M₂) = 0 := rfl

instance unique_of_left [subsingleton M] : unique (M →ₗ[R] M₂) :=
{ uniq := λ f, ext $ λ x, by rw [subsingleton.elim x 0, map_zero, map_zero],
  .. linear_map.inhabited }

instance unique_of_right [subsingleton M₂] : unique (M →ₗ[R] M₂) :=
coe_injective.unique

/-- The sum of two linear maps is linear. -/
instance : has_add (M →ₗ[R] M₂) :=
⟨λ f g, ⟨λ b, f b + g b, by simp [add_comm, add_left_comm], by simp [smul_add]⟩⟩

@[simp] lemma add_apply (x : M) : (f + g) x = f x + g x := rfl

/-- The type of linear maps is an additive monoid. -/
instance : add_comm_monoid (M →ₗ[R] M₂) :=
by refine {zero := 0, add := (+), ..};
   intros; ext; simp [add_comm, add_left_comm]

instance linear_map_apply_is_add_monoid_hom (a : M) :
  is_add_monoid_hom (λ f : M →ₗ[R] M₂, f a) :=
{ map_add := λ f g, linear_map.add_apply f g a,
  map_zero := rfl }

lemma add_comp (g : M₂ →ₗ[R] M₃) (h : M₂ →ₗ[R] M₃) :
  (h + g).comp f = h.comp f + g.comp f := rfl

lemma comp_add (g : M →ₗ[R] M₂) (h : M₂ →ₗ[R] M₃) :
  h.comp (f + g) = h.comp f + h.comp g := by { ext, simp }

lemma sum_apply (t : finset ι) (f : ι → M →ₗ[R] M₂) (b : M) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
(t.sum_hom (λ g : M →ₗ[R] M₂, g b)).symm

/-- `λb, f b • x` is a linear map. -/
def smul_right (f : M₂ →ₗ[R] R) (x : M) : M₂ →ₗ[R] M :=
⟨λb, f b • x, by simp [add_smul], by simp [smul_smul]⟩.

@[simp] theorem smul_right_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
  (smul_right f x : M₂ → M) c = f c • x := rfl

instance : has_one (M →ₗ[R] M) := ⟨linear_map.id⟩
instance : has_mul (M →ₗ[R] M) := ⟨linear_map.comp⟩

lemma mul_eq_comp (f g : M →ₗ[R] M) : f * g = f.comp g := rfl

@[simp] lemma one_app (x : M) : (1 : M →ₗ[R] M) x = x := rfl
@[simp] lemma mul_app (A B : M →ₗ[R] M) (x : M) : (A * B) x = A (B x) := rfl

@[simp] theorem comp_zero : f.comp (0 : M₃ →ₗ[R] M) = 0 :=
ext $ assume c, by rw [comp_apply, zero_apply, zero_apply, f.map_zero]

@[simp] theorem zero_comp : (0 : M₂ →ₗ[R] M₃).comp f = 0 :=
rfl

@[norm_cast] lemma coe_fn_sum {ι : Type*} (t : finset ι) (f : ι → M →ₗ[R] M₂) :
  ⇑(∑ i in t, f i) = ∑ i in t, (f i : M → M₂) :=
add_monoid_hom.map_sum ⟨@to_fun R M M₂ _ _ _ _ _, rfl, λ x y, rfl⟩ _ _

instance : monoid (M →ₗ[R] M) :=
by refine {mul := (*), one := 1, ..}; { intros, apply linear_map.ext, simp {proj := ff} }

section
open_locale classical

/-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
of the canonical basis. -/
lemma pi_apply_eq_sum_univ [fintype ι] (f : (ι → R) →ₗ[R] M) (x : ι → R) :
  f x = ∑ i, x i • (f (λj, if i = j then 1 else 0)) :=
begin
  conv_lhs { rw [pi_eq_sum_univ x, f.map_sum] },
  apply finset.sum_congr rfl (λl hl, _),
  rw f.map_smul
end

end

section
variables (R M M₂)

/-- The first projection of a product is a linear map. -/
def fst : M × M₂ →ₗ[R] M := ⟨prod.fst, λ x y, rfl, λ x y, rfl⟩

/-- The second projection of a product is a linear map. -/
def snd : M × M₂ →ₗ[R] M₂ := ⟨prod.snd, λ x y, rfl, λ x y, rfl⟩
end

@[simp] theorem fst_apply (x : M × M₂) : fst R M M₂ x = x.1 := rfl
@[simp] theorem snd_apply (x : M × M₂) : snd R M M₂ x = x.2 := rfl

/-- The prod of two linear maps is a linear map. -/
def prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : M →ₗ[R] M₂ × M₃ :=
{ to_fun    := λ x, (f x, g x),
  map_add'  := λ x y, by simp only [prod.mk_add_mk, map_add],
  map_smul' := λ c x, by simp only [prod.smul_mk, map_smul] }

@[simp] theorem prod_apply (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (x : M) :
  prod f g x = (f x, g x) := rfl

@[simp] theorem fst_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  (fst R M₂ M₃).comp (prod f g) = f := by ext; refl

@[simp] theorem snd_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  (snd R M₂ M₃).comp (prod f g) = g := by ext; refl

@[simp] theorem pair_fst_snd : prod (fst R M M₂) (snd R M M₂) = linear_map.id :=
by ext; refl

section
variables (R M M₂)

/-- The left injection into a product is a linear map. -/
def inl : M →ₗ[R] M × M₂ := by refine ⟨add_monoid_hom.inl _ _, _, _⟩; intros; simp

/-- The right injection into a product is a linear map. -/
def inr : M₂ →ₗ[R] M × M₂ := by refine ⟨add_monoid_hom.inr _ _, _, _⟩; intros; simp

end

@[simp] theorem inl_apply (x : M) : inl R M M₂ x = (x, 0) := rfl
@[simp] theorem inr_apply (x : M₂) : inr R M M₂ x = (0, x) := rfl

theorem inl_injective : function.injective (inl R M M₂) :=
λ _, by simp

theorem inr_injective : function.injective (inr R M M₂) :=
λ _, by simp

/-- The coprod function `λ x : M × M₂, f x.1 + g x.2` is a linear map. -/
def coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : M × M₂ →ₗ[R] M₃ :=
{ to_fun    := λ x, f x.1 + g x.2,
  map_add'  := λ x y, by simp only [map_add, prod.snd_add, prod.fst_add]; cc,
  map_smul' := λ x y, by simp only [smul_add, prod.smul_snd, prod.smul_fst, map_smul] }

@[simp] theorem coprod_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (x : M) (y : M₂) :
  coprod f g (x, y) = f x + g y := rfl

@[simp] theorem coprod_inl (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (coprod f g).comp (inl R M M₂) = f :=
by ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

@[simp] theorem coprod_inr (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (coprod f g).comp (inr R M M₂) = g :=
by ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

@[simp] theorem coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = linear_map.id :=
by ext ⟨x, y⟩; simp only [prod.mk_add_mk, add_zero, id_apply, coprod_apply,
  inl_apply, inr_apply, zero_add]

theorem fst_eq_coprod : fst R M M₂ = coprod linear_map.id 0 := by ext ⟨x, y⟩; simp

theorem snd_eq_coprod : snd R M M₂ = coprod 0 linear_map.id := by ext ⟨x, y⟩; simp

theorem inl_eq_prod : inl R M M₂ = prod linear_map.id 0 := rfl

theorem inr_eq_prod : inr R M M₂ = prod 0 linear_map.id := rfl

/-- `prod.map` of two linear maps. -/
def prod_map (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : (M × M₂) →ₗ[R] (M₃ × M₄) :=
(f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))

@[simp] theorem prod_map_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) (x) :
  f.prod_map g x = (f x.1, g x.2) := rfl

end add_comm_monoid

section add_comm_group

variables [semiring R]
  [add_comm_monoid M] [add_comm_group M₂] [add_comm_group M₃] [add_comm_group M₄]
  [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]
  (f g : M →ₗ[R] M₂)

/-- The negation of a linear map is linear. -/
instance : has_neg (M →ₗ[R] M₂) :=
⟨λ f, ⟨λ b, - f b, by simp [add_comm], by simp⟩⟩

@[simp] lemma neg_apply (x : M) : (- f) x = - f x := rfl

@[simp] lemma comp_neg (g : M₂ →ₗ[R] M₃) : g.comp (- f) = - g.comp f := by { ext, simp }

/-- The negation of a linear map is linear. -/
instance : has_sub (M →ₗ[R] M₂) :=
⟨λ f g,
  ⟨λ b, f b - g b,
   by { simp only [map_add, sub_eq_add_neg, neg_add], cc },
   by { intros, simp only [map_smul, smul_sub] }⟩⟩

@[simp] lemma sub_apply (x : M) : (f - g) x = f x - g x := rfl

lemma sub_comp (g : M₂ →ₗ[R] M₃) (h : M₂ →ₗ[R] M₃) :
  (g - h).comp f = g.comp f - h.comp f := rfl

lemma comp_sub (g : M →ₗ[R] M₂) (h : M₂ →ₗ[R] M₃) :
  h.comp (g - f) = h.comp g - h.comp f := by { ext, simp }

/-- The type of linear maps is an additive group. -/
instance : add_comm_group (M →ₗ[R] M₂) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, sub := has_sub.sub, sub_eq_add_neg := _, ..};
   intros; ext; simp [add_comm, add_left_comm, sub_eq_add_neg]

instance linear_map_apply_is_add_group_hom (a : M) :
  is_add_group_hom (λ f : M →ₗ[R] M₂, f a) :=
{ map_add := λ f g, linear_map.add_apply f g a }

end add_comm_group

section has_scalar
variables {S : Type*} [semiring R] [monoid S]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
  [semimodule R M] [semimodule R M₂] [semimodule R M₃]
  [distrib_mul_action S M₂] [smul_comm_class R S M₂]
  (f : M →ₗ[R] M₂)

instance : has_scalar S (M →ₗ[R] M₂) :=
⟨λ a f, ⟨λ b, a • f b, λ x y, by rw [f.map_add, smul_add],
  λ c x, by simp only [f.map_smul, smul_comm c]⟩⟩

@[simp] lemma smul_apply (a : S) (x : M) : (a • f) x = a • f x := rfl

instance : distrib_mul_action S (M →ₗ[R] M₂) :=
{ one_smul := λ f, ext $ λ _, one_smul _ _,
  mul_smul := λ c c' f, ext $ λ _, mul_smul _ _ _,
  smul_add := λ c f g, ext $ λ x, smul_add _ _ _,
  smul_zero := λ c, ext $ λ x, smul_zero _ }

theorem smul_comp (a : S) (g : M₃ →ₗ[R] M₂) (f : M →ₗ[R] M₃) : (a • g).comp f = a • (g.comp f) :=
rfl

end has_scalar

section semimodule

variables {S : Type*} [semiring R] [semiring S]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
  [semimodule R M] [semimodule R M₂] [semimodule R M₃]
  [semimodule S M₂] [semimodule S M₃] [smul_comm_class R S M₂] [smul_comm_class R S M₃]
  (f : M →ₗ[R] M₂)

instance : semimodule S (M →ₗ[R] M₂) :=
{ add_smul := λ a b f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `applyₗ` for a version where `S = R` -/
def applyₗ' (v : M) : (M →ₗ[R] M₂) →ₗ[S] M₂ :=
{ to_fun := λ f, f v,
  map_add' := λ f g, f.add_apply g v,
  map_smul' := λ x f, f.smul_apply x v }

end semimodule

section comm_semiring

variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
variables (f g : M →ₗ[R] M₂)
include R

theorem comp_smul (g : M₂ →ₗ[R] M₃) (a : R) : g.comp (a • f) = a • (g.comp f) :=
ext $ assume b, by rw [comp_apply, smul_apply, g.map_smul]; refl

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M₂ → M₃`. -/
def comp_right (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] (M →ₗ[R] M₃) :=
⟨f.comp,
λ _ _, linear_map.ext $ λ _, f.2 _ _,
λ _ _, linear_map.ext $ λ _, f.3 _ _⟩

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `linear_map.applyₗ'` for a version that works with two different semirings. -/
def applyₗ (v : M) : (M →ₗ[R] M₂) →ₗ[R] M₂ :=
applyₗ' R v

end comm_semiring

section semiring

variables [semiring R] [add_comm_monoid M] [semimodule R M]

instance endomorphism_semiring : semiring (M →ₗ[R] M) :=
by refine {mul := (*), one := 1, ..linear_map.add_comm_monoid, ..};
  { intros, apply linear_map.ext, simp {proj := ff} }

lemma mul_apply (f g : M →ₗ[R] M) (x : M) : (f * g) x = f (g x) := rfl

end semiring

section ring

variables [ring R] [add_comm_group M] [semimodule R M]

instance endomorphism_ring : ring (M →ₗ[R] M) :=
{ ..linear_map.endomorphism_semiring, ..linear_map.add_comm_group }

end ring

section comm_ring
variables [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smul_rightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M :=
{ to_fun := λ f, {
    to_fun    := linear_map.smul_right f,
    map_add'  := λ m m', by { ext, apply smul_add, },
    map_smul' := λ c m, by { ext, apply smul_comm, } },
  map_add'  := λ f f', by { ext, apply add_smul, },
  map_smul' := λ c f, by { ext, apply mul_smul, } }

@[simp] lemma smul_rightₗ_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
  (smul_rightₗ : (M₂ →ₗ R) →ₗ M →ₗ M₂ →ₗ M) f x c = (f c) • x := rfl

end comm_ring

end linear_map

/-! ### Properties of submodules -/

namespace submodule

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
variables (p p' : submodule R M) (q q' : submodule R M₂)
variables {r : R} {x y : M}
open set

instance : partial_order (submodule R M) :=
{ le := λ p p', ∀ ⦃x⦄, x ∈ p → x ∈ p',
  ..partial_order.lift (coe : submodule R M → set M) coe_injective }

variables {p p'}

lemma le_def : p ≤ p' ↔ (p : set M) ⊆ p' := iff.rfl

lemma le_def' : p ≤ p' ↔ ∀ x ∈ p, x ∈ p' := iff.rfl

lemma lt_def : p < p' ↔ (p : set M) ⊂ p' := iff.rfl

lemma not_le_iff_exists : ¬ (p ≤ p') ↔ ∃ x ∈ p, x ∉ p' := not_subset

lemma exists_of_lt {p p' : submodule R M} : p < p' → ∃ x ∈ p', x ∉ p := exists_of_ssubset

lemma lt_iff_le_and_exists : p < p' ↔ p ≤ p' ∧ ∃ x ∈ p', x ∉ p :=
by rw [lt_iff_le_not_le, not_le_iff_exists]

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `of_le p p'` is the linear map version of
this inclusion. -/
def of_le (h : p ≤ p') : p →ₗ[R] p' :=
p.subtype.cod_restrict p' $ λ ⟨x, hx⟩, h hx

@[simp] theorem coe_of_le (h : p ≤ p') (x : p) :
  (of_le h x : M) = x := rfl

theorem of_le_apply (h : p ≤ p') (x : p) : of_le h x = ⟨x, h x.2⟩ := rfl

variables (p p')

lemma subtype_comp_of_le (p q : submodule R M) (h : p ≤ q) :
  q.subtype.comp (of_le h) = p.subtype :=
by { ext ⟨b, hb⟩, refl }

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : has_bot (submodule R M) :=
⟨{ carrier := {0}, smul_mem' := by simp { contextual := tt }, .. (⊥ : add_submonoid M)}⟩

instance inhabited' : inhabited (submodule R M) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : submodule R M) : set M) = {0} := rfl

section
variables (R)
@[simp] lemma mem_bot : x ∈ (⊥ : submodule R M) ↔ x = 0 := mem_singleton_iff
end

lemma nonzero_mem_of_bot_lt {I : submodule R M} (bot_lt : ⊥ < I) : ∃ a : I, a ≠ 0 :=
begin
  have h := (submodule.lt_iff_le_and_exists.1 bot_lt).2,
  tidy,
end

instance : order_bot (submodule R M) :=
{ bot := ⊥,
  bot_le := λ p x, by simp {contextual := tt},
  ..submodule.partial_order }

protected lemma eq_bot_iff (p : submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
⟨ λ h, h.symm ▸ λ x hx, (mem_bot R).mp hx,
  λ h, eq_bot_iff.mpr (λ x hx, (mem_bot R).mpr (h x hx)) ⟩

protected lemma ne_bot_iff (p : submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) :=
by { haveI := classical.prop_decidable, simp_rw [ne.def, p.eq_bot_iff, not_forall] }

/-- The universal set is the top element of the lattice of submodules. -/
instance : has_top (submodule R M) :=
⟨{ carrier := univ, smul_mem' := λ _ _ _, trivial, .. (⊤ : add_submonoid M)}⟩

@[simp] lemma top_coe : ((⊤ : submodule R M) : set M) = univ := rfl

@[simp] lemma mem_top : x ∈ (⊤ : submodule R M) := trivial

lemma eq_bot_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : p = ⊥ :=
by ext x; simp [semimodule.eq_zero_of_zero_eq_one x zero_eq_one]

instance : order_top (submodule R M) :=
{ top := ⊤,
  le_top := λ p x _, trivial,
  ..submodule.partial_order }

instance : has_Inf (submodule R M) :=
⟨λ S, {
  carrier   := ⋂ s ∈ S, (s : set M),
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt} }⟩

private lemma Inf_le' {S : set (submodule R M)} {p} : p ∈ S → Inf S ≤ p :=
bInter_subset_of_mem

private lemma le_Inf' {S : set (submodule R M)} {p} : (∀p' ∈ S, p ≤ p') → p ≤ Inf S :=
subset_bInter

instance : has_inf (submodule R M) :=
⟨λ p p', {
  carrier   := p ∩ p',
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt} }⟩

instance : complete_lattice (submodule R M) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c, subset_inter,
  inf_le_left  := λ a b, inter_subset_left _ _,
  inf_le_right := λ a b, inter_subset_right _ _,
  Sup          := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ p' hp', hp' _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..submodule.order_top,
  ..submodule.order_bot }

instance add_comm_monoid_submodule : add_comm_monoid (submodule R M) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

@[simp] lemma add_eq_sup (p q : submodule R M) : p + q = p ⊔ q := rfl
@[simp] lemma zero_eq_bot : (0 : submodule R M) = ⊥ := rfl

lemma eq_top_iff' {p : submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, @h x trivial, λ h x _, h x⟩

lemma bot_ne_top [nontrivial M] : (⊥ : submodule R M) ≠ ⊤ :=
λ h, let ⟨a, ha⟩ := exists_ne (0 : M) in ha $ (mem_bot R).1 $ (eq_top_iff.1 h) trivial

@[simp] theorem inf_coe : (p ⊓ p' : set M) = p ∩ p' := rfl

@[simp] theorem mem_inf {p p' : submodule R M} :
  x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[simp] theorem Inf_coe (P : set (submodule R M)) : (↑(Inf P) : set M) = ⋂ p ∈ P, ↑p := rfl

@[simp] theorem infi_coe {ι} (p : ι → submodule R M) :
  (↑⨅ i, p i : set M) = ⋂ i, ↑(p i) :=
by rw [infi, Inf_coe]; ext a; simp; exact
⟨λ h i, h _ i rfl, λ h i x e, e ▸ h _⟩

@[simp] lemma mem_Inf {S : set (submodule R M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
set.mem_bInter_iff

@[simp] theorem mem_infi {ι} (p : ι → submodule R M) :
  x ∈ (⨅ i, p i) ↔ ∀ i, x ∈ p i :=
by rw [← mem_coe, infi_coe, mem_Inter]; refl

theorem disjoint_def {p p' : submodule R M} :
  disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0:M) :=
show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : set M)) ↔ _, by simp

theorem disjoint_def' {p p' : submodule R M} :
  disjoint p p' ↔ ∀ (x ∈ p) (y ∈ p'), x = y → x = (0:M) :=
disjoint_def.trans ⟨λ h x hx y hy hxy, h x hx $ hxy.symm ▸ hy,
  λ h x hx hx', h _ hx x hx' rfl⟩

theorem mem_right_iff_eq_zero_of_disjoint {p p' : submodule R M} (h : disjoint p p') {x : p} :
  (x:M) ∈ p' ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x x.2 hx, λ h, h.symm ▸ p'.zero_mem⟩

theorem mem_left_iff_eq_zero_of_disjoint {p p' : submodule R M} (h : disjoint p p') {x : p'} :
  (x:M) ∈ p ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x hx x.2, λ h, h.symm ▸ p.zero_mem⟩

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ₗ[R] M₂) (p : submodule R M) : submodule R M₂ :=
{ carrier   := f '' p,
  smul_mem' := by rintro a _ ⟨b, hb, rfl⟩; exact ⟨_, p.smul_mem _ hb, f.map_smul _ _⟩,
  .. p.to_add_submonoid.map f.to_add_monoid_hom }

@[simp] lemma map_coe (f : M →ₗ[R] M₂) (p : submodule R M) :
  (map f p : set M₂) = f '' p := rfl

@[simp] lemma mem_map {f : M →ₗ[R] M₂} {p : submodule R M} {x : M₂} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

theorem mem_map_of_mem {f : M →ₗ[R] M₂} {p : submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
set.mem_image_of_mem _ h

@[simp] lemma map_id : map linear_map.id p = p :=
submodule.ext $ λ a, by simp

lemma map_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : submodule R M) :
  map (g.comp f) p = map g (map f p) :=
submodule.coe_injective $ by simp [map_coe]; rw ← image_comp

lemma map_mono {f : M →ₗ[R] M₂} {p p' : submodule R M} : p ≤ p' → map f p ≤ map f p' :=
image_subset _

@[simp] lemma map_zero : map (0 : M →ₗ[R] M₂) p = ⊥ :=
have ∃ (x : M), x ∈ p := ⟨0, p.zero_mem⟩,
ext $ by simp [this, eq_comm]

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : M →ₗ[R] M₂) (p : submodule R M₂) : submodule R M :=
{ carrier   := f ⁻¹' p,
  smul_mem' := λ a x h, by simp [p.smul_mem _ h],
  .. p.to_add_submonoid.comap f.to_add_monoid_hom }

@[simp] lemma comap_coe (f : M →ₗ[R] M₂) (p : submodule R M₂) :
  (comap f p : set M) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : M →ₗ[R] M₂} {p : submodule R M₂} :
  x ∈ comap f p ↔ f x ∈ p := iff.rfl

lemma comap_id : comap linear_map.id p = p :=
submodule.coe_injective rfl

lemma comap_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : submodule R M₃) :
  comap (g.comp f) p = comap f (comap g p) := rfl

lemma comap_mono {f : M →ₗ[R] M₂} {q q' : submodule R M₂} : q ≤ q' → comap f q ≤ comap f q' :=
preimage_mono

lemma map_le_iff_le_comap {f : M →ₗ[R] M₂} {p : submodule R M} {q : submodule R M₂} :
  map f p ≤ q ↔ p ≤ comap f q := image_subset_iff

lemma gc_map_comap (f : M →ₗ[R] M₂) : galois_connection (map f) (comap f)
| p q := map_le_iff_le_comap

@[simp] lemma map_bot (f : M →ₗ[R] M₂) : map f ⊥ = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma map_sup (f : M →ₗ[R] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
(gc_map_comap f).l_sup

@[simp] lemma map_supr {ι : Sort*} (f : M →ₗ[R] M₂) (p : ι → submodule R M) :
  map f (⨆i, p i) = (⨆i, map f (p i)) :=
(gc_map_comap f).l_supr

@[simp] lemma comap_top (f : M →ₗ[R] M₂) : comap f ⊤ = ⊤ := rfl

@[simp] lemma comap_inf (f : M →ₗ[R] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' := rfl

@[simp] lemma comap_infi {ι : Sort*} (f : M →ₗ[R] M₂) (p : ι → submodule R M₂) :
  comap f (⨅i, p i) = (⨅i, comap f (p i)) :=
(gc_map_comap f).u_infi

@[simp] lemma comap_zero : comap (0 : M →ₗ[R] M₂) q = ⊤ :=
ext $ by simp

lemma map_comap_le (f : M →ₗ[R] M₂) (q : submodule R M₂) : map f (comap f q) ≤ q :=
(gc_map_comap f).l_u_le _

lemma le_comap_map (f : M →ₗ[R] M₂) (p : submodule R M) : p ≤ comap f (map f p) :=
(gc_map_comap f).le_u_l _

--TODO(Mario): is there a way to prove this from order properties?
lemma map_inf_eq_map_inf_comap {f : M →ₗ[R] M₂}
  {p : submodule R M} {p' : submodule R M₂} :
  map f p ⊓ p' = map f (p ⊓ comap f p') :=
le_antisymm
  (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
  (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

lemma map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
ext $ λ x, ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

lemma eq_zero_of_bot_submodule : ∀(b : (⊥ : submodule R M)), b = 0
| ⟨b', hb⟩ := subtype.eq $ show b' = 0, from (mem_bot R).1 hb

section
variables (R)

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : set M) : submodule R M := Inf {p | s ⊆ p}
end

variables {s t : set M}
lemma mem_span : x ∈ span R s ↔ ∀ p : submodule R M, s ⊆ p → x ∈ p :=
mem_bInter_iff

lemma subset_span : s ⊆ span R s :=
λ x h, mem_span.2 $ λ p hp, hp h

lemma span_le {p} : span R s ≤ p ↔ s ⊆ p :=
⟨subset.trans subset_span, λ ss x h, mem_span.1 h _ ss⟩

lemma span_mono (h : s ⊆ t) : span R s ≤ span R t :=
span_le.2 $ subset.trans h subset_span

lemma span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
le_antisymm (span_le.2 h₁) h₂

@[simp] lemma span_eq : span R (p : set M) = p :=
span_eq_of_le _ (subset.refl _) subset_span

lemma map_span (f : M →ₗ[R] M₂) (s : set M) :
  (span R s).map f = span R (f '' s) :=
eq.symm $ span_eq_of_le _ (set.image_subset f subset_span) $
map_le_iff_le_comap.2 $ span_le.2 $ λ x hx, subset_span ⟨x, hx, rfl⟩

/- See also `span_preimage_eq` below. -/
lemma span_preimage_le (f : M →ₗ[R] M₂) (s : set M₂) :
  span R (f ⁻¹' s) ≤ (span R s).comap f :=
by { rw [span_le, comap_coe], exact preimage_mono (subset_span), }

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
@[elab_as_eliminator] lemma span_induction {p : M → Prop} (h : x ∈ span R s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (a:R) x, p x → p (a • x)) : p x :=
(@span_le _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hs h

section
variables (R M)

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi : galois_insertion (@span R M _ _ _) coe :=
{ choice := λ s _, span R s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }

end

@[simp] lemma span_empty : span R (∅ : set M) = ⊥ :=
(submodule.gi R M).gc.l_bot

@[simp] lemma span_univ : span R (univ : set M) = ⊤ :=
eq_top_iff.2 $ le_def.2 $ subset_span

lemma span_union (s t : set M) : span R (s ∪ t) = span R s ⊔ span R t :=
(submodule.gi R M).gc.l_sup

lemma span_Union {ι} (s : ι → set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
(submodule.gi R M).gc.l_supr

@[simp] theorem coe_supr_of_directed {ι} [hι : nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) :
  ((supr S : submodule R M) : set M) = ⋃ i, S i :=
begin
  refine subset.antisymm _ (Union_subset $ le_supr S),
  suffices : (span R (⋃ i, (S i : set M)) : set M) ⊆ ⋃ (i : ι), ↑(S i),
    by simpa only [span_Union, span_eq] using this,
  refine (λ x hx, span_induction hx (λ _, id) _ _ _);
    simp only [mem_Union, exists_imp_distrib],
  { exact hι.elim (λ i, ⟨i, (S i).zero_mem⟩) },
  { intros x y i hi j hj,
    rcases H i j with ⟨k, ik, jk⟩,
    exact ⟨k, add_mem _ (ik hi) (jk hj)⟩ },
  { exact λ a x i hi, ⟨i, smul_mem _ a hi⟩ },
end

lemma mem_sup_left {S T : submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mem_supr_of_mem {ι : Sort*} {b : M} {p : ι → submodule R M} (i : ι) (h : b ∈ p i) :
  b ∈ (⨆i, p i) :=
have p i ≤ (⨆i, p i) := le_supr p i,
@this b h

lemma mem_Sup_of_mem {S : set (submodule R M)} {s : submodule R M}
  (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

@[simp] theorem mem_supr_of_directed {ι} [nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) {x} :
  x ∈ supr S ↔ ∃ i, x ∈ S i :=
by { rw [← mem_coe, coe_supr_of_directed S H, mem_Union], refl }

theorem mem_Sup_of_directed {s : set (submodule R M)}
  {z} (hs : s.nonempty) (hdir : directed_on (≤) s) :
  z ∈ Sup s ↔ ∃ y ∈ s, z ∈ y :=
begin
  haveI : nonempty s := hs.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed _ hdir.directed_coe, set_coe.exists, subtype.coe_mk]
end

section

variables {p p'}

lemma mem_sup : x ∈ p ⊔ p' ↔ ∃ (y ∈ p) (z ∈ p'), y + z = x :=
⟨λ h, begin
  rw [← span_eq p, ← span_eq p', ← span_union] at h,
  apply span_induction h,
  { rintro y (h | h),
    { exact ⟨y, h, 0, by simp, by simp⟩ },
    { exact ⟨0, by simp, y, h, by simp⟩ } },
  { exact ⟨0, by simp, 0, by simp⟩ },
  { rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩,
    exact ⟨_, add_mem _ hy₁ hy₂, _, add_mem _ hz₁ hz₂, by simp [add_assoc]; cc⟩ },
  { rintro a _ ⟨y, hy, z, hz, rfl⟩,
    exact ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by simp [smul_add]⟩ }
end,
by rintro ⟨y, hy, z, hz, rfl⟩; exact add_mem _
  ((le_sup_left : p ≤ p ⊔ p') hy)
  ((le_sup_right : p' ≤ p ⊔ p') hz)⟩

lemma mem_sup' : x ∈ p ⊔ p' ↔ ∃ (y : p) (z : p'), (y:M) + z = x :=
mem_sup.trans $ by simp only [submodule.exists, coe_mk]

end

notation R`∙`:1000 x := span R (@singleton _ _ set.has_singleton x)

lemma mem_span_singleton_self (x : M) : x ∈ R ∙ x := subset_span rfl

lemma nontrivial_span_singleton {x : M} (h : x ≠ 0) : nontrivial (R ∙ x) :=
⟨begin
    use [0, x, submodule.mem_span_singleton_self x],
    intros H,
    rw [eq_comm, submodule.mk_eq_zero] at H,
    exact h H
end⟩

lemma mem_span_singleton {y : M} : x ∈ (R ∙ y) ↔ ∃ a:R, a • y = x :=
⟨λ h, begin
  apply span_induction h,
  { rintro y (rfl|⟨⟨⟩⟩), exact ⟨1, by simp⟩ },
  { exact ⟨0, by simp⟩ },
  { rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩,
    exact ⟨a + b, by simp [add_smul]⟩ },
  { rintro a _ ⟨b, rfl⟩,
    exact ⟨a * b, by simp [smul_smul]⟩ }
end,
by rintro ⟨a, y, rfl⟩; exact
  smul_mem _ _ (subset_span $ by simp)⟩

lemma le_span_singleton_iff {s : submodule R M} {v₀ : M} :
  s ≤ (R ∙ v₀) ↔ ∀ v ∈ s, ∃ r : R, r • v₀ = v :=
by simp_rw [le_def', mem_span_singleton]

@[simp] lemma span_zero_singleton : (R ∙ (0:M)) = ⊥ :=
by { ext, simp [mem_span_singleton, eq_comm] }

lemma span_singleton_eq_range (y : M) : ↑(R ∙ y) = range ((• y) : R → M) :=
set.ext $ λ x, mem_span_singleton

lemma span_singleton_smul_le (r : R) (x : M) : (R ∙ (r • x)) ≤ R ∙ x :=
begin
  rw [span_le, set.singleton_subset_iff, mem_coe],
  exact smul_mem _ _ (mem_span_singleton_self _)
end

lemma span_singleton_smul_eq {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {r : K} (x : E) (hr : r ≠ 0) : (K ∙ (r • x)) = K ∙ x :=
begin
  refine le_antisymm (span_singleton_smul_le r x) _,
  convert span_singleton_smul_le r⁻¹ (r • x),
  exact (inv_smul_smul' hr _).symm
end

lemma disjoint_span_singleton {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {s : submodule K E} {x : E} :
  disjoint s (K ∙ x) ↔ (x ∈ s → x = 0) :=
begin
  refine disjoint_def.trans ⟨λ H hx, H x hx $ subset_span $ mem_singleton x, _⟩,
  assume H y hy hyx,
  obtain ⟨c, hc⟩ := mem_span_singleton.1 hyx,
  subst y,
  classical, by_cases hc : c = 0, by simp only [hc, zero_smul],
  rw [s.smul_mem_iff hc] at hy,
  rw [H hy, smul_zero]
end

lemma disjoint_span_singleton' {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {p : submodule K E} {x : E} (x0 : x ≠ 0) :
  disjoint p (K ∙ x) ↔ x ∉ p :=
disjoint_span_singleton.trans ⟨λ h₁ h₂, x0 (h₁ h₂), λ h₁ h₂, (h₁ h₂).elim⟩

lemma mem_span_insert {y} : x ∈ span R (insert y s) ↔ ∃ (a:R) (z ∈ span R s), x = a • y + z :=
begin
  simp only [← union_singleton, span_union, mem_sup, mem_span_singleton, exists_prop,
    exists_exists_eq_and],
  rw [exists_comm],
  simp only [eq_comm, add_comm, exists_and_distrib_left]
end

lemma span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
span_eq_of_le _ (set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono $ subset_insert _ _)

lemma span_span : span R (span R s : set M) = span R s := span_eq _

lemma span_eq_bot : span R (s : set M) = ⊥ ↔ ∀ x ∈ s, (x:M) = 0 :=
eq_bot_iff.trans ⟨
  λ H x h, (mem_bot R).1 $ H $ subset_span h,
  λ H, span_le.2 (λ x h, (mem_bot R).2 $ H x h)⟩

@[simp] lemma span_singleton_eq_bot : (R ∙ x) = ⊥ ↔ x = 0 :=
span_eq_bot.trans $ by simp

@[simp] lemma span_zero : span R (0 : set M) = ⊥ := by rw [←singleton_zero, span_singleton_eq_bot]

@[simp] lemma span_image (f : M →ₗ[R] M₂) : span R (f '' s) = map f (span R s) :=
span_eq_of_le _ (image_subset _ subset_span) $ map_le_iff_le_comap.2 $
span_le.2 $ image_subset_iff.1 subset_span

lemma supr_eq_span {ι : Sort w} (p : ι → submodule R M) :
  (⨆ (i : ι), p i) = submodule.span R (⋃ (i : ι), ↑(p i)) :=
le_antisymm
  (supr_le $ assume i, subset.trans (assume m hm, set.mem_Union.mpr ⟨i, hm⟩) subset_span)
  (span_le.mpr $ Union_subset_iff.mpr $ assume i m hm, mem_supr_of_mem i hm)

lemma span_singleton_le_iff_mem (m : M) (p : submodule R M) : (R ∙ m) ≤ p ↔ m ∈ p :=
by rw [span_le, singleton_subset_iff, mem_coe]

lemma lt_add_iff_not_mem {I : submodule R M} {a : M} : I < I + (R ∙ a) ↔ a ∉ I :=
begin
  split,
  { intro h,
    by_contra akey,
    have h1 : I + (R ∙ a) ≤ I,
    { simp only [add_eq_sup, sup_le_iff],
      split,
      { exact le_refl I, },
      { exact (span_singleton_le_iff_mem a I).mpr akey, } },
    have h2 := gt_of_ge_of_gt h1 h,
    exact lt_irrefl I h2, },
  { intro h,
    apply lt_iff_le_and_exists.mpr, split,
    simp only [add_eq_sup, le_sup_left],
    use a,
    split, swap, { assumption, },
    { have : (R ∙ a) ≤ I + (R ∙ a) := le_sup_right,
      exact this (mem_span_singleton_self a), } },
end

lemma mem_supr {ι : Sort w} (p : ι → submodule R M) {m : M} :
  (m ∈ ⨆ i, p i) ↔ (∀ N, (∀ i, p i ≤ N) → m ∈ N) :=
begin
  rw [← span_singleton_le_iff_mem, le_supr_iff],
  simp only [span_singleton_le_iff_mem],
end

/-- The product of two submodules is a submodule. -/
def prod : submodule R (M × M₂) :=
{ carrier   := set.prod p q,
  smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩,
  .. p.to_add_submonoid.prod q.to_add_submonoid }

@[simp] lemma prod_coe :
  (prod p q : set (M × M₂)) = set.prod p q := rfl

@[simp] lemma mem_prod {p : submodule R M} {q : submodule R M₂} {x : M × M₂} :
  x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q := set.mem_prod

lemma span_prod_le (s : set M) (t : set M₂) :
  span R (set.prod s t) ≤ prod (span R s) (span R t) :=
span_le.2 $ set.prod_mono subset_span subset_span

@[simp] lemma prod_top : (prod ⊤ ⊤ : submodule R (M × M₂)) = ⊤ :=
by ext; simp

@[simp] lemma prod_bot : (prod ⊥ ⊥ : submodule R (M × M₂)) = ⊥ :=
by ext ⟨x, y⟩; simp [prod.zero_eq_mk]

lemma prod_mono {p p' : submodule R M} {q q' : submodule R M₂} :
  p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' := prod_mono

@[simp] lemma prod_inf_prod : prod p q ⊓ prod p' q' = prod (p ⊓ p') (q ⊓ q') :=
coe_injective set.prod_inter_prod

@[simp] lemma prod_sup_prod : prod p q ⊔ prod p' q' = prod (p ⊔ p') (q ⊔ q') :=
begin
  refine le_antisymm (sup_le
    (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right)) _,
  simp [le_def'], intros xx yy hxx hyy,
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩,
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩,
  refine mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩
end

end add_comm_monoid

variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
variables (p p' : submodule R M) (q q' : submodule R M₂)
variables {r : R} {x y : M}
open set

@[simp] lemma neg_coe : -(p : set M) = p := set.ext $ λ x, p.neg_mem_iff

@[simp] protected lemma map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
ext $ λ y, ⟨λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, neg_mem _ hx, f.map_neg x⟩,
  λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, neg_mem _ hx, ((-f).map_neg _).trans (neg_neg (f x))⟩⟩

@[simp] lemma span_neg (s : set M) : span R (-s) = span R s :=
calc span R (-s) = span R ((-linear_map.id : M →ₗ[R] M) '' s) : by simp
 ... = map (-linear_map.id) (span R s) : (map_span _ _).symm
... = span R s : by simp

lemma mem_span_insert' {y} {s : set M} : x ∈ span R (insert y s) ↔ ∃(a:R), x + a • y ∈ span R s :=
begin
  rw mem_span_insert, split,
  { rintro ⟨a, z, hz, rfl⟩, exact ⟨-a, by simp [hz, add_assoc]⟩ },
  { rintro ⟨a, h⟩, exact ⟨-a, _, h, by simp [add_comm, add_left_comm]⟩ }
end

-- TODO(Mario): Factor through add_subgroup
/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `y - x ∈ p`. -/
def quotient_rel : setoid M :=
⟨λ x y, x - y ∈ p, λ x, by simp,
 λ x y h, by simpa using neg_mem _ h,
 λ x y z h₁ h₂, by simpa [sub_eq_add_neg, add_left_comm, add_assoc] using add_mem _ h₁ h₂⟩

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
def quotient : Type* := quotient (quotient_rel p)

namespace quotient

/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : submodule R M} : M → quotient p := quotient.mk'

@[simp] theorem mk_eq_mk {p : submodule R M} (x : M) : (quotient.mk x : quotient p) = mk x := rfl
@[simp] theorem mk'_eq_mk {p : submodule R M} (x : M) : (quotient.mk' x : quotient p) = mk x := rfl
@[simp] theorem quot_mk_eq_mk {p : submodule R M} (x : M) : (quot.mk _ x : quotient p) = mk x := rfl

protected theorem eq {x y : M} : (mk x : quotient p) = mk y ↔ x - y ∈ p := quotient.eq'

instance : has_zero (quotient p) := ⟨mk 0⟩
instance : inhabited (quotient p) := ⟨0⟩

@[simp] theorem mk_zero : mk 0 = (0 : quotient p) := rfl

@[simp] theorem mk_eq_zero : (mk x : quotient p) = 0 ↔ x ∈ p :=
by simpa using (quotient.eq p : mk x = 0 ↔ _)

instance : has_add (quotient p) :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, mk (a + b)) $
  λ a₁ a₂ b₁ b₂ h₁ h₂, (quotient.eq p).2 $
    by simpa [sub_eq_add_neg, add_left_comm, add_comm] using add_mem p h₁ h₂⟩

@[simp] theorem mk_add : (mk (x + y) : quotient p) = mk x + mk y := rfl

instance : has_neg (quotient p) :=
⟨λ a, quotient.lift_on' a (λ a, mk (-a)) $
 λ a b h, (quotient.eq p).2 $ by simpa using neg_mem p h⟩

@[simp] theorem mk_neg : (mk (-x) : quotient p) = -mk x := rfl

instance : has_sub (quotient p) :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, mk (a - b)) $
  λ a₁ a₂ b₁ b₂ h₁ h₂, (quotient.eq p).2 $
  by simpa [sub_eq_add_neg, add_left_comm, add_comm] using add_mem p h₁ (neg_mem p h₂)⟩

@[simp] theorem mk_sub : (mk (x - y) : quotient p) = mk x - mk y := rfl

instance : add_comm_group (quotient p) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, sub := has_sub.sub, sub_eq_add_neg := _, ..};
   repeat {rintro ⟨⟩};
   simp [-mk_zero, ← mk_zero p, -mk_add, ← mk_add p, -mk_neg, ← mk_neg p, -mk_sub,
         ← mk_sub p, sub_eq_add_neg];
   cc

instance : has_scalar R (quotient p) :=
⟨λ a x, quotient.lift_on' x (λ x, mk (a • x)) $
 λ x y h, (quotient.eq p).2 $ by simpa [smul_sub] using smul_mem p a h⟩

@[simp] theorem mk_smul : (mk (r • x) : quotient p) = r • mk x := rfl

instance : semimodule R (quotient p) :=
semimodule.of_core $ by refine {smul := (•), ..};
  repeat {rintro ⟨⟩ <|> intro}; simp [smul_add, add_smul, smul_smul,
    -mk_add, (mk_add p).symm, -mk_smul, (mk_smul p).symm]

lemma mk_surjective : function.surjective (@mk _ _ _ _ _ p) :=
by { rintros ⟨x⟩, exact ⟨x, rfl⟩ }

lemma nontrivial_of_lt_top (h : p < ⊤) : nontrivial (p.quotient) :=
begin
  obtain ⟨x, _, not_mem_s⟩ := exists_of_lt h,
  refine ⟨⟨mk x, 0, _⟩⟩,
  simpa using not_mem_s
end

end quotient

lemma quot_hom_ext ⦃f g : quotient p →ₗ[R] M₂⦄ (h : ∀ x, f (quotient.mk x) = g (quotient.mk x)) :
  f = g :=
linear_map.ext $ λ x, quotient.induction_on' x h

end submodule

namespace submodule
variables [field K]
variables [add_comm_group V] [vector_space K V]
variables [add_comm_group V₂] [vector_space K V₂]

lemma comap_smul (f : V →ₗ[K] V₂) (p : submodule K V₂) (a : K) (h : a ≠ 0) :
  p.comap (a • f) = p.comap f :=
by ext b; simp only [submodule.mem_comap, p.smul_mem_iff h, linear_map.smul_apply]

lemma map_smul (f : V →ₗ[K] V₂) (p : submodule K V) (a : K) (h : a ≠ 0) :
  p.map (a • f) = p.map f :=
le_antisymm
  begin rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap], exact le_refl _ end
  begin rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap], exact le_refl _ end


lemma comap_smul' (f : V →ₗ[K] V₂) (p : submodule K V₂) (a : K) :
  p.comap (a • f) = (⨅ h : a ≠ 0, p.comap f) :=
by classical; by_cases a = 0; simp [h, comap_smul]

lemma map_smul' (f : V →ₗ[K] V₂) (p : submodule K V) (a : K) :
  p.map (a • f) = (⨆ h : a ≠ 0, p.map f) :=
by classical; by_cases a = 0; simp [h, map_smul]

end submodule

/-! ### Properties of linear maps -/
namespace linear_map

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
include R
open submodule

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

See also `linear_map.eq_on_span'` for a version using `set.eq_on`. -/
lemma eq_on_span {s : set M} {f g : M →ₗ[R] M₂} (H : set.eq_on f g s) ⦃x⦄ (h : x ∈ span R s) :
  f x = g x :=
by apply span_induction h H; simp {contextual := tt}

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

This version uses `set.eq_on`, and the hidden argument will expand to `h : x ∈ (span R s : set M)`.
See `linear_map.eq_on_span` for a version that takes `h : x ∈ span R s` as an argument. -/
lemma eq_on_span' {s : set M} {f g : M →ₗ[R] M₂} (H : set.eq_on f g s) :
  set.eq_on f g (span R s : set M) :=
eq_on_span H

/-- If `s` generates the whole semimodule and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
lemma ext_on {s : set M} {f g : M →ₗ[R] M₂} (hv : span R s = ⊤) (h : set.eq_on f g s) :
  f = g :=
linear_map.ext (λ x, eq_on_span h (eq_top_iff'.1 hv _))

/-- If the range of `v : ι → M` generates the whole semimodule and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
lemma ext_on_range {v : ι → M} {f g : M →ₗ[R] M₂} (hv : span R (set.range v) = ⊤)
  (h : ∀i, f (v i) = g (v i)) : f = g :=
ext_on hv (set.forall_range_iff.2 h)

@[simp] lemma finsupp_sum {γ} [has_zero γ]
  (f : M →ₗ[R] M₂) {t : ι →₀ γ} {g : ι → γ → M} :
  f (t.sum g) = t.sum (λi d, f (g i d)) := f.map_sum

theorem map_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (h p') :
  submodule.map (cod_restrict p f h) p' = comap p.subtype (p'.map f) :=
submodule.ext $ λ ⟨x, hx⟩, by simp [subtype.ext_iff_val]

theorem comap_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (hf p') :
  submodule.comap (cod_restrict p f hf) p' = submodule.comap f (map p.subtype p') :=
submodule.ext $ λ x, ⟨λ h, ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`. -/
def range (f : M →ₗ[R] M₂) : submodule R M₂ := map f ⊤

theorem range_coe (f : M →ₗ[R] M₂) : (range f : set M₂) = set.range f := set.image_univ

@[simp] theorem mem_range {f : M →ₗ[R] M₂} : ∀ {x}, x ∈ range f ↔ ∃ y, f y = x :=
set.ext_iff.1 (range_coe f)

theorem mem_range_self (f : M →ₗ[R] M₂) (x : M) : f x ∈ f.range := mem_range.2 ⟨x, rfl⟩

@[simp] theorem range_id : range (linear_map.id : M →ₗ[R] M) = ⊤ := map_id _

theorem range_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : range (g.comp f) = map g (range f) :=
map_comp _ _ _

theorem range_comp_le_range (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : range (g.comp f) ≤ range g :=
by rw range_comp; exact map_mono le_top

theorem range_eq_top {f : M →ₗ[R] M₂} : range f = ⊤ ↔ surjective f :=
by rw [submodule.ext'_iff, range_coe, top_coe, set.range_iff_surjective]

lemma range_le_iff_comap {f : M →ₗ[R] M₂} {p : submodule R M₂} : range f ≤ p ↔ comap f p = ⊤ :=
by rw [range, map_le_iff_le_comap, eq_top_iff]

lemma map_le_range {f : M →ₗ[R] M₂} {p : submodule R M} : map f p ≤ range f :=
map_mono le_top

lemma range_coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (f.coprod g).range = f.range ⊔ g.range :=
submodule.ext $ λ x, by simp [mem_sup]

lemma is_compl_range_inl_inr : is_compl (inl R M M₂).range (inr R M M₂).range :=
begin
  split,
  { rintros ⟨_, _⟩ ⟨⟨x, -, hx⟩, ⟨y, -, hy⟩⟩,
    simp only [prod.ext_iff, inl_apply, inr_apply, mem_bot] at hx hy ⊢,
    exact ⟨hy.1.symm, hx.2.symm⟩ },
  { rintros ⟨x, y⟩ -,
    simp only [mem_sup, mem_range, exists_prop],
    refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, _⟩,
    simp }
end

lemma sup_range_inl_inr : (inl R M M₂).range ⊔ (inr R M M₂).range = ⊤ :=
is_compl_range_inl_inr.sup_eq_top

/-- Restrict the codomain of a linear map `f` to `f.range`. -/
@[reducible] def range_restrict (f : M →ₗ[R] M₂) : M →ₗ[R] f.range :=
f.cod_restrict f.range f.mem_range_self

section
variables (R) (M)

/-- Given an element `x` of a module `M` over `R`, the natural map from
    `R` to scalar multiples of `x`.-/
def to_span_singleton (x : M) : R →ₗ[R] M := linear_map.id.smul_right x

/-- The range of `to_span_singleton x` is the span of `x`.-/
lemma span_singleton_eq_range (x : M) : (R ∙ x) = (to_span_singleton R M x).range :=
submodule.ext $ λ y, by {refine iff.trans _ mem_range.symm, exact mem_span_singleton }

lemma to_span_singleton_one (x : M) : to_span_singleton R M x 1 = x := one_smul _ _

end

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : M →ₗ[R] M₂) : submodule R M := comap f ⊥

@[simp] theorem mem_ker {f : M →ₗ[R] M₂} {y} : y ∈ ker f ↔ f y = 0 := mem_bot R

@[simp] theorem ker_id : ker (linear_map.id : M →ₗ[R] M) = ⊥ := rfl

@[simp] theorem map_coe_ker (f : M →ₗ[R] M₂) (x : ker f) : f x = 0 := mem_ker.1 x.2

lemma comp_ker_subtype (f : M →ₗ[R] M₂) : f.comp f.ker.subtype = 0 :=
linear_map.ext $ λ x, suffices f x = 0, by simp [this], mem_ker.1 x.2

theorem ker_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : ker (g.comp f) = comap f (ker g) := rfl

theorem ker_le_ker_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : ker f ≤ ker (g.comp f) :=
by rw ker_comp; exact comap_mono bot_le

theorem disjoint_ker {f : M →ₗ[R] M₂} {p : submodule R M} :
  disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
by simp [disjoint_def]

lemma disjoint_inl_inr : disjoint (inl R M M₂).range (inr R M M₂).range :=
by simp [disjoint_def, @eq_comm M 0, @eq_comm M₂ 0] {contextual := tt}; intros; refl

theorem ker_eq_bot' {f : M →ₗ[R] M₂} :
  ker f = ⊥ ↔ (∀ m, f m = 0 → m = 0) :=
by simpa [disjoint] using @disjoint_ker _ _ _ _ _ _ _ _ f ⊤

lemma le_ker_iff_map {f : M →ₗ[R] M₂} {p : submodule R M} : p ≤ ker f ↔ map f p = ⊥ :=
by rw [ker, eq_bot_iff, map_le_iff_le_comap]

lemma ker_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (hf) :
  ker (cod_restrict p f hf) = ker f :=
by rw [ker, comap_cod_restrict, map_bot]; refl

lemma range_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (hf) :
  range (cod_restrict p f hf) = comap p.subtype f.range :=
map_cod_restrict _ _ _ _

lemma ker_restrict {p : submodule R M} {f : M →ₗ[R] M} (hf : ∀ x : M, x ∈ p → f x ∈ p) :
  ker (f.restrict hf) = (f.dom_restrict p).ker :=
by rw [restrict_eq_cod_restrict_dom_restrict, ker_cod_restrict]

lemma map_comap_eq (f : M →ₗ[R] M₂) (q : submodule R M₂) :
  map f (comap f q) = range f ⊓ q :=
le_antisymm (le_inf (map_mono le_top) (map_comap_le _ _)) $
by rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

lemma map_comap_eq_self {f : M →ₗ[R] M₂} {q : submodule R M₂} (h : q ≤ range f) :
  map f (comap f q) = q :=
by rwa [map_comap_eq, inf_eq_right]

@[simp] theorem ker_zero : ker (0 : M →ₗ[R] M₂) = ⊤ :=
eq_top_iff'.2 $ λ x, by simp

@[simp] theorem range_zero : range (0 : M →ₗ[R] M₂) = ⊥ :=
submodule.map_zero _

theorem ker_eq_top {f : M →ₗ[R] M₂} : ker f = ⊤ ↔ f = 0 :=
⟨λ h, ext $ λ x, mem_ker.1 $ h.symm ▸ trivial, λ h, h.symm ▸ ker_zero⟩

lemma range_le_bot_iff (f : M →ₗ[R] M₂) : range f ≤ ⊥ ↔ f = 0 :=
by rw [range_le_iff_comap]; exact ker_eq_top

theorem range_eq_bot {f : M →ₗ[R] M₂} : range f = ⊥ ↔ f = 0 :=
by rw [← range_le_bot_iff, le_bot_iff]

lemma range_le_ker_iff {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} : range f ≤ ker g ↔ g.comp f = 0 :=
⟨λ h, ker_eq_top.1 $ eq_top_iff'.2 $ λ x, h $ mem_map_of_mem trivial,
 λ h x hx, mem_ker.2 $ exists.elim hx $ λ y ⟨_, hy⟩, by rw [←hy, ←comp_apply, h, zero_apply]⟩

theorem comap_le_comap_iff {f : M →ₗ[R] M₂} (hf : range f = ⊤) {p p'} :
  comap f p ≤ comap f p' ↔ p ≤ p' :=
⟨λ H x hx, by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩

theorem comap_injective {f : M →ₗ[R] M₂} (hf : range f = ⊤) : injective (comap f) :=
λ p p' h, le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h))
  ((comap_le_comap_iff hf).1 (ge_of_eq h))

theorem map_coprod_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃)
  (p : submodule R M) (q : submodule R M₂) :
  map (coprod f g) (p.prod q) = map f p ⊔ map g q :=
begin
  refine le_antisymm _ (sup_le (map_le_iff_le_comap.2 _) (map_le_iff_le_comap.2 _)),
  { rw le_def', rintro _ ⟨x, ⟨h₁, h₂⟩, rfl⟩,
    exact mem_sup.2 ⟨_, ⟨_, h₁, rfl⟩, _, ⟨_, h₂, rfl⟩, rfl⟩ },
  { exact λ x hx, ⟨(x, 0), by simp [hx]⟩ },
  { exact λ x hx, ⟨(0, x), by simp [hx]⟩ }
end

theorem comap_prod_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃)
  (p : submodule R M₂) (q : submodule R M₃) :
  comap (prod f g) (p.prod q) = comap f p ⊓ comap g q :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_inf_comap (p : submodule R M) (q : submodule R M₂) :
  p.prod q = p.comap (linear_map.fst R M M₂) ⊓ q.comap (linear_map.snd R M M₂) :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_sup_map (p : submodule R M) (q : submodule R M₂) :
  p.prod q = p.map (linear_map.inl R M M₂) ⊔ q.map (linear_map.inr R M M₂) :=
by rw [← map_coprod_prod, coprod_inl_inr, map_id]

lemma span_inl_union_inr {s : set M} {t : set M₂} :
  span R (inl R M  M₂ '' s ∪ inr R M M₂ '' t) = (span R s).prod (span R t) :=
by rw [span_union, prod_eq_sup_map, ← span_image, ← span_image]; refl

@[simp] lemma ker_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  ker (prod f g) = ker f ⊓ ker g :=
by rw [ker, ← prod_bot, comap_prod_prod]; refl

lemma range_prod_le (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  range (prod f g) ≤ (range f).prod (range g) :=
begin
  simp only [le_def', prod_apply, mem_range, mem_coe, mem_prod, exists_imp_distrib],
  rintro _ x rfl,
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩
end

theorem ker_eq_bot_of_injective {f : M →ₗ[R] M₂} (hf : injective f) : ker f = ⊥ :=
begin
  have : disjoint ⊤ f.ker, by { rw [disjoint_ker, ← map_zero f], exact λ x hx H, hf H },
  simpa [disjoint]
end

end add_comm_monoid

section add_comm_group

variables [semiring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
include R
open submodule

lemma comap_map_eq (f : M →ₗ[R] M₂) (p : submodule R M) :
  comap f (map f p) = p ⊔ ker f :=
begin
  refine le_antisymm _ (sup_le (le_comap_map _ _) (comap_mono bot_le)),
  rintro x ⟨y, hy, e⟩,
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩
end

lemma comap_map_eq_self {f : M →ₗ[R] M₂} {p : submodule R M} (h : ker f ≤ p) :
  comap f (map f p) = p :=
by rw [comap_map_eq, sup_of_le_left h]

theorem map_le_map_iff (f : M →ₗ[R] M₂) {p p'} : map f p ≤ map f p' ↔ p ≤ p' ⊔ ker f :=
by rw [map_le_iff_le_comap, comap_map_eq]

theorem map_le_map_iff' {f : M →ₗ[R] M₂} (hf : ker f = ⊥) {p p'} : map f p ≤ map f p' ↔ p ≤ p' :=
by rw [map_le_map_iff, hf, sup_bot_eq]

theorem map_injective {f : M →ₗ[R] M₂} (hf : ker f = ⊥) : injective (map f) :=
λ p p' h, le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))

theorem map_eq_top_iff {f : M →ₗ[R] M₂} (hf : range f = ⊤) {p : submodule R M} :
  p.map f = ⊤ ↔ p ⊔ f.ker = ⊤ :=
by simp_rw [← top_le_iff, ← hf, range, map_le_map_iff]

end add_comm_group

section ring

variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
variables {f : M →ₗ[R] M₂}
include R
open submodule

theorem sub_mem_ker_iff {x y} : x - y ∈ f.ker ↔ f x = f y :=
by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker' {p : submodule R M} :
  disjoint p (ker f) ↔ ∀ x y ∈ p, f x = f y → x = y :=
disjoint_ker.trans
⟨λ H x y hx hy h, eq_of_sub_eq_zero $ H _ (sub_mem _ hx hy) (by simp [h]),
 λ H x h₁ h₂, H x 0 h₁ (zero_mem _) (by simpa using h₂)⟩

theorem inj_of_disjoint_ker {p : submodule R M}
  {s : set M} (h : s ⊆ p) (hd : disjoint p (ker f)) :
  ∀ x y ∈ s, f x = f y → x = y :=
λ x y hx hy, disjoint_ker'.1 hd _ _ (h hx) (h hy)

theorem ker_eq_bot : ker f = ⊥ ↔ injective f :=
by simpa [disjoint] using @disjoint_ker' _ _ _ _ _ _ _ _ f ⊤

lemma ker_le_iff {p : submodule R M} : ker f ≤ p ↔ ∃ (y ∈ range f), f ⁻¹' {y} ⊆ p :=
begin
  split,
  { intros h, use 0, rw [← mem_coe, f.range_coe], exact ⟨⟨0, map_zero f⟩, h⟩, },
  { rintros ⟨y, h₁, h₂⟩,
    rw le_def, intros z hz, simp only [mem_ker, mem_coe] at hz,
    rw [← mem_coe, f.range_coe, set.mem_range] at h₁, obtain ⟨x, hx⟩ := h₁,
    have hx' : x ∈ p, { exact h₂ hx, },
    have hxz : z + x ∈ p, { apply h₂, simp [hx, hz], },
    suffices : z + x - x ∈ p, { simpa only [this, add_sub_cancel],  },
    exact p.sub_mem hxz hx', },
end

/-- If the union of the kernels `ker f` and `ker g` spans the domain, then the range of
`prod f g` is equal to the product of `range f` and `range g`. -/
lemma range_prod_eq {g : M →ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤) :
  range (prod f g) = (range f).prod (range g) :=
begin
  refine le_antisymm (f.range_prod_le g) _,
  simp only [le_def', prod_apply, mem_range, mem_coe, mem_prod, exists_imp_distrib, and_imp,
    prod.forall],
  rintros _ _ x rfl y rfl,
  simp only [prod.mk.inj_iff, ← sub_mem_ker_iff],
  have : y - x ∈ ker f ⊔ ker g, { simp only [h, mem_top] },
  rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩,
  refine ⟨x' + x, _, _⟩,
  { rwa add_sub_cancel },
  { rwa [← eq_sub_iff_add_eq.1 H, add_sub_add_right_eq_sub, ← neg_mem_iff, neg_sub,
      add_sub_cancel'] }
end

end ring

section field

variables [field K]
variables [add_comm_group V] [vector_space K V]
variables [add_comm_group V₂] [vector_space K V₂]

lemma ker_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
submodule.comap_smul f _ a h

lemma ker_smul' (f : V →ₗ[K] V₂) (a : K) : ker (a • f) = ⨅(h : a ≠ 0), ker f :=
submodule.comap_smul' f _ a

lemma range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f :=
submodule.map_smul f _ a h

lemma range_smul' (f : V →ₗ[K] V₂) (a : K) : range (a • f) = ⨆(h : a ≠ 0), range f :=
submodule.map_smul' f _ a

end field

end linear_map

lemma submodule.sup_eq_range [semiring R] [add_comm_monoid M] [semimodule R M]
  (p q : submodule R M) : p ⊔ q = (p.subtype.coprod q.subtype).range :=
submodule.ext $ λ x, by simp [submodule.mem_sup, submodule.exists]

namespace is_linear_map

lemma is_linear_map_add [semiring R] [add_comm_monoid M] [semimodule R M] :
  is_linear_map R (λ (x : M × M), x.1 + x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp, cc },
  { intros x y,
    simp [smul_add] }
end

lemma is_linear_map_sub {R M : Type*} [semiring R] [add_comm_group M] [semimodule R M]:
  is_linear_map R (λ (x : M × M), x.1 - x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp [add_comm, add_left_comm, sub_eq_add_neg] },
  { intros x y,
    simp [smul_sub] }
end

end is_linear_map

namespace submodule

section add_comm_monoid

variables {T : semiring R} [add_comm_monoid M] [add_comm_monoid M₂]
variables [semimodule R M] [semimodule R M₂]
variables (p p' : submodule R M) (q : submodule R M₂)
include T
open linear_map

@[simp] theorem map_top (f : M →ₗ[R] M₂) : map f ⊤ = range f := rfl

@[simp] theorem comap_bot (f : M →ₗ[R] M₂) : comap f ⊥ = ker f := rfl

@[simp] theorem ker_subtype : p.subtype.ker = ⊥ :=
ker_eq_bot_of_injective $ λ x y, subtype.ext_val

@[simp] theorem range_subtype : p.subtype.range = p :=
by simpa using map_comap_subtype p ⊤

lemma map_subtype_le (p' : submodule R p) : map p.subtype p' ≤ p :=
by simpa using (map_mono le_top : map p.subtype p' ≤ p.subtype.range)

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p `. -/
@[simp] lemma map_subtype_top : map p.subtype (⊤ : submodule R p) = p :=
by simp

@[simp] lemma comap_subtype_eq_top {p p' : submodule R M} :
  comap p.subtype p' = ⊤ ↔ p ≤ p' :=
eq_top_iff.trans $ map_le_iff_le_comap.symm.trans $ by rw [map_subtype_top]

@[simp] lemma comap_subtype_self : comap p.subtype p = ⊤ :=
comap_subtype_eq_top.2 (le_refl _)

@[simp] theorem ker_of_le (p p' : submodule R M) (h : p ≤ p') : (of_le h).ker = ⊥ :=
by rw [of_le, ker_cod_restrict, ker_subtype]

lemma range_of_le (p q : submodule R M) (h : p ≤ q) : (of_le h).range = comap q.subtype p :=
by rw [← map_top, of_le, linear_map.map_cod_restrict, map_top, range_subtype]

@[simp] theorem map_inl : p.map (inl R M M₂) = prod p ⊥ :=
by { ext ⟨x, y⟩, simp only [and.left_comm, eq_comm, mem_map, prod.mk.inj_iff, inl_apply, mem_bot,
  exists_eq_left', mem_prod] }

@[simp] theorem map_inr : q.map (inr R M M₂) = prod ⊥ q :=
by ext ⟨x, y⟩; simp [and.left_comm, eq_comm]

@[simp] theorem comap_fst : p.comap (fst R M M₂) = prod p ⊤ :=
by ext ⟨x, y⟩; simp

@[simp] theorem comap_snd : q.comap (snd R M M₂) = prod ⊤ q :=
by ext ⟨x, y⟩; simp

@[simp] theorem prod_comap_inl : (prod p q).comap (inl R M M₂) = p := by ext; simp

@[simp] theorem prod_comap_inr : (prod p q).comap (inr R M M₂) = q := by ext; simp

@[simp] theorem prod_map_fst : (prod p q).map (fst R M M₂) = p :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

@[simp] theorem prod_map_snd : (prod p q).map (snd R M M₂) = q :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

@[simp] theorem ker_inl : (inl R M M₂).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inl]

@[simp] theorem ker_inr : (inr R M M₂).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inr]

@[simp] theorem range_fst : (fst R M M₂).range = ⊤ :=
by rw [range, ← prod_top, prod_map_fst]

@[simp] theorem range_snd : (snd R M M₂).range = ⊤ :=
by rw [range, ← prod_top, prod_map_snd]

end add_comm_monoid

section ring

variables {T : ring R} [add_comm_group M] [add_comm_group M₂] [semimodule R M] [semimodule R M₂]
variables (p p' : submodule R M) (q : submodule R M₂)
include T
open linear_map

lemma disjoint_iff_comap_eq_bot {p q : submodule R M} :
  disjoint p q ↔ comap p.subtype q = ⊥ :=
by rw [eq_bot_iff, ← map_le_map_iff' p.ker_subtype, map_bot, map_comap_subtype, disjoint]

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N` -/
def map_subtype.rel_iso :
  submodule R p ≃o {p' : submodule R M // p' ≤ p} :=
{ to_fun    := λ p', ⟨map p.subtype p', map_subtype_le p _⟩,
  inv_fun   := λ q, comap p.subtype q,
  left_inv  := λ p', comap_map_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.ext_val $ by simp [map_comap_subtype p, inf_of_le_right hq],
  map_rel_iff'      := λ p₁ p₂, map_le_map_iff' (ker_subtype p) }

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def map_subtype.order_embedding :
  submodule R p ↪o submodule R M :=
(rel_iso.to_rel_embedding $ map_subtype.rel_iso p).trans (subtype.rel_embedding _ _)

@[simp] lemma map_subtype_embedding_eq (p' : submodule R p) :
  map_subtype.order_embedding p p' = map p.subtype p' := rfl


/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkq : M →ₗ[R] p.quotient := ⟨quotient.mk, by simp, by simp⟩

@[simp] theorem mkq_apply (x : M) : p.mkq x = quotient.mk x := rfl

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftq (f : M →ₗ[R] M₂) (h : p ≤ f.ker) : p.quotient →ₗ[R] M₂ :=
⟨λ x, _root_.quotient.lift_on' x f $
   λ a b (ab : a - b ∈ p), eq_of_sub_eq_zero $ by simpa using h ab,
 by rintro ⟨x⟩ ⟨y⟩; exact f.map_add x y,
 by rintro a ⟨x⟩; exact f.map_smul a x⟩

@[simp] theorem liftq_apply (f : M →ₗ[R] M₂) {h} (x : M) :
  p.liftq f h (quotient.mk x) = f x := rfl

@[simp] theorem liftq_mkq (f : M →ₗ[R] M₂) (h) : (p.liftq f h).comp p.mkq = f :=
by ext; refl

@[simp] theorem range_mkq : p.mkq.range = ⊤ :=
eq_top_iff'.2 $ by rintro ⟨x⟩; exact ⟨x, trivial, rfl⟩

@[simp] theorem ker_mkq : p.mkq.ker = p :=
by ext; simp

lemma le_comap_mkq (p' : submodule R p.quotient) : p ≤ comap p.mkq p' :=
by simpa using (comap_mono bot_le : p.mkq.ker ≤ comap p.mkq p')

@[simp] theorem mkq_map_self : map p.mkq p = ⊥ :=
by rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkq]; exact le_refl _

@[simp] theorem comap_map_mkq : comap p.mkq (map p.mkq p') = p ⊔ p' :=
by simp [comap_map_eq, sup_comm]

@[simp] theorem map_mkq_eq_top : map p.mkq p' = ⊤ ↔ p ⊔ p' = ⊤ :=
by simp only [map_eq_top_iff p.range_mkq, sup_comm, ker_mkq]

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapq (f : M →ₗ[R] M₂) (h : p ≤ comap f q) : p.quotient →ₗ[R] q.quotient :=
p.liftq (q.mkq.comp f) $ by simpa [ker_comp] using h

@[simp] theorem mapq_apply (f : M →ₗ[R] M₂) {h} (x : M) :
  mapq p q f h (quotient.mk x) = quotient.mk (f x) := rfl

theorem mapq_mkq (f : M →ₗ[R] M₂) {h} : (mapq p q f h).comp p.mkq = q.mkq.comp f :=
by ext x; refl

theorem comap_liftq (f : M →ₗ[R] M₂) (h) :
  q.comap (p.liftq f h) = (q.comap f).map (mkq p) :=
le_antisymm
  (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
  (by rw [map_le_iff_le_comap, ← comap_comp, liftq_mkq]; exact le_refl _)

theorem map_liftq (f : M →ₗ[R] M₂) (h) (q : submodule R (quotient p)) :
  q.map (p.liftq f h) = (q.comap p.mkq).map f :=
le_antisymm
  (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
  (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨quotient.mk x, hxq, rfl⟩)

theorem ker_liftq (f : M →ₗ[R] M₂) (h) :
  ker (p.liftq f h) = (ker f).map (mkq p) := comap_liftq _ _ _ _

theorem range_liftq (f : M →ₗ[R] M₂) (h) :
  range (p.liftq f h) = range f := map_liftq _ _ _ _

theorem ker_liftq_eq_bot (f : M →ₗ[R] M₂) (h) (h' : ker f ≤ p) : ker (p.liftq f h) = ⊥ :=
by rw [ker_liftq, le_antisymm h h', mkq_map_self]

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def comap_mkq.rel_iso :
  submodule R p.quotient ≃o {p' : submodule R M // p ≤ p'} :=
{ to_fun    := λ p', ⟨comap p.mkq p', le_comap_mkq p _⟩,
  inv_fun   := λ q, map p.mkq q,
  left_inv  := λ p', map_comap_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.ext_val $ by simpa [comap_map_mkq p],
  map_rel_iff'      := λ p₁ p₂, comap_le_comap_iff $ range_mkq _ }

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comap_mkq.order_embedding :
  submodule R p.quotient ↪o submodule R M :=
(rel_iso.to_rel_embedding $ comap_mkq.rel_iso p).trans (subtype.rel_embedding _ _)

@[simp] lemma comap_mkq_embedding_eq (p' : submodule R p.quotient) :
  comap_mkq.order_embedding p p' = comap p.mkq p' := rfl

lemma span_preimage_eq {f : M →ₗ[R] M₂} {s : set M₂} (h₀ : s.nonempty) (h₁ : s ⊆ range f) :
  span R (f ⁻¹' s) = (span R s).comap f :=
begin
  suffices : (span R s).comap f ≤ span R (f ⁻¹' s),
  { exact le_antisymm (span_preimage_le f s) this, },
  have hk : ker f ≤ span R (f ⁻¹' s),
  { let y := classical.some h₀, have hy : y ∈ s, { exact classical.some_spec h₀, },
    rw ker_le_iff, use [y, h₁ hy], rw ← set.singleton_subset_iff at hy,
    exact set.subset.trans subset_span (span_mono (set.preimage_mono hy)), },
  rw ← left_eq_sup at hk, rw f.range_coe at h₁,
  rw [hk, ← map_le_map_iff, map_span, map_comap_eq, set.image_preimage_eq_of_subset h₁],
  exact inf_le_right,
end

end ring

end submodule

namespace linear_map
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]

lemma range_mkq_comp (f : M →ₗ[R] M₂) : f.range.mkq.comp f = 0 :=
linear_map.ext $ λ x, by simp

lemma ker_le_range_iff {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} :
  g.ker ≤ f.range ↔ f.range.mkq.comp g.ker.subtype = 0 :=
by rw [←range_le_ker_iff, submodule.ker_mkq, submodule.range_subtype]

/-- A monomorphism is injective. -/
lemma ker_eq_bot_of_cancel {f : M →ₗ[R] M₂}
  (h : ∀ (u v : f.ker →ₗ[R] M), f.comp u = f.comp v → u = v) : f.ker = ⊥ :=
begin
  have h₁ : f.comp (0 : f.ker →ₗ[R] M) = 0 := comp_zero _,
  rw [←submodule.range_subtype f.ker, ←h 0 f.ker.subtype (eq.trans h₁ (comp_ker_subtype f).symm)],
  exact range_zero
end

/-- An epimorphism is surjective. -/
lemma range_eq_top_of_cancel {f : M →ₗ[R] M₂}
  (h : ∀ (u v : M₂ →ₗ[R] f.range.quotient), u.comp f = v.comp f → u = v) : f.range = ⊤ :=
begin
  have h₁ : (0 : M₂ →ₗ[R] f.range.quotient).comp f = 0 := zero_comp _,
  rw [←submodule.ker_mkq f.range, ←h 0 f.range.mkq (eq.trans h₁ (range_mkq_comp _).symm)],
  exact ker_zero
end

end linear_map

@[simp] lemma linear_map.range_range_restrict [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
  [semimodule R M] [semimodule R M₂] (f : M →ₗ[R] M₂) :
  f.range_restrict.range = ⊤ :=
by simp [f.range_cod_restrict _]

/-! ### Linear equivalences -/
namespace linear_equiv

section add_comm_monoid
variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
[add_comm_monoid M₃] [add_comm_monoid M₄]

section
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables (e e' : M ≃ₗ[R] M₂)

lemma map_eq_comap {p : submodule R M} : (p.map e : submodule R M₂) = p.comap e.symm :=
submodule.coe_injective $ by simp [e.image_eq_preimage]

/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
of the domain onto the image of the submodule. -/
def of_submodule (p : submodule R M) : p ≃ₗ[R] ↥(p.map ↑e : submodule R M₂) :=
{ inv_fun   := λ y, ⟨e.symm y, by {
    rcases y with ⟨y', hy⟩, rw submodule.mem_map at hy, rcases hy with ⟨x, hx, hxy⟩, subst hxy,
    simp only [symm_apply_apply, submodule.coe_mk, coe_coe, hx], }⟩,
  left_inv  := λ x, by simp,
  right_inv := λ y, by { apply set_coe.ext, simp, },
  ..((e : M →ₗ[R] M₂).dom_restrict p).cod_restrict (p.map ↑e) (λ x, ⟨x, by simp⟩) }

@[simp] lemma of_submodule_apply (p : submodule R M) (x : p) :
  ↑(e.of_submodule p x) = e x := rfl

@[simp] lemma of_submodule_symm_apply (p : submodule R M) (x : (p.map ↑e : submodule R M₂)) :
  ↑((e.of_submodule p).symm x) = e.symm x := rfl

end

section prod

variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄}
variables (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Product of linear equivalences; the maps come from `equiv.prod_congr`. -/
protected def prod :
  (M × M₃) ≃ₗ[R] (M₂ × M₄) :=
{ map_add'  := λ x y, prod.ext (e₁.map_add _ _) (e₂.map_add _ _),
  map_smul' := λ c x, prod.ext (e₁.map_smul c _) (e₂.map_smul c _),
  .. equiv.prod_congr e₁.to_equiv e₂.to_equiv }

lemma prod_symm : (e₁.prod e₂).symm = e₁.symm.prod e₂.symm := rfl

@[simp] lemma prod_apply (p) :
  e₁.prod e₂ p = (e₁ p.1, e₂ p.2) := rfl

@[simp, norm_cast] lemma coe_prod :
  (e₁.prod e₂ : (M × M₃) →ₗ[R] (M₂ × M₄)) = (e₁ : M →ₗ[R] M₂).prod_map (e₂ : M₃ →ₗ[R] M₄) := rfl

end prod

section uncurry

variables (V V₂ R)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `tensor_product.curry`. -/
protected def uncurry :
  (V → V₂ → R) ≃ₗ[R] (V × V₂ → R) :=
{ map_add'  := λ _ _, by { ext ⟨⟩, refl },
  map_smul' := λ _ _, by { ext ⟨⟩, refl },
  .. equiv.arrow_arrow_equiv_prod_arrow _ _ _}

@[simp] lemma coe_uncurry : ⇑(linear_equiv.uncurry R V V₂) = uncurry := rfl

@[simp] lemma coe_uncurry_symm : ⇑(linear_equiv.uncurry R V V₂).symm = curry := rfl

end uncurry

section
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M) (e : M ≃ₗ[R] M₂)

variables (p q : submodule R M)

/-- Linear equivalence between two equal submodules. -/
def of_eq (h : p = q) : p ≃ₗ[R] q :=
{ map_smul' := λ _ _, rfl, map_add' := λ _ _, rfl, .. equiv.set.of_eq (congr_arg _ h) }

variables {p q}

@[simp] lemma coe_of_eq_apply (h : p = q) (x : p) : (of_eq p q h x : M) = x := rfl

@[simp] lemma of_eq_symm (h : p = q) : (of_eq p q h).symm = of_eq q p h.symm := rfl

/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
def of_submodules (p : submodule R M) (q : submodule R M₂) (h : p.map ↑e = q) : p ≃ₗ[R] q :=
(e.of_submodule p).trans (linear_equiv.of_eq _ _ h)

@[simp] lemma of_submodules_apply {p : submodule R M} {q : submodule R M₂}
  (h : p.map ↑e = q) (x : p) : ↑(e.of_submodules p q h x) = e x := rfl

@[simp] lemma of_submodules_symm_apply {p : submodule R M} {q : submodule R M₂}
  (h : p.map ↑e = q) (x : q) : ↑((e.of_submodules p q h).symm x) = e.symm x := rfl

variable (p)

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def of_top (h : p = ⊤) : p ≃ₗ[R] M :=
{ inv_fun   := λ x, ⟨x, h.symm ▸ trivial⟩,
  left_inv  := λ ⟨x, h⟩, rfl,
  right_inv := λ x, rfl,
  .. p.subtype }

@[simp] theorem of_top_apply {h} (x : p) : of_top p h x = x := rfl

@[simp] theorem coe_of_top_symm_apply {h} (x : M) : ((of_top p h).symm x : M) = x := rfl

theorem of_top_symm_apply {h} (x : M) : (of_top p h).symm x = ⟨x, h.symm ▸ trivial⟩ := rfl

/-- If a linear map has an inverse, it is a linear equivalence. -/
def of_linear (h₁ : f.comp g = linear_map.id) (h₂ : g.comp f = linear_map.id) : M ≃ₗ[R] M₂ :=
{ inv_fun   := g,
  left_inv  := linear_map.ext_iff.1 h₂,
  right_inv := linear_map.ext_iff.1 h₁,
  ..f }

@[simp] theorem of_linear_apply {h₁ h₂} (x : M) : of_linear f g h₁ h₂ x = f x := rfl

@[simp] theorem of_linear_symm_apply {h₁ h₂} (x : M₂) : (of_linear f g h₁ h₂).symm x = g x := rfl

@[simp] protected theorem range : (e : M →ₗ[R] M₂).range = ⊤ :=
linear_map.range_eq_top.2 e.to_equiv.surjective

lemma eq_bot_of_equiv [semimodule R M₂] (e : p ≃ₗ[R] (⊥ : submodule R M₂)) : p = ⊥ :=
begin
  refine bot_unique (submodule.le_def'.2 $ assume b hb, (submodule.mem_bot R).2 _),
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff],
  apply submodule.eq_zero_of_bot_submodule
end

@[simp] protected theorem ker : (e : M →ₗ[R] M₂).ker = ⊥ :=
linear_map.ker_eq_bot_of_injective e.to_equiv.injective

end

end add_comm_monoid

section add_comm_group

variables [semiring R]
variables [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [add_comm_group M₄]
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄}
variables (e e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

@[simp] theorem map_neg (a : M) : e (-a) = -e a := e.to_linear_map.map_neg a
@[simp] theorem map_sub (a b : M) : e (a - b) = e a - e b :=
e.to_linear_map.map_sub a b

/-- Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
protected def skew_prod (f : M →ₗ[R] M₄) :
  (M × M₃) ≃ₗ[R] M₂ × M₄ :=
{ inv_fun := λ p : M₂ × M₄, (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1))),
  left_inv := λ p, by simp,
  right_inv := λ p, by simp,
  .. ((e₁ : M →ₗ[R] M₂).comp (linear_map.fst R M M₃)).prod
    ((e₂ : M₃ →ₗ[R] M₄).comp (linear_map.snd R M M₃) +
      f.comp (linear_map.fst R M M₃)) }

@[simp] lemma skew_prod_apply (f : M →ₗ[R] M₄) (x) :
  e₁.skew_prod e₂ f x = (e₁ x.1, e₂ x.2 + f x.1) := rfl

@[simp] lemma skew_prod_symm_apply (f : M →ₗ[R] M₄) (x) :
  (e₁.skew_prod e₂ f).symm x = (e₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1))) := rfl

end add_comm_group

section neg

variables (R) [semiring R] [add_comm_group M] [semimodule R M]

/-- `x ↦ -x` as a `linear_equiv` -/
def neg : M ≃ₗ[R] M := { .. equiv.neg M, .. (-linear_map.id : M →ₗ[R] M) }

variable {R}

@[simp] lemma coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id := rfl

lemma neg_apply (x : M) : neg R x = -x := by simp

@[simp] lemma symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R := rfl

end neg

section ring

variables [ring R] [add_comm_group M] [add_comm_group M₂]
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables (f : M →ₗ[R] M₂) (e : M ≃ₗ[R] M₂)

/-- An `injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. -/
noncomputable def of_injective (h : f.ker = ⊥) : M ≃ₗ[R] f.range :=
{ .. (equiv.set.range f $ linear_map.ker_eq_bot.1 h).trans (equiv.set.of_eq f.range_coe.symm),
  .. f.cod_restrict f.range (λ x, f.mem_range_self x) }

@[simp] theorem of_injective_apply {h : f.ker = ⊥} (x : M) :
  ↑(of_injective f h x) = f x := rfl

/-- A bijective linear map is a linear equivalence. Here, bijectivity is described by saying that
the kernel of `f` is `{0}` and the range is the universal set. -/
noncomputable def of_bijective (hf₁ : f.ker = ⊥) (hf₂ : f.range = ⊤) : M ≃ₗ[R] M₂ :=
(of_injective f hf₁).trans (of_top _ hf₂)

@[simp] theorem of_bijective_apply {hf₁ hf₂} (x : M) :
  of_bijective f hf₁ hf₂ x = f x := rfl

end ring

section comm_ring
variables [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]
open linear_map

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smul_of_unit (a : units R) : M ≃ₗ[R] M :=
of_linear ((a:R) • 1 : M →ₗ M) (((a⁻¹ : units R) : R) • 1 : M →ₗ M)
  (by rw [smul_comp, comp_smul, smul_smul, units.mul_inv, one_smul]; refl)
  (by rw [smul_comp, comp_smul, smul_smul, units.inv_mul, one_smul]; refl)

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrow_congr {R M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_ring R]
  [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₂₁] [add_comm_group M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) :
  (M₁ →ₗ[R] M₂₁) ≃ₗ[R] (M₂ →ₗ[R] M₂₂) :=
{ to_fun := λ f, (e₂ : M₂₁ →ₗ[R] M₂₂).comp $ f.comp e₁.symm,
  inv_fun := λ f, (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp $ f.comp e₁,
  left_inv := λ f, by { ext x, simp },
  right_inv := λ f, by { ext x, simp },
  map_add' := λ f g, by { ext x, simp },
  map_smul' := λ c f, by { ext x, simp } }

@[simp] lemma arrow_congr_apply {R M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_ring R]
  [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₂₁] [add_comm_group M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₁ →ₗ[R] M₂₁) (x : M₂) :
  arrow_congr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
rfl

@[simp] lemma arrow_congr_symm_apply {R M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_ring R]
  [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₂₁] [add_comm_group M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₂ →ₗ[R] M₂₂) (x : M₁) :
  (arrow_congr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
rfl

lemma arrow_congr_comp {N N₂ N₃ : Sort*}
  [add_comm_group N] [add_comm_group N₂] [add_comm_group N₃]
  [module R N] [module R N₂] [module R N₃]
  (e₁ : M ≃ₗ[R] N) (e₂ : M₂ ≃ₗ[R] N₂) (e₃ : M₃ ≃ₗ[R] N₃) (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
  arrow_congr e₁ e₃ (g.comp f) = (arrow_congr e₂ e₃ g).comp (arrow_congr e₁ e₂ f) :=
by { ext, simp only [symm_apply_apply, arrow_congr_apply, linear_map.comp_apply], }

lemma arrow_congr_trans {M₁ M₂ M₃ N₁ N₂ N₃ : Sort*}
  [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]
  [add_comm_group M₃] [module R M₃] [add_comm_group N₁] [module R N₁]
  [add_comm_group N₂] [module R N₂] [add_comm_group N₃] [module R N₃]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : N₁ ≃ₗ[R] N₂) (e₃ : M₂ ≃ₗ[R] M₃) (e₄ : N₂ ≃ₗ[R] N₃) :
  (arrow_congr e₁ e₂).trans (arrow_congr e₃ e₄) = arrow_congr (e₁.trans e₃) (e₂.trans e₄) :=
rfl

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congr_right (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ (M →ₗ M₃) :=
arrow_congr (linear_equiv.refl R M) f

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic. -/
def conj (e : M ≃ₗ[R] M₂) : (module.End R M) ≃ₗ[R] (module.End R M₂) := arrow_congr e e

lemma conj_apply (e : M ≃ₗ[R] M₂) (f : module.End R M) :
  e.conj f = ((↑e : M →ₗ[R] M₂).comp f).comp e.symm := rfl

lemma symm_conj_apply (e : M ≃ₗ[R] M₂) (f : module.End R M₂) :
  e.symm.conj f = ((↑e.symm : M₂ →ₗ[R] M).comp f).comp e := rfl

lemma conj_comp (e : M ≃ₗ[R] M₂) (f g : module.End R M) :
  e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
arrow_congr_comp e e e f g

lemma conj_trans (e₁ : M ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) :
  e₁.conj.trans e₂.conj = (e₁.trans e₂).conj :=
by { ext f x, refl, }

@[simp] lemma conj_id (e : M ≃ₗ[R] M₂) : e.conj linear_map.id = linear_map.id :=
by { ext, simp [conj_apply], }

end comm_ring

section field
variables [field K] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module K M] [module K M₂] [module K M₃]
variables (K) (M)
open linear_map

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
def smul_of_ne_zero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
smul_of_unit $ units.mk0 a ha

section

noncomputable theory
open_locale classical

lemma ker_to_span_singleton {x : M} (h : x ≠ 0) : (to_span_singleton K M x).ker = ⊥ :=
begin
  ext c, split,
  { intros hc, rw submodule.mem_bot, rw mem_ker at hc, by_contra hc',
    have : x = 0,
      calc x = c⁻¹ • (c • x) : by rw [← mul_smul, inv_mul_cancel hc', one_smul]
      ... = c⁻¹ • ((to_span_singleton K M x) c) : rfl
      ... = 0 : by rw [hc, smul_zero],
    tauto },
  { rw [mem_ker, submodule.mem_bot], intros h, rw h, simp }
end

/-- Given a nonzero element `x` of a vector space `M` over a field `K`, the natural
    map from `K` to the span of `x`, with invertibility check to consider it as an
    isomorphism.-/
def to_span_nonzero_singleton (x : M) (h : x ≠ 0) : K ≃ₗ[K] (K ∙ x) :=
linear_equiv.trans
  (linear_equiv.of_injective (to_span_singleton K M x) (ker_to_span_singleton K M h))
  (of_eq (to_span_singleton K M x).range (K ∙ x)
    (span_singleton_eq_range K M x).symm)

lemma to_span_nonzero_singleton_one (x : M) (h : x ≠ 0) : to_span_nonzero_singleton K M x h 1
  = (⟨x, submodule.mem_span_singleton_self x⟩ : K ∙ x) :=
begin
  apply submodule.coe_eq_coe.mp,
  have : ↑(to_span_nonzero_singleton K M x h 1) = to_span_singleton K M x 1 := rfl,
  rw [this, to_span_singleton_one, submodule.coe_mk],
end

/-- Given a nonzero element `x` of a vector space `M` over a field `K`, the natural map
    from the span of `x` to `K`.-/
abbreviation coord (x : M) (h : x ≠ 0) : (K ∙ x) ≃ₗ[K] K :=
(to_span_nonzero_singleton K M x h).symm

lemma coord_self (x : M) (h : x ≠ 0) :
  (coord K M x h) (⟨x, submodule.mem_span_singleton_self x⟩ : K ∙ x) = 1 :=
by rw [← to_span_nonzero_singleton_one K M x h, symm_apply_apply]

end

end field

end linear_equiv

namespace submodule

section semimodule

variables [semiring R] [add_comm_monoid M] [semimodule R M]

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
def comap_subtype_equiv_of_le {p q : submodule R M} (hpq : p ≤ q) :
comap q.subtype p ≃ₗ[R] p :=
{ to_fun := λ x, ⟨x, x.2⟩,
  inv_fun := λ x, ⟨⟨x, hpq x.2⟩, x.2⟩,
  left_inv := λ x, by simp only [coe_mk, submodule.eta, coe_coe],
  right_inv := λ x, by simp only [subtype.coe_mk, submodule.eta, coe_coe],
  map_add' := λ x y, rfl,
  map_smul' := λ c x, rfl }

end semimodule

variables [ring R] [add_comm_group M] [module R M]
variables (p : submodule R M)

open linear_map

/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
def quot_equiv_of_eq_bot (hp : p = ⊥) : p.quotient ≃ₗ[R] M :=
linear_equiv.of_linear (p.liftq id $ hp.symm ▸ bot_le) p.mkq (liftq_mkq _ _ _) $
  p.quot_hom_ext $ λ x, rfl

@[simp] lemma quot_equiv_of_eq_bot_apply_mk (hp : p = ⊥) (x : M) :
  p.quot_equiv_of_eq_bot hp (quotient.mk x) = x := rfl

@[simp] lemma quot_equiv_of_eq_bot_symm_apply (hp : p = ⊥) (x : M) :
  (p.quot_equiv_of_eq_bot hp).symm x = quotient.mk x := rfl

@[simp] lemma coe_quot_equiv_of_eq_bot_symm (hp : p = ⊥) :
  ((p.quot_equiv_of_eq_bot hp).symm : M →ₗ[R] p.quotient) = p.mkq := rfl

variables (q : submodule R M)

/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
def quot_equiv_of_eq (h : p = q) : p.quotient ≃ₗ[R] q.quotient :=
{ map_add' := by { rintros ⟨x⟩ ⟨y⟩, refl }, map_smul' := by { rintros x ⟨y⟩, refl },
  ..@quotient.congr _ _ (quotient_rel p) (quotient_rel q) (equiv.refl _) $
    λ a b, by { subst h, refl } }

end submodule

namespace submodule

variables [comm_ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
variables (p : submodule R M) (q : submodule R M₂)

@[simp] lemma mem_map_equiv {e : M ≃ₗ[R] M₂} {x : M₂} : x ∈ p.map (e : M →ₗ[R] M₂) ↔ e.symm x ∈ p :=
begin
  rw submodule.mem_map, split,
  { rintros ⟨y, hy, hx⟩, simp [←hx, hy], },
  { intros hx, refine ⟨e.symm x, hx, by simp⟩, },
end

lemma comap_le_comap_smul (f : M →ₗ[R] M₂) (c : R) :
  comap f q ≤ comap (c • f) q :=
begin
  rw le_def',
  intros m h,
  change c • (f m) ∈ q,
  change f m ∈ q at h,
  apply q.smul_mem _ h,
end

lemma inf_comap_le_comap_add (f₁ f₂ : M →ₗ[R] M₂) :
  comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q :=
begin
  rw le_def',
  intros m h,
  change f₁ m + f₂ m ∈ q,
  change f₁ m ∈ q ∧ f₂ m ∈ q at h,
  apply q.add_mem h.1 h.2,
end

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`, the
set of maps $\\{f ∈ Hom(M, M₂) | f(p) ⊆ q \\}$ is a submodule of `Hom(M, M₂)`. -/
def compatible_maps : submodule R (M →ₗ[R] M₂) :=
{ carrier   := {f | p ≤ comap f q},
  zero_mem' := by { change p ≤ comap 0 q, rw comap_zero, refine le_top, },
  add_mem'  := λ f₁ f₂ h₁ h₂, by { apply le_trans _ (inf_comap_le_comap_add q f₁ f₂), rw le_inf_iff,
                                 exact ⟨h₁, h₂⟩, },
  smul_mem' := λ c f h, le_trans h (comap_le_comap_smul q f c), }

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`, the
natural map $\\{f ∈ Hom(M, M₂) | f(p) ⊆ q \\} \to Hom(M/p, M₂/q)$ is linear. -/
def mapq_linear : compatible_maps p q →ₗ[R] p.quotient →ₗ[R] q.quotient :=
{ to_fun    := λ f, mapq _ _ f.val f.property,
  map_add'  := λ x y, by { ext m', apply quotient.induction_on' m', intros m, refl, },
  map_smul' := λ c f, by { ext m', apply quotient.induction_on' m', intros m, refl, } }

end submodule

namespace equiv
variables [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def to_linear_equiv (e : M ≃ M₂) (h : is_linear_map R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
{ .. e, .. h.mk' e}

end equiv

namespace add_equiv
variables [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂]

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def to_linear_equiv (e : M ≃+ M₂) (h : ∀ (c : R) x, e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
{ map_smul' := h, .. e, }

@[simp] lemma coe_to_linear_equiv (e : M ≃+ M₂) (h : ∀ (c : R) x, e (c • x) = c • e x) :
  ⇑(e.to_linear_equiv h) = e :=
rfl

@[simp] lemma coe_to_linear_equiv_symm (e : M ≃+ M₂) (h : ∀ (c : R) x, e (c • x) = c • e x) :
  ⇑(e.to_linear_equiv h).symm = e.symm :=
rfl

end add_equiv

namespace linear_map

open submodule

section isomorphism_laws

variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
variables (f : M →ₗ[R] M₂)

/-- The first isomorphism law for modules. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`. -/
noncomputable def quot_ker_equiv_range : f.ker.quotient ≃ₗ[R] f.range :=
(linear_equiv.of_injective (f.ker.liftq f $ le_refl _) $
  submodule.ker_liftq_eq_bot _ _ _ (le_refl f.ker)).trans
  (linear_equiv.of_eq _ _ $ submodule.range_liftq _ _ _)

@[simp] lemma quot_ker_equiv_range_apply_mk (x : M) :
  (f.quot_ker_equiv_range (submodule.quotient.mk x) : M₂) = f x :=
rfl

@[simp] lemma quot_ker_equiv_range_symm_apply_image (x : M) (h : f x ∈ f.range) :
  f.quot_ker_equiv_range.symm ⟨f x, h⟩ = f.ker.mkq x :=
f.quot_ker_equiv_range.symm_apply_apply (f.ker.mkq x)

/--
Canonical linear map from the quotient `p/(p ∩ p')` to `(p+p')/p'`, mapping `x + (p ∩ p')`
to `x + p'`, where `p` and `p'` are submodules of an ambient module.
-/
def quotient_inf_to_sup_quotient (p p' : submodule R M) :
  (comap p.subtype (p ⊓ p')).quotient →ₗ[R] (comap (p ⊔ p').subtype p').quotient :=
(comap p.subtype (p ⊓ p')).liftq
  ((comap (p ⊔ p').subtype p').mkq.comp (of_le le_sup_left)) begin
rw [ker_comp, of_le, comap_cod_restrict, ker_mkq, map_comap_subtype],
exact comap_mono (inf_le_inf_right _ le_sup_left) end

/--
Second Isomorphism Law : the canonical map from `p/(p ∩ p')` to `(p+p')/p'` as a linear isomorphism.
-/
noncomputable def quotient_inf_equiv_sup_quotient (p p' : submodule R M) :
  (comap p.subtype (p ⊓ p')).quotient ≃ₗ[R] (comap (p ⊔ p').subtype p').quotient :=
linear_equiv.of_bijective (quotient_inf_to_sup_quotient p p')
  begin
    rw [quotient_inf_to_sup_quotient, ker_liftq_eq_bot],
    rw [ker_comp, ker_mkq],
    exact λ ⟨x, hx1⟩ hx2, ⟨hx1, hx2⟩
  end
  begin
    rw [quotient_inf_to_sup_quotient, range_liftq, eq_top_iff'],
    rintros ⟨x, hx⟩, rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩,
    use [⟨y, hy⟩, trivial], apply (submodule.quotient.eq _).2,
    change y - (y + z) ∈ p',
    rwa [sub_add_eq_sub_sub, sub_self, zero_sub, neg_mem_iff]
  end

@[simp] lemma coe_quotient_inf_to_sup_quotient (p p' : submodule R M) :
  ⇑(quotient_inf_to_sup_quotient p p') = quotient_inf_equiv_sup_quotient p p' := rfl

@[simp] lemma quotient_inf_equiv_sup_quotient_apply_mk (p p' : submodule R M) (x : p) :
  quotient_inf_equiv_sup_quotient p p' (submodule.quotient.mk x) =
    submodule.quotient.mk (of_le (le_sup_left : p ≤ p ⊔ p') x) :=
rfl

lemma quotient_inf_equiv_sup_quotient_symm_apply_left (p p' : submodule R M)
  (x : p ⊔ p') (hx : (x:M) ∈ p) :
  (quotient_inf_equiv_sup_quotient p p').symm (submodule.quotient.mk x) =
    submodule.quotient.mk ⟨x, hx⟩ :=
(linear_equiv.symm_apply_eq _).2 $ by simp [of_le_apply]

@[simp] lemma quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff {p p' : submodule R M}
  {x : p ⊔ p'} :
  (quotient_inf_equiv_sup_quotient p p').symm (submodule.quotient.mk x) = 0 ↔ (x:M) ∈ p' :=
(linear_equiv.symm_apply_eq _).trans $ by simp [of_le_apply]

lemma quotient_inf_equiv_sup_quotient_symm_apply_right (p p' : submodule R M) {x : p ⊔ p'}
  (hx : (x:M) ∈ p') :
  (quotient_inf_equiv_sup_quotient p p').symm (submodule.quotient.mk x) = 0 :=
quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff.2 hx

end isomorphism_laws

section prod

lemma is_linear_map_prod_iso {R M M₂ M₃ : Type*}
  [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
  [add_comm_group M₃] [semimodule R M] [semimodule R M₂] [semimodule R M₃] :
  is_linear_map R (λ(p : (M →ₗ[R] M₂) × (M →ₗ[R] M₃)),
    (linear_map.prod p.1 p.2 : (M →ₗ[R] (M₂ × M₃)))) :=
⟨λu v, rfl, λc u, rfl⟩

end prod

section pi
universe i
variables [semiring R] [add_comm_monoid M₂] [semimodule R M₂] [add_comm_monoid M₃] [semimodule R M₃]
{φ : ι → Type i} [∀i, add_comm_monoid (φ i)] [∀i, semimodule R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : Πi, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (Πi, φ i) :=
⟨λc i, f i c, λ c d, funext $ λ i, (f i).map_add _ _, λ c d, funext $ λ i, (f i).map_smul _ _⟩

@[simp] lemma pi_apply (f : Πi, M₂ →ₗ[R] φ i) (c : M₂) (i : ι) :
  pi f c i = f i c := rfl

lemma ker_pi (f : Πi, M₂ →ₗ[R] φ i) : ker (pi f) = (⨅i:ι, ker (f i)) :=
by ext c; simp [funext_iff]; refl

lemma pi_eq_zero (f : Πi, M₂ →ₗ[R] φ i) : pi f = 0 ↔ (∀i, f i = 0) :=
by simp only [linear_map.ext_iff, pi_apply, funext_iff]; exact ⟨λh a b, h b a, λh a b, h b a⟩

lemma pi_zero : pi (λi, 0 : Πi, M₂ →ₗ[R] φ i) = 0 :=
by ext; refl

lemma pi_comp (f : Πi, M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) : (pi f).comp g = pi (λi, (f i).comp g) :=
rfl

/-- The projections from a family of modules are linear maps. -/
def proj (i : ι) : (Πi, φ i) →ₗ[R] φ i :=
⟨ λa, a i, assume f g, rfl, assume c f, rfl ⟩

@[simp] lemma proj_apply (i : ι) (b : Πi, φ i) : (proj i : (Πi, φ i) →ₗ[R] φ i) b = b i := rfl

lemma proj_pi (f : Πi, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
ext $ assume c, rfl

lemma infi_ker_proj : (⨅i, ker (proj i) : submodule R (Πi, φ i)) = ⊥ :=
bot_unique $ submodule.le_def'.2 $ assume a h,
begin
  simp only [mem_infi, mem_ker, proj_apply] at h,
  exact (mem_bot _).2 (funext $ assume i, h i)
end

section
variables (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv {I J : set ι} [decidable_pred (λi, i ∈ I)]
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) :
  (⨅i ∈ J, ker (proj i) : submodule R (Πi, φ i)) ≃ₗ[R] (Πi:I, φ i) :=
begin
  refine linear_equiv.of_linear
    (pi $ λi, (proj (i:ι)).comp (submodule.subtype _))
    (cod_restrict _ (pi $ λi, if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _,
  { assume b,
    simp only [mem_infi, mem_ker, funext_iff, proj_apply, pi_apply],
    assume j hjJ,
    have : j ∉ I := assume hjI, hd ⟨hjI, hjJ⟩,
    rw [dif_neg this, zero_apply] },
  { simp only [pi_comp, comp_assoc, subtype_comp_cod_restrict, proj_pi, dif_pos, subtype.coe_prop],
    ext b ⟨j, hj⟩, refl },
  { ext1 ⟨b, hb⟩,
    apply subtype.ext,
    ext j,
    have hb : ∀i ∈ J, b i = 0,
    { simpa only [mem_infi, mem_ker, proj_apply] using (mem_infi _).1 hb },
    simp only [comp_apply, pi_apply, id_apply, proj_apply, subtype_apply, cod_restrict_apply],
    split_ifs,
    { refl },
    { exact (hb _ $ (hu trivial).resolve_left h).symm } }
end
end

section
variable [decidable_eq ι]

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
@function.update ι (λj, φ i →ₗ[R] φ j) _ 0 i id j

lemma update_apply (f : Πi, M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
  (update f i b j) c = update (λi, f i c) i (b c) j :=
begin
  by_cases j = i,
  { rw [h, update_same, update_same] },
  { rw [update_noteq h, update_noteq h] }
end

end

section
variable [decidable_eq ι]
variables (R φ)

/-- The standard basis of the product of `φ`. -/
def std_basis (i : ι) : φ i →ₗ[R] (Πi, φ i) := pi (diag i)

lemma std_basis_apply (i : ι) (b : φ i) : std_basis R φ i b = update 0 i b :=
by ext j; rw [std_basis, pi_apply, diag, update_apply]; refl

@[simp] lemma std_basis_same (i : ι) (b : φ i) : std_basis R φ i b i = b :=
by rw [std_basis_apply, update_same]

lemma std_basis_ne (i j : ι) (h : j ≠ i) (b : φ i) : std_basis R φ i b j = 0 :=
by rw [std_basis_apply, update_noteq h]; refl

lemma ker_std_basis (i : ι) : ker (std_basis R φ i) = ⊥ :=
ker_eq_bot_of_injective $ assume f g hfg,
  have std_basis R φ i f i = std_basis R φ i g i := hfg ▸ rfl,
  by simpa only [std_basis_same]

lemma proj_comp_std_basis (i j : ι) : (proj i).comp (std_basis R φ j) = diag j i :=
by rw [std_basis, proj_pi]

lemma proj_std_basis_same (i : ι) : (proj i).comp (std_basis R φ i) = id :=
by ext b; simp

lemma proj_std_basis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (std_basis R φ j) = 0 :=
by ext b; simp [std_basis_ne R φ _ _ h]

lemma supr_range_std_basis_le_infi_ker_proj (I J : set ι) (h : disjoint I J) :
  (⨆i∈I, range (std_basis R φ i)) ≤ (⨅i∈J, ker (proj i)) :=
begin
  refine (supr_le $ assume i, supr_le $ assume hi, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, le_def', mem_ker, comap_infi, mem_infi],
  assume b hb j hj,
  have : i ≠ j := assume eq, h ⟨hi, eq.symm ▸ hj⟩,
  rw [proj_std_basis_ne R φ j i this.symm, zero_apply]
end

lemma infi_ker_proj_le_supr_range_std_basis {I : finset ι} {J : set ι} (hu : set.univ ⊆ ↑I ∪ J) :
  (⨅ i∈J, ker (proj i)) ≤ (⨆i∈I, range (std_basis R φ i)) :=
submodule.le_def'.2
begin
  assume b hb,
  simp only [mem_infi, mem_ker, proj_apply] at hb,
  rw ← show ∑ i in I, std_basis R φ i (b i) = b,
  { ext i,
    rw [finset.sum_apply, ← std_basis_same R φ i (b i)],
    refine finset.sum_eq_single i (assume j hjI ne, std_basis_ne _ _ _ _ ne.symm _) _,
    assume hiI,
    rw [std_basis_same],
    exact hb _ ((hu trivial).resolve_left hiI) },
  exact sum_mem _ (assume i hiI, mem_supr_of_mem i $ mem_supr_of_mem hiI $
    (std_basis R φ i).mem_range_self (b i))
end

lemma supr_range_std_basis_eq_infi_ker_proj {I J : set ι}
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) (hI : set.finite I) :
  (⨆i∈I, range (std_basis R φ i)) = (⨅i∈J, ker (proj i)) :=
begin
  refine le_antisymm (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _,
  have : set.univ ⊆ ↑hI.to_finset ∪ J, { rwa [hI.coe_to_finset] },
  refine le_trans (infi_ker_proj_le_supr_range_std_basis R φ this) (supr_le_supr $ assume i, _),
  rw [set.finite.mem_to_finset],
  exact le_refl _
end

lemma supr_range_std_basis [fintype ι] : (⨆i:ι, range (std_basis R φ i)) = ⊤ :=
have (set.univ : set ι) ⊆ ↑(finset.univ : finset ι) ∪ ∅ := by rw [finset.coe_univ, set.union_empty],
begin
  apply top_unique,
  convert (infi_ker_proj_le_supr_range_std_basis R φ this),
  exact infi_emptyset.symm,
  exact (funext $ λi, (@supr_pos _ _ _ (λh, range (std_basis R φ i)) $ finset.mem_univ i).symm)
end

lemma disjoint_std_basis_std_basis (I J : set ι) (h : disjoint I J) :
  disjoint (⨆i∈I, range (std_basis R φ i)) (⨆i∈J, range (std_basis R φ i)) :=
begin
  refine disjoint.mono
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ disjoint_compl_right)
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ disjoint_compl_right) _,
  simp only [disjoint, submodule.le_def', mem_infi, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff],
  rintros b ⟨hI, hJ⟩ i,
  classical,
  by_cases hiI : i ∈ I,
  { by_cases hiJ : i ∈ J,
    { exact (h ⟨hiI, hiJ⟩).elim },
    { exact hJ i hiJ } },
  { exact hI i hiI }
end

lemma std_basis_eq_single {a : R} :
  (λ (i : ι), (std_basis R (λ _ : ι, R) i) a) = λ (i : ι), (finsupp.single i a) :=
begin
  ext i j,
  rw [std_basis_apply, finsupp.single_apply],
  split_ifs,
  { rw [h, function.update_same] },
  { rw [function.update_noteq (ne.symm h)], refl },
end

end

end pi

section fun_left
variables (R M) [semiring R] [add_comm_monoid M] [semimodule R M]
variables {m n p : Type*}

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def fun_left (f : m → n) : (n → M) →ₗ[R] (m → M) :=
mk (∘f) (λ _ _, rfl) (λ _ _, rfl)

@[simp] theorem fun_left_apply (f : m → n) (g : n → M) (i : m) : fun_left R M f g i = g (f i) :=
rfl

@[simp] theorem fun_left_id (g : n → M) : fun_left R M _root_.id g = g :=
rfl

theorem fun_left_comp (f₁ : n → p) (f₂ : m → n) :
  fun_left R M (f₁ ∘ f₂) = (fun_left R M f₂).comp (fun_left R M f₁) :=
rfl

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def fun_congr_left (e : m ≃ n) : (n → M) ≃ₗ[R] (m → M) :=
linear_equiv.of_linear (fun_left R M e) (fun_left R M e.symm)
  (ext $ λ x, funext $ λ i,
    by rw [id_apply, ← fun_left_comp, equiv.symm_comp_self, fun_left_id])
  (ext $ λ x, funext $ λ i,
    by rw [id_apply, ← fun_left_comp, equiv.self_comp_symm, fun_left_id])

@[simp] theorem fun_congr_left_apply (e : m ≃ n) (x : n → M) :
  fun_congr_left R M e x = fun_left R M e x :=
rfl

@[simp] theorem fun_congr_left_id :
  fun_congr_left R M (equiv.refl n) = linear_equiv.refl R (n → M) :=
rfl

@[simp] theorem fun_congr_left_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
  fun_congr_left R M (equiv.trans e₁ e₂) =
    linear_equiv.trans (fun_congr_left R M e₂) (fun_congr_left R M e₁) :=
rfl

@[simp] lemma fun_congr_left_symm (e : m ≃ n) :
  (fun_congr_left R M e).symm = fun_congr_left R M e.symm :=
rfl

end fun_left

universe i
variables [semiring R] [add_comm_monoid M] [semimodule R M]

variables (R M)

instance automorphism_group : group (M ≃ₗ[R] M) :=
{ mul := λ f g, g.trans f,
  one := linear_equiv.refl R M,
  inv := λ f, f.symm,
  mul_assoc := λ f g h, by {ext, refl},
  mul_one := λ f, by {ext, refl},
  one_mul := λ f, by {ext, refl},
  mul_left_inv := λ f, by {ext, exact f.left_inv x} }

instance automorphism_group.to_linear_map_is_monoid_hom :
  is_monoid_hom (linear_equiv.to_linear_map : (M ≃ₗ[R] M) → (M →ₗ[R] M)) :=
{ map_one := rfl,
  map_mul := λ f g, rfl }

/-- The group of invertible linear maps from `M` to itself -/
@[reducible] def general_linear_group := units (M →ₗ[R] M)

namespace general_linear_group
variables {R M}

instance : has_coe_to_fun (general_linear_group R M) := by apply_instance

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def to_linear_equiv (f : general_linear_group R M) : (M ≃ₗ[R] M) :=
{ inv_fun := f.inv.to_fun,
  left_inv := λ m, show (f.inv * f.val) m = m,
    by erw f.inv_val; simp,
  right_inv := λ m, show (f.val * f.inv) m = m,
    by erw f.val_inv; simp,
  ..f.val }

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def of_linear_equiv (f : (M ≃ₗ[R] M)) : general_linear_group R M :=
{ val := f,
  inv := f.symm,
  val_inv := linear_map.ext $ λ _, f.apply_symm_apply _,
  inv_val := linear_map.ext $ λ _, f.symm_apply_apply _ }

variables (R M)

/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def general_linear_equiv : general_linear_group R M ≃* (M ≃ₗ[R] M) :=
{ to_fun := to_linear_equiv,
  inv_fun := of_linear_equiv,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl },
  map_mul' := λ x y, by {ext, refl} }

@[simp] lemma general_linear_equiv_to_linear_map (f : general_linear_group R M) :
  (general_linear_equiv R M f : M →ₗ[R] M) = f :=
by {ext, refl}

end general_linear_group

end linear_map
