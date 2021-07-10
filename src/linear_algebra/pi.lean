/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
import linear_algebra.basic

/-!
# Pi types of modules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `linear_map.ker`.

## Main definitions

- pi types in the codomain:
  - `linear_map.pi`
  - `linear_map.single`
- pi types in the domain:
  - `linear_map.proj`
- `linear_map.diag`

-/

universes u v w x y z u' v' w' x' y'
variables {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variables {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open function submodule
open_locale big_operators

namespace linear_map

universe i
variables [semiring R] [add_comm_monoid M₂] [module R M₂] [add_comm_monoid M₃] [module R M₃]
{φ : ι → Type i} [∀i, add_comm_monoid (φ i)] [∀i, module R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : Πi, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (Πi, φ i) :=
{ to_fun := λ c i, f i c,
  map_add' := λ c d, funext $ λ i, (f i).map_add _ _,
  map_smul' := λ c d, funext $ λ i, (f i).map_smul _ _ }

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

/-- The projections from a family of modules are linear maps.

Note:  known here as `linear_map.proj`, this construction is in other categories called `eval`, for
example `pi.eval_monoid_hom`, `pi.eval_ring_hom`. -/
def proj (i : ι) : (Πi, φ i) →ₗ[R] φ i :=
{ to_fun := function.eval i, map_add' := λ f g, rfl, map_smul' := λ c f, rfl }

@[simp] lemma coe_proj (i : ι) : ⇑(proj i : (Πi, φ i) →ₗ[R] φ i) = function.eval i := rfl

lemma proj_apply (i : ι) (b : Πi, φ i) : (proj i : (Πi, φ i) →ₗ[R] φ i) b = b i := rfl

lemma proj_pi (f : Πi, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
ext $ assume c, rfl

lemma infi_ker_proj : (⨅i, ker (proj i) : submodule R (Πi, φ i)) = ⊥ :=
bot_unique $ set_like.le_def.2 $ assume a h,
begin
  simp only [mem_infi, mem_ker, proj_apply] at h,
  exact (mem_bot _).2 (funext $ assume i, h i)
end

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps] protected def comp_left (f : M₂ →ₗ[R] M₃) (I : Type*) : (I → M₂) →ₗ[R] (I → M₃) :=
{ to_fun := λ h, f ∘ h,
  map_smul' := λ c h, by { ext x, exact f.map_smul' c (h x) },
  .. f.to_add_monoid_hom.comp_left I }

lemma apply_single [add_comm_monoid M] [module R M] [decidable_eq ι]
  (f : Π i, φ i →ₗ[R] M) (i j : ι) (x : φ i) :
  f j (pi.single i x j) = pi.single i (f i x) j :=
pi.apply_single (λ i, f i) (λ i, (f i).map_zero) _ _ _

/-- The `linear_map` version of `add_monoid_hom.single` and `pi.single`. -/
def single [decidable_eq ι] (i : ι) : φ i →ₗ[R] (Πi, φ i) :=
{ to_fun := pi.single i,
  map_smul' := pi.single_smul i,
  .. add_monoid_hom.single φ i}

@[simp] lemma coe_single [decidable_eq ι] (i : ι) :
  ⇑(single i : φ i →ₗ[R] (Π i, φ i)) = pi.single i := rfl

variables (R φ)

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps] def lsum (S) [add_comm_monoid M] [module R M] [fintype ι] [decidable_eq ι]
  [semiring S] [module S M]  [smul_comm_class R S M] :
  (Π i, φ i →ₗ[R] M) ≃ₗ[S] ((Π i, φ i) →ₗ[R] M) :=
{ to_fun := λ f, ∑ i : ι, (f i).comp (proj i),
  inv_fun := λ f i, f.comp (single i),
  map_add' := λ f g, by simp only [pi.add_apply, add_comp, finset.sum_add_distrib],
  map_smul' := λ c f, by simp only [pi.smul_apply, smul_comp, finset.smul_sum],
  left_inv := λ f, by { ext i x, simp [apply_single] },
  right_inv := λ f,
    begin
      ext,
      suffices : f (∑ j, pi.single j (x j)) = f x, by simpa [apply_single],
      rw finset.univ_sum_single
    end }

variables {R φ}

section ext

variables [fintype ι] [decidable_eq ι] [add_comm_monoid M] [module R M]
  {f g : (Π i, φ i) →ₗ[R] M}

lemma pi_ext (h : ∀ i x, f (pi.single i x) = g (pi.single i x)) :
  f = g :=
to_add_monoid_hom_injective $ add_monoid_hom.functions_ext _ _ _ h

lemma pi_ext_iff : f = g ↔ ∀ i x, f (pi.single i x) = g (pi.single i x) :=
⟨λ h i x, h ▸ rfl, pi_ext⟩

/-- This is used as the ext lemma instead of `linear_map.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext] lemma pi_ext' (h : ∀ i, f.comp (single i) = g.comp (single i)) : f = g :=
begin
  refine pi_ext (λ i x, _),
  convert linear_map.congr_fun (h i) x
end

lemma pi_ext'_iff : f = g ↔ ∀ i, f.comp (single i) = g.comp (single i) :=
⟨λ h i, h ▸ rfl, pi_ext'⟩

end ext

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

end linear_map

namespace submodule

variables [semiring R] {φ : ι → Type*} [∀ i, add_comm_monoid (φ i)] [∀ i, module R (φ i)]

open linear_map

/-- A version of `set.pi` for submodules. Given an index set `I` and a family of submodules
`p : Π i, submodule R (φ i)`, `pi I s` is the submodule of dependent functions `f : Π i, φ i`
such that `f i` belongs to `p a` whenever `i ∈ I`. -/
def pi (I : set ι) (p : Π i, submodule R (φ i)) : submodule R (Π i, φ i) :=
{ carrier := set.pi I (λ i, p i),
  zero_mem' := λ i hi, (p i).zero_mem,
  add_mem' := λ x y hx hy i hi, (p i).add_mem (hx i hi) (hy i hi),
  smul_mem' := λ c x hx i hi, (p i).smul_mem c (hx i hi) }

variables {I : set ι} {p : Π i, submodule R (φ i)} {x : Π i, φ i}

@[simp] lemma mem_pi : x ∈ pi I p ↔ ∀ i ∈ I, x i ∈ p i := iff.rfl

@[simp, norm_cast] lemma coe_pi : (pi I p : set (Π i, φ i)) = set.pi I (λ i, p i) := rfl

lemma binfi_comap_proj : (⨅ i ∈ I, comap (proj i) (p i)) = pi I p :=
by { ext x, simp }

lemma infi_comap_proj : (⨅ i, comap (proj i) (p i)) = pi set.univ p :=
by { ext x, simp }

lemma supr_map_single [decidable_eq ι] [fintype ι] :
  (⨆ i, map (linear_map.single i) (p i)) = pi set.univ p :=
begin
  refine (supr_le $ λ i, _).antisymm _,
  { rintro _ ⟨x, hx : x ∈ p i, rfl⟩ j -,
    rcases em (j = i) with rfl|hj; simp * },
  { intros x hx,
    rw [← finset.univ_sum_single x],
    exact sum_mem_supr (λ i, mem_map_of_mem (hx i trivial)) }
end

end submodule

namespace linear_equiv

variables [semiring R] {φ ψ χ : ι → Type*} [∀ i, add_comm_monoid (φ i)] [∀ i, module R (φ i)]
variables [∀ i, add_comm_monoid (ψ i)] [∀ i, module R (ψ i)]
variables [∀ i, add_comm_monoid (χ i)] [∀ i, module R (χ i)]

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `equiv.Pi_congr_right` as a `linear_equiv` -/
@[simps apply] def Pi_congr_right (e : Π i, φ i ≃ₗ[R] ψ i) : (Π i, φ i) ≃ₗ[R] (Π i, ψ i) :=
{ to_fun := λ f i, e i (f i),
  inv_fun := λ f i, (e i).symm (f i),
  map_smul' := λ c f, by { ext, simp },
  .. add_equiv.Pi_congr_right (λ j, (e j).to_add_equiv) }

@[simp]
lemma Pi_congr_right_refl : Pi_congr_right (λ j, refl R (φ j)) = refl _ _ := rfl

@[simp]
lemma Pi_congr_right_symm (e : Π i, φ i ≃ₗ[R] ψ i) :
  (Pi_congr_right e).symm = (Pi_congr_right $ λ i, (e i).symm) := rfl

@[simp]
lemma Pi_congr_right_trans (e : Π i, φ i ≃ₗ[R] ψ i) (f : Π i, ψ i ≃ₗ[R] χ i) :
  (Pi_congr_right e).trans (Pi_congr_right f) = (Pi_congr_right $ λ i, (e i).trans (f i)) :=
rfl

variables (R φ)

/-- Transport dependent functions through an equivalence of the base space.

This is `equiv.Pi_congr_left'` as a `linear_equiv`. -/
@[simps {simp_rhs := tt}]
def Pi_congr_left' (e : ι ≃ ι') : (Π i', φ i') ≃ₗ[R] (Π i, φ $ e.symm i) :=
{ map_add' := λ x y, rfl, map_smul' := λ x y, rfl, .. equiv.Pi_congr_left' φ e }

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `equiv.Pi_congr_left` as a `linear_equiv` -/
def Pi_congr_left (e : ι' ≃ ι) : (Π i', φ (e i')) ≃ₗ[R] (Π i, φ i) :=
(Pi_congr_left' R φ e.symm).symm

variables (ι R M) (S : Type*) [fintype ι] [decidable_eq ι] [semiring S]
  [add_comm_monoid M] [module R M] [module S M] [smul_comm_class R S M]

/-- Linear equivalence between linear functions `Rⁿ → M` and `Mⁿ`. The spaces `Rⁿ` and `Mⁿ`
are represented as `ι → R` and `ι → M`, respectively, where `ι` is a finite type.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings]. -/
def pi_ring : ((ι → R) →ₗ[R] M) ≃ₗ[S] (ι → M) :=
(linear_map.lsum R (λ i : ι, R) S).symm.trans
  (Pi_congr_right $ λ i, linear_map.ring_lmap_equiv_self R M S)

variables {ι R M}

@[simp] lemma pi_ring_apply (f : (ι → R) →ₗ[R] M) (i : ι) :
  pi_ring R M ι S f i = f (pi.single i 1) :=
rfl

@[simp] lemma pi_ring_symm_apply (f : ι → M) (g : ι → R) :
  (pi_ring R M ι S).symm f g = ∑ i, g i • f i :=
by simp [pi_ring, linear_map.lsum]

/--
`equiv.sum_arrow_equiv_prod_arrow` as a linear equivalence.
-/
-- TODO additive version?
def sum_arrow_lequiv_prod_arrow (α β R M : Type*) [semiring R] [add_comm_monoid M] [module R M] :
  ((α ⊕ β) → M) ≃ₗ[R] (α → M) × (β → M) :=
{ map_add' := by { intros f g, ext; refl },
  map_smul' := by { intros r f, ext; refl, },
  .. equiv.sum_arrow_equiv_prod_arrow α β M, }

@[simp] lemma sum_arrow_lequiv_prod_arrow_apply_fst {α β} (f : (α ⊕ β) → M) (a : α) :
  (sum_arrow_lequiv_prod_arrow α β R M f).1 a = f (sum.inl a) := rfl
@[simp] lemma sum_arrow_lequiv_prod_arrow_apply_snd {α β} (f : (α ⊕ β) → M) (b : β) :
  (sum_arrow_lequiv_prod_arrow α β R M f).2 b = f (sum.inr b) := rfl
@[simp] lemma sum_arrow_lequiv_prod_arrow_symm_apply_inl {α β} (f : α → M) (g : β → M) (a : α) :
  ((sum_arrow_lequiv_prod_arrow α β R M).symm (f, g)) (sum.inl a) = f a := rfl
@[simp] lemma sum_arrow_lequiv_prod_arrow_symm_apply_inr {α β} (f : α → M) (g : β → M) (b : β) :
  ((sum_arrow_lequiv_prod_arrow α β R M).symm (f, g)) (sum.inr b) = g b := rfl

end linear_equiv
