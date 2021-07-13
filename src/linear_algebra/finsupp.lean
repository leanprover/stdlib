/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.finsupp.basic
import linear_algebra.basic
import linear_algebra.pi

/-!
# Properties of the module `α →₀ M`

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`data.finsupp.basic`.

In this file we define `finsupp.supported s` to be the set `{f : α →₀ M | f.support ⊆ s}`
interpreted as a submodule of `α →₀ M`. We also define `linear_map` versions of various maps:

* `finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `finsupp.single a` as a linear map;

* `finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `λ f, f a` as a linear map;

* `finsupp.lsubtype_domain (s : set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;

* `finsupp.restrict_dom`: `finsupp.filter` as a linear map to `finsupp.supported s`;

* `finsupp.lsum`: `finsupp.sum` or `finsupp.lift_add_hom` as a `linear_map`;

* `finsupp.total α M R (v : ι → M)`: sends `l : ι → R` to the linear combination of `v i` with
  coefficients `l i`;

* `finsupp.total_on`: a restricted version of `finsupp.total` with domain `finsupp.supported R R s`
  and codomain `submodule.span R (v '' s)`;

* `finsupp.supported_equiv_finsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;

* `finsupp.lmap_domain`: a linear map version of `finsupp.map_domain`;

* `finsupp.dom_lcongr`: a `linear_equiv` version of `finsupp.dom_congr`;

* `finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

* `finsupp.lcongr`: a `linear_equiv`alence between `α →₀ M` and `β →₀ N` constructed using `e : α ≃
  β` and `e' : M ≃ₗ[R] N`.

## Tags

function with finite support, module, linear algebra
-/

noncomputable theory

open set linear_map submodule

open_locale classical big_operators

namespace finsupp

variables {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variables [semiring R] [semiring S] [add_comm_monoid M] [module R M]
variables [add_comm_monoid N] [module R N]
variables [add_comm_monoid P] [module R P]

/-- Interpret `finsupp.single a` as a linear map. -/
def lsingle (a : α) : M →ₗ[R] (α →₀ M) :=
{ map_smul' := assume a b, (smul_single _ _ _).symm, ..finsupp.single_add_hom a }

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere. -/
lemma lhom_ext ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a b, φ (single a b) = ψ (single a b)) :
  φ = ψ :=
linear_map.to_add_monoid_hom_injective $ add_hom_ext h

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext] lemma lhom_ext' ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
  φ = ψ :=
lhom_ext $ λ a, linear_map.congr_fun (h a)

/-- Interpret `λ (f : α →₀ M), f a` as a linear map. -/
def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
{ map_smul' := assume a b, rfl, ..finsupp.apply_add_hom a }

section lsubtype_domain
variables (s : set α)

/-- Interpret `finsupp.subtype_domain s` as a linear map. -/
def lsubtype_domain : (α →₀ M) →ₗ[R] (s →₀ M) :=
{ to_fun := subtype_domain (λx, x ∈ s),
  map_add' := λ a b, subtype_domain_add,
  map_smul' := λ c a, ext $ λ a, rfl }

lemma lsubtype_domain_apply (f : α →₀ M) :
  (lsubtype_domain s : (α →₀ M) →ₗ[R] (s →₀ M)) f = subtype_domain (λx, x ∈ s) f := rfl

end lsubtype_domain

@[simp] lemma lsingle_apply (a : α) (b : M) : (lsingle a : M →ₗ[R] (α →₀ M)) b = single a b  :=
rfl

@[simp] lemma lapply_apply (a : α) (f : α →₀ M) : (lapply a : (α →₀ M) →ₗ[R] M) f = f a  :=
rfl

@[simp] lemma ker_lsingle (a : α) : (lsingle a : M →ₗ[R] (α →₀ M)).ker = ⊥ :=
ker_eq_bot_of_injective (single_injective a)

lemma lsingle_range_le_ker_lapply (s t : set α) (h : disjoint s t) :
  (⨆a∈s, (lsingle a : M →ₗ[R] (α →₀ M)).range) ≤ (⨅a∈t, ker (lapply a)) :=
begin
  refine supr_le (assume a₁, supr_le $ assume h₁, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, set_like.le_def, mem_ker, comap_infi, mem_infi],
  assume b hb a₂ h₂,
  have : a₁ ≠ a₂ := assume eq, h ⟨h₁, eq.symm ▸ h₂⟩,
  exact single_eq_of_ne this
end

lemma infi_ker_lapply_le_bot : (⨅a, ker (lapply a : (α →₀ M) →ₗ[R] M)) ≤ ⊥ :=
begin
  simp only [set_like.le_def, mem_infi, mem_ker, mem_bot, lapply_apply],
  exact assume a h, finsupp.ext h
end

lemma supr_lsingle_range : (⨆a, (lsingle a : M →ₗ[R] (α →₀ M)).range) = ⊤ :=
begin
  refine (eq_top_iff.2 $ set_like.le_def.2 $ assume f _, _),
  rw [← sum_single f],
  exact sum_mem _ (assume a ha, submodule.mem_supr_of_mem a ⟨_, rfl⟩),
end

lemma disjoint_lsingle_lsingle (s t : set α) (hs : disjoint s t) :
  disjoint (⨆a∈s, (lsingle a : M →ₗ[R] (α →₀ M)).range) (⨆a∈t, (lsingle a).range) :=
begin
  refine disjoint.mono
    (lsingle_range_le_ker_lapply _ _ $ disjoint_compl_right)
    (lsingle_range_le_ker_lapply _ _ $ disjoint_compl_right)
    (le_trans (le_infi $ assume i, _) infi_ker_lapply_le_bot),
  classical,
  by_cases his : i ∈ s,
  { by_cases hit : i ∈ t,
    { exact (hs ⟨his, hit⟩).elim },
    exact inf_le_of_right_le (infi_le_of_le i $ infi_le _ hit) },
  exact inf_le_of_left_le (infi_le_of_le i $ infi_le _ his)
end

lemma span_single_image (s : set M) (a : α) :
  submodule.span R (single a '' s) = (submodule.span R s).map (lsingle a) :=
by rw ← span_image; refl

variables (M R)

/-- `finsupp.supported M R s` is the `R`-submodule of all `p : α →₀ M` such that `p.support ⊆ s`. -/
def supported (s : set α) : submodule R (α →₀ M) :=
begin
  refine ⟨ {p | ↑p.support ⊆ s }, _, _, _ ⟩,
  { simp only [subset_def, finset.mem_coe, set.mem_set_of_eq, mem_support_iff, zero_apply],
    assume h ha, exact (ha rfl).elim },
  { assume p q hp hq,
    refine subset.trans
      (subset.trans (finset.coe_subset.2 support_add) _) (union_subset hp hq),
    rw [finset.coe_union] },
  { assume a p hp,
    refine subset.trans (finset.coe_subset.2 support_smul) hp }
end

variables {M}

lemma mem_supported {s : set α} (p : α →₀ M) : p ∈ (supported M R s) ↔ ↑p.support ⊆ s :=
iff.rfl

lemma mem_supported' {s : set α}  (p : α →₀ M) :
  p ∈ supported M R s ↔ ∀ x ∉ s, p x = 0 :=
by haveI := classical.dec_pred (λ (x : α), x ∈ s);
   simp [mem_supported, set.subset_def, not_imp_comm]

lemma single_mem_supported {s : set α} {a : α} (b : M) (h : a ∈ s) :
  single a b ∈ supported M R s :=
set.subset.trans support_single_subset (finset.singleton_subset_set_iff.2 h)

lemma supported_eq_span_single (s : set α) :
  supported R R s = span R ((λ i, single i 1) '' s) :=
begin
  refine (span_eq_of_le _ _ (set_like.le_def.2 $ λ l hl, _)).symm,
  { rintro _ ⟨_, hp, rfl ⟩ , exact single_mem_supported R 1 hp },
  { rw ← l.sum_single,
    refine sum_mem _ (λ i il, _),
    convert @smul_mem R (α →₀ R) _ _ _ _ (single i 1) (l i) _,
    { simp },
    apply subset_span,
    apply set.mem_image_of_mem _ (hl il) }
end

variables (M R)

/-- Interpret `finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`. -/
def restrict_dom (s : set α) : (α →₀ M) →ₗ supported M R s :=
linear_map.cod_restrict _
  { to_fun := filter (∈ s),
    map_add' := λ l₁ l₂, filter_add,
    map_smul' := λ a l, filter_smul }
  (λ l, (mem_supported' _ _).2 $ λ x, filter_apply_neg (∈ s) l)

variables {M R}

section
@[simp] theorem restrict_dom_apply (s : set α) (l : α →₀ M) :
  ((restrict_dom M R s : (α →₀ M) →ₗ supported M R s) l : α →₀ M) = finsupp.filter (∈ s) l := rfl
end

theorem restrict_dom_comp_subtype (s : set α) :
  (restrict_dom M R s).comp (submodule.subtype _) = linear_map.id :=
begin
  ext l a,
  by_cases a ∈ s; simp [h],
  exact ((mem_supported' R l.1).1 l.2 a h).symm
end

theorem range_restrict_dom (s : set α) :
  (restrict_dom M R s).range = ⊤ :=
range_eq_top.2 $ function.right_inverse.surjective $
  linear_map.congr_fun (restrict_dom_comp_subtype s)

theorem supported_mono {s t : set α} (st : s ⊆ t) :
  supported M R s ≤ supported M R t :=
λ l h, set.subset.trans h st

@[simp] theorem supported_empty : supported M R (∅ : set α) = ⊥ :=
eq_bot_iff.2 $ λ l h, (submodule.mem_bot R).2 $
by ext; simp [*, mem_supported'] at *

@[simp] theorem supported_univ : supported M R (set.univ : set α) = ⊤ :=
eq_top_iff.2 $ λ l _, set.subset_univ _

theorem supported_Union {δ : Type*} (s : δ → set α) :
  supported M R (⋃ i, s i) = ⨆ i, supported M R (s i) :=
begin
  refine le_antisymm _ (supr_le $ λ i, supported_mono $ set.subset_Union _ _),
  haveI := classical.dec_pred (λ x, x ∈ (⋃ i, s i)),
  suffices : ((submodule.subtype $ supported M R (⋃ i, s i))
    .comp (restrict_dom M R (⋃ i, s i))).range ≤ ⨆ i, supported M R (s i),
  { rwa [linear_map.range_comp, range_restrict_dom, map_top, range_subtype] at this },
  rw [range_le_iff_comap, eq_top_iff],
  rintro l ⟨⟩,
  apply finsupp.induction l, {exact zero_mem _},
  refine λ x a l hl a0, add_mem _ _,
  by_cases (∃ i, x ∈ s i); simp [h],
  { cases h with i hi,
    exact le_supr (λ i, supported M R (s i)) i (single_mem_supported R _ hi) }
end

theorem supported_union (s t : set α) :
  supported M R (s ∪ t) = supported M R s ⊔ supported M R t :=
by erw [set.union_eq_Union, supported_Union, supr_bool_eq]; refl

theorem supported_Inter {ι : Type*} (s : ι → set α) :
  supported M R (⋂ i, s i) = ⨅ i, supported M R (s i) :=
submodule.ext $ λ x, by simp [mem_supported, subset_Inter_iff]

theorem supported_inter (s t : set α) :
  supported M R (s ∩ t) = supported M R s ⊓ supported M R t :=
by rw [set.inter_eq_Inter, supported_Inter, infi_bool_eq]; refl

theorem disjoint_supported_supported {s t : set α} (h : disjoint s t) :
  disjoint (supported M R s) (supported M R t) :=
disjoint_iff.2 $ by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]

theorem disjoint_supported_supported_iff [nontrivial M] {s t : set α} :
  disjoint (supported M R s) (supported M R t) ↔ disjoint s t :=
begin
  refine ⟨λ h x hx, _, disjoint_supported_supported⟩,
  rcases exists_ne (0 : M) with ⟨y, hy⟩,
  have := h ⟨single_mem_supported R y hx.1, single_mem_supported R y hx.2⟩,
  rw [mem_bot, single_eq_zero] at this,
  exact hy this
end

/-- Interpret `finsupp.restrict_support_equiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
def supported_equiv_finsupp (s : set α) : (supported M R s) ≃ₗ[R] (s →₀ M) :=
begin
  let F : (supported M R s) ≃ (s →₀ M) := restrict_support_equiv s M,
  refine F.to_linear_equiv _,
  have : (F : (supported M R s) → (↥s →₀ M)) = ((lsubtype_domain s : (α →₀ M) →ₗ[R] (s →₀ M)).comp
    (submodule.subtype (supported M R s))) := rfl,
  rw this,
  exact linear_map.is_linear _
end

section lsum

variables (S) [module S N] [smul_comm_class R S N]

/-- Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from `α →₀ M` to
`N` using `finsupp.sum`. This is an upgraded version of `finsupp.lift_add_hom`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
def lsum : (α → M →ₗ[R] N) ≃ₗ[S] ((α →₀ M) →ₗ[R] N) :=
{ to_fun := λ F, {
    to_fun := λ d, d.sum (λ i, F i),
    map_add' := (lift_add_hom (λ x, (F x).to_add_monoid_hom)).map_add,
    map_smul' := λ c f, by simp [sum_smul_index', smul_sum] },
  inv_fun := λ F x, F.comp (lsingle x),
  left_inv := λ F, by { ext x y, simp },
  right_inv := λ F, by { ext x y, simp },
  map_add' := λ F G, by { ext x y, simp },
  map_smul' := λ F G, by { ext x y, simp } }

@[simp] lemma coe_lsum (f : α → M →ₗ[R] N) : (lsum S f : (α →₀ M) → N) = λ d, d.sum (λ i, f i) :=
rfl

theorem lsum_apply (f : α → M →ₗ[R] N) (l : α →₀ M) :
  finsupp.lsum S f l = l.sum (λ b, f b) := rfl

theorem lsum_single (f : α → M →ₗ[R] N) (i : α) (m : M) :
  finsupp.lsum S f (finsupp.single i m) = f i m :=
finsupp.sum_single_index (f i).map_zero

theorem lsum_symm_apply (f : (α →₀ M) →ₗ[R] N) (x : α) :
  (lsum S).symm f x = f.comp (lsingle x) := rfl

end lsum

section
variables (M) (R) (X : Type*)

/--
A slight rearrangement from `lsum` gives us
the bijection underlying the free-forgetful adjunction for R-modules.
-/
noncomputable def lift : (X → M) ≃+ ((X →₀ R) →ₗ[R] M) :=
(add_equiv.arrow_congr (equiv.refl X) (ring_lmap_equiv_self R M ℕ).to_add_equiv.symm).trans
  (lsum _ : _ ≃ₗ[ℕ] _).to_add_equiv

@[simp]
lemma lift_symm_apply (f) (x) : ((lift M R X).symm f) x = f (single x 1) :=
rfl
@[simp]
lemma lift_apply (f) (g) :
  ((lift M R X) f) g = g.sum (λ x r, r • f x) :=
rfl

end

section lmap_domain
variables {α' : Type*} {α'' : Type*} (M R)

/-- Interpret `finsupp.map_domain` as a linear map. -/
def lmap_domain (f : α → α') : (α →₀ M) →ₗ[R] (α' →₀ M) :=
{ to_fun := map_domain f, map_add' := λ a b, map_domain_add, map_smul' := map_domain_smul }

@[simp] theorem lmap_domain_apply (f : α → α') (l : α →₀ M) :
  (lmap_domain M R f : (α →₀ M) →ₗ[R] (α' →₀ M)) l = map_domain f l := rfl

@[simp] theorem lmap_domain_id : (lmap_domain M R id : (α →₀ M) →ₗ[R] α →₀ M) = linear_map.id :=
linear_map.ext $ λ l, map_domain_id

theorem lmap_domain_comp (f : α → α') (g : α' → α'') :
  lmap_domain M R (g ∘ f) = (lmap_domain M R g).comp (lmap_domain M R f) :=
linear_map.ext $ λ l, map_domain_comp

theorem supported_comap_lmap_domain (f : α → α') (s : set α') :
  supported M R (f ⁻¹' s) ≤ (supported M R s).comap (lmap_domain M R f) :=
λ l (hl : ↑l.support ⊆ f ⁻¹' s),
show ↑(map_domain f l).support ⊆ s, begin
  rw [← set.image_subset_iff, ← finset.coe_image] at hl,
  exact set.subset.trans map_domain_support hl
end

theorem lmap_domain_supported [nonempty α] (f : α → α') (s : set α) :
  (supported M R s).map (lmap_domain M R f) = supported M R (f '' s) :=
begin
  inhabit α,
  refine le_antisymm (map_le_iff_le_comap.2 $
    le_trans (supported_mono $ set.subset_preimage_image _ _)
       (supported_comap_lmap_domain _ _ _ _)) _,
  intros l hl,
  refine ⟨(lmap_domain M R (function.inv_fun_on f s) : (α' →₀ M) →ₗ α →₀ M) l, λ x hx, _, _⟩,
  { rcases finset.mem_image.1 (map_domain_support hx) with ⟨c, hc, rfl⟩,
    exact function.inv_fun_on_mem (by simpa using hl hc) },
  { rw [← linear_map.comp_apply, ← lmap_domain_comp],
    refine (map_domain_congr $ λ c hc, _).trans map_domain_id,
    exact function.inv_fun_on_eq (by simpa using hl hc) }
end

theorem lmap_domain_disjoint_ker (f : α → α') {s : set α}
  (H : ∀ a b ∈ s, f a = f b → a = b) :
  disjoint (supported M R s) (lmap_domain M R f).ker :=
begin
  rintro l ⟨h₁, h₂⟩,
  rw [set_like.mem_coe, mem_ker, lmap_domain_apply, map_domain] at h₂,
  simp, ext x,
  haveI := classical.dec_pred (λ x, x ∈ s),
  by_cases xs : x ∈ s,
  { have : finsupp.sum l (λ a, finsupp.single (f a)) (f x) = 0, {rw h₂, refl},
    rw [finsupp.sum_apply, finsupp.sum, finset.sum_eq_single x] at this,
    { simpa [finsupp.single_apply] },
    { intros y hy xy, simp [mt (H _ _ (h₁ hy) xs) xy] },
    { simp {contextual := tt} } },
  { by_contra h, exact xs (h₁ $ finsupp.mem_support_iff.2 h) }
end

end lmap_domain

section total
variables (α) {α' : Type*} (M) {M' : Type*} (R)
          [add_comm_monoid M'] [module R M']
          (v : α → M) {v' : α' → M'}

/-- Interprets (l : α →₀ R) as linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
protected def total : (α →₀ R) →ₗ[R] M := finsupp.lsum ℕ (λ i, linear_map.id.smul_right (v i))

variables {α M v}

theorem total_apply (l : α →₀ R) :
  finsupp.total α M R v l = l.sum (λ i a, a • v i) := rfl

theorem total_apply_of_mem_supported {l : α →₀ R} {s : finset α}
  (hs : l ∈ supported R R (↑s : set α)) :
  finsupp.total α M R v l = s.sum (λ i, l i • v i) :=
finset.sum_subset hs $ λ x _ hxg, show l x • v x = 0, by rw [not_mem_support_iff.1 hxg, zero_smul]

@[simp] theorem total_single (c : R) (a : α) :
  finsupp.total α M R v (single a c) = c • (v a) :=
by simp [total_apply, sum_single_index]

theorem total_unique [unique α] (l : α →₀ R) (v) :
  finsupp.total α M R v l = l (default α) • v (default α) :=
by rw [← total_single, ← unique_single l]

lemma total_surjective (h : function.surjective v) : function.surjective (finsupp.total α M R v) :=
begin
  intro x,
  obtain ⟨y, hy⟩ := h x,
  exact ⟨finsupp.single y 1, by simp [hy]⟩
end

theorem total_range (h : function.surjective v) : (finsupp.total α M R v).range = ⊤ :=
range_eq_top.2 $ total_surjective R h

/-- Any module is a quotient of a free module. This is stated as surjectivity of
`finsupp.total M M R id : (M →₀ R) →ₗ[R] M`. -/
lemma total_id_surjective (M) [add_comm_monoid M] [module R M] :
  function.surjective (finsupp.total M M R id) :=
total_surjective R function.surjective_id

lemma range_total : (finsupp.total α M R v).range = span R (range v) :=
begin
  ext x,
  split,
  { intros hx,
    rw [linear_map.mem_range] at hx,
    rcases hx with ⟨l, hl⟩,
    rw ← hl,
    rw finsupp.total_apply,
    unfold finsupp.sum,
    apply sum_mem (span R (range v)),
    exact λ i hi, submodule.smul_mem _ _ (subset_span (mem_range_self i)) },
  { apply span_le.2,
    intros x hx,
    rcases hx with ⟨i, hi⟩,
    rw [set_like.mem_coe, linear_map.mem_range],
    use finsupp.single i 1,
    simp [hi] }
end

theorem lmap_domain_total (f : α → α') (g : M →ₗ[R] M') (h : ∀ i, g (v i) = v' (f i)) :
  (finsupp.total α' M' R v').comp (lmap_domain R R f) = g.comp (finsupp.total α M R v) :=
by ext l; simp [total_apply, finsupp.sum_map_domain_index, add_smul, h]

theorem total_emb_domain (f : α ↪ α') (l : α →₀ R) :
  (finsupp.total α' M' R v') (emb_domain f l) = (finsupp.total α M' R (v' ∘ f)) l :=
by simp [total_apply, finsupp.sum, support_emb_domain, emb_domain_apply]

theorem total_map_domain (f : α → α') (hf : function.injective f) (l : α →₀ R) :
  (finsupp.total α' M' R v') (map_domain f l) = (finsupp.total α M' R (v' ∘ f)) l :=
begin
  have : map_domain f l = emb_domain ⟨f, hf⟩ l,
  { rw emb_domain_eq_map_domain ⟨f, hf⟩,
    refl },
  rw this,
  apply total_emb_domain R ⟨f, hf⟩ l
end

/-- A version of `finsupp.range_total` which is useful for going in the other direction -/
theorem span_eq_range_total (s : set M) :
  span R s = (finsupp.total s M R coe).range :=
by rw [range_total, subtype.range_coe_subtype, set.set_of_mem_eq]

theorem mem_span_iff_total (s : set M) (x : M) :
  x ∈ span R s ↔ ∃ l : s →₀ R, finsupp.total s M R coe l = x :=
(set_like.ext_iff.1 $ span_eq_range_total _ _) x

theorem span_image_eq_map_total (s : set α):
  span R (v '' s) = submodule.map (finsupp.total α M R v) (supported R R s) :=
begin
  apply span_eq_of_le,
  { intros x hx,
    rw set.mem_image at hx,
    apply exists.elim hx,
    intros i hi,
    exact ⟨_, finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩ },
  { refine map_le_iff_le_comap.2 (λ z hz, _),
    have : ∀i, z i • v i ∈ span R (v '' s),
    { intro c,
      haveI := classical.dec_pred (λ x, x ∈ s),
      by_cases c ∈ s,
      { exact smul_mem _ _ (subset_span (set.mem_image_of_mem _ h)) },
      { simp [(finsupp.mem_supported' R _).1 hz _ h] } },
    refine sum_mem _ _, simp [this] }
end

theorem mem_span_image_iff_total {s : set α} {x : M} :
  x ∈ span R (v '' s) ↔ ∃ l ∈ supported R R s, finsupp.total α M R v l = x :=
by { rw span_image_eq_map_total, simp, }

@[simp] lemma total_fin_zero (f : fin 0 → M) :
  finsupp.total (fin 0) M R f = 0 :=
by { ext i, apply fin_zero_elim i }

variables (α) (M) (v)

/-- `finsupp.total_on M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : set α` of indices.
-/
protected def total_on (s : set α) : supported R R s →ₗ[R] span R (v '' s) :=
linear_map.cod_restrict _ ((finsupp.total _ _ _ v).comp (submodule.subtype (supported R R s))) $
  λ ⟨l, hl⟩, (mem_span_image_iff_total _).2 ⟨l, hl, rfl⟩

variables {α} {M} {v}

theorem total_on_range (s : set α) : (finsupp.total_on α M R v s).range = ⊤ :=
begin
  rw [finsupp.total_on, linear_map.range_eq_map, linear_map.map_cod_restrict,
    ← linear_map.range_le_iff_comap, range_subtype, map_top, linear_map.range_comp, range_subtype],
  exact (span_image_eq_map_total _ _).le
end

theorem total_comp (f : α' → α) :
  (finsupp.total α' M R (v ∘ f)) = (finsupp.total α M R v).comp (lmap_domain R R f) :=
by { ext, simp [total_apply] }

lemma total_comap_domain
 (f : α → α') (l : α' →₀ R) (hf : set.inj_on f (f ⁻¹' ↑l.support)) :
 finsupp.total α M R v (finsupp.comap_domain f l hf) =
   (l.support.preimage f hf).sum (λ i, (l (f i)) • (v i)) :=
by rw finsupp.total_apply; refl

lemma total_on_finset
  {s : finset α} {f : α → R} (g : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s):
  finsupp.total α M R g (finsupp.on_finset s f hf) =
    finset.sum s (λ (x : α), f x • g x) :=
begin
  simp only [finsupp.total_apply, finsupp.sum, finsupp.on_finset_apply, finsupp.support_on_finset],
  rw finset.sum_filter_of_ne,
  intros x hx h,
  contrapose! h,
  simp [h],
end

end total

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `finsupp.dom_congr` as a `linear_equiv`.-/
protected def dom_lcongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) :
  (α₁ →₀ M) ≃ₗ[R] (α₂ →₀ M) :=
(finsupp.dom_congr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).to_linear_equiv $
by simpa only [equiv_map_domain_eq_map_domain, dom_congr_apply]
  using (lmap_domain M R e).map_smul

@[simp]
lemma dom_lcongr_apply {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (v : α₁ →₀ M) :
  (finsupp.dom_lcongr e : _ ≃ₗ[R] _) v = finsupp.dom_congr e v :=
rfl

@[simp]
lemma dom_lcongr_refl : finsupp.dom_lcongr (equiv.refl α) = linear_equiv.refl R (α →₀ M) :=
linear_equiv.ext $ λ _, equiv_map_domain_refl _

lemma dom_lcongr_trans {α₁ α₂ α₃ : Type*} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) :
  (finsupp.dom_lcongr f).trans (finsupp.dom_lcongr f₂) =
    (finsupp.dom_lcongr (f.trans f₂) : (_ →₀ M) ≃ₗ[R] _) :=
linear_equiv.ext $ λ _, (equiv_map_domain_trans _ _ _).symm

@[simp]
lemma dom_lcongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) :
  ((finsupp.dom_lcongr f).symm : (_ →₀ M) ≃ₗ[R] _) = finsupp.dom_lcongr f.symm :=
linear_equiv.ext $ λ x, rfl

@[simp] theorem dom_lcongr_single {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
  (finsupp.dom_lcongr e : _ ≃ₗ[R] _) (finsupp.single i m) = finsupp.single (e i) m :=
by simp [finsupp.dom_lcongr, finsupp.dom_congr, equiv_map_domain_single]

/-- An equivalence of sets induces a linear equivalence of `finsupp`s supported on those sets. -/
noncomputable def congr {α' : Type*} (s : set α) (t : set α') (e : s ≃ t) :
  supported M R s ≃ₗ[R] supported M R t :=
begin
  haveI := classical.dec_pred (λ x, x ∈ s),
  haveI := classical.dec_pred (λ x, x ∈ t),
  refine linear_equiv.trans (finsupp.supported_equiv_finsupp s)
      (linear_equiv.trans _ (finsupp.supported_equiv_finsupp t).symm),
  exact finsupp.dom_lcongr e
end

/-- `finsupp.map_range` as a `linear_map`. -/
@[simps]
def map_range.linear_map (f : M →ₗ[R] N) : (α →₀ M) →ₗ[R] (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_smul' := λ c v, map_range_smul c v (f.map_smul c),
  ..map_range.add_monoid_hom f.to_add_monoid_hom }

@[simp]
lemma map_range.linear_map_id :
  map_range.linear_map linear_map.id = (linear_map.id : (α →₀ M) →ₗ[R] _):=
linear_map.ext map_range_id

lemma map_range.linear_map_comp (f : N →ₗ[R] P) (f₂ : M →ₗ[R] N) :
  (map_range.linear_map (f.comp f₂) : (α →₀ _) →ₗ[R] _) =
    (map_range.linear_map f).comp (map_range.linear_map f₂) :=
linear_map.ext $ map_range_comp _ _ _ _ _

/-- `finsupp.map_range` as a `linear_equiv`. -/
@[simps apply]
def map_range.linear_equiv (e : M ≃ₗ[R] N) : (α →₀ M) ≃ₗ[R] (α →₀ N) :=
{ to_fun := map_range e e.map_zero,
  inv_fun := map_range e.symm e.symm.map_zero,
  ..map_range.linear_map e.to_linear_map,
  ..map_range.add_equiv e.to_add_equiv}

@[simp]
lemma map_range.linear_equiv_refl :
  map_range.linear_equiv (linear_equiv.refl R M) = linear_equiv.refl R (α →₀ M) :=
linear_equiv.ext map_range_id

lemma map_range.linear_equiv_trans (f : M ≃ₗ[R] N) (f₂ : N ≃ₗ[R] P) :
  (map_range.linear_equiv (f.trans f₂) : linear_equiv R (α →₀ _) _) =
    (map_range.linear_equiv f).trans (map_range.linear_equiv f₂) :=
linear_equiv.ext $ map_range_comp _ _ _ _ _

@[simp]
lemma map_range.linear_equiv_symm (f : M ≃ₗ[R] N) :
  ((map_range.linear_equiv f).symm : (α →₀ _) ≃ₗ[R] _) = map_range.linear_equiv f.symm :=
linear_equiv.ext $ λ x, rfl

/-- An equivalence of domain and a linear equivalence of codomain induce a linear equivalence of the
corresponding finitely supported functions. -/
def lcongr {ι κ : Sort*} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) : (ι →₀ M) ≃ₗ[R] (κ →₀ N) :=
(finsupp.dom_lcongr e₁).trans (map_range.linear_equiv e₂)

@[simp] theorem lcongr_single {ι κ : Sort*} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (i : ι) (m : M) :
  lcongr e₁ e₂ (finsupp.single i m) = finsupp.single (e₁ i) (e₂ m) :=
by simp [lcongr]

@[simp] lemma lcongr_apply_apply {ι κ : Sort*} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (f : ι →₀ M) (k : κ) :
  lcongr e₁ e₂ f k = e₂ (f (e₁.symm k)) :=
begin
  apply finsupp.induction_linear f,
  { simp, },
  { intros f g hf hg, simp [map_add, hf, hg], },
  { intros i m,
    simp only [finsupp.lcongr_single],
    simp only [finsupp.single, equiv.eq_symm_apply, finsupp.coe_mk],
    split_ifs; simp, },
end

theorem lcongr_symm_single {ι κ : Sort*} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (k : κ) (n : N) :
  (lcongr e₁ e₂).symm (finsupp.single k n) = finsupp.single (e₁.symm k) (e₂.symm n) :=
begin
  apply_fun lcongr e₁ e₂ using (lcongr e₁ e₂).injective,
  simp,
end

@[simp] lemma lcongr_symm {ι κ : Sort*} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) :
  (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm :=
begin
  ext f i,
  simp only [equiv.symm_symm, finsupp.lcongr_apply_apply],
  apply finsupp.induction_linear f,
  { simp, },
  { intros f g hf hg, simp [map_add, hf, hg], },
  { intros k m,
    simp only [finsupp.lcongr_symm_single],
    simp only [finsupp.single, equiv.symm_apply_eq, finsupp.coe_mk],
    split_ifs; simp, },
end

section sum

variables (R)

/-- The linear equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `linear_equiv` version of `finsupp.sum_finsupp_equiv_prod_finsupp`. -/
@[simps apply symm_apply] def sum_finsupp_lequiv_prod_finsupp {α β : Type*} :
  ((α ⊕ β) →₀ M) ≃ₗ[R] (α →₀ M) × (β →₀ M) :=
{ map_smul' :=
    by { intros, ext;
          simp only [add_equiv.to_fun_eq_coe, prod.smul_fst, prod.smul_snd, smul_apply,
              snd_sum_finsupp_add_equiv_prod_finsupp, fst_sum_finsupp_add_equiv_prod_finsupp] },
  .. sum_finsupp_add_equiv_prod_finsupp }

lemma fst_sum_finsupp_lequiv_prod_finsupp {α β : Type*}
  (f : (α ⊕ β) →₀ M) (x : α) :
  (sum_finsupp_lequiv_prod_finsupp R f).1 x = f (sum.inl x) :=
rfl

lemma snd_sum_finsupp_lequiv_prod_finsupp {α β : Type*}
  (f : (α ⊕ β) →₀ M) (y : β) :
  (sum_finsupp_lequiv_prod_finsupp R f).2 y = f (sum.inr y) :=
rfl

lemma sum_finsupp_lequiv_prod_finsupp_symm_inl {α β : Type*}
  (fg : (α →₀ M) × (β →₀ M)) (x : α) :
  ((sum_finsupp_lequiv_prod_finsupp R).symm fg) (sum.inl x) = fg.1 x :=
rfl

lemma sum_finsupp_lequiv_prod_finsupp_symm_inr {α β : Type*}
  (fg : (α →₀ M) × (β →₀ M)) (y : β) :
  ((sum_finsupp_lequiv_prod_finsupp R).symm fg) (sum.inr y) = fg.2 y :=
rfl

end sum

section sigma

variables {η : Type*} [fintype η] {ιs : η → Type*} [has_zero α]
variables (R)

/-- On a `fintype η`, `finsupp.split` is a linear equivalence between
`(Σ (j : η), ιs j) →₀ M` and `Π j, (ιs j →₀ M)`.

This is the `linear_equiv` version of `finsupp.sigma_finsupp_add_equiv_pi_finsupp`. -/
noncomputable def sigma_finsupp_lequiv_pi_finsupp
  {M : Type*} {ιs : η → Type*} [add_comm_monoid M] [module R M] :
  ((Σ j, ιs j) →₀ M) ≃ₗ[R] Π j, (ιs j →₀ M) :=
{ map_smul' := λ c f, by { ext, simp },
  .. sigma_finsupp_add_equiv_pi_finsupp }

@[simp] lemma sigma_finsupp_lequiv_pi_finsupp_apply
  {M : Type*} {ιs : η → Type*} [add_comm_monoid M] [module R M]
  (f : (Σ j, ιs j) →₀ M) (j i) :
  sigma_finsupp_lequiv_pi_finsupp R f j i = f ⟨j, i⟩ := rfl

@[simp] lemma sigma_finsupp_lequiv_pi_finsupp_symm_apply
  {M : Type*} {ιs : η → Type*} [add_comm_monoid M] [module R M]
  (f : Π j, (ιs j →₀ M)) (ji) :
  (finsupp.sigma_finsupp_lequiv_pi_finsupp R).symm f ji = f ji.1 ji.2 := rfl

end sigma

section prod

/-- The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `linear_equiv` version of `finsupp.finsupp_prod_equiv`. -/
noncomputable def finsupp_prod_lequiv {α β : Type*} (R : Type*) {M : Type*}
  [semiring R] [add_comm_monoid M] [module R M] :
  (α × β →₀ M) ≃ₗ[R] (α →₀ β →₀ M) :=
{ map_add' := λ f g, by { ext, simp [finsupp_prod_equiv, curry_apply] },
  map_smul' := λ c f, by { ext, simp [finsupp_prod_equiv, curry_apply] },
  .. finsupp_prod_equiv }

@[simp] lemma finsupp_prod_lequiv_apply {α β R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M] (f : α × β →₀ M) (x y) :
  finsupp_prod_lequiv R f x y = f (x, y) :=
by rw [finsupp_prod_lequiv, linear_equiv.coe_mk, finsupp_prod_equiv, finsupp.curry_apply]

@[simp] lemma finsupp_prod_lequiv_symm_apply {α β R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M] (f : α →₀ β →₀ M) (xy) :
  (finsupp_prod_lequiv R).symm f xy = f xy.1 xy.2 :=
by conv_rhs
  { rw [← (finsupp_prod_lequiv R).apply_symm_apply f, finsupp_prod_lequiv_apply, prod.mk.eta] }

end prod

end finsupp

variables {R : Type*} {M : Type*} {N : Type*}
variables [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]

lemma submodule.finsupp_sum_mem {ι β : Type*} [has_zero β] (S : submodule R M) (f : ι →₀ β)
  (g : ι → β → M) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.sum g ∈ S :=
S.to_add_submonoid.finsupp_sum_mem f g h

lemma linear_map.map_finsupp_total
  (f : M →ₗ[R] N) {ι : Type*} {g : ι → M} (l : ι →₀ R) :
  f (finsupp.total ι M R g l) = finsupp.total ι N R (f ∘ g) l :=
by simp only [finsupp.total_apply, finsupp.total_apply, finsupp.sum, f.map_sum, f.map_smul]

lemma submodule.exists_finset_of_mem_supr
  {ι : Sort*} (p : ι → submodule R M) {m : M} (hm : m ∈ ⨆ i, p i) :
  ∃ s : finset ι, m ∈ ⨆ i ∈ s, p i :=
begin
  obtain ⟨f, hf, rfl⟩ : ∃ f ∈ finsupp.supported R R (⋃ i, ↑(p i)), finsupp.total M M R id f = m,
  { have aux : (id : M → M) '' (⋃ (i : ι), ↑(p i)) = (⋃ (i : ι), ↑(p i)) := set.image_id _,
    rwa [supr_eq_span, ← aux, finsupp.mem_span_image_iff_total R] at hm },
  let t : finset M := f.support,
  have ht : ∀ x : {x // x ∈ t}, ∃ i, ↑x ∈ p i,
  { intros x,
    rw finsupp.mem_supported at hf,
    specialize hf x.2,
    rwa set.mem_Union at hf },
  choose g hg using ht,
  let s : finset ι := finset.univ.image g,
  use s,
  simp only [mem_supr, supr_le_iff],
  assume N hN,
  rw [finsupp.total_apply, finsupp.sum, ← set_like.mem_coe],
  apply N.sum_mem,
  assume x hx,
  apply submodule.smul_mem,
  let i : ι := g ⟨x, hx⟩,
  have hi : i ∈ s, { rw finset.mem_image, exact ⟨⟨x, hx⟩, finset.mem_univ _, rfl⟩ },
  exact hN i hi (hg _),
end

lemma mem_span_finset {s : finset M} {x : M} :
  x ∈ span R (↑s : set M) ↔ ∃ f : M → R, ∑ i in s, f i • i = x :=
⟨λ hx, let ⟨v, hvs, hvx⟩ := (finsupp.mem_span_image_iff_total _).1
    (show x ∈ span R (id '' (↑s : set M)), by rwa set.image_id) in
  ⟨v, hvx ▸ (finsupp.total_apply_of_mem_supported _ hvs).symm⟩,
λ ⟨f, hf⟩, hf ▸ sum_mem _ (λ i hi, smul_mem _ _ $ subset_span hi)⟩

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses `finsupp.sum`. -/
lemma mem_span_set {m : M} {s : set M} :
  m ∈ submodule.span R s ↔ ∃ c : M →₀ R, (c.support : set M) ⊆ s ∧ c.sum (λ mi r, r • mi) = m :=
begin
  conv_lhs { rw ←set.image_id s },
  simp_rw ←exists_prop,
  exact finsupp.mem_span_image_iff_total R,
end

/-- If `subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`. -/
@[simps]
def module.subsingleton_equiv (R M ι: Type*) [semiring R] [subsingleton R] [add_comm_monoid M]
  [module R M] : M ≃ₗ[R] ι →₀ R :=
{ to_fun := λ m, 0,
  inv_fun := λ f, 0,
  left_inv := λ m, by { letI := module.subsingleton R M, simp only [eq_iff_true_of_subsingleton] },
  right_inv := λ f, by simp only [eq_iff_true_of_subsingleton],
  map_add' := λ m n, (add_zero 0).symm,
  map_smul' := λ r m, (smul_zero r).symm }

namespace linear_map

variables {R M} {α : Type*}
open finsupp function

/-- A surjective linear map to finitely supported functions has a splitting. -/
-- See also `linear_map.splitting_of_fun_on_fintype_surjective`
def splitting_of_finsupp_surjective (f : M →ₗ[R] (α →₀ R)) (s : surjective f) : (α →₀ R) →ₗ[R] M :=
finsupp.lift _ _ _ (λ x : α, (s (finsupp.single x 1)).some)

lemma splitting_of_finsupp_surjective_splits (f : M →ₗ[R] (α →₀ R)) (s : surjective f) :
  f.comp (splitting_of_finsupp_surjective f s) = linear_map.id :=
begin
  ext x y,
  dsimp [splitting_of_finsupp_surjective],
  congr,
  rw [sum_single_index, one_smul],
  { exact (s (finsupp.single x 1)).some_spec, },
  { rw zero_smul, },
end

lemma left_inverse_splitting_of_finsupp_surjective (f : M →ₗ[R] (α →₀ R)) (s : surjective f) :
  left_inverse f (splitting_of_finsupp_surjective f s) :=
λ g, linear_map.congr_fun (splitting_of_finsupp_surjective_splits f s) g

lemma splitting_of_finsupp_surjective_injective (f : M →ₗ[R] (α →₀ R)) (s : surjective f) :
  injective (splitting_of_finsupp_surjective f s) :=
(left_inverse_splitting_of_finsupp_surjective f s).injective

/-- A surjective linear map to functions on a finite type has a splitting. -/
-- See also `linear_map.splitting_of_finsupp_surjective`
def splitting_of_fun_on_fintype_surjective [fintype α] (f : M →ₗ[R] (α → R)) (s : surjective f) :
  (α → R) →ₗ[R] M :=
(finsupp.lift _ _ _ (λ x : α, (s (finsupp.single x 1)).some)).comp
  (@linear_equiv_fun_on_fintype R R α _ _ _ _).symm.to_linear_map

lemma splitting_of_fun_on_fintype_surjective_splits
  [fintype α] (f : M →ₗ[R] (α → R)) (s : surjective f) :
  f.comp (splitting_of_fun_on_fintype_surjective f s) = linear_map.id :=
begin
  ext x y,
  dsimp [splitting_of_fun_on_fintype_surjective],
  rw [linear_equiv_fun_on_fintype_symm_single, finsupp.sum_single_index, one_smul,
    linear_map.id_coe, id_def,
    (s (finsupp.single x 1)).some_spec, finsupp.single_eq_pi_single],
  rw [zero_smul],
end

lemma left_inverse_splitting_of_fun_on_fintype_surjective
  [fintype α] (f : M →ₗ[R] (α → R)) (s : surjective f) :
  left_inverse f (splitting_of_fun_on_fintype_surjective f s) :=
λ g, linear_map.congr_fun (splitting_of_fun_on_fintype_surjective_splits f s) g

lemma splitting_of_fun_on_fintype_surjective_injective
  [fintype α] (f : M →ₗ[R] (α → R)) (s : surjective f) :
  injective (splitting_of_fun_on_fintype_surjective f s) :=
(left_inverse_splitting_of_fun_on_fintype_surjective f s).injective

end linear_map
