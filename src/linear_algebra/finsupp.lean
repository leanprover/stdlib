/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.finsupp.basic
import linear_algebra.basic

/-!
# Properties of the semimodule `α →₀ M`

Given an `R`-semimodule `M`, the `R`-semimodule structure on `α →₀ M` is defined in
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

function with finite support, semimodule, linear algebra
-/

noncomputable theory

open set linear_map submodule

open_locale classical big_operators

namespace finsupp

variables {α : Type*} {M : Type*} {N : Type*} {R : Type*} {S : Type*}
variables [semiring R] [semiring S] [add_comm_monoid M] [semimodule R M]
variables [add_comm_monoid N] [semimodule R N]

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
⟨subtype_domain (λx, x ∈ s), assume a b, subtype_domain_add, assume c a, ext $ assume a, rfl⟩

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
  simp only [(ker_comp _ _).symm, eq_top_iff, le_def', mem_ker, comap_infi, mem_infi],
  assume b hb a₂ h₂,
  have : a₁ ≠ a₂ := assume eq, h ⟨h₁, eq.symm ▸ h₂⟩,
  exact single_eq_of_ne this
end

lemma infi_ker_lapply_le_bot : (⨅a, ker (lapply a : (α →₀ M) →ₗ[R] M)) ≤ ⊥ :=
begin
  simp only [le_def', mem_infi, mem_ker, mem_bot, lapply_apply],
  exact assume a h, finsupp.ext h
end

lemma supr_lsingle_range : (⨆a, (lsingle a : M →ₗ[R] (α →₀ M)).range) = ⊤ :=
begin
  refine (eq_top_iff.2 $ le_def'.2 $ assume f _, _),
  rw [← sum_single f],
  refine sum_mem _ (assume a ha, submodule.mem_supr_of_mem a $ set.mem_image_of_mem _ trivial)
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
    exact inf_le_right_of_le (infi_le_of_le i $ infi_le _ hit) },
  exact inf_le_left_of_le (infi_le_of_le i $ infi_le _ his)
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
  refine (span_eq_of_le _ _ (le_def'.2 $ λ l hl, _)).symm,
  { rintro _ ⟨_, hp, rfl ⟩ , exact single_mem_supported R 1 hp },
  { rw ← l.sum_single,
    refine sum_mem _ (λ i il, _),
    convert smul_mem _ (l i) (_ : single i (1 : R) ∈ _),
    { simp },
    apply_instance,
    apply_instance,
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
begin
  have := linear_map.range_comp (submodule.subtype _) (restrict_dom M R s),
  rw [restrict_dom_comp_subtype, linear_map.range_id] at this,
  exact eq_top_mono (submodule.map_mono le_top) this.symm
end

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
  suffices : ((submodule.subtype _).comp (restrict_dom M R (⋃ i, s i))).range ≤
    ⨆ i, supported M R (s i),
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

variables (S) [semimodule S N] [smul_comm_class R S N]

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
⟨map_domain f, assume a b, map_domain_add, map_domain_smul⟩

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
  rw [mem_coe, mem_ker, lmap_domain_apply, map_domain] at h₂,
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
          [add_comm_monoid M'] [semimodule R M']
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

theorem total_range (h : function.surjective v) : (finsupp.total α M R v).range = ⊤ :=
begin
  apply range_eq_top.2,
  intros x,
  apply exists.elim (h x),
  exact λ i hi, ⟨single i 1, by simp [hi]⟩
end

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
    rw [mem_coe, linear_map.mem_range],
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

theorem span_eq_map_total (s : set α):
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

theorem mem_span_iff_total {s : set α} {x : M} :
  x ∈ span R (v '' s) ↔ ∃ l ∈ supported R R s, finsupp.total α M R v l = x :=
by rw span_eq_map_total; simp

variables (α) (M) (v)

/-- `finsupp.total_on M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : set α` of indices.
-/
protected def total_on (s : set α) : supported R R s →ₗ[R] span R (v '' s) :=
linear_map.cod_restrict _ ((finsupp.total _ _ _ v).comp (submodule.subtype (supported R R s))) $
  λ ⟨l, hl⟩, (mem_span_iff_total _).2 ⟨l, hl, rfl⟩

variables {α} {M} {v}

theorem total_on_range (s : set α) : (finsupp.total_on α M R v s).range = ⊤ :=
by rw [finsupp.total_on, linear_map.range, linear_map.map_cod_restrict,
  ← linear_map.range_le_iff_comap, range_subtype, map_top, linear_map.range_comp, range_subtype];
    exact le_of_eq (span_eq_map_total _ _)

theorem total_comp (f : α' → α) :
  (finsupp.total α' M R (v ∘ f)) = (finsupp.total α M R v).comp (lmap_domain R R f) :=
begin
 ext l,
 simp [total_apply],
 rw sum_map_domain_index; simp [add_smul],
end

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

/-- An equivalence of domains induces a linear equivalence of finitely supported functions. -/
protected def dom_lcongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) :
  (α₁ →₀ M) ≃ₗ[R] (α₂ →₀ M) :=
(finsupp.dom_congr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).to_linear_equiv (lmap_domain M R e).map_smul

@[simp] theorem dom_lcongr_single {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
  (finsupp.dom_lcongr e : _ ≃ₗ[R] _) (finsupp.single i m) = finsupp.single (e i) m :=
by simp [finsupp.dom_lcongr, finsupp.dom_congr, map_domain_single]

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

/-- An equivalence of domain and a linear equivalence of codomain induce a linear equivalence of the
corresponding finitely supported functions. -/
def lcongr {ι κ : Sort*} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) : (ι →₀ M) ≃ₗ[R] (κ →₀ N) :=
(finsupp.dom_lcongr e₁).trans
{ to_fun := map_range e₂ e₂.map_zero,
  inv_fun := map_range e₂.symm e₂.symm.map_zero,
  left_inv := λ f, finsupp.induction f (by simp_rw map_range_zero) $ λ a b f ha hb ih,
    by rw [map_range_add e₂.map_add, map_range_add e₂.symm.map_add,
      map_range_single, map_range_single, e₂.symm_apply_apply, ih],
  right_inv := λ f, finsupp.induction f (by simp_rw map_range_zero) $ λ a b f ha hb ih,
    by rw [map_range_add e₂.symm.map_add, map_range_add e₂.map_add,
      map_range_single, map_range_single, e₂.apply_symm_apply, ih],
  map_add' := map_range_add e₂.map_add,
  map_smul' := λ c f, finsupp.induction f
    (by rw [smul_zero, map_range_zero, smul_zero]) $ λ a b f ha hb ih,
    by rw [smul_add, smul_single, map_range_add e₂.map_add, map_range_single, e₂.map_smul, ih,
      map_range_add e₂.map_add, smul_add, map_range_single, smul_single] }

@[simp] theorem lcongr_single {ι κ : Sort*} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N)
  (i : ι) (m : M) : lcongr e₁ e₂ (finsupp.single i m) = finsupp.single (e₁ i) (e₂ m) :=
by simp [lcongr]

end finsupp

variables {R : Type*} {M : Type*} {N : Type*}
variables [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N]

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
    rwa [supr_eq_span, ← aux, finsupp.mem_span_iff_total R] at hm },
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
  rw [finsupp.total_apply, finsupp.sum, ← submodule.mem_coe],
  apply N.sum_mem,
  assume x hx,
  apply submodule.smul_mem,
  let i : ι := g ⟨x, hx⟩,
  have hi : i ∈ s, { rw finset.mem_image, exact ⟨⟨x, hx⟩, finset.mem_univ _, rfl⟩ },
  exact hN i hi (hg _),
end

lemma mem_span_finset {s : finset M} {x : M} :
  x ∈ span R (↑s : set M) ↔ ∃ f : M → R, ∑ i in s, f i • i = x :=
⟨λ hx, let ⟨v, hvs, hvx⟩ := (finsupp.mem_span_iff_total _).1
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
  exact finsupp.mem_span_iff_total R,
end
