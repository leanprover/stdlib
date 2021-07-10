/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.subset_properties
import topology.connected
import topology.algebra.monoid
import tactic.tfae
import tactic.fin_cases

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `is_locally_constant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `locally_constant X Y` : the type of locally constant maps from `X` to `Y`
* `locally_constant.map` : push-forward of locally constant maps
* `locally_constant.comap` : pull-back of locally constant maps

-/

variables {X Y Z α : Type*} [topological_space X]

open set filter
open_locale topological_space

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def is_locally_constant (f : X → Y) : Prop := ∀ s : set Y, is_open (f ⁻¹' s)

namespace is_locally_constant

protected lemma tfae (f : X → Y) :
  tfae [is_locally_constant f,
    ∀ x, ∀ᶠ x' in 𝓝 x, f x' = f x,
    ∀ x, is_open {x' | f x' = f x},
    ∀ y, is_open (f ⁻¹' {y}),
    ∀ x, ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x] :=
begin
  tfae_have : 1 → 4, from λ h y, h {y},
  tfae_have : 4 → 3, from λ h x, h (f x),
  tfae_have : 3 → 2, from λ h x, is_open.mem_nhds (h x) rfl,
  tfae_have : 2 → 5,
  { intros h x,
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩,
    exact ⟨U, hU, hx, eq⟩ },
  tfae_have : 5 → 1,
  { intros h s,
    refine is_open_iff_forall_mem_open.2 (λ x hx, _),
    rcases h x with ⟨U, hU, hxU, eq⟩,
    exact ⟨U, λ x' hx', mem_preimage.2 $ (eq x' hx').symm ▸ hx, hU, hxU⟩ },
  tfae_finish
end

@[nontriviality] lemma of_discrete [discrete_topology X] (f : X → Y) :
  is_locally_constant f :=
λ s, is_open_discrete _

lemma is_open_fiber {f : X → Y} (hf : is_locally_constant f) (y : Y) :
  is_open {x | f x = y} :=
hf {y}

lemma is_closed_fiber {f : X → Y} (hf : is_locally_constant f) (y : Y) :
  is_closed {x | f x = y} :=
⟨hf {y}ᶜ⟩

lemma is_clopen_fiber {f : X → Y} (hf : is_locally_constant f) (y : Y) :
  is_clopen {x | f x = y} :=
⟨is_open_fiber hf _, is_closed_fiber hf _⟩

lemma iff_exists_open (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
(is_locally_constant.tfae f).out 0 4

lemma iff_eventually_eq (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∀ᶠ y in 𝓝 x, f y = f x :=
(is_locally_constant.tfae f).out 0 1

lemma exists_open {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
(iff_exists_open f).1 hf x

protected lemma eventually_eq {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∀ᶠ y in 𝓝 x, f y = f x :=
(iff_eventually_eq f).1 hf x

protected lemma continuous [topological_space Y] {f : X → Y} (hf : is_locally_constant f) :
  continuous f :=
⟨λ U hU, hf _⟩

lemma iff_continuous {_ : topological_space Y} [discrete_topology Y] (f : X → Y) :
  is_locally_constant f ↔ continuous f :=
⟨is_locally_constant.continuous, λ h s, h.is_open_preimage s (is_open_discrete _)⟩

lemma iff_continuous_bot (f : X → Y) :
  is_locally_constant f ↔ @continuous X Y _ ⊥ f :=
iff_continuous f

lemma of_constant (f : X → Y) (h : ∀ x y, f x = f y) :
  is_locally_constant f :=
(iff_eventually_eq f).2 $ λ x, eventually_of_forall $ λ x', h _ _

lemma const (y : Y) : is_locally_constant (function.const X y) :=
of_constant _ $ λ _ _, rfl

lemma comp {f : X → Y} (hf : is_locally_constant f) (g : Y → Z) :
  is_locally_constant (g ∘ f) :=
λ s, by { rw set.preimage_comp, exact hf _ }

lemma prod_mk {Y'} {f : X → Y} {f' : X → Y'} (hf : is_locally_constant f)
  (hf' : is_locally_constant f') :
  is_locally_constant (λ x, (f x, f' x)) :=
(iff_eventually_eq _).2 $ λ x, (hf.eventually_eq x).mp $ (hf'.eventually_eq x).mono $
  λ x' hf' hf, prod.ext hf hf'

lemma comp₂ {Y₁ Y₂ Z : Type*} {f : X → Y₁} {g : X → Y₂}
  (hf : is_locally_constant f) (hg : is_locally_constant g) (h : Y₁ → Y₂ → Z) :
  is_locally_constant (λ x, h (f x) (g x)) :=
(hf.prod_mk hg).comp (λ x : Y₁ × Y₂, h x.1 x.2)

lemma comp_continuous [topological_space Y] {g : Y → Z} {f : X → Y}
  (hg : is_locally_constant g) (hf : continuous f) :
  is_locally_constant (g ∘ f) :=
λ s, by { rw set.preimage_comp, exact hf.is_open_preimage _ (hg _) }

/-- A locally constant function is constant on any preconnected set. -/
lemma apply_eq_of_is_preconnected {f : X → Y} (hf : is_locally_constant f)
  {s : set X} (hs : is_preconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y :=
begin
  let U := f ⁻¹' {f y},
  suffices : x ∉ Uᶜ, from not_not.1 this,
  intro hxV,
  specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩,
  { simp only [union_compl_self, subset_univ] },
  { simpa only [inter_empty, not_nonempty_empty, inter_compl_self] using hs }
end

lemma iff_is_const [preconnected_space X] {f : X → Y} :
  is_locally_constant f ↔ ∀ x y, f x = f y :=
⟨λ h x y, h.apply_eq_of_is_preconnected is_preconnected_univ trivial trivial, of_constant _⟩

lemma range_finite [compact_space X] {f : X → Y} (hf : is_locally_constant f) :
  (set.range f).finite :=
begin
  letI : topological_space Y := ⊥,
  haveI : discrete_topology Y := ⟨rfl⟩,
  rw @iff_continuous X Y ‹_› ‹_› at hf,
  exact finite_of_is_compact_of_discrete _ (is_compact_range hf)
end

@[to_additive] lemma one [has_one Y] : is_locally_constant (1 : X → Y) := const 1

@[to_additive] lemma inv [has_inv Y] ⦃f : X → Y⦄ (hf : is_locally_constant f) :
  is_locally_constant f⁻¹ :=
hf.comp (λ x, x⁻¹)

@[to_additive]
lemma mul [has_mul Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f * g) :=
hf.comp₂ hg (*)

@[to_additive]
lemma div [has_div Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f / g) :=
hf.comp₂ hg (/)

/-- If a composition of a function `f` followed by an injection `g` is locally
constant, then the locally constant property descends to `f`. -/
lemma desc {α β : Type*} (f : X → α) (g : α → β)
  (h : is_locally_constant (g ∘ f)) (inj : function.injective g) : is_locally_constant f :=
begin
  rw (is_locally_constant.tfae f).out 0 3,
  intros a,
  have : f ⁻¹' {a} = (g ∘ f) ⁻¹' { g a },
  { ext x,
    simp only [mem_singleton_iff, function.comp_app, mem_preimage],
    exact ⟨λ h, by rw h, λ h, inj h⟩ },
  rw this,
  apply h,
end

end is_locally_constant

/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
structure locally_constant (X Y : Type*) [topological_space X] :=
(to_fun : X → Y)
(is_locally_constant : is_locally_constant to_fun)

namespace locally_constant

instance [inhabited Y] : inhabited (locally_constant X Y) :=
⟨⟨_, is_locally_constant.const (default Y)⟩⟩

instance : has_coe_to_fun (locally_constant X Y) := ⟨_, locally_constant.to_fun⟩

initialize_simps_projections locally_constant (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : locally_constant X Y) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : locally_constant X Y) = f := rfl

theorem congr_fun {f g : locally_constant X Y} (h : f = g) (x : X) : f x = g x :=
congr_arg (λ h : locally_constant X Y, h x) h

theorem congr_arg (f : locally_constant X Y) {x y : X} (h : x = y) : f x = f y :=
congr_arg (λ x : X, f x) h

theorem coe_injective : function.injective (λ (f : locally_constant X Y) (x : X), f x)
| ⟨f, hf⟩ ⟨g, hg⟩ h := have f = g, from h, by subst f

@[simp, norm_cast] theorem coe_inj {f g : locally_constant X Y} : (f : X → Y) = g ↔ f = g :=
coe_injective.eq_iff

@[ext] theorem ext ⦃f g : locally_constant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

theorem ext_iff {f g : locally_constant X Y} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

protected lemma continuous [topological_space Y] (f : locally_constant X Y) : continuous f :=
f.is_locally_constant.continuous

/-- The constant locally constant function on `X` with value `y : Y`. -/
def const (X : Type*) {Y : Type*} [topological_space X] (y : Y) :
  locally_constant X Y :=
⟨function.const X y, is_locally_constant.const _⟩

/-- The locally constant function to `fin 2` associated to a clopen set. -/
def of_clopen {X : Type*} [topological_space X] {U : set X} [∀ x, decidable (x ∈ U)]
  (hU : is_clopen U) : locally_constant X (fin 2) :=
{ to_fun := λ x, if x ∈ U then 0 else 1,
  is_locally_constant := begin
    rw (is_locally_constant.tfae (λ x, if x ∈ U then (0 : fin 2) else 1)).out 0 3,
    intros e,
    fin_cases e,
    { convert hU.1 using 1,
      ext,
      simp only [nat.one_ne_zero, mem_singleton_iff, fin.one_eq_zero_iff,
        mem_preimage, ite_eq_left_iff],
      tauto },
    { rw ← is_closed_compl_iff,
      convert hU.2,
      ext,
      simp }
  end }

@[simp] lemma of_clopen_fiber_zero {X : Type*} [topological_space X] {U : set X}
  [∀ x, decidable (x ∈ U)] (hU : is_clopen U) : of_clopen hU ⁻¹' ({0} : set (fin 2)) = U :=
begin
  ext,
  simp only [of_clopen, nat.one_ne_zero, mem_singleton_iff,
    fin.one_eq_zero_iff, coe_mk, mem_preimage, ite_eq_left_iff],
  tauto,
end

@[simp] lemma of_clopen_fiber_one {X : Type*} [topological_space X] {U : set X}
  [∀ x, decidable (x ∈ U)] (hU : is_clopen U) : of_clopen hU ⁻¹' ({1} : set (fin 2)) = Uᶜ :=
begin
  ext,
  simp only [of_clopen, nat.one_ne_zero, mem_singleton_iff, coe_mk,
    fin.zero_eq_one_iff, mem_preimage, ite_eq_right_iff,
    mem_compl_eq],
  tauto,
end

lemma locally_constant_eq_of_fiber_zero_eq {X : Type*} [topological_space X]
  (f g : locally_constant X (fin 2)) (h : f ⁻¹' ({0} : set (fin 2)) = g ⁻¹' {0}) : f = g :=
begin
  simp only [set.ext_iff, mem_singleton_iff, mem_preimage] at h,
  ext1 x,
  have := h x,
  set a := f x,
  set b := g x,
  fin_cases a; fin_cases b; finish
end

lemma range_finite [compact_space X] (f : locally_constant X Y) :
  (set.range f).finite :=
f.is_locally_constant.range_finite

lemma apply_eq_of_is_preconnected (f : locally_constant X Y) {s : set X} (hs : is_preconnected s)
  {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y :=
f.is_locally_constant.apply_eq_of_is_preconnected hs hx hy

lemma apply_eq_of_preconnected_space [preconnected_space X] (f : locally_constant X Y) (x y : X) :
  f x = f y :=
f.is_locally_constant.apply_eq_of_is_preconnected is_preconnected_univ trivial trivial

lemma eq_const [preconnected_space X] (f : locally_constant X Y) (x : X) :
  f = const X (f x) :=
ext $ λ y, apply_eq_of_preconnected_space f _ _

lemma exists_eq_const [preconnected_space X] [nonempty Y] (f : locally_constant X Y) :
  ∃ y, f = const X y :=
begin
  rcases classical.em (nonempty X) with ⟨⟨x⟩⟩|hX,
  { exact ⟨f x, f.eq_const x⟩ },
  { exact ⟨classical.arbitrary Y, ext $ λ x, (hX ⟨x⟩).elim⟩ }
end

/-- Push forward of locally constant maps under any map, by post-composition. -/
def map (f : Y → Z) : locally_constant X Y → locally_constant X Z :=
λ g, ⟨f ∘ g, λ s, by { rw set.preimage_comp, apply g.is_locally_constant }⟩

@[simp] lemma map_apply (f : Y → Z) (g : locally_constant X Y) : ⇑(map f g) = f ∘ g := rfl

@[simp] lemma map_id : @map X Y Y _ id = id := by { ext, refl }

@[simp] lemma map_comp {Y₁ Y₂ Y₃ : Type*} (g : Y₂ → Y₃) (f : Y₁ → Y₂) :
  @map X _ _ _ g ∘ map f = map (g ∘ f) := by { ext, refl }

/-- Given a locally constant function to `α → β`, construct a family of locally constant
functions with values in β indexed by α. -/
def flip {X α β : Type*} [topological_space X] (f : locally_constant X (α → β)) (a : α) :
  locally_constant X β := f.map (λ f, f a)

/-- If α is finite, this constructs a locally constant function to `α → β` given a
family of locally constant functions with values in β indexed by α. -/
def unflip {X α β : Type*} [fintype α] [topological_space X] (f : α → locally_constant X β) :
  locally_constant X (α → β) :=
{ to_fun := λ x a, f a x,
  is_locally_constant := begin
    rw (is_locally_constant.tfae (λ x a, f a x)).out 0 3,
    intros g,
    have : (λ (x : X) (a : α), f a x) ⁻¹' {g} = ⋂ (a : α), (f a) ⁻¹' {g a}, by tidy,
    rw this,
    apply is_open_Inter,
    intros a,
    apply (f a).is_locally_constant,
  end }

@[simp]
lemma unflip_flip {X α β : Type*} [fintype α] [topological_space X]
  (f : locally_constant X (α → β)) : unflip f.flip = f := by { ext, refl }

@[simp]
lemma flip_unflip {X α β : Type*} [fintype α] [topological_space X]
  (f : α → locally_constant X β) : (unflip f).flip = f := by { ext, refl }

section comap

open_locale classical

variables [topological_space Y]

/-- Pull back of locally constant maps under any map, by pre-composition.

This definition only makes sense if `f` is continuous,
in which case it sends locally constant functions to their precomposition with `f`.
See also `locally_constant.coe_comap`. -/
noncomputable
def comap (f : X → Y) :
  locally_constant Y Z → locally_constant X Z :=
if hf : continuous f
then λ g, ⟨g ∘ f, g.is_locally_constant.comp_continuous hf⟩
else
begin
  by_cases H : nonempty X,
  { introsI g, exact const X (g $ f $ classical.arbitrary X) },
  { intro g, refine ⟨λ x, (H ⟨x⟩).elim, _⟩,
    intro s, rw is_open_iff_nhds, intro x, exact (H ⟨x⟩).elim }
end

@[simp] lemma coe_comap (f : X → Y) (g : locally_constant Y Z) (hf : continuous f) :
  ⇑(comap f g) = g ∘ f :=
by { rw [comap, dif_pos hf], refl }

@[simp] lemma comap_id : @comap X X Z _ _ id = id :=
by { ext, simp only [continuous_id, id.def, function.comp.right_id, coe_comap] }

lemma comap_comp [topological_space Z]
  (f : X → Y) (g : Y → Z) (hf : continuous f) (hg : continuous g) :
  @comap _ _ α _ _ f ∘ comap g = comap (g ∘ f) :=
by { ext, simp only [hf, hg, hg.comp hf, coe_comap] }

lemma comap_const (f : X → Y) (y : Y) (h : ∀ x, f x = y) :
  (comap f : locally_constant Y Z → locally_constant X Z) =
  λ g, ⟨λ x, g y, is_locally_constant.const _⟩ :=
begin
  ext, rw coe_comap,
  { simp only [h, coe_mk, function.comp_app] },
  { rw show f = λ x, y, by ext; apply h,
    exact continuous_const }
end

end comap

section desc

/-- If a locally constant function factors through an injection, then it factors through a locally
constant function. -/
def desc {X α β : Type*} [topological_space X] {g : α → β} (f : X → α) (h : locally_constant X β)
  (cond : g ∘ f = h) (inj : function.injective g) : locally_constant X α :=
{ to_fun := f,
  is_locally_constant := is_locally_constant.desc _ g (by { rw cond, exact h.2 }) inj }

@[simp]
lemma coe_desc {X α β : Type*} [topological_space X] (f : X → α) (g : α → β)
  (h : locally_constant X β) (cond : g ∘ f = h) (inj : function.injective g) :
  ⇑(desc f h cond inj) = f := rfl

end desc

end locally_constant
