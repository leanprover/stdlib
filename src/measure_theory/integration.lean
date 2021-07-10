/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import measure_theory.measure_space
import measure_theory.borel_space
import algebra.indicator_function
import algebra.support

/-!
# Lebesgue integral for `ℝ≥0∞`-valued functions

We define simple functions and show that each Borel measurable function on `ℝ≥0∞` can be
approximated by a sequence of simple functions.

To prove something for an arbitrary measurable function into `ℝ≥0∞`, the theorem
`measurable.ennreal_induction` shows that is it sufficient to show that the property holds for
(multiples of) characteristic functions and is closed under addition and supremum of increasing
sequences of functions.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.

-/

noncomputable theory
open set (hiding restrict restrict_apply) filter ennreal function (support)
open_locale classical topological_space big_operators nnreal ennreal

namespace measure_theory

variables {α β γ δ : Type*}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure {u v} simple_func (α : Type u) [measurable_space α] (β : Type v) :=
(to_fun : α → β)
(measurable_set_fiber' : ∀ x, measurable_set (to_fun ⁻¹' {x}))
(finite_range' : (set.range to_fun).finite)

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section measurable
variables [measurable_space α]
instance has_coe_to_fun : has_coe_to_fun (α →ₛ β) := ⟨_, to_fun⟩

lemma coe_injective ⦃f g : α →ₛ β⦄ (H : ⇑f = g) : f = g :=
by cases f; cases g; congr; exact H

@[ext] theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
coe_injective $ funext H

lemma finite_range (f : α →ₛ β) : (set.range f).finite := f.finite_range'

lemma measurable_set_fiber (f : α →ₛ β) (x : β) : measurable_set (f ⁻¹' {x}) :=
f.measurable_set_fiber' x

/-- Range of a simple function `α →ₛ β` as a `finset β`. -/
protected def range (f : α →ₛ β) : finset β := f.finite_range.to_finset

@[simp] theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
finite.mem_to_finset _

theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range := mem_range.2 ⟨x, rfl⟩

@[simp] lemma coe_range (f : α →ₛ β) : (↑f.range : set β) = set.range f :=
f.finite_range.coe_to_finset

theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : measure α} (H : μ (f ⁻¹' {x}) ≠ 0) :
  x ∈ f.range :=
let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H in
mem_range.2 ⟨a, ha⟩

lemma forall_range_iff {f : α →ₛ β} {p : β → Prop} :
  (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) :=
by simp only [mem_range, set.forall_range_iff]

lemma exists_range_iff {f : α →ₛ β} {p : β → Prop} :
  (∃ y ∈ f.range, p y) ↔ ∃ x, p (f x) :=
by simpa only [mem_range, exists_prop] using set.exists_range_iff

lemma preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
preimage_singleton_eq_empty.trans $ not_congr mem_range.symm

lemma exists_forall_le [nonempty β] [directed_order β] (f : α →ₛ β) :
  ∃ C, ∀ x, f x ≤ C :=
f.range.exists_le.imp $ λ C, forall_range_iff.1

/-- Constant function as a `simple_func`. -/
def const (α) {β} [measurable_space α] (b : β) : α →ₛ β :=
⟨λ a, b, λ x, measurable_set.const _, finite_range_const⟩

instance [inhabited β] : inhabited (α →ₛ β) := ⟨const _ (default _)⟩

theorem const_apply (a : α) (b : β) : (const α b) a = b := rfl

@[simp] theorem coe_const (b : β) : ⇑(const α b) = function.const α b := rfl

@[simp] lemma range_const (α) [measurable_space α] [nonempty α] (b : β) :
  (const α b).range = {b} :=
finset.coe_injective $ by simp

lemma measurable_set_cut (r : α → β → Prop) (f : α →ₛ β)
  (h : ∀b, measurable_set {a | r a b}) : measurable_set {a | r a (f a)} :=
begin
  have : {a | r a (f a)} = ⋃ b ∈ range f, {a | r a b} ∩ f ⁻¹' {b},
  { ext a,
    suffices : r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i, by simpa,
    exact ⟨λ h, ⟨a, ⟨h, rfl⟩⟩, λ ⟨a', ⟨h', e⟩⟩, e.symm ▸ h'⟩ },
  rw this,
  exact measurable_set.bUnion f.finite_range.countable
    (λ b _, measurable_set.inter (h b) (f.measurable_set_fiber _))
end

@[measurability]
theorem measurable_set_preimage (f : α →ₛ β) (s) : measurable_set (f ⁻¹' s) :=
measurable_set_cut (λ _ b, b ∈ s) f (λ b, measurable_set.const (b ∈ s))

/-- A simple function is measurable -/
@[measurability]
protected theorem measurable [measurable_space β] (f : α →ₛ β) : measurable f :=
λ s _, measurable_set_preimage f s

@[measurability]
protected theorem ae_measurable [measurable_space β] {μ : measure α} (f : α →ₛ β) :
  ae_measurable f μ :=
f.measurable.ae_measurable

protected lemma sum_measure_preimage_singleton (f : α →ₛ β) {μ : measure α} (s : finset β) :
  ∑ y in s, μ (f ⁻¹' {y}) = μ (f ⁻¹' ↑s) :=
sum_measure_preimage_singleton _ (λ _ _, f.measurable_set_fiber _)

lemma sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : measure α) :
  ∑ y in f.range, μ (f ⁻¹' {y}) = μ univ :=
by rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]

/-- If-then-else as a `simple_func`. -/
def piecewise (s : set α) (hs : measurable_set s) (f g : α →ₛ β) : α →ₛ β :=
⟨s.piecewise f g,
 λ x, by letI : measurable_space β := ⊤; exact
   f.measurable.piecewise hs g.measurable trivial,
 (f.finite_range.union g.finite_range).subset range_ite_subset⟩

@[simp] theorem coe_piecewise {s : set α} (hs : measurable_set s) (f g : α →ₛ β) :
  ⇑(piecewise s hs f g) = s.piecewise f g :=
rfl

theorem piecewise_apply {s : set α} (hs : measurable_set s) (f g : α →ₛ β) (a) :
  piecewise s hs f g a = if a ∈ s then f a else g a :=
rfl

@[simp] lemma piecewise_compl {s : set α} (hs : measurable_set sᶜ) (f g : α →ₛ β) :
  piecewise sᶜ hs f g = piecewise s hs.of_compl g f :=
coe_injective $ by simp [hs]

@[simp] lemma piecewise_univ (f g : α →ₛ β) : piecewise univ measurable_set.univ f g = f :=
coe_injective $ by simp

@[simp] lemma piecewise_empty (f g : α →ₛ β) : piecewise ∅ measurable_set.empty f g = g :=
coe_injective $ by simp

lemma measurable_bind [measurable_space γ] (f : α →ₛ β) (g : β → α → γ)
  (hg : ∀ b, measurable (g b)) : measurable (λ a, g (f a) a) :=
λ s hs, f.measurable_set_cut (λ a b, g b a ∈ s) $ λ b, hg b hs

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
⟨λa, g (f a) a,
 λ c, f.measurable_set_cut (λ a b, g b a = c) $ λ b, (g b).measurable_set_preimage {c},
 (f.finite_range.bUnion (λ b _, (g b).finite_range)).subset $
 by rintro _ ⟨a, rfl⟩; simp; exact ⟨a, a, rfl⟩⟩

@[simp] theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) :
  f.bind g a = g (f a) a := rfl

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
    function `g ∘ f : α →ₛ γ` -/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ := bind f (const α ∘ g)

theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) := rfl

theorem map_map (g : β → γ) (h: γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) := rfl

@[simp] theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f := rfl

@[simp] theorem range_map [decidable_eq γ] (g : β → γ) (f : α →ₛ β) :
  (f.map g).range = f.range.image g :=
finset.coe_injective $ by simp [range_comp]

@[simp] theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) := rfl

lemma map_preimage (f : α →ₛ β) (g : β → γ) (s : set γ) :
  (f.map g) ⁻¹' s = f ⁻¹' ↑(f.range.filter (λb, g b ∈ s)) :=
by { simp only [coe_range, sep_mem_eq, set.mem_range, function.comp_app, coe_map, finset.coe_filter,
  ← mem_preimage, inter_comm, preimage_inter_range], apply preimage_comp }

lemma map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
  (f.map g) ⁻¹' {c} = f ⁻¹' ↑(f.range.filter (λ b, g b = c)) :=
map_preimage _ _ _

/-- Composition of a `simple_fun` and a measurable function is a `simple_func`. -/
def comp [measurable_space β] (f : β →ₛ γ) (g : α → β) (hgm : measurable g) : α →ₛ γ :=
{ to_fun := f ∘ g,
  finite_range' := f.finite_range.subset $ set.range_comp_subset_range _ _,
  measurable_set_fiber' := λ z, hgm (f.measurable_set_fiber z) }

@[simp] lemma coe_comp [measurable_space β] (f : β →ₛ γ) {g : α → β} (hgm : measurable g) :
  ⇑(f.comp g hgm) = f ∘ g :=
rfl

lemma range_comp_subset_range [measurable_space β] (f : β →ₛ γ) {g : α → β} (hgm : measurable g) :
  (f.comp g hgm).range ⊆ f.range :=
finset.coe_subset.1 $ by simp only [coe_range, coe_comp, set.range_comp_subset_range]

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ (β → γ)) (g : α →ₛ β) : α →ₛ γ := f.bind (λf, g.map f)

@[simp] lemma seq_apply (f : α →ₛ (β → γ)) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) := rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `λ a, (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ (β × γ) := (f.map prod.mk).seq g

@[simp] lemma pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) := rfl

lemma pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : set β) (t : set γ) :
  (pair f g) ⁻¹' (set.prod s t) = (f ⁻¹' s) ∩ (g ⁻¹' t) := rfl

/- A special form of `pair_preimage` -/
lemma pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
  (pair f g) ⁻¹' {(b, c)} = (f ⁻¹' {b}) ∩ (g ⁻¹' {c}) :=
by { rw ← singleton_prod_singleton, exact pair_preimage _ _ _ _ }

theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp

instance [has_zero β] : has_zero (α →ₛ β) := ⟨const α 0⟩
instance [has_add β] : has_add (α →ₛ β) := ⟨λf g, (f.map (+)).seq g⟩
instance [has_mul β] : has_mul (α →ₛ β) := ⟨λf g, (f.map (*)).seq g⟩
instance [has_sup β] : has_sup (α →ₛ β) := ⟨λf g, (f.map (⊔)).seq g⟩
instance [has_inf β] : has_inf (α →ₛ β) := ⟨λf g, (f.map (⊓)).seq g⟩
instance [has_le β] : has_le (α →ₛ β) := ⟨λf g, ∀a, f a ≤ g a⟩

@[simp, norm_cast] lemma coe_zero [has_zero β] : ⇑(0 : α →ₛ β) = 0 := rfl
@[simp] lemma const_zero [has_zero β] : const α (0:β) = 0 := rfl
@[simp, norm_cast] lemma coe_add [has_add β] (f g : α →ₛ β) : ⇑(f + g) = f + g := rfl
@[simp, norm_cast] lemma coe_mul [has_mul β] (f g : α →ₛ β) : ⇑(f * g) = f * g := rfl
@[simp, norm_cast] lemma coe_le [preorder β] {f g : α →ₛ β} : (f : α → β) ≤ g ↔ f ≤ g := iff.rfl

@[simp] lemma range_zero [nonempty α] [has_zero β] : (0 : α →ₛ β).range = {0} :=
finset.ext $ λ x, by simp [eq_comm]

lemma eq_zero_of_mem_range_zero [has_zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
forall_range_iff.2 $ λ x, rfl

lemma sup_apply [has_sup β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
lemma mul_apply [has_mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a := rfl
lemma add_apply [has_add β] (f g : α →ₛ β) (a : α) : (f + g) a = f a + g a := rfl

lemma add_eq_map₂ [has_add β] (f g : α →ₛ β) : f + g = (pair f g).map (λp:β×β, p.1 + p.2) :=
rfl

lemma mul_eq_map₂ [has_mul β] (f g : α →ₛ β) : f * g = (pair f g).map (λp:β×β, p.1 * p.2) :=
rfl

lemma sup_eq_map₂ [has_sup β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map (λp:β×β, p.1 ⊔ p.2) :=
rfl

lemma const_mul_eq_map [has_mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map (λa, b * a) := rfl

theorem map_add [has_add β] [has_add γ] {g : β → γ}
  (hg : ∀ x y, g (x + y) = g x + g y) (f₁ f₂ : α →ₛ β) : (f₁ + f₂).map g = f₁.map g + f₂.map g :=
ext $ λ x, hg _ _

instance [add_monoid β] : add_monoid (α →ₛ β) :=
function.injective.add_monoid (λ f, show α → β, from f) coe_injective coe_zero coe_add

instance add_comm_monoid [add_comm_monoid β] : add_comm_monoid (α →ₛ β) :=
function.injective.add_comm_monoid (λ f, show α → β, from f) coe_injective coe_zero coe_add

instance [has_neg β] : has_neg (α →ₛ β) := ⟨λf, f.map (has_neg.neg)⟩

@[simp, norm_cast] lemma coe_neg [has_neg β] (f : α →ₛ β) : ⇑(-f) = -f := rfl

instance [has_sub β] : has_sub (α →ₛ β) := ⟨λf g, (f.map (has_sub.sub)).seq g⟩

@[simp, norm_cast] lemma coe_sub [has_sub β] (f g : α →ₛ β) : ⇑(f - g) = f - g :=
rfl

lemma sub_apply [has_sub β] (f g : α →ₛ β) (x : α) : (f - g) x = f x - g x := rfl

instance [add_group β] : add_group (α →ₛ β) :=
function.injective.add_group (λ f, show α → β, from f) coe_injective
  coe_zero coe_add coe_neg coe_sub

instance [add_comm_group β] : add_comm_group (α →ₛ β) :=
function.injective.add_comm_group (λ f, show α → β, from f) coe_injective
  coe_zero coe_add coe_neg coe_sub

variables {K : Type*}

instance [has_scalar K β] : has_scalar K (α →ₛ β) := ⟨λk f, f.map ((•) k)⟩

@[simp] lemma coe_smul [has_scalar K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • f := rfl

lemma smul_apply [has_scalar K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a := rfl

instance [semiring K] [add_comm_monoid β] [module K β] : module K (α →ₛ β) :=
function.injective.module K ⟨λ f, show α → β, from f, coe_zero, coe_add⟩
  coe_injective coe_smul

lemma smul_eq_map [has_scalar K β] (k : K) (f : α →ₛ β) : k • f = f.map ((•) k) := rfl

instance [preorder β] : preorder (α →ₛ β) :=
{ le_refl := λf a, le_refl _,
  le_trans := λf g h hfg hgh a, le_trans (hfg _) (hgh a),
  .. simple_func.has_le }

instance [partial_order β] : partial_order (α →ₛ β) :=
{ le_antisymm := assume f g hfg hgf, ext $ assume a, le_antisymm (hfg a) (hgf a),
  .. simple_func.preorder }

instance [order_bot β] : order_bot (α →ₛ β) :=
{ bot := const α ⊥, bot_le := λf a, bot_le, .. simple_func.partial_order }

instance [order_top β] : order_top (α →ₛ β) :=
{ top := const α ⊤, le_top := λf a, le_top, .. simple_func.partial_order }

instance [semilattice_inf β] : semilattice_inf (α →ₛ β) :=
{ inf := (⊓),
  inf_le_left := assume f g a, inf_le_left,
  inf_le_right := assume f g a, inf_le_right,
  le_inf := assume f g h hfh hgh a, le_inf (hfh a) (hgh a),
  .. simple_func.partial_order }

instance [semilattice_sup β] : semilattice_sup (α →ₛ β) :=
{ sup := (⊔),
  le_sup_left := assume f g a, le_sup_left,
  le_sup_right := assume f g a, le_sup_right,
  sup_le := assume f g h hfh hgh a, sup_le (hfh a) (hgh a),
  .. simple_func.partial_order }

instance [semilattice_sup_bot β] : semilattice_sup_bot (α →ₛ β) :=
{ .. simple_func.semilattice_sup,.. simple_func.order_bot }

instance [lattice β] : lattice (α →ₛ β) :=
{ .. simple_func.semilattice_sup,.. simple_func.semilattice_inf }

instance [bounded_lattice β] : bounded_lattice (α →ₛ β) :=
{ .. simple_func.lattice, .. simple_func.order_bot, .. simple_func.order_top }

lemma finset_sup_apply [semilattice_sup_bot β] {f : γ → α →ₛ β} (s : finset γ) (a : α) :
  s.sup f a = s.sup (λc, f c a) :=
begin
  refine finset.induction_on s rfl _,
  assume a s hs ih,
  rw [finset.sup_insert, finset.sup_insert, sup_apply, ih]
end

section restrict

variables [has_zero β]

/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict (f : α →ₛ β) (s : set α) : α →ₛ β :=
if hs : measurable_set s then piecewise s hs f 0 else 0

theorem restrict_of_not_measurable {f : α →ₛ β} {s : set α}
  (hs : ¬measurable_set s) :
  restrict f s = 0 :=
dif_neg hs

@[simp] theorem coe_restrict (f : α →ₛ β) {s : set α} (hs : measurable_set s) :
  ⇑(restrict f s) = indicator s f :=
by { rw [restrict, dif_pos hs], refl }

@[simp] theorem restrict_univ (f : α →ₛ β) : restrict f univ = f :=
by simp [restrict]

@[simp] theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 :=
by simp [restrict]

theorem map_restrict_of_zero [has_zero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : set α) :
  (f.restrict s).map g = (f.map g).restrict s :=
ext $ λ x,
if hs : measurable_set s then by simp [hs, set.indicator_comp_of_zero hg]
else by simp [restrict_of_not_measurable hs, hg]

theorem map_coe_ennreal_restrict (f : α →ₛ ℝ≥0) (s : set α) :
  (f.restrict s).map (coe : ℝ≥0 → ℝ≥0∞) = (f.map coe).restrict s :=
map_restrict_of_zero ennreal.coe_zero _ _

theorem map_coe_nnreal_restrict (f : α →ₛ ℝ≥0) (s : set α) :
  (f.restrict s).map (coe : ℝ≥0 → ℝ) = (f.map coe).restrict s :=
map_restrict_of_zero nnreal.coe_zero _ _

theorem restrict_apply (f : α →ₛ β) {s : set α} (hs : measurable_set s) (a) :
  restrict f s a = indicator s f a :=
by simp only [f.coe_restrict hs]

theorem restrict_preimage (f : α →ₛ β) {s : set α} (hs : measurable_set s)
  {t : set β} (ht : (0:β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t :=
by simp [hs, indicator_preimage_of_not_mem _ _ ht, inter_comm]

theorem restrict_preimage_singleton (f : α →ₛ β) {s : set α} (hs : measurable_set s)
  {r : β} (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
f.restrict_preimage hs hr.symm

lemma mem_restrict_range {r : β} {s : set α} {f : α →ₛ β} (hs : measurable_set s) :
  r ∈ (restrict f s).range ↔ (r = 0 ∧ s ≠ univ) ∨ (r ∈ f '' s) :=
by rw [← finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]

lemma mem_image_of_mem_range_restrict {r : β} {s : set α} {f : α →ₛ β}
  (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) :
  r ∈ f '' s :=
if hs : measurable_set s then by simpa [mem_restrict_range hs, h0] using hr
else by { rw [restrict_of_not_measurable hs] at hr,
  exact (h0 $ eq_zero_of_mem_range_zero hr).elim }

@[mono] lemma restrict_mono [preorder β] (s : set α) {f g : α →ₛ β} (H : f ≤ g) :
  f.restrict s ≤ g.restrict s :=
if hs : measurable_set s then λ x, by simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
else by simp only [restrict_of_not_measurable hs, le_refl]

end restrict

section approx

section
variables [semilattice_sup_bot β] [has_zero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `supr_approx_apply` for details. -/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
(finset.range n).sup (λk, restrict (const α (i k)) {a:α | i k ≤ f a})

lemma approx_apply [topological_space β] [order_closed_topology β] [measurable_space β]
  [opens_measurable_space β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : measurable f) :
  (approx i f n : α →ₛ β) a = (finset.range n).sup (λk, if i k ≤ f a then i k else 0) :=
begin
  dsimp only [approx],
  rw [finset_sup_apply],
  congr,
  funext k,
  rw [restrict_apply],
  refl,
  exact (hf measurable_set_Ici)
end

lemma monotone_approx (i : ℕ → β) (f : α → β) : monotone (approx i f) :=
assume n m h, finset.sup_mono $ finset.range_subset.2 h

lemma approx_comp [topological_space β] [order_closed_topology β] [measurable_space β]
  [opens_measurable_space β] [measurable_space γ]
  {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
  (hf : measurable f) (hg : measurable g) :
  (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) :=
by rw [approx_apply _ hf, approx_apply _ (hf.comp hg)]

end

lemma supr_approx_apply [topological_space β] [complete_lattice β] [order_closed_topology β]
  [has_zero β] [measurable_space β] [opens_measurable_space β]
  (i : ℕ → β) (f : α → β) (a : α) (hf : measurable f) (h_zero : (0 : β) = ⊥) :
  (⨆n, (approx i f n : α →ₛ β) a) = (⨆k (h : i k ≤ f a), i k) :=
begin
  refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume k, supr_le $ assume hk, _),
  { rw [approx_apply a hf, h_zero],
    refine finset.sup_le (assume k hk, _),
    split_ifs,
    exact le_supr_of_le k (le_supr _ h),
    exact bot_le },
  { refine le_supr_of_le (k+1) _,
    rw [approx_apply a hf],
    have : k ∈ finset.range (k+1) := finset.mem_range.2 (nat.lt_succ_self _),
    refine le_trans (le_of_eq _) (finset.le_sup this),
    rw [if_pos hk] }
end

end approx

section eapprox

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def ennreal_rat_embed (n : ℕ) : ℝ≥0∞ :=
ennreal.of_real ((encodable.decode ℚ n).get_or_else (0 : ℚ))

lemma ennreal_rat_embed_encode (q : ℚ) :
  ennreal_rat_embed (encodable.encode q) = real.to_nnreal q :=
by rw [ennreal_rat_embed, encodable.encodek]; refl

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
approx ennreal_rat_embed

lemma eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ :=
begin
  simp only [eapprox, approx, finset_sup_apply, finset.sup_lt_iff, with_top.zero_lt_top,
    finset.mem_range, ennreal.bot_eq_zero, restrict],
  assume b hb,
  split_ifs,
  { simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const],
    calc {a : α | ennreal_rat_embed b ≤ f a}.indicator (λ x, ennreal_rat_embed b) a
        ≤ ennreal_rat_embed b : indicator_le_self _ _ a
    ... < ⊤ : ennreal.coe_lt_top },
  { exact with_top.zero_lt_top },
end

@[mono] lemma monotone_eapprox (f : α → ℝ≥0∞) : monotone (eapprox f) :=
monotone_approx _ f

lemma supr_eapprox_apply (f : α → ℝ≥0∞) (hf : measurable f) (a : α) :
  (⨆n, (eapprox f n : α →ₛ ℝ≥0∞) a) = f a :=
begin
  rw [eapprox, supr_approx_apply ennreal_rat_embed f a hf rfl],
  refine le_antisymm (supr_le $ assume i, supr_le $ assume hi, hi) (le_of_not_gt _),
  assume h,
  rcases ennreal.lt_iff_exists_rat_btwn.1 h with ⟨q, hq, lt_q, q_lt⟩,
  have : (real.to_nnreal q : ℝ≥0∞) ≤
      (⨆ (k : ℕ) (h : ennreal_rat_embed k ≤ f a), ennreal_rat_embed k),
  { refine le_supr_of_le (encodable.encode q) _,
    rw [ennreal_rat_embed_encode q],
    refine le_supr_of_le (le_of_lt q_lt) _,
    exact le_refl _ },
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
end

lemma eapprox_comp [measurable_space γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ}
  (hf : measurable f) (hg : measurable g) :
  (eapprox (f ∘ g) n : α → ℝ≥0∞) = (eapprox f n : γ →ₛ ℝ≥0∞) ∘ g :=
funext $ assume a, approx_comp a hf hg

/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
def eapprox_diff (f : α → ℝ≥0∞) : ∀ (n : ℕ), α →ₛ ℝ≥0
| 0 := (eapprox f 0).map ennreal.to_nnreal
| (n+1) := (eapprox f (n+1) - eapprox f n).map ennreal.to_nnreal

lemma sum_eapprox_diff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
  (∑ k in finset.range (n+1), (eapprox_diff f k a : ℝ≥0∞)) = eapprox f n a :=
begin
  induction n with n IH,
  { simp only [nat.nat_zero_eq_zero, finset.sum_singleton, finset.range_one], refl },
  { rw [finset.sum_range_succ, nat.succ_eq_add_one, IH, eapprox_diff, coe_map, function.comp_app,
        coe_sub, pi.sub_apply, ennreal.coe_to_nnreal,
        ennreal.add_sub_cancel_of_le (monotone_eapprox f (nat.le_succ _) _)],
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n+1) a)).ne,
    rw ennreal.sub_le_iff_le_add,
    exact le_self_add },
end

lemma tsum_eapprox_diff (f : α → ℝ≥0∞) (hf : measurable f) (a : α) :
  (∑' n, (eapprox_diff f n a : ℝ≥0∞)) = f a :=
by simp_rw [ennreal.tsum_eq_supr_nat' (tendsto_add_at_top_nat 1), sum_eapprox_diff,
  supr_eapprox_apply f hf a]

end eapprox

end measurable

section measure
variables [measurable_space α] {μ : measure α}

/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral (f : α →ₛ ℝ≥0∞) (μ : measure α) : ℝ≥0∞ :=
∑ x in f.range, x * μ (f ⁻¹' {x})

lemma lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : finset ℝ≥0∞}
  (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
  f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
begin
  refine finset.sum_bij_ne_zero (λr _ _, r) _ _ _ _,
  { simpa only [forall_range_iff, mul_ne_zero_iff, and_imp] },
  { intros, assumption },
  { intros b _ hb,
    refine ⟨b, _, hb, rfl⟩,
    rw [mem_range, ← preimage_singleton_nonempty],
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2 },
  { intros, refl }
end

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`.  -/
lemma map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) :
  (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x}) :=
begin
  simp only [lintegral, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, finset.mul_sum],
  refine finset.sum_congr _ _,
  { congr },
  { assume x, simp only [finset.mem_filter], rintro ⟨_, h⟩, rw h },
end

lemma add_lintegral (f g : α →ₛ ℝ≥0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
calc (f + g).lintegral μ =
      ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) :
    by rw [add_eq_map₂, map_lintegral]; exact finset.sum_congr rfl (assume a ha, add_mul _ _ _)
  ... = ∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x}) +
      ∑ x in (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) : by rw [finset.sum_add_distrib]
  ... = ((pair f g).map prod.fst).lintegral μ + ((pair f g).map prod.snd).lintegral μ :
    by rw [map_lintegral, map_lintegral]
  ... = lintegral f μ + lintegral g μ : rfl

lemma const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) :
  (const α x * f).lintegral μ = x * f.lintegral μ :=
calc (f.map (λa, x * a)).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) :
    map_lintegral _ _
  ... = ∑ r in f.range, x * (r * μ (f ⁻¹' {r})) :
    finset.sum_congr rfl (assume a ha, mul_assoc _ _ _)
  ... = x * f.lintegral μ :
    finset.mul_sum.symm

/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
def lintegralₗ : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] measure α →ₗ[ℝ≥0∞] ℝ≥0∞ :=
{ to_fun := λ f,
  { to_fun := lintegral f,
    map_add' := by simp [lintegral, mul_add, finset.sum_add_distrib],
    map_smul' := λ c μ, by simp [lintegral, mul_left_comm _ c, finset.mul_sum] },
  map_add' := λ f g, linear_map.ext (λ μ, add_lintegral f g),
  map_smul' := λ c f, linear_map.ext (λ μ, const_mul_lintegral f c) }

@[simp] lemma zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
linear_map.ext_iff.1 lintegralₗ.map_zero μ

lemma lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
(lintegralₗ f).map_add μ ν

lemma lintegral_smul (f : α →ₛ ℝ≥0∞) (c : ℝ≥0∞) :
  f.lintegral (c • μ) = c • f.lintegral μ :=
(lintegralₗ f).map_smul c μ

@[simp] lemma lintegral_zero (f : α →ₛ ℝ≥0∞) :
  f.lintegral 0 = 0 :=
(lintegralₗ f).map_zero

lemma lintegral_sum {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → measure α) :
  f.lintegral (measure.sum μ) = ∑' i, f.lintegral (μ i) :=
begin
  simp only [lintegral, measure.sum_apply, f.measurable_set_preimage, ← finset.tsum_subtype,
    ← ennreal.tsum_mul_left],
  apply ennreal.tsum_comm
end

lemma restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
calc (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :
  lintegral_eq_of_subset _ $ λ x hx, if hxs : x ∈ s
    then λ _, by simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
    else false.elim $ hx $ by simp [*]
... = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :
  finset.sum_congr rfl $ forall_range_iff.2 $ λ b, if hb : f b = 0 then by simp only [hb, zero_mul]
    else by rw [restrict_preimage_singleton _ hs hb, inter_comm]

lemma lintegral_restrict (f : α →ₛ ℝ≥0∞) (s : set α) (μ : measure α) :
  f.lintegral (μ.restrict s) = ∑ y in f.range, y * μ (f ⁻¹' {y} ∩ s) :=
by simp only [lintegral, measure.restrict_apply, f.measurable_set_preimage]

lemma restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : set α}
  (hs : measurable_set s) :
  (restrict f s).lintegral μ = f.lintegral (μ.restrict s) :=
by rw [f.restrict_lintegral hs, lintegral_restrict]

lemma const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c * μ univ :=
begin
  rw [lintegral],
  by_cases ha : nonempty α,
  { resetI, simp [preimage_const_of_mem] },
  { simp [μ.eq_zero_of_not_nonempty ha] }
end

lemma const_lintegral_restrict (c : ℝ≥0∞) (s : set α) :
  (const α c).lintegral (μ.restrict s) = c * μ s :=
by rw [const_lintegral, measure.restrict_apply measurable_set.univ, univ_inter]

lemma restrict_const_lintegral (c : ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  ((const α c).restrict s).lintegral μ = c * μ s :=
by rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]

lemma le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
calc f.lintegral μ ⊔ g.lintegral μ =
      ((pair f g).map prod.fst).lintegral μ ⊔ ((pair f g).map prod.snd).lintegral μ : rfl
  ... ≤ ∑ x in (pair f g).range, (x.1 ⊔ x.2) * μ (pair f g ⁻¹' {x}) :
  begin
    rw [map_lintegral, map_lintegral],
    refine sup_le _ _;
      refine finset.sum_le_sum (λ a _, canonically_ordered_semiring.mul_le_mul _ (le_refl _)),
    exact le_sup_left,
    exact le_sup_right
  end
  ... = (f ⊔ g).lintegral μ : by rw [sup_eq_map₂, map_lintegral]

/-- `simple_func.lintegral` is monotone both in function and in measure. -/
@[mono] lemma lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) {μ ν : measure α} (hμν : μ ≤ ν) :
  f.lintegral μ ≤ g.lintegral ν :=
calc f.lintegral μ ≤ f.lintegral μ ⊔ g.lintegral μ : le_sup_left
  ... ≤ (f ⊔ g).lintegral μ : le_sup_lintegral _ _
  ... = g.lintegral μ : by rw [sup_of_le_right hfg]
  ... ≤ g.lintegral ν : finset.sum_le_sum $ λ y hy, ennreal.mul_left_mono $
                          hμν _ (g.measurable_set_preimage _)

/-- `simple_func.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
lemma lintegral_eq_of_measure_preimage [measurable_space β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞}
  {ν : measure β} (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) :
  f.lintegral μ = g.lintegral ν :=
begin
  simp only [lintegral, ← H],
  apply lintegral_eq_of_subset,
  simp only [H],
  intros,
  exact mem_range_of_measure_ne_zero ‹_›
end

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
lemma lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) :
  f.lintegral μ = g.lintegral μ :=
lintegral_eq_of_measure_preimage $ λ y, measure_congr $
  eventually.set_eq $ h.mono $ λ x hx, by simp [hx]

lemma lintegral_map {β} [measurable_space β] {μ' : measure β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞)
  (m : α → β) (eq : ∀a:α, f a = g (m a)) (h : ∀s:set β, measurable_set s → μ' s = μ (m ⁻¹' s)) :
  f.lintegral μ = g.lintegral μ' :=
lintegral_eq_of_measure_preimage $ λ y,
by { simp only [preimage, eq], exact (h (g ⁻¹' {y}) (g.measurable_set_preimage _)).symm }

/-- The `lintegral` of simple functions transforms appropriately under a measurable equivalence.
(Compare `lintegral_map`, which applies to a broader class of transformations of the domain, but
requires measurability of the function being integrated.) -/
lemma lintegral_map_equiv {β} [measurable_space β] (g : β →ₛ ℝ≥0∞) (m : α ≃ᵐ β) :
  (g.comp m m.measurable).lintegral μ = g.lintegral (measure.map m μ) :=
begin
  simp [simple_func.lintegral],
  have : (g.comp m m.measurable).range = g.range,
  { refine le_antisymm _ _,
    { exact g.range_comp_subset_range m.measurable },
    convert (g.comp m m.measurable).range_comp_subset_range m.symm.measurable,
    apply simple_func.ext,
    intros a,
    exact congr_arg g (congr_fun m.self_comp_symm.symm a) },
  rw this,
  congr' 1,
  funext,
  rw [m.map_apply (g ⁻¹' {x})],
  refl,
end

end measure

section fin_meas_supp

variables [measurable_space α] [has_zero β] [has_zero γ] {μ : measure α}

open finset function

lemma support_eq (f : α →ₛ β) : support f = ⋃ y ∈ f.range.filter (λ y, y ≠ 0), f ⁻¹' {y} :=
set.ext $ λ x, by simp only [finset.set_bUnion_preimage_singleton, mem_support, set.mem_preimage,
  finset.mem_coe, mem_filter, mem_range_self, true_and]

/-- A `simple_func` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def fin_meas_supp (f : α →ₛ β) (μ : measure α) : Prop :=
f =ᶠ[μ.cofinite] 0

lemma fin_meas_supp_iff_support {f : α →ₛ β} {μ : measure α} :
  f.fin_meas_supp μ ↔ μ (support f) < ∞ :=
iff.rfl

lemma fin_meas_supp_iff {f : α →ₛ β} {μ : measure α} :
  f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
begin
  split,
  { refine λ h y hy, lt_of_le_of_lt (measure_mono _) h,
    exact λ x hx (H : f x = 0), hy $ H ▸ eq.symm hx },
  { intro H,
    rw [fin_meas_supp_iff_support, support_eq],
    refine lt_of_le_of_lt (measure_bUnion_finset_le _ _) (sum_lt_top _),
    exact λ y hy, H y (finset.mem_filter.1 hy).2 }
end

namespace fin_meas_supp

lemma meas_preimage_singleton_ne_zero {f : α →ₛ β} (h : f.fin_meas_supp μ) {y : β} (hy : y ≠ 0) :
  μ (f ⁻¹' {y}) < ∞ :=
fin_meas_supp_iff.1 h y hy

protected lemma map {f : α →ₛ β} {g : β → γ} (hf : f.fin_meas_supp μ) (hg : g 0 = 0) :
  (f.map g).fin_meas_supp μ :=
flip lt_of_le_of_lt hf (measure_mono $ support_comp_subset hg f)

lemma of_map {f : α →ₛ β} {g : β → γ} (h : (f.map g).fin_meas_supp μ) (hg : ∀b, g b = 0 → b = 0) :
  f.fin_meas_supp μ :=
flip lt_of_le_of_lt h $ measure_mono $ support_subset_comp hg _

lemma map_iff {f : α →ₛ β} {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) :
  (f.map g).fin_meas_supp μ ↔ f.fin_meas_supp μ :=
⟨λ h, h.of_map $ λ b, hg.1, λ h, h.map $ hg.2 rfl⟩

protected lemma pair {f : α →ₛ β} {g : α →ₛ γ} (hf : f.fin_meas_supp μ) (hg : g.fin_meas_supp μ) :
  (pair f g).fin_meas_supp μ :=
calc μ (support $ pair f g) = μ (support f ∪ support g) : congr_arg μ $ support_prod_mk f g
... ≤ μ (support f) + μ (support g) : measure_union_le _ _
... < _ : add_lt_top.2 ⟨hf, hg⟩

protected lemma map₂ [has_zero δ] {μ : measure α} {f : α →ₛ β} (hf : f.fin_meas_supp μ)
  {g : α →ₛ γ} (hg : g.fin_meas_supp μ) {op : β → γ → δ} (H : op 0 0 = 0) :
  ((pair f g).map (function.uncurry op)).fin_meas_supp μ :=
(hf.pair hg).map H

protected lemma add {β} [add_monoid β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f + g).fin_meas_supp μ :=
by { rw [add_eq_map₂], exact hf.map₂ hg (zero_add 0) }

protected lemma mul {β} [monoid_with_zero β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f * g).fin_meas_supp μ :=
by { rw [mul_eq_map₂], exact hf.map₂ hg (zero_mul 0) }

lemma lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.fin_meas_supp μ) (hf : ∀ᵐ a ∂μ, f a < ∞) :
  f.lintegral μ < ∞ :=
begin
  refine sum_lt_top (λ a ha, _),
  rcases eq_or_lt_of_le (le_top : a ≤ ∞) with rfl|ha,
  { simp only [ae_iff, lt_top_iff_ne_top, ne.def, not_not] at hf,
    simp [set.preimage, hf] },
  { by_cases ha0 : a = 0,
    { subst a, rwa [zero_mul] },
    { exact mul_lt_top ha (fin_meas_supp_iff.1 hm _ ha0) } }
end

lemma of_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ < ∞) : f.fin_meas_supp μ :=
begin
  refine fin_meas_supp_iff.2 (λ b hb, _),
  rw [lintegral, sum_lt_top_iff] at h,
  by_cases b_mem : b ∈ f.range,
  { rw ennreal.lt_top_iff_ne_top,
    have h : ¬ _ = ∞ := ennreal.lt_top_iff_ne_top.1 (h b b_mem),
    simp only [mul_eq_top, not_or_distrib, not_and_distrib] at h,
    rcases h with ⟨h, h'⟩,
    refine or.elim h (λh, by contradiction) (λh, h) },
  { rw ← preimage_eq_empty_iff at b_mem,
    rw [b_mem, measure_empty],
    exact with_top.zero_lt_top }
end

lemma iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐ a ∂μ, f a < ∞) :
  f.fin_meas_supp μ ↔ f.lintegral μ < ∞ :=
⟨λ h, h.lintegral_lt_top hf, λ h, of_lintegral_lt_top h⟩

end fin_meas_supp

end fin_meas_supp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`) -/
@[elab_as_eliminator]
protected lemma induction {α γ} [measurable_space α] [add_monoid γ] {P : simple_func α γ → Prop}
  (h_ind : ∀ c {s} (hs : measurable_set s),
    P (simple_func.piecewise s hs (simple_func.const _ c) (simple_func.const _ 0)))
  (h_add : ∀ ⦃f g : simple_func α γ⦄, disjoint (support f) (support g) → P f → P g → P (f + g))
  (f : simple_func α γ) : P f :=
begin
  generalize' h : f.range \ {0} = s,
  rw [← finset.coe_inj, finset.coe_sdiff, finset.coe_singleton, simple_func.coe_range] at h,
  revert s f h, refine finset.induction _ _,
  { intros f hf, rw [finset.coe_empty, diff_eq_empty, range_subset_singleton] at hf,
    convert h_ind 0 measurable_set.univ, ext x, simp [hf] },
  { intros x s hxs ih f hf,
    have mx := f.measurable_set_preimage {x},
    let g := simple_func.piecewise (f ⁻¹' {x}) mx 0 f,
    have Pg : P g,
    { apply ih, simp only [g, simple_func.coe_piecewise, range_piecewise],
      rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, hf, finset.coe_insert,
        insert_diff_self_of_not_mem, diff_eq_empty.mpr, set.empty_union],
      { rw [set.image_subset_iff], convert set.subset_univ _,
        exact preimage_const_of_mem (mem_singleton _) },
      { rwa [finset.mem_coe] }},
    convert h_add _ Pg (h_ind x mx),
    { ext1 y, by_cases hy : y ∈ f ⁻¹' {x}; [simpa [hy], simp [hy]] },
    rintro y, by_cases hy : y ∈ f ⁻¹' {x}; simp [hy] }
end

end simple_func

section lintegral
open simple_func
variables [measurable_space α] {μ : measure α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
def lintegral (μ : measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
⨆ (g : α →ₛ ℝ≥0∞) (hf : ⇑g ≤ f), g.lintegral μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ∥x∥ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/
notation `∫⁻` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := lintegral μ r
notation `∫⁻` binders `, ` r:(scoped:60 f, lintegral volume f) := r
notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 :=
  lintegral (measure.restrict μ s) r
notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, lintegral (measure.restrict volume s) f) := r

theorem simple_func.lintegral_eq_lintegral (f : α →ₛ ℝ≥0∞) (μ : measure α) :
  ∫⁻ a, f a ∂ μ = f.lintegral μ :=
le_antisymm
  (bsupr_le $ λ g hg, lintegral_mono hg $ le_refl _)
  (le_supr_of_le f $ le_supr_of_le (le_refl _) (le_refl _))

@[mono] lemma lintegral_mono' ⦃μ ν : measure α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν :=
supr_le_supr $ λ φ, supr_le_supr2 $ λ hφ, ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩

lemma lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
lintegral_mono' (le_refl μ) hfg

lemma lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
begin
  refine lintegral_mono _,
  intro a,
  rw ennreal.coe_le_coe,
  exact h a,
end

lemma lintegral_mono_set ⦃μ : measure α⦄
  {s t : set α} {f : α → ℝ≥0∞} (hst : s ⊆ t) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
lintegral_mono' (measure.restrict_mono hst (le_refl μ)) (le_refl f)

lemma lintegral_mono_set' ⦃μ : measure α⦄
  {s t : set α} {f : α → ℝ≥0∞} (hst : s ≤ᵐ[μ] t) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
lintegral_mono' (measure.restrict_mono' hst (le_refl μ)) (le_refl f)

lemma monotone_lintegral (μ : measure α) : monotone (lintegral μ) :=
lintegral_mono

@[simp] lemma lintegral_const (c : ℝ≥0∞) : ∫⁻ a, c ∂μ = c * μ univ :=
by rw [← simple_func.const_lintegral, ← simple_func.lintegral_eq_lintegral, simple_func.coe_const]

@[simp] lemma lintegral_one : ∫⁻ a, (1 : ℝ≥0∞) ∂μ = μ univ :=
by rw [lintegral_const, one_mul]

lemma set_lintegral_const (s : set α) (c : ℝ≥0∞) : ∫⁻ a in s, c ∂μ = c * μ s :=
by rw [lintegral_const, measure.restrict_apply_univ]

lemma set_lintegral_one (s) : ∫⁻ a in s, 1 ∂μ = μ s :=
by rw [set_lintegral_const, one_mul]

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
lemma lintegral_eq_nnreal (f : α → ℝ≥0∞) (μ : measure α) :
  (∫⁻ a, f a ∂μ) = (⨆ (φ : α →ₛ ℝ≥0) (hf : ∀ x, ↑(φ x) ≤ f x),
      (φ.map (coe : ℝ≥0 → ℝ≥0∞)).lintegral μ) :=
begin
  refine le_antisymm
    (bsupr_le $ assume φ hφ, _)
    (supr_le_supr2 $ λ φ, ⟨φ.map (coe : ℝ≥0 → ℝ≥0∞), le_refl _⟩),
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞,
  { let ψ := φ.map ennreal.to_nnreal,
    replace h : ψ.map (coe : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ :=
      h.mono (λ a, ennreal.coe_to_nnreal),
    have : ∀ x, ↑(ψ x) ≤ f x := λ x, le_trans ennreal.coe_to_nnreal_le_self (hφ x),
    exact le_supr_of_le (φ.map ennreal.to_nnreal)
      (le_supr_of_le this (ge_of_eq $ lintegral_congr h)) },
  { have h_meas : μ (φ ⁻¹' {∞}) ≠ 0, from mt measure_zero_iff_ae_nmem.1 h,
    refine le_trans le_top (ge_of_eq $ (supr_eq_top _).2 $ λ b hb, _),
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞}), from exists_nat_mul_gt h_meas (ne_of_lt hb),
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞}),
    simp only [lt_supr_iff, exists_prop, coe_restrict, φ.measurable_set_preimage, coe_const,
      ennreal.coe_indicator, map_coe_ennreal_restrict, map_const, ennreal.coe_nat,
      restrict_const_lintegral],
    refine ⟨indicator_le (λ x hx, le_trans _ (hφ _)), hn⟩,
    simp only [mem_preimage, mem_singleton_iff] at hx,
    simp only [hx, le_top] }
end

lemma exists_simple_func_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ < ∞)
  {ε : ℝ≥0∞} (hε : 0 < ε) :
  ∃ φ : α →ₛ ℝ≥0, (∀ x, ↑(φ x) ≤ f x) ∧ ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) →
    (map coe (ψ - φ)).lintegral μ < ε :=
begin
  rw lintegral_eq_nnreal at h,
  have := ennreal.lt_add_right h hε,
  erw ennreal.bsupr_add at this; [skip, exact ⟨0, λ x, by simp⟩],
  simp_rw [lt_supr_iff, supr_lt_iff, supr_le_iff] at this,
  rcases this with ⟨φ, hle : ∀ x, ↑(φ x) ≤ f x, b, hbφ, hb⟩,
  refine ⟨φ, hle, λ ψ hψ, _⟩,
  have : (map coe φ).lintegral μ < ∞, from (le_bsupr φ hle).trans_lt h,
  rw [← add_lt_add_iff_left this, ← add_lintegral, ← map_add @ennreal.coe_add],
  refine (hb _ (λ x, le_trans _ (max_le (hle x) (hψ x)))).trans_lt hbφ,
  norm_cast,
  simp only [add_apply, sub_apply, nnreal.add_sub_eq_max]
end

theorem supr_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
  (⨆i, ∫⁻ a, f i a ∂μ) ≤ (∫⁻ a, ⨆i, f i a ∂μ) :=
begin
  simp only [← supr_apply],
  exact (monotone_lintegral μ).le_map_supr
end

theorem supr2_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ℝ≥0∞) :
  (⨆i (h : ι' i), ∫⁻ a, f i h a ∂μ) ≤ (∫⁻ a, ⨆i (h : ι' i), f i h a ∂μ) :=
by { convert (monotone_lintegral μ).le_map_supr2 f, ext1 a, simp only [supr_apply] }

theorem le_infi_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
  (∫⁻ a, ⨅i, f i a ∂μ) ≤ (⨅i, ∫⁻ a, f i a ∂μ) :=
by { simp only [← infi_apply], exact (monotone_lintegral μ).map_infi_le }

theorem le_infi2_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ℝ≥0∞) :
  (∫⁻ a, ⨅ i (h : ι' i), f i h a ∂μ) ≤ (⨅ i (h : ι' i), ∫⁻ a, f i h a ∂μ) :=
by { convert (monotone_lintegral μ).map_infi2_le f, ext1 a, simp only [infi_apply] }

lemma lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
  (∫⁻ a, f a ∂μ) ≤ (∫⁻ a, g a ∂μ) :=
begin
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩,
  have : ∀ᵐ x ∂μ, x ∉ t := measure_zero_iff_ae_nmem.1 ht0,
  refine (supr_le $ assume s, supr_le $ assume hfs,
    le_supr_of_le (s.restrict tᶜ) $ le_supr_of_le _ _),
  { assume a,
    by_cases a ∈ t;
      simp [h, restrict_apply, ht.compl],
    exact le_trans (hfs a) (by_contradiction $ assume hnfg, h (hts hnfg)) },
  { refine le_of_eq (simple_func.lintegral_congr $ this.mono $ λ a hnt, _),
    by_cases hat : a ∈ t; simp [hat, ht.compl],
    exact (hnt hat).elim }
end

lemma lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
  (∫⁻ a, f a ∂μ) = (∫⁻ a, g a ∂μ) :=
le_antisymm (lintegral_mono_ae $ h.le) (lintegral_mono_ae $ h.symm.le)

lemma lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) :
  (∫⁻ a, f a ∂μ) = (∫⁻ a, g a ∂μ) :=
by simp only [h]

lemma set_lintegral_congr {f : α → ℝ≥0∞} {s t : set α} (h : s =ᵐ[μ] t) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
by rw [restrict_congr_set h]

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_supr
  {f : ℕ → α → ℝ≥0∞} (hf : ∀n, measurable (f n)) (h_mono : monotone f) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
begin
  set c : ℝ≥0 → ℝ≥0∞ := coe,
  set F := λ a:α, ⨆n, f n a,
  have hF : measurable F := measurable_supr hf,
  refine le_antisymm _ (supr_lintegral_le _),
  rw [lintegral_eq_nnreal],
  refine supr_le (assume s, supr_le (assume hsf, _)),
  refine ennreal.le_of_forall_lt_one_mul_le (assume a ha, _),
  rcases ennreal.lt_iff_exists_coe.1 ha with ⟨r, rfl, ha⟩,
  have ha : r < 1 := ennreal.coe_lt_coe.1 ha,
  let rs := s.map (λa, r * a),
  have eq_rs : (const α r : α →ₛ ℝ≥0∞) * map c s = rs.map c,
  { ext1 a, exact ennreal.coe_mul.symm },
  have eq : ∀p, (rs.map c) ⁻¹' {p} = (⋃n, (rs.map c) ⁻¹' {p} ∩ {a | p ≤ f n a}),
  { assume p,
    rw [← inter_Union, ← inter_univ ((map c rs) ⁻¹' {p})] {occs := occurrences.pos [1]},
    refine set.ext (assume x, and_congr_right $ assume hx, (true_iff _).2 _),
    by_cases p_eq : p = 0, { simp [p_eq] },
    simp at hx, subst hx,
    have : r * s x ≠ 0, { rwa [(≠), ← ennreal.coe_eq_zero] },
    have : s x ≠ 0, { refine mt _ this, assume h, rw [h, mul_zero] },
    have : (rs.map c) x < ⨆ (n : ℕ), f n x,
    { refine lt_of_lt_of_le (ennreal.coe_lt_coe.2 (_)) (hsf x),
      suffices : r * s x < 1 * s x, simpa [rs],
      exact mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this) },
    rcases lt_supr_iff.1 this with ⟨i, hi⟩,
    exact mem_Union.2 ⟨i, le_of_lt hi⟩ },
  have mono : ∀r:ℝ≥0∞, monotone (λn, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}),
  { assume r i j h,
    refine inter_subset_inter (subset.refl _) _,
    assume x hx, exact le_trans hx (h_mono h x) },
  have h_meas : ∀n, measurable_set {a : α | ⇑(map c rs) a ≤ f n a} :=
    assume n, measurable_set_le (simple_func.measurable _) (hf n),
  calc (r:ℝ≥0∞) * (s.map c).lintegral μ = ∑ r in (rs.map c).range, r * μ ((rs.map c) ⁻¹' {r}) :
      by rw [← const_mul_lintegral, eq_rs, simple_func.lintegral]
    ... ≤ ∑ r in (rs.map c).range, r * μ (⋃n, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      le_of_eq (finset.sum_congr rfl $ assume x hx, by rw ← eq)
    ... ≤ ∑ r in (rs.map c).range, (⨆n, r * μ ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a})) :
      le_of_eq (finset.sum_congr rfl $ assume x hx,
        begin
          rw [measure_Union_eq_supr _ (directed_of_sup $ mono x), ennreal.mul_supr],
          { assume i,
            refine ((rs.map c).measurable_set_preimage _).inter _,
            exact hf i measurable_set_Ici }
        end)
    ... ≤ ⨆n, ∑ r in (rs.map c).range, r * μ ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      begin
        refine le_of_eq _,
        rw [ennreal.finset_sum_supr_nat],
        assume p i j h,
        exact canonically_ordered_semiring.mul_le_mul (le_refl _) (measure_mono $ mono p h)
      end
    ... ≤ (⨆n:ℕ, ((rs.map c).restrict {a | (rs.map c) a ≤ f n a}).lintegral μ) :
    begin
      refine supr_le_supr (assume n, _),
      rw [restrict_lintegral _ (h_meas n)],
      { refine le_of_eq (finset.sum_congr rfl $ assume r hr, _),
        congr' 2 with a,
        refine and_congr_right _,
        simp {contextual := tt} }
    end
    ... ≤ (⨆n, ∫⁻ a, f n a ∂μ) :
    begin
      refine supr_le_supr (assume n, _),
      rw [← simple_func.lintegral_eq_lintegral],
      refine lintegral_mono (assume a, _),
      simp only [map_apply] at h_meas,
      simp only [coe_map, restrict_apply _ (h_meas _), (∘)],
      exact indicator_apply_le id,
    end
end

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_supr' {f : ℕ → α → ℝ≥0∞} (hf : ∀n, ae_measurable (f n) μ)
  (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x)) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
begin
  simp_rw ←supr_apply,
  let p : α → (ℕ → ℝ≥0∞) → Prop := λ x f', monotone f',
  have hp : ∀ᵐ x ∂μ, p x (λ i, f i x), from h_mono,
  have h_ae_seq_mono : monotone (ae_seq hf p),
  { intros n m hnm x,
    by_cases hx : x ∈ ae_seq_set hf p,
    { exact ae_seq.prop_of_mem_ae_seq_set hf hx hnm, },
    { simp only [ae_seq, hx, if_false],
      exact le_refl _, }, },
  rw lintegral_congr_ae (ae_seq.supr hf hp).symm,
  simp_rw supr_apply,
  rw @lintegral_supr _ _ μ _ (ae_seq.measurable hf p) h_ae_seq_mono,
  congr,
  exact funext (λ n, lintegral_congr_ae (ae_seq.ae_seq_n_eq_fun_n_ae hf hp n)),
end

/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
  (hf : ∀n, ae_measurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x))
  (h_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 $ F x)) :
  tendsto (λ n, ∫⁻ x, f n x ∂μ) at_top (𝓝 $ ∫⁻ x, F x ∂μ) :=
begin
  have : monotone (λ n, ∫⁻ x, f n x ∂μ) :=
    λ i j hij, lintegral_mono_ae (h_mono.mono $ λ x hx, hx hij),
  suffices key : ∫⁻ x, F x ∂μ = ⨆n, ∫⁻ x, f n x ∂μ,
  { rw key,
    exact tendsto_at_top_supr this },
  rw ← lintegral_supr' hf h_mono,
  refine lintegral_congr_ae _,
  filter_upwards [h_mono, h_tendsto],
  exact λ x hx_mono hx_tendsto, tendsto_nhds_unique hx_tendsto (tendsto_at_top_supr hx_mono),
end

lemma lintegral_eq_supr_eapprox_lintegral {f : α → ℝ≥0∞} (hf : measurable f) :
  (∫⁻ a, f a ∂μ) = (⨆n, (eapprox f n).lintegral μ) :=
calc (∫⁻ a, f a ∂μ) = (∫⁻ a, ⨆n, (eapprox f n : α → ℝ≥0∞) a ∂μ) :
  by congr; ext a; rw [supr_eapprox_apply f hf]
... = (⨆n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ) :
begin
  rw [lintegral_supr],
  { measurability, },
  { assume i j h, exact (monotone_eapprox f h) }
end
... = (⨆n, (eapprox f n).lintegral μ) : by congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
lemma exists_pos_set_lintegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ < ∞)
  {ε : ℝ≥0∞} (hε : 0 < ε) :
  ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε :=
begin
  rcases exists_between hε with ⟨ε₂, hε₂0, hε₂ε⟩, rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩,
  rcases exists_simple_func_forall_lintegral_sub_lt_of_pos h hε₁0 with ⟨φ, hle, hφ⟩,
  rcases φ.exists_forall_le with ⟨C, hC⟩,
  use [(ε₂ - ε₁) / C, ennreal.div_pos_iff.2 ⟨(zero_lt_sub_iff_lt.2 hε₁₂).ne', ennreal.coe_ne_top⟩],
  intros s hs,
  simp only [lintegral_eq_nnreal, supr_lt_iff, supr_le_iff],
  refine ⟨ε₂, hε₂ε, λ ψ hψ, _⟩,
  calc (map coe ψ).lintegral (μ.restrict s)
      ≤ (map coe φ).lintegral (μ.restrict s) + (map coe (ψ - φ)).lintegral (μ.restrict s) :
    begin
      rw [← simple_func.add_lintegral, ← simple_func.map_add @ennreal.coe_add],
      refine simple_func.lintegral_mono (λ x, _) le_rfl,
      simp [-ennreal.coe_add, nnreal.add_sub_eq_max, le_max_right]
    end
  ... ≤ (map coe φ).lintegral (μ.restrict s) + ε₁ :
    begin
      refine add_le_add le_rfl (le_trans _ (hφ _ hψ).le),
      exact simple_func.lintegral_mono le_rfl measure.restrict_le_self
    end
  ... ≤ (simple_func.const α (C : ℝ≥0∞)).lintegral (μ.restrict s) + ε₁ :
    by { mono*, exacts [λ x, coe_le_coe.2 (hC x), le_rfl, le_rfl] }
  ... = C * μ s + ε₁ : by simp [← simple_func.lintegral_eq_lintegral]
  ... ≤ C * ((ε₂ - ε₁) / C) + ε₁ : by { mono*, exacts [le_rfl, hs.le, le_rfl] }
  ... ≤ (ε₂ - ε₁) + ε₁ : add_le_add mul_div_le le_rfl
  ... = ε₂ : sub_add_cancel_of_le hε₁₂.le,
end

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
lemma tendsto_set_lintegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ < ∞)
  {l : filter ι} {s : ι → set α} (hl : tendsto (μ ∘ s) l (𝓝 0)) :
  tendsto (λ i, ∫⁻ x in s i, f x ∂μ) l (𝓝 0) :=
begin
  simp only [ennreal.nhds_zero, tendsto_infi, tendsto_principal, mem_Iio, ← pos_iff_ne_zero]
    at hl ⊢,
  intros ε ε0,
  rcases exists_pos_set_lintegral_lt_of_measure_lt h ε0 with ⟨δ, δ0, hδ⟩,
  exact (hl δ δ0).mono (λ i, hδ _)
end

@[simp] lemma lintegral_add {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :=
calc (∫⁻ a, f a + g a ∂μ) =
    (∫⁻ a, (⨆n, (eapprox f n : α → ℝ≥0∞) a) + (⨆n, (eapprox g n : α → ℝ≥0∞) a) ∂μ) :
    by simp only [supr_eapprox_apply, hf, hg]
  ... = (∫⁻ a, (⨆n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a) ∂μ) :
  begin
    congr, funext a,
    rw [ennreal.supr_add_supr_of_monotone], { refl },
    { assume i j h, exact monotone_eapprox _ h a },
    { assume i j h, exact monotone_eapprox _ h a },
  end
  ... = (⨆n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ) :
  begin
    rw [lintegral_supr],
    { congr,
      funext n, rw [← simple_func.add_lintegral, ← simple_func.lintegral_eq_lintegral],
      refl },
    { measurability, },
    { assume i j h a, exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _) }
  end
  ... = (⨆n, (eapprox f n).lintegral μ) + (⨆n, (eapprox g n).lintegral μ) :
  by refine (ennreal.supr_add_supr_of_monotone _ _).symm;
     { assume i j h, exact simple_func.lintegral_mono (monotone_eapprox _ h) (le_refl μ) }
  ... = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :
    by rw [lintegral_eq_supr_eapprox_lintegral hf, lintegral_eq_supr_eapprox_lintegral hg]

lemma lintegral_add' {f g : α → ℝ≥0∞} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :=
calc (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, hf.mk f a + hg.mk g a ∂μ) :
  lintegral_congr_ae (eventually_eq.add hf.ae_eq_mk hg.ae_eq_mk)
... = (∫⁻ a, hf.mk f a ∂μ) + (∫⁻ a, hg.mk g a ∂μ) : lintegral_add hf.measurable_mk hg.measurable_mk
... = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) : begin
  congr' 1,
  { exact lintegral_congr_ae hf.ae_eq_mk.symm },
  { exact lintegral_congr_ae hg.ae_eq_mk.symm },
end

lemma lintegral_zero : (∫⁻ a:α, 0 ∂μ) = 0 := by simp

lemma lintegral_zero_fun : (∫⁻ a:α, (0 : α → ℝ≥0∞) a ∂μ) = 0 := by simp

@[simp] lemma lintegral_smul_measure (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂ (c • μ) = c * ∫⁻ a, f a ∂μ :=
by simp only [lintegral, supr_subtype', simple_func.lintegral_smul, ennreal.mul_supr, smul_eq_mul]

@[simp] lemma lintegral_sum_measure {ι} (f : α → ℝ≥0∞) (μ : ι → measure α) :
  ∫⁻ a, f a ∂(measure.sum μ) = ∑' i, ∫⁻ a, f a ∂(μ i) :=
begin
  simp only [lintegral, supr_subtype', simple_func.lintegral_sum, ennreal.tsum_eq_supr_sum],
  rw [supr_comm],
  congr, funext s,
  induction s using finset.induction_on with i s hi hs, { apply bot_unique, simp },
  simp only [finset.sum_insert hi, ← hs],
  refine (ennreal.supr_add_supr _).symm,
  intros φ ψ,
  exact ⟨⟨φ ⊔ ψ, λ x, sup_le (φ.2 x) (ψ.2 x)⟩,
    add_le_add (simple_func.lintegral_mono le_sup_left (le_refl _))
      (finset.sum_le_sum $ λ j hj, simple_func.lintegral_mono le_sup_right (le_refl _))⟩
end

@[simp] lemma lintegral_add_measure (f : α → ℝ≥0∞) (μ ν : measure α) :
  ∫⁻ a, f a ∂ (μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν :=
by simpa [tsum_fintype] using lintegral_sum_measure f (λ b, cond b μ ν)

@[simp] lemma lintegral_zero_measure (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂0 = 0 :=
bot_unique $ by simp [lintegral]

lemma lintegral_finset_sum (s : finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b ∈ s, measurable (f b)) :
  (∫⁻ a, ∑ b in s, f b a ∂μ) = ∑ b in s, ∫⁻ a, f b a ∂μ :=
begin
  induction s using finset.induction_on with a s has ih,
  { simp },
  { simp only [finset.sum_insert has],
    rw [finset.forall_mem_insert] at hf,
    rw [lintegral_add hf.1 (s.measurable_sum hf.2), ih hf.2] }
end

@[simp] lemma lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
calc (∫⁻ a, r * f a ∂μ) = (∫⁻ a, (⨆n, (const α r * eapprox f n) a) ∂μ) :
    by { congr, funext a, rw [← supr_eapprox_apply f hf, ennreal.mul_supr], refl }
  ... = (⨆n, r * (eapprox f n).lintegral μ) :
  begin
    rw [lintegral_supr],
    { congr, funext n,
      rw [← simple_func.const_mul_lintegral, ← simple_func.lintegral_eq_lintegral] },
    { assume n, exact simple_func.measurable _ },
    { assume i j h a, exact canonically_ordered_semiring.mul_le_mul (le_refl _)
        (monotone_eapprox _ h _) }
  end
  ... = r * (∫⁻ a, f a ∂μ) : by rw [← ennreal.mul_supr, lintegral_eq_supr_eapprox_lintegral hf]

lemma lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
begin
  have A : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk,
  have B : ∫⁻ a, r * f a ∂μ = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (eventually_eq.fun_comp hf.ae_eq_mk _),
  rw [A, B, lintegral_const_mul _ hf.measurable_mk],
end

lemma lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
  r * (∫⁻ a, f a ∂μ) ≤ (∫⁻ a, r * f a ∂μ) :=
begin
  rw [lintegral, ennreal.mul_supr],
  refine supr_le (λs, _),
  rw [ennreal.mul_supr],
  simp only [supr_le_iff, ge_iff_le],
  assume hs,
  rw ← simple_func.const_mul_lintegral,
  refine le_supr_of_le (const α r * s) (le_supr_of_le (λx, _) (le_refl _)),
  exact canonically_ordered_semiring.mul_le_mul (le_refl _) (hs x)
end

lemma lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
begin
  by_cases h : r = 0,
  { simp [h] },
  apply le_antisymm _ (lintegral_const_mul_le r f),
  have rinv : r * r⁻¹  = 1 := ennreal.mul_inv_cancel h hr,
  have rinv' : r ⁻¹ * r = 1, by { rw mul_comm, exact rinv },
  have := lintegral_const_mul_le (r⁻¹) (λx, r * f x),
  simp [(mul_assoc _ _ _).symm, rinv'] at this,
  simpa [(mul_assoc _ _ _).symm, rinv]
    using canonically_ordered_semiring.mul_le_mul (le_refl r) this
end

lemma lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul r hf]

lemma lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul'' r hf]

lemma lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂μ * r ≤ ∫⁻ a, f a * r ∂μ :=
by simp_rw [mul_comm, lintegral_const_mul_le r f]

lemma lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞):
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul' r f hr]

/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/
lemma lintegral_lintegral_mul {β} [measurable_space β] {ν : measure β}
  {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : ae_measurable f μ) (hg : ae_measurable g ν) :
  ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = ∫⁻ x, f x ∂μ * ∫⁻ y, g y ∂ν :=
by simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
  (∫⁻ a, g (f a) ∂μ) = (∫⁻ a, g (f' a) ∂μ) :=
lintegral_congr_ae $ h.mono $ λ a h, by rw h

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁')
  (h₂ : f₂ =ᵐ[μ] f₂') (g : β → γ → ℝ≥0∞) :
  (∫⁻ a, g (f₁ a) (f₂ a) ∂μ) = (∫⁻ a, g (f₁' a) (f₂' a) ∂μ) :=
lintegral_congr_ae $ h₁.mp $ h₂.mono $ λ _ h₂ h₁, by rw [h₁, h₂]

@[simp] lemma lintegral_indicator (f : α → ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ :=
begin
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, supr_subtype'],
  apply le_antisymm; refine supr_le_supr2 (subtype.forall.2 $ λ φ hφ, _),
  { refine ⟨⟨φ, le_trans hφ (indicator_le_self _ _)⟩, _⟩,
    refine simple_func.lintegral_mono (λ x, _) (le_refl _),
    by_cases hx : x ∈ s,
    { simp [hx, hs, le_refl] },
    { apply le_trans (hφ x),
      simp [hx, hs, le_refl] } },
  { refine ⟨⟨φ.restrict s, λ x, _⟩, le_refl _⟩,
    simp [hφ x, hs, indicator_le_indicator] }
end

/-- Chebyshev's inequality -/
lemma mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : measurable f) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ :=
begin
  have : measurable_set {a : α | ε ≤ f a }, from hf measurable_set_Ici,
  rw [← simple_func.restrict_const_lintegral _ this, ← simple_func.lintegral_eq_lintegral],
  refine lintegral_mono (λ a, _),
  simp only [restrict_apply _ this],
  exact indicator_apply_le id
end

lemma meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : measurable f) {ε : ℝ≥0∞}
  (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
  μ {x | ε ≤ f x} ≤ (∫⁻ a, f a ∂μ) / ε :=
(ennreal.le_div_iff_mul_le (or.inl hε) (or.inl hε')).2 $
by { rw [mul_comm], exact mul_meas_ge_le_lintegral hf ε }

@[simp] lemma lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂μ = 0 ↔ (f =ᵐ[μ] 0) :=
begin
  refine iff.intro (assume h, _) (assume h, _),
  { have : ∀n:ℕ, ∀ᵐ a ∂μ, f a < n⁻¹,
    { assume n,
      rw [ae_iff, ← nonpos_iff_eq_zero, ← @ennreal.zero_div n⁻¹,
        ennreal.le_div_iff_mul_le, mul_comm],
      simp only [not_lt],
      -- TODO: why `rw ← h` fails with "not an equality or an iff"?
      exacts [h ▸ mul_meas_ge_le_lintegral hf n⁻¹,
        or.inl (ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top),
        or.inr ennreal.zero_ne_top] },
    refine (ae_all_iff.2 this).mono (λ a ha, _),
    by_contradiction h,
    rcases ennreal.exists_inv_nat_lt h with ⟨n, hn⟩,
    exact (lt_irrefl _ $ lt_trans hn $ ha n).elim },
  { calc ∫⁻ a, f a ∂μ = ∫⁻ a, 0 ∂μ : lintegral_congr_ae h
      ... = 0 : lintegral_zero }
end

@[simp] lemma lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  ∫⁻ a, f a ∂μ = 0 ↔ (f =ᵐ[μ] 0) :=
begin
  have : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk,
  rw [this, lintegral_eq_zero_iff hf.measurable_mk],
  exact ⟨λ H, hf.ae_eq_mk.trans H, λ H, hf.ae_eq_mk.symm.trans H⟩
end

lemma lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : measurable f) :
  0 < ∫⁻ a, f a ∂μ ↔ 0 < μ (function.support f) :=
by simp [pos_iff_ne_zero, hf, filter.eventually_eq, ae_iff, function.support]

/-- Weaker version of the monotone convergence theorem-/
lemma lintegral_supr_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀n, measurable (f n))
  (h_mono : ∀n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
let ⟨s, hs⟩ := exists_measurable_superset_of_null
                       (ae_iff.1 (ae_all_iff.2 h_mono)) in
let g := λ n a, if a ∈ s then 0 else f n a in
have g_eq_f : ∀ᵐ a ∂μ, ∀n, g n a = f n a,
  from (measure_zero_iff_ae_nmem.1 hs.2.2).mono (assume a ha n, if_neg ha),
calc
  ∫⁻ a, ⨆n, f n a ∂μ = ∫⁻ a, ⨆n, g n a ∂μ :
  lintegral_congr_ae $ g_eq_f.mono $ λ a ha, by simp only [ha]
  ... = ⨆n, (∫⁻ a, g n a ∂μ) :
  lintegral_supr
    (assume n, measurable_const.piecewise hs.2.1 (hf n))
    (monotone_of_monotone_nat $ assume n a, classical.by_cases
      (assume h : a ∈ s, by simp [g, if_pos h])
      (assume h : a ∉ s,
      begin
        simp only [g, if_neg h], have := hs.1, rw subset_def at this, have := mt (this a) h,
        simp only [not_not, mem_set_of_eq] at this, exact this n
      end))
  ... = ⨆n, (∫⁻ a, f n a ∂μ) :
    by simp only [lintegral_congr_ae (g_eq_f.mono $ λ a ha, ha _)]

lemma lintegral_sub {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g)
  (hg_fin : ∫⁻ a, g a ∂μ < ∞) (h_le : g ≤ᵐ[μ] f) :
  ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
begin
  rw [← ennreal.add_left_inj hg_fin,
        ennreal.sub_add_cancel_of_le (lintegral_mono_ae h_le),
      ← lintegral_add (hf.sub hg) hg],
  refine lintegral_congr_ae (h_le.mono $ λ x hx, _),
  exact ennreal.sub_add_cancel_of_le hx
end

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi_ae
  {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n))
  (h_mono : ∀n:ℕ, f n.succ ≤ᵐ[μ] f n) (h_fin : ∫⁻ a, f 0 a ∂μ < ∞) :
  ∫⁻ a, ⨅n, f n a ∂μ = ⨅n, ∫⁻ a, f n a ∂μ :=
have fn_le_f0 : ∫⁻ a, ⨅n, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ, from
  lintegral_mono (assume a, infi_le_of_le 0 (le_refl _)),
have fn_le_f0' : (⨅n, ∫⁻ a, f n a ∂μ) ≤ ∫⁻ a, f 0 a ∂μ, from infi_le_of_le 0 (le_refl _),
(ennreal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 $
show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅n, f n a ∂μ = ∫⁻ a, f 0 a ∂μ - (⨅n, ∫⁻ a, f n a ∂μ), from
calc
  ∫⁻ a, f 0 a ∂μ - (∫⁻ a, ⨅n, f n a ∂μ) = ∫⁻ a, f 0 a - ⨅n, f n a ∂μ:
    (lintegral_sub (h_meas 0) (measurable_infi h_meas)
    (calc
      (∫⁻ a, ⨅n, f n a ∂μ)  ≤ ∫⁻ a, f 0 a ∂μ : lintegral_mono (assume a, infi_le _ _)
          ... < ∞ : h_fin  )
    (ae_of_all _ $ assume a, infi_le _ _)).symm
  ... = ∫⁻ a, ⨆n, f 0 a - f n a ∂μ : congr rfl (funext (assume a, ennreal.sub_infi))
  ... = ⨆n, ∫⁻ a, f 0 a - f n a ∂μ :
    lintegral_supr_ae
      (assume n, (h_meas 0).sub (h_meas n))
      (assume n, (h_mono n).mono $ assume a ha, ennreal.sub_le_sub (le_refl _) ha)
  ... = ⨆n, ∫⁻ a, f 0 a ∂μ - ∫⁻ a, f n a ∂μ :
    have h_mono : ∀ᵐ a ∂μ, ∀n:ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono,
    have h_mono : ∀n, ∀ᵐ a ∂μ, f n a ≤ f 0 a := assume n, h_mono.mono $ assume a h,
    begin
      induction n with n ih,
      {exact le_refl _}, {exact le_trans (h n) ih}
    end,
    congr rfl (funext $ assume n, lintegral_sub (h_meas _) (h_meas _)
      (calc
        ∫⁻ a, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ : lintegral_mono_ae $ h_mono n
        ... < ∞ : h_fin)
        (h_mono n))
  ... = ∫⁻ a, f 0 a ∂μ - ⨅n, ∫⁻ a, f n a ∂μ : ennreal.sub_infi.symm

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi
  {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n))
  (h_mono : ∀ ⦃m n⦄, m ≤ n → f n ≤ f m) (h_fin : ∫⁻ a, f 0 a ∂μ < ∞) :
  ∫⁻ a, ⨅n, f n a ∂μ = ⨅n, ∫⁻ a, f n a ∂μ :=
lintegral_infi_ae h_meas (λ n, ae_of_all _ $ h_mono $ le_of_lt n.lt_succ_self) h_fin

/-- Known as Fatou's lemma, version with `ae_measurable` functions -/
lemma lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, ae_measurable (f n) μ) :
  ∫⁻ a, liminf at_top (λ n, f n a) ∂μ ≤ liminf at_top (λ n, ∫⁻ a, f n a ∂μ) :=
calc
  ∫⁻ a, liminf at_top (λ n, f n a) ∂μ = ∫⁻ a, ⨆n:ℕ, ⨅i≥n, f i a ∂μ :
     by simp only [liminf_eq_supr_infi_of_nat]
  ... = ⨆n:ℕ, ∫⁻ a, ⨅i≥n, f i a ∂μ :
    lintegral_supr'
      (assume n, ae_measurable_binfi _ (countable_encodable _) h_meas)
      (ae_of_all μ (assume a n m hnm, infi_le_infi_of_subset $ λ i hi, le_trans hnm hi))
  ... ≤ ⨆n:ℕ, ⨅i≥n, ∫⁻ a, f i a ∂μ :
    supr_le_supr $ λ n, le_infi2_lintegral _
  ... = at_top.liminf (λ n, ∫⁻ a, f n a ∂μ) : filter.liminf_eq_supr_infi_of_nat.symm

/-- Known as Fatou's lemma -/
lemma lintegral_liminf_le {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n)) :
  ∫⁻ a, liminf at_top (λ n, f n a) ∂μ ≤ liminf at_top (λ n, ∫⁻ a, f n a ∂μ) :=
lintegral_liminf_le' (λ n, (h_meas n).ae_measurable)

lemma limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
  (hf_meas : ∀ n, measurable (f n)) (h_bound : ∀n, f n ≤ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ < ∞) :
  limsup at_top (λn, ∫⁻ a, f n a ∂μ) ≤ ∫⁻ a, limsup at_top (λn, f n a) ∂μ :=
calc
  limsup at_top (λn, ∫⁻ a, f n a ∂μ) = ⨅n:ℕ, ⨆i≥n, ∫⁻ a, f i a ∂μ :
    limsup_eq_infi_supr_of_nat
  ... ≤ ⨅n:ℕ, ∫⁻ a, ⨆i≥n, f i a ∂μ :
    infi_le_infi $ assume n, supr2_lintegral_le _
  ... = ∫⁻ a, ⨅n:ℕ, ⨆i≥n, f i a ∂μ :
    begin
      refine (lintegral_infi _ _ _).symm,
      { assume n, exact measurable_bsupr _ (countable_encodable _) hf_meas },
      { assume n m hnm a, exact (supr_le_supr_of_subset $ λ i hi, le_trans hnm hi) },
      { refine lt_of_le_of_lt (lintegral_mono_ae _) h_fin,
        refine (ae_all_iff.2 h_bound).mono (λ n hn, _),
        exact supr_le (λ i, supr_le $ λ hi, hn i) }
    end
  ... = ∫⁻ a, limsup at_top (λn, f n a) ∂μ :
    by simp only [limsup_eq_infi_supr_of_nat]

/-- Dominated convergence theorem for nonnegative functions -/
lemma tendsto_lintegral_of_dominated_convergence
  {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀n, measurable (F n)) (h_bound : ∀n, F n ≤ᵐ[μ] bound)
  (h_fin : ∫⁻ a, bound a ∂μ < ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) at_top (𝓝 (∫⁻ a, f a ∂μ)) :=
tendsto_of_le_liminf_of_limsup_le
(calc ∫⁻ a, f a ∂μ = ∫⁻ a, liminf at_top (λ (n : ℕ), F n a) ∂μ :
      lintegral_congr_ae $ h_lim.mono $ assume a h, h.liminf_eq.symm
 ... ≤ liminf at_top (λ n, ∫⁻ a, F n a ∂μ) : lintegral_liminf_le hF_meas)
(calc limsup at_top (λ (n : ℕ), ∫⁻ a, F n a ∂μ) ≤ ∫⁻ a, limsup at_top (λn, F n a) ∂μ :
      limsup_lintegral_le hF_meas h_bound h_fin
 ... = ∫⁻ a, f a ∂μ : lintegral_congr_ae $ h_lim.mono $ λ a h, h.limsup_eq)

/-- Dominated convergence theorem for nonnegative functions which are just almost everywhere
measurable. -/
lemma tendsto_lintegral_of_dominated_convergence'
  {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀n, ae_measurable (F n) μ) (h_bound : ∀n, F n ≤ᵐ[μ] bound)
  (h_fin : ∫⁻ a, bound a ∂μ < ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) at_top (𝓝 (∫⁻ a, f a ∂μ)) :=
begin
  have : ∀ n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ :=
    λ n, lintegral_congr_ae (hF_meas n).ae_eq_mk,
  simp_rw this,
  apply tendsto_lintegral_of_dominated_convergence bound (λ n, (hF_meas n).measurable_mk) _ h_fin,
  { have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a :=
      λ n, (hF_meas n).ae_eq_mk.symm,
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this,
    filter_upwards [this, h_lim],
    assume a H H',
    simp_rw H,
    exact H' },
  { assume n,
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk],
    assume a H H',
    rwa H' at H }
end

/-- Dominated convergence theorem for filters with a countable basis -/
lemma tendsto_lintegral_filter_of_dominated_convergence {ι} {l : filter ι}
  {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hl_cb : l.is_countably_generated)
  (hF_meas : ∀ᶠ n in l, measurable (F n))
  (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
  (h_fin : ∫⁻ a, bound a ∂μ < ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) l (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) l (𝓝 $ ∫⁻ a, f a ∂μ) :=
begin
  rw hl_cb.tendsto_iff_seq_tendsto,
  { intros x xl,
    have hxl, { rw tendsto_at_top' at xl, exact xl },
    have h := inter_mem_sets hF_meas h_bound,
    replace h := hxl _ h,
    rcases h with ⟨k, h⟩,
    rw ← tendsto_add_at_top_iff_nat k,
    refine tendsto_lintegral_of_dominated_convergence _ _ _ _ _,
    { exact bound },
    { intro, refine (h _ _).1, exact nat.le_add_left _ _ },
    { intro, refine (h _ _).2, exact nat.le_add_left _ _ },
    { assumption },
    { refine h_lim.mono (λ a h_lim, _),
      apply @tendsto.comp _ _ _ (λn, x (n + k)) (λn, F n a),
      { assumption },
      rw tendsto_add_at_top_iff_nat,
      assumption } },
end

section
open encodable

/-- Monotone convergence for a suprema over a directed family and indexed by an encodable type -/
theorem lintegral_supr_directed [encodable β] {f : β → α → ℝ≥0∞}
  (hf : ∀b, measurable (f b)) (h_directed : directed (≤) f) :
  ∫⁻ a, ⨆b, f b a ∂μ = ⨆b, ∫⁻ a, f b a ∂μ :=
begin
  by_cases hβ : nonempty β, swap,
  { simp [supr_of_empty hβ] },
  resetI, inhabit β,
  have : ∀a, (⨆ b, f b a) = (⨆ n, f (h_directed.sequence f n) a),
  { assume a,
    refine le_antisymm (supr_le $ assume b, _) (supr_le $ assume n, le_supr (λn, f n a) _),
    exact le_supr_of_le (encode b + 1) (h_directed.le_sequence b a) },
  calc ∫⁻ a, ⨆ b, f b a ∂μ = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ :
      by simp only [this]
    ... = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :
      lintegral_supr (assume n, hf _) h_directed.sequence_mono
    ... = ⨆ b, ∫⁻ a, f b a ∂μ :
    begin
      refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume b, _),
      { exact le_supr (λb, ∫⁻ a, f b a ∂μ) _ },
      { exact le_supr_of_le (encode b + 1)
          (lintegral_mono $ h_directed.le_sequence b) }
    end
end

end

lemma lintegral_tsum [encodable β] {f : β → α → ℝ≥0∞} (hf : ∀i, measurable (f i)) :
  ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ :=
begin
  simp only [ennreal.tsum_eq_supr_sum],
  rw [lintegral_supr_directed],
  { simp [lintegral_finset_sum _ (λ i _, hf i)] },
  { assume b, exact finset.measurable_sum _ (λ i _, hf i) },
  { assume s t,
    use [s ∪ t],
    split,
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_left _ _),
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_right _ _) }
end

open measure

lemma lintegral_Union [encodable β] {s : β → set α} (hm : ∀ i, measurable_set (s i))
  (hd : pairwise (disjoint on s)) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
by simp only [measure.restrict_Union hd hm, lintegral_sum_measure]

lemma lintegral_Union_le [encodable β] (s : β → set α) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ :=
begin
  rw [← lintegral_sum_measure],
  exact lintegral_mono' restrict_Union_le (le_refl _)
end

lemma lintegral_map [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  (hf : measurable f) (hg : measurable g) : ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
begin
  simp only [lintegral_eq_supr_eapprox_lintegral, hf, hf.comp hg],
  { congr, funext n, symmetry,
    apply simple_func.lintegral_map,
    { assume a, exact congr_fun (simple_func.eapprox_comp hf hg) a },
    { assume s hs, exact map_apply hg hs } },
end

lemma lintegral_map' [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  (hf : ae_measurable f (measure.map g μ)) (hg : measurable g) :
  ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, f (g a) ∂μ :=
calc ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, hf.mk f a ∂(measure.map g μ) :
  lintegral_congr_ae hf.ae_eq_mk
... = ∫⁻ a, hf.mk f (g a) ∂μ : lintegral_map hf.measurable_mk hg
... = ∫⁻ a, f (g a) ∂μ : lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

lemma lintegral_comp [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  (hf : measurable f) (hg : measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂(map g μ) :=
(lintegral_map hf hg).symm

lemma set_lintegral_map [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  {s : set β} (hs : measurable_set s) (hf : measurable f) (hg : measurable g) :
  ∫⁻ y in s, f y ∂(map g μ) = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ :=
by rw [restrict_map hg hs, lintegral_map hf hg]

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
lemma lintegral_map_equiv [measurable_space β] (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
  ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
begin
  refine le_antisymm _ _,
  { refine supr_le_supr2 _,
    intros f₀,
    use f₀.comp g g.measurable,
    refine supr_le_supr2 _,
    intros hf₀,
    use λ x, hf₀ (g x),
    exact (lintegral_map_equiv f₀ g).symm.le },
  { refine supr_le_supr2 _,
    intros f₀,
    use f₀.comp g.symm g.symm.measurable,
    refine supr_le_supr2 _,
    intros hf₀,
    have : (λ a, (f₀.comp (g.symm) g.symm.measurable) a) ≤ λ (a : β), f a,
    { convert λ x, hf₀ (g.symm x),
      funext,
      simp [congr_arg f (congr_fun g.self_comp_symm a)] },
    use this,
    convert (lintegral_map_equiv (f₀.comp g.symm g.symm.measurable) g).le,
    apply simple_func.ext,
    intros a,
    convert congr_arg f₀ (congr_fun g.symm_comp_self a).symm using 1 }
end

lemma lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂(dirac a) = f a :=
by simp [lintegral_congr_ae (ae_eq_dirac' hf)]

lemma lintegral_dirac [measurable_singleton_class α] (a : α) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂(dirac a) = f a :=
by simp [lintegral_congr_ae (ae_eq_dirac f)]

lemma lintegral_count' {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂count = ∑' a, f a :=
begin
  rw [count, lintegral_sum_measure],
  congr,
  exact funext (λ a, lintegral_dirac' a hf),
end

lemma lintegral_count [measurable_singleton_class α] (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂count = ∑' a, f a :=
begin
  rw [count, lintegral_sum_measure],
  congr,
  exact funext (λ a, lintegral_dirac a f),
end

lemma ae_lt_top {f : α → ℝ≥0∞} (hf : measurable f) (h2f : ∫⁻ x, f x ∂μ < ∞) :
  ∀ᵐ x ∂μ, f x < ∞ :=
begin
  simp_rw [ae_iff, ennreal.not_lt_top], by_contra h, rw [← not_le] at h2f, apply h2f,
  have : (f ⁻¹' {∞}).indicator ⊤ ≤ f,
  { intro x, by_cases hx : x ∈ f ⁻¹' {∞}; [simpa [hx], simp [hx]] },
  convert lintegral_mono this,
  rw [lintegral_indicator _ (hf (measurable_set_singleton ∞))], simp [ennreal.top_mul, preimage, h]
end

lemma ae_lt_top' {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (h2f : ∫⁻ x, f x ∂μ < ∞) :
  ∀ᵐ x ∂μ, f x < ∞ :=
begin
  have h2f_meas : ∫⁻ x, hf.mk f x ∂μ < ∞, by rwa ←lintegral_congr_ae hf.ae_eq_mk,
  exact (ae_lt_top hf.measurable_mk h2f_meas).mp (hf.ae_eq_mk.mono (λ x hx h, by rwa hx)),
end

/-- Given a measure `μ : measure α` and a function `f : α → ℝ≥0∞`, `μ.with_density f` is the
measure such that for a measurable set `s` we have `μ.with_density f s = ∫⁻ a in s, f a ∂μ`. -/
def measure.with_density (μ : measure α) (f : α → ℝ≥0∞) : measure α :=
measure.of_measurable (λs hs, ∫⁻ a in s, f a ∂μ) (by simp) (λ s hs hd, lintegral_Union hs hd _)

@[simp] lemma with_density_apply (f : α → ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  μ.with_density f s = ∫⁻ a in s, f a ∂μ :=
measure.of_measurable_apply s hs

end lintegral

end measure_theory

open measure_theory measure_theory.simple_func
/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_eliminator]
theorem measurable.ennreal_induction {α} [measurable_space α] {P : (α → ℝ≥0∞) → Prop}
  (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, measurable_set s → P (indicator s (λ _, c)))
  (h_add : ∀ ⦃f g : α → ℝ≥0∞⦄, disjoint (support f) (support g) → measurable f → measurable g →
    P f → P g → P (f + g))
  (h_supr : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄ (hf : ∀n, measurable (f n)) (h_mono : monotone f)
    (hP : ∀ n, P (f n)), P (λ x, ⨆ n, f n x))
  ⦃f : α → ℝ≥0∞⦄ (hf : measurable f) : P f :=
begin
  convert h_supr (λ n, (eapprox f n).measurable) (monotone_eapprox f) _,
  { ext1 x, rw [supr_eapprox_apply f hf] },
  { exact λ n, simple_func.induction (λ c s hs, h_ind c hs)
      (λ f g hfg hf hg, h_add hfg f.measurable g.measurable hf hg) (eapprox f n) }
end

namespace measure_theory

/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.with_density f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.with_density f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
lemma lintegral_with_density_eq_lintegral_mul {α} [measurable_space α] (μ : measure α)
  {f : α → ℝ≥0∞} (h_mf : measurable f) : ∀ {g : α → ℝ≥0∞}, measurable g →
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  apply measurable.ennreal_induction,
  { intros c s h_ms,
    simp [*, mul_comm _ c, ← indicator_mul_right], },
  { intros g h h_univ h_mea_g h_mea_h h_ind_g h_ind_h,
    simp [mul_add, *, measurable.mul] },
  { intros g h_mea_g h_mono_g h_ind,
    have : monotone (λ n a, f a * g n a) := λ m n hmn x, ennreal.mul_le_mul le_rfl (h_mono_g hmn x),
    simp [lintegral_supr, ennreal.mul_supr, h_mf.mul (h_mea_g _), *] }
end

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
lemma exists_integrable_pos_of_sigma_finite
  {α} [measurable_space α] (μ : measure α) [sigma_finite μ] {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ measurable g ∧ (∫⁻ x, g x ∂μ < ε) :=
begin
  /- The desired function is almost `∑' n, indicator (s n) * δ n / μ (s n)` where `s n` is any
    sequence of finite measure sets covering the whole space, which exists by sigma-finiteness,
    and `δ n` is any summable sequence with sum at most `ε`.
    The only problem with this definition is that `μ (s n)` might be small, so it is not guaranteed
    that this series converges everywhere (although it does almost everywhere, as its integral is
    `∑ n, δ n`). We solve this by using instead `∑' n, indicator (s n) * δ n / max (1, μ (s n))` -/
  obtain ⟨δ, δpos, ⟨cδ, δsum, c_lt⟩⟩ :
    ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ ∃ (c : ℝ≥0), has_sum δ c ∧ c < ε :=
    nnreal.exists_pos_sum_of_encodable εpos ℕ,
  set s := spanning_sets μ with hs,
  have I : ∀ n, 0 < max 1 (μ (s n)).to_nnreal := λ n, zero_lt_one.trans_le (le_max_left _ _),
  let ρ := λ n, δ n / max 1 (μ (s n)).to_nnreal,
  let g := λ x, ∑' n, ((s n).indicator (λ x, ρ n) x),
  have A : summable ρ,
  { apply nnreal.summable_of_le (λ n, _) δsum.summable,
    rw nnreal.div_le_iff (I n).ne',
    conv_lhs { rw ← mul_one (δ n) },
    exact mul_le_mul (le_refl _) (le_max_left _ _) bot_le bot_le },
  have B : ∀ x, summable (λ n, (s n).indicator (λ x, ρ n) x),
  { assume x,
    apply nnreal.summable_of_le (λ n, _) A,
    simp only [set.indicator],
    split_ifs,
    { exact le_refl _ },
    { exact bot_le } },
  have M : ∀ n, measurable ((s n).indicator (λ x, ρ n)) :=
    λ n, measurable_const.indicator (measurable_spanning_sets μ n),
  refine ⟨g, λ x, _, measurable.nnreal_tsum M, _⟩,
  { have : x ∈ (⋃ n, s n), by { rw [hs, Union_spanning_sets], exact set.mem_univ _ },
    rcases set.mem_Union.1 this with ⟨n, hn⟩,
    simp only [nnreal.tsum_pos (B x) n, hn, set.indicator_of_mem, nnreal.div_pos (δpos n) (I n)] },
  { calc ∫⁻ (x : α), (g x) ∂μ
        = ∫⁻ x, ∑' n, (((s n).indicator (λ x, ρ n) x : ℝ≥0) : ℝ≥0∞) ∂μ :
      by { apply lintegral_congr (λ x, _), simp_rw [g, ennreal.coe_tsum (B x)] }
    ... = ∑' n, ∫⁻ x, (((s n).indicator (λ x, ρ n) x : ℝ≥0) : ℝ≥0∞) ∂μ :
      lintegral_tsum (λ n, (M n).coe_nnreal_ennreal)
    ... = ∑' n, μ (s n) * ρ n :
      by simp only [measurable_spanning_sets μ, lintegral_const, measurable_set.univ, mul_comm,
                    lintegral_indicator, univ_inter, coe_indicator, measure.restrict_apply]
    ... ≤ ∑' n, δ n :
      begin
        apply ennreal.tsum_le_tsum (λ n, _),
        rw [ennreal.coe_div (I n).ne', ← mul_div_assoc, mul_comm, ennreal.coe_max],
        apply ennreal.div_le_of_le_mul (ennreal.mul_le_mul (le_refl _) _),
        convert le_max_right _ _,
        exact ennreal.coe_to_nnreal (measure_spanning_sets_lt_top μ n).ne
      end
    ... < ε : by rwa [← ennreal.coe_tsum δsum.summable, ennreal.coe_lt_coe, δsum.tsum_eq] }
end

lemma lintegral_trim {α : Type*} {m m0 : measurable_space α} {μ : measure α} (hm : m ≤ m0)
  {f : α → ℝ≥0∞} (hf : @measurable _ _ m _ f) :
  @lintegral _ m (μ.trim hm) f = ∫⁻ a, f a ∂μ :=
begin
  refine @measurable.ennreal_induction α m
    (λ f, @lintegral _ m (μ.trim hm) f = ∫⁻ a, f a ∂μ) _ _ _ f hf,
  { intros c s hs,
    rw [@lintegral_indicator α m _ _ _ hs, @lintegral_indicator α _ _ _ _ (hm s hs),
      @set_lintegral_const α m, set_lintegral_const],
    suffices h_trim_s : μ.trim hm s = μ s, by rw h_trim_s,
    exact trim_measurable_set_eq hm hs, },
  { intros f g hfg hf hg hf_prop hg_prop,
    have h_m := @lintegral_add _ m (μ.trim hm) f g hf hg,
    have h_m0 := @lintegral_add _ m0 μ f g (measurable.mono hf hm le_rfl)
      (measurable.mono hg hm le_rfl),
    rwa [hf_prop, hg_prop, ← h_m0] at h_m, },
  { intros f hf hf_mono hf_prop,
    rw @lintegral_supr α m (μ.trim hm) _ hf hf_mono,
    rw @lintegral_supr α m0 μ _ (λ n, measurable.mono (hf n) hm le_rfl) hf_mono,
    congr,
    exact funext (λ n, hf_prop n), },
end

lemma lintegral_trim_ae {α : Type*} {m m0 : measurable_space α} {μ : measure α} (hm : m ≤ m0)
  {f : α → ℝ≥0∞} (hf : @ae_measurable _ _ m _ f (μ.trim hm)) :
  @lintegral _ m (μ.trim hm) f = ∫⁻ a, f a ∂μ :=
begin
  let f' := @ae_measurable.mk _ _ m _ _ _ hf,
  have hff'_m : eventually_eq (@measure.ae  _ m (μ.trim hm)) f' f,
    from (@ae_measurable.ae_eq_mk _ _ m _ _ _ hf).symm,
  have hff' : f' =ᵐ[μ] f, from ae_eq_of_ae_eq_trim hff'_m,
  rw [lintegral_congr_ae hff'.symm, @lintegral_congr_ae _ m _ _ _ hff'_m.symm,
    lintegral_trim hm (@ae_measurable.measurable_mk _ _ m _ _ _ hf)],
end

end measure_theory
