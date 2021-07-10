/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Nicolò Cavalleri
-/
import topology.algebra.module
import topology.continuous_function.basic
import algebra.algebra.subalgebra

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over the type `continuous_map α β`
(denoted `C(α, β)`) of **bundled** continuous maps from `α` to `β`. For example, `C(α, β)`
is a group when `β` is a group, a ring when `β` is a ring, etc.

For each type of algebraic structure, we also define an appropriate subobject of `α → β`
with carrier `{ f : α → β | continuous f }`. For example, when `β` is a group, a subgroup
`continuous_subgroup α β` of `α → β` is constructed with carrier `{ f : α → β | continuous f }`.

Note that, rather than using the derived algebraic structures on these subobjects
(for example, when `β` is a group, the derived group structure on `continuous_subgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/

local attribute [elab_simple] continuous.comp

namespace continuous_functions

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
variables {f g : {f : α → β | continuous f }}

instance : has_coe_to_fun {f : α → β | continuous f} :=  ⟨_, subtype.val⟩

end continuous_functions

namespace continuous_map
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

@[to_additive]
instance has_mul [has_mul β] [has_continuous_mul β] : has_mul C(α, β) :=
⟨λ f g, ⟨f * g, continuous_mul.comp (f.continuous.prod_mk g.continuous : _)⟩⟩

@[simp, norm_cast, to_additive]
lemma coe_mul [has_mul β] [has_continuous_mul β] (f g : C(α, β)) :
  ((f * g : C(α, β)) : α → β) = (f : α → β) * (g : α → β) := rfl

@[to_additive]
instance [has_one β] : has_one C(α, β) := ⟨const (1 : β)⟩

@[simp, norm_cast, to_additive]
lemma coe_one [has_one β]  :
  ((1 : C(α, β)) : α → β) = (1 : α → β) := rfl

@[simp, to_additive] lemma mul_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [semigroup γ] [has_continuous_mul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
  (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
by { ext, simp, }

@[simp, to_additive] lemma one_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ] [has_one γ] (g : C(α, β)) :
  (1 : C(β, γ)).comp g = 1 :=
by { ext, simp, }

end continuous_map

section group_structure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/

section subtype

/-- The `submonoid` of continuous maps `α → β`. -/
@[to_additive "The `add_submonoid` of continuous maps `α → β`. "]
def continuous_submonoid (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : submonoid (α → β) :=
{ carrier := { f : α → β | continuous f },
  one_mem' := @continuous_const _ _ _ _ 1,
  mul_mem' := λ f g fc gc, continuous.comp
    has_continuous_mul.continuous_mul (continuous.prod_mk fc gc : _) }

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive "The `add_subgroup` of continuous maps `α → β`. "]
def continuous_subgroup (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  [group β] [topological_group β] : subgroup (α → β) :=
{ inv_mem' := λ f fc, continuous.comp (@topological_group.continuous_inv β _ _ _) fc,
  ..continuous_submonoid α β, }.

end subtype

namespace continuous_map

@[to_additive]
instance {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [semigroup β] [has_continuous_mul β] : semigroup C(α, β) :=
{ mul_assoc := λ a b c, by ext; exact mul_assoc _ _ _,
  ..continuous_map.has_mul}

@[to_additive]
instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  ..continuous_map.semigroup,
  ..continuous_map.has_one }

/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[to_additive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.",
  simps]
def coe_fn_monoid_hom {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : C(α, β) →* (α → β) :=
{ to_fun := coe_fn, map_one' := coe_one, map_mul' := coe_mul }

/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`monoid_hom`. Similar to `monoid_hom.comp_left`. -/
@[to_additive "Composition on the left by a (continuous) homomorphism of topological `add_monoid`s,
as an `add_monoid_hom`. Similar to `add_monoid_hom.comp_left`.", simps]
protected def _root_.monoid_hom.comp_left_continuous (α : Type*) {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [monoid β] [has_continuous_mul β]
  [topological_space γ] [monoid γ] [has_continuous_mul γ] (g : β →* γ) (hg : continuous g)  :
  C(α, β) →* C(α, γ) :=
{ to_fun := λ f, (⟨g, hg⟩ : C(β, γ)).comp f,
  map_one' := ext $ λ x, g.map_one,
  map_mul' := λ f₁ f₂, ext $ λ x, g.map_mul _ _ }

/-- Composition on the right as a `monoid_hom`. Similar to `monoid_hom.comp_hom'`. -/
@[to_additive "Composition on the right as an `add_monoid_hom`. Similar to
`add_monoid_hom.comp_hom'`.", simps]
def comp_monoid_hom' {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [monoid γ] [has_continuous_mul γ] (g : C(α, β)) : C(β, γ) →* C(α, γ) :=
{ to_fun := λ f, f.comp g, map_one' := one_comp g, map_mul' := λ f₁ f₂, mul_comp f₁ f₂ g }

@[simp, norm_cast]
lemma coe_pow {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] (f : C(α, β)) (n : ℕ) :
  ((f^n : C(α, β)) : α → β) = (f : α → β)^n :=
(coe_fn_monoid_hom : C(α, β) →* _).map_pow f n

@[simp] lemma pow_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [monoid γ] [has_continuous_mul γ] (f : C(β, γ)) (n : ℕ) (g : C(α, β)) :
  (f^n).comp g = (f.comp g)^n :=
(comp_monoid_hom' g).map_pow f n

@[to_additive]
instance {α : Type*} {β : Type*} [topological_space α]
[topological_space β] [comm_monoid β] [has_continuous_mul β] : comm_monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  mul_comm := λ a b, by ext; exact mul_comm _ _,
  ..continuous_map.semigroup,
  ..continuous_map.has_one }

open_locale big_operators
@[simp, to_additive] lemma coe_prod {α : Type*} {β : Type*} [comm_monoid β]
  [topological_space α] [topological_space β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → C(α, β)) :
  ⇑(∏ i in s, f i) = (∏ i in s, (f i : α → β)) :=
(coe_fn_monoid_hom : C(α, β) →* _).map_prod f s

@[to_additive]
lemma prod_apply {α : Type*} {β : Type*} [comm_monoid β]
  [topological_space α] [topological_space β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → C(α, β)) (a : α) :
  (∏ i in s, f i) a = (∏ i in s, f i a) :=
by simp

@[to_additive]
instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] : group C(α, β) :=
{ inv := λ f, ⟨λ x, (f x)⁻¹, continuous_inv.comp f.continuous⟩,
  mul_left_inv := λ a, by ext; exact mul_left_inv _,
  ..continuous_map.monoid }

@[simp, norm_cast, to_additive]
lemma coe_inv {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] (f : C(α, β)) :
  ((f⁻¹ : C(α, β)) : α → β) = (f⁻¹ : α → β) :=
rfl

@[simp, norm_cast, to_additive]
lemma coe_div {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] (f g : C(α, β)) :
  ((f / g : C(α, β)) : α → β) = (f : α → β) / (g : α → β) :=
by { simp only [div_eq_mul_inv], refl, }

@[simp, to_additive] lemma inv_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [group γ] [topological_group γ] (f : C(β, γ)) (g : C(α, β)) :
  (f⁻¹).comp g = (f.comp g)⁻¹ :=
by { ext, simp, }

@[simp, to_additive] lemma div_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [group γ] [topological_group γ] (f g : C(β, γ)) (h : C(α, β)) :
  (f / g).comp h = (f.comp h) / (g.comp h) :=
by { ext, simp, }

@[to_additive]
instance {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [comm_group β] [topological_group β] : comm_group C(α, β) :=
{ ..continuous_map.group,
  ..continuous_map.comm_monoid }

end continuous_map

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological ring `R` inherit
the structure of a ring.
-/

section subtype

/-- The subsemiring of continuous maps `α → β`. -/
def continuous_subsemiring (α : Type*) (R : Type*) [topological_space α] [topological_space R]
  [semiring R] [topological_semiring R] : subsemiring (α → R) :=
{ ..continuous_add_submonoid α R,
  ..continuous_submonoid α R }.

/-- The subring of continuous maps `α → β`. -/
def continuous_subring (α : Type*) (R : Type*) [topological_space α] [topological_space R]
  [ring R] [topological_ring R] : subring (α → R) :=
{ ..continuous_subsemiring α R,
  ..continuous_add_subgroup α R }.

end subtype

namespace continuous_map

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semiring β] [topological_semiring β] : semiring C(α, β) :=
{ left_distrib := λ a b c, by ext; exact left_distrib _ _ _,
  right_distrib := λ a b c, by ext; exact right_distrib _ _ _,
  zero_mul := λ a, by ext; exact zero_mul _,
  mul_zero := λ a, by ext; exact mul_zero _,
  ..continuous_map.add_comm_monoid,
  ..continuous_map.monoid }

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : ring C(α, β) :=
{ ..continuous_map.semiring,
  ..continuous_map.add_comm_group, }

instance {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [comm_ring β] [topological_ring β] : comm_ring C(α, β) :=
{ ..continuous_map.semiring,
  ..continuous_map.add_comm_group,
  ..continuous_map.comm_monoid,}

/-- Composition on the left by a (continuous) homomorphism of topological rings, as a `ring_hom`.
Similar to `ring_hom.comp_left`. -/
@[simps] protected def _root_.ring_hom.comp_left_continuous (α : Type*) {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [semiring β] [topological_semiring β]
  [topological_space γ] [semiring γ] [topological_semiring γ] (g : β →+* γ) (hg : continuous g) :
  C(α, β) →+* C(α, γ) :=
{ .. g.to_monoid_hom.comp_left_continuous α hg,
  .. g.to_add_monoid_hom.comp_left_continuous α hg }

/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coe_fn_ring_hom {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : C(α, β) →+* (α → β) :=
{ to_fun := coe_fn,
  ..(coe_fn_monoid_hom : C(α, β) →* _),
  ..(coe_fn_add_monoid_hom : C(α, β) →+ _) }

end continuous_map

end ring_structure

local attribute [ext] subtype.eq

section module_structure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/

section subtype

variables (α : Type*) [topological_space α]
variables (R : Type*) [semiring R] [topological_space R]
variables (M : Type*) [topological_space M] [add_comm_group M]
variables [module R M] [has_continuous_smul R M] [topological_add_group M]

/-- The `R`-submodule of continuous maps `α → M`. -/
def continuous_submodule : submodule R (α → M) :=
{ carrier := { f : α → M | continuous f },
  smul_mem' := λ c f hf, continuous_smul.comp
    (continuous.prod_mk (continuous_const : continuous (λ x, c)) hf),
  ..continuous_add_subgroup α M }

end subtype

namespace continuous_map
variables {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_monoid M]
  {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]

instance
  [module R M] [has_continuous_smul R M] :
  has_scalar R C(α, M) :=
⟨λ r f, ⟨r • f, f.continuous.const_smul r⟩⟩

@[simp, norm_cast]
lemma coe_smul [module R M] [has_continuous_smul R M]
  (c : R) (f : C(α, M)) : ⇑(c • f) = c • f := rfl

lemma smul_apply [module R M] [has_continuous_smul R M]
  (c : R) (f : C(α, M)) (a : α) : (c • f) a = c • (f a) :=
by simp

@[simp] lemma smul_comp {α : Type*} {β : Type*}
  [topological_space α] [topological_space β]
   [module R M] [has_continuous_smul R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
  (r • f).comp g = r • (f.comp g) :=
by { ext, simp, }

variables [has_continuous_add M] [module R M] [has_continuous_smul R M]
variables [has_continuous_add M₂] [module R M₂] [has_continuous_smul R M₂]

instance module : module R C(α, M) :=
{ smul     := (•),
  smul_add := λ c f g, by { ext, exact smul_add c (f x) (g x) },
  add_smul := λ c₁ c₂ f, by { ext, exact add_smul c₁ c₂ (f x) },
  mul_smul := λ c₁ c₂ f, by { ext, exact mul_smul c₁ c₂ (f x) },
  one_smul := λ f, by { ext, exact one_smul R (f x) },
  zero_smul := λ f, by { ext, exact zero_smul _ _ },
  smul_zero := λ r, by { ext, exact smul_zero _ } }

variables (R)

/-- Composition on the left by a continuous linear map, as a `linear_map`.
Similar to `linear_map.comp_left`. -/
@[simps] protected def _root_.continuous_linear_map.comp_left_continuous (α : Type*)
  [topological_space α] (g : M →L[R] M₂) :
  C(α, M) →ₗ[R] C(α, M₂) :=
{ map_smul' := λ c f, ext $ λ x, g.map_smul' c _,
  .. g.to_linear_map.to_add_monoid_hom.comp_left_continuous α g.continuous }

/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coe_fn_linear_map : C(α, M) →ₗ[R] (α → M) :=
{ to_fun := coe_fn,
  map_smul' := coe_smul,
  ..(coe_fn_add_monoid_hom : C(α, M) →+ _) }

end continuous_map

end module_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `has_continuous_smul` and a `topological_semiring`.-/

section subtype

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [semiring A]
[algebra R A] [topological_semiring A]

/-- The `R`-subalgebra of continuous maps `α → A`. -/
def continuous_subalgebra : subalgebra R (α → A) :=
{ carrier := { f : α → A | continuous f },
  algebra_map_mem' := λ r, (continuous_const : continuous $ λ (x : α), algebra_map R A r),
  ..continuous_subsemiring α A }

end subtype

section continuous_map

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [semiring A]
[algebra R A] [topological_semiring A]
{A₂ : Type*} [topological_space A₂] [semiring A₂]
[algebra R A₂] [topological_semiring A₂]

/-- Continuous constant functions as a `ring_hom`. -/
def continuous_map.C : R →+* C(α, A) :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

@[simp] lemma continuous_map.C_apply (r : R) (a : α) : continuous_map.C r a = algebra_map R A r :=
rfl

variables [topological_space R] [has_continuous_smul R A] [has_continuous_smul R A₂]

instance continuous_map.algebra : algebra R C(α, A) :=
{ to_ring_hom := continuous_map.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _, }

variables (R)

/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`alg_hom`. Similar to `alg_hom.comp_left`. -/
@[simps] protected def alg_hom.comp_left_continuous {α : Type*} [topological_space α]
  (g : A →ₐ[R] A₂) (hg : continuous g) :
  C(α, A) →ₐ[R] C(α, A₂) :=
{ commutes' := λ c, continuous_map.ext $ λ _, g.commutes' _,
  .. g.to_ring_hom.comp_left_continuous α hg }

/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def continuous_map.coe_fn_alg_hom : C(α, A) →ₐ[R] (α → A) :=
{ to_fun := coe_fn,
  commutes' := λ r, rfl,
  -- `..(continuous_map.coe_fn_ring_hom : C(α, A) →+* _)` times out for some reason
  map_zero' := continuous_map.coe_zero,
  map_one' := continuous_map.coe_one,
  map_add' := continuous_map.coe_add,
  map_mul' := continuous_map.coe_mul }

instance: is_scalar_tower R A C(α, A) :=
{ smul_assoc := λ _ _ _, by { ext, simp } }

variables {R}

/--
A version of `separates_points` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbreviation subalgebra.separates_points (s : subalgebra R C(α, A)) : Prop :=
set.separates_points ((λ f : C(α, A), (f : α → A)) '' (s : set C(α, A)))

lemma subalgebra.separates_points_monotone :
  monotone (λ s : subalgebra R C(α, A), s.separates_points) :=
λ s s' r h x y n,
begin
  obtain ⟨f, m, w⟩ := h n,
  rcases m with ⟨f, ⟨m, rfl⟩⟩,
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩,
end

@[simp] lemma algebra_map_apply (k : R) (a : α) :
  algebra_map R C(α, A) k a = k • 1 :=
by { rw algebra.algebra_map_eq_smul_one, refl, }

variables {𝕜 : Type*} [topological_space 𝕜]

/--
A set of continuous maps "separates points strongly"
if for each pair of distinct points there is a function with specified values on them.

We give a slightly unusual formulation, where the specified values are given by some
function `v`, and we ask `f x = v x ∧ f y = v y`. This avoids needing a hypothesis `x ≠ y`.

In fact, this definition would work perfectly well for a set of non-continuous functions,
but as the only current use case is in the Stone-Weierstrass theorem,
writing it this way avoids having to deal with casts inside the set.
(This may need to change if we do Stone-Weierstrass on non-compact spaces,
where the functions would be continuous functions vanishing at infinity.)
-/
def set.separates_points_strongly (s : set C(α, 𝕜)) : Prop :=
∀ (v : α → 𝕜) (x y : α), ∃ f : s, (f x : 𝕜) = v x ∧ f y = v y

variables [field 𝕜] [topological_ring 𝕜]

/--
Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
lemma subalgebra.separates_points.strongly {s : subalgebra 𝕜 C(α, 𝕜)} (h : s.separates_points) :
  (s : set C(α, 𝕜)).separates_points_strongly :=
λ v x y,
begin
  by_cases n : x = y,
  { subst n,
    use ((v x) • 1 : C(α, 𝕜)),
    { apply s.smul_mem,
      apply s.one_mem, },
    { simp, }, },
  obtain ⟨f, ⟨f, ⟨m, rfl⟩⟩, w⟩ := h n,
  replace w : f x - f y ≠ 0 := sub_ne_zero_of_ne w,
  let a := v x,
  let b := v y,
  let f' := ((b - a) * (f x - f y)⁻¹) • (continuous_map.C (f x) - f) + continuous_map.C a,
  refine ⟨⟨f', _⟩, _, _⟩,
  { simp only [f', set_like.mem_coe, subalgebra.mem_to_submodule],
    -- TODO should there be a tactic for this?
    -- We could add an attribute `@[subobject_mem]`, and a tactic
    -- ``def subobject_mem := `[solve_by_elim with subobject_mem { max_depth := 10 }]``
    solve_by_elim
      [subalgebra.add_mem, subalgebra.smul_mem, subalgebra.sub_mem, subalgebra.algebra_map_mem]
      { max_depth := 6 }, },
  { simp [f'], },
  { simp [f', inv_mul_cancel_right' w], },
end

end continuous_map

-- TODO[gh-6025]: make this an instance once safe to do so
lemma continuous_map.subsingleton_subalgebra (α : Type*) [topological_space α]
  (R : Type*) [comm_semiring R] [topological_space R] [topological_semiring R]
  [subsingleton α] : subsingleton (subalgebra R C(α, R)) :=
begin
  fsplit,
  intros s₁ s₂,
  by_cases n : nonempty α,
  { obtain ⟨x⟩ := n,
    ext f,
    have h : f = algebra_map R C(α, R) (f x),
    { ext x', simp only [mul_one, algebra.id.smul_eq_mul, algebra_map_apply], congr, },
    rw h,
    simp only [subalgebra.algebra_map_mem], },
  { ext f,
    have h : f = 0,
    { ext x', exact false.elim (n ⟨x'⟩), },
    subst h,
    simp only [subalgebra.zero_mem], },
end

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `R`. -/

namespace continuous_map

instance has_scalar' {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_monoid M]
  [module R M] [has_continuous_smul R M] :
  has_scalar C(α, R) C(α, M) :=
⟨λ f g, ⟨λ x, (f x) • (g x), (continuous.smul f.2 g.2)⟩⟩

instance module' {α : Type*} [topological_space α]
  (R : Type*) [ring R] [topological_space R] [topological_ring R]
  (M : Type*) [topological_space M] [add_comm_monoid M] [has_continuous_add M]
  [module R M] [has_continuous_smul R M] :
  module C(α, R) C(α, M) :=
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x),
  zero_smul := λ f, by ext x; exact zero_smul _ _,
  smul_zero := λ r, by ext x; exact smul_zero _, }

end continuous_map

end module_over_continuous_functions

/-!
We now provide formulas for `f ⊓ g` and `f ⊔ g`, where `f g : C(α, β)`,
in terms of `continuous_map.abs`.
-/

section
variables {R : Type*} [linear_ordered_field R]

-- TODO:
-- This lemma (and the next) could go all the way back in `algebra.ordered_field`,
-- except that it is tedious to prove without tactics.
-- Rather than stranding it at some intermediate location,
-- it's here, immediately prior to the point of use.
lemma min_eq_half_add_sub_abs_sub {x y : R} : min x y = 2⁻¹ * (x + y - abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring_nf; linarith,
end

lemma max_eq_half_add_add_abs_sub {x y : R} : max x y = 2⁻¹ * (x + y + abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring_nf; linarith,
end
end

namespace continuous_map

section lattice
variables {α : Type*} [topological_space α]
variables {β : Type*} [linear_ordered_field β] [topological_space β]
  [order_topology β] [topological_ring β]

lemma inf_eq (f g : C(α, β)) : f ⊓ g = (2⁻¹ : β) • (f + g - (f - g).abs) :=
ext (λ x, by simpa using min_eq_half_add_sub_abs_sub)

-- Not sure why this is grosser than `inf_eq`:
lemma sup_eq (f g : C(α, β)) : f ⊔ g = (2⁻¹ : β) • (f + g + (f - g).abs) :=
ext (λ x, by simpa [mul_add] using @max_eq_half_add_add_abs_sub _ _ (f x) (g x))

end lattice

end continuous_map
