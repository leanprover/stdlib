/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import linear_algebra.affine_space.basic
import linear_algebra.tensor_product

/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `affine_map` is the type of affine maps between two affine spaces with the same ring `k`.  Various
  basic examples of affine maps are defined, including `const`, `id`, `line_map` and `homothety`.

## Notations

* `P1 →ᵃ[k] P2` is a notation for `affine_map k P1 P2`;
* `affine_space V P`: a localized notation for `add_torsor V P` defined in
  `linear_algebra.affine_space.basic`.

## Implementation notes

`out_param` is used in the definition of `[add_torsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases; `include V` is needed in many cases for `V`, and type classes
using it, to be added as implicit arguments to individual lemmas.  As for modules, `k` is an
explicit argument rather than implied by `P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `analysis.normed_space.add_torsor` and
`topology.algebra.affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

open_locale affine

/-- An `affine_map k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure affine_map (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2] :=
(to_fun : P1 → P2)
(linear : linear_map k V1 V2)
(map_vadd' : ∀ (p : P1) (v : V1), to_fun (v +ᵥ p) =  linear v +ᵥ to_fun p)

notation P1 ` →ᵃ[`:25 k:25 `] `:0 P2:0 := affine_map k P1 P2

instance (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2]:
    has_coe_to_fun (P1 →ᵃ[k] P2) := ⟨_, affine_map.to_fun⟩

namespace linear_map

variables {k : Type*} {V₁ : Type*} {V₂ : Type*} [ring k] [add_comm_group V₁] [module k V₁]
  [add_comm_group V₂] [module k V₂] (f : V₁ →ₗ[k] V₂)

/-- Reinterpret a linear map as an affine map. -/
def to_affine_map : V₁ →ᵃ[k] V₂ :=
{ to_fun := f,
  linear := f,
  map_vadd' := λ p v, f.map_add v p }

@[simp] lemma coe_to_affine_map : ⇑f.to_affine_map = f := rfl

@[simp] lemma to_affine_map_linear : f.to_affine_map.linear = f := rfl

end linear_map

namespace affine_map

variables {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*}
    {V3 : Type*} {P3 : Type*} {V4 : Type*} {P4 : Type*} [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2]
    [add_comm_group V3] [module k V3] [affine_space V3 P3]
    [add_comm_group V4] [module k V4] [affine_space V4 P4]
include V1 V2

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp] lemma coe_mk (f : P1 → P2) (linear add) :
  ((mk f linear add : P1 →ᵃ[k] P2) : P1 → P2) = f := rfl

/-- `to_fun` is the same as the result of coercing to a function. -/
@[simp] lemma to_fun_eq_coe (f : P1 →ᵃ[k] P2) : f.to_fun = ⇑f := rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp] lemma map_vadd (f : P1 →ᵃ[k] P2) (p : P1) (v : V1) :
  f (v +ᵥ p) = f.linear v +ᵥ f p := f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp] lemma linear_map_vsub (f : P1 →ᵃ[k] P2) (p1 p2 : P1) :
  f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
by conv_rhs { rw [←vsub_vadd p1 p2, map_vadd, vadd_vsub] }

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext] lemma ext {f g : P1 →ᵃ[k] P2} (h : ∀ p, f p = g p) : f = g :=
begin
  rcases f with ⟨f, f_linear, f_add⟩,
  rcases g with ⟨g, g_linear, g_add⟩,
  have : f = g := funext h,
  subst g,
  congr' with v,
  cases (add_torsor.nonempty : nonempty P1) with p,
  apply vadd_right_cancel (f p),
  erw [← f_add, ← g_add]
end

lemma ext_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ ∀ p, f p = g p := ⟨λ h p, h ▸ rfl, ext⟩

lemma injective_coe_fn : function.injective (λ (f : P1 →ᵃ[k] P2) (x : P1), f x) :=
λ f g H, ext $ congr_fun H

protected lemma congr_arg (f : P1 →ᵃ[k] P2) {x y : P1} (h : x = y) : f x = f y :=
congr_arg _ h

protected lemma congr_fun {f g : P1 →ᵃ[k] P2} (h : f = g) (x : P1) : f x = g x :=
h ▸ rfl

variables (k P1)

/-- Constant function as an `affine_map`. -/
def const (p : P2) : P1 →ᵃ[k] P2 :=
{ to_fun := function.const P1 p,
  linear := 0,
  map_vadd' := λ p v, by simp }

@[simp] lemma coe_const (p : P2) : ⇑(const k P1 p) = function.const P1 p := rfl

@[simp] lemma const_linear (p : P2) : (const k P1 p).linear = 0 := rfl

variables {k P1}

instance nonempty : nonempty (P1 →ᵃ[k] P2) :=
(add_torsor.nonempty : nonempty P2).elim $ λ p, ⟨const k P1 p⟩

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
  P1 →ᵃ[k] P2 :=
{ to_fun := f,
  linear := f',
  map_vadd' := λ p' v, by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_assoc] }

@[simp] lemma coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f := rfl

@[simp] lemma mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' := rfl

/-- The set of affine maps to a vector space is an additive commutative group. -/
instance : add_comm_group (P1 →ᵃ[k] V2) :=
{ zero := ⟨0, 0, λ p v, (zero_vadd _ _).symm⟩,
  add := λ f g, ⟨f + g, f.linear + g.linear, λ p v, by simp [add_add_add_comm]⟩,
  neg := λ f, ⟨-f, -f.linear, λ p v, by simp [add_comm]⟩,
  add_assoc := λ f₁ f₂ f₃, ext $ λ p, add_assoc _ _ _,
  zero_add := λ f, ext $ λ p, zero_add (f p),
  add_zero := λ f, ext $ λ p, add_zero (f p),
  add_comm := λ f g, ext $ λ p, add_comm (f p) (g p),
  add_left_neg := λ f, ext $ λ p, add_left_neg (f p) }

@[simp, norm_cast] lemma coe_zero : ⇑(0 : P1 →ᵃ[k] V2) = 0 := rfl
@[simp] lemma zero_linear : (0 : P1 →ᵃ[k] V2).linear = 0 := rfl
@[simp, norm_cast] lemma coe_add (f g : P1 →ᵃ[k] V2) : ⇑(f + g) = f + g := rfl
@[simp]
lemma add_linear (f g : P1 →ᵃ[k] V2) : (f + g).linear = f.linear + g.linear := rfl

/-- The space of affine maps from `P1` to `P2` is an affine space over the space of affine maps
from `P1` to the vector space `V2` corresponding to `P2`. -/
instance : affine_space (P1 →ᵃ[k] V2) (P1 →ᵃ[k] P2) :=
{ vadd := λ f g, ⟨λ p, f p +ᵥ g p, f.linear + g.linear, λ p v,
    by simp [vadd_assoc, add_right_comm]⟩,
  zero_vadd' := λ f, ext $ λ p, zero_vadd _ (f p),
  vadd_assoc' := λ f₁ f₂ f₃, ext $ λ p, vadd_assoc (f₁ p) (f₂ p) (f₃ p),
  vsub := λ f g, ⟨λ p, f p -ᵥ g p, f.linear - g.linear, λ p v,
    by simp [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub, sub_add_eq_add_sub]⟩,
  vsub_vadd' := λ f g, ext $ λ p, vsub_vadd (f p) (g p),
  vadd_vsub' := λ f g, ext $ λ p, vadd_vsub (f p) (g p) }

@[simp] lemma vadd_apply (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) (p : P1) :
  (f +ᵥ g) p = f p +ᵥ g p :=
rfl

@[simp] lemma vsub_apply (f g : P1 →ᵃ[k] P2) (p : P1) :
  (f -ᵥ g : P1 →ᵃ[k] V2) p = f p -ᵥ g p :=
rfl

/-- `prod.fst` as an `affine_map`. -/
def fst : (P1 × P2) →ᵃ[k] P1 :=
{ to_fun := prod.fst,
  linear := linear_map.fst k V1 V2,
  map_vadd' := λ _ _, rfl }

@[simp] lemma coe_fst : ⇑(fst : (P1 × P2) →ᵃ[k] P1) = prod.fst := rfl
@[simp] lemma fst_linear : (fst : (P1 × P2) →ᵃ[k] P1).linear = linear_map.fst k V1 V2 := rfl

/-- `prod.snd` as an `affine_map`. -/
def snd : (P1 × P2) →ᵃ[k] P2 :=
{ to_fun := prod.snd,
  linear := linear_map.snd k V1 V2,
  map_vadd' := λ _ _, rfl }

@[simp] lemma coe_snd : ⇑(snd : (P1 × P2) →ᵃ[k] P2) = prod.snd := rfl
@[simp] lemma snd_linear : (snd : (P1 × P2) →ᵃ[k] P2).linear = linear_map.snd k V1 V2 := rfl

variables (k P1)
omit V2

/-- Identity map as an affine map. -/
def id : P1 →ᵃ[k] P1 :=
{ to_fun := id,
  linear := linear_map.id,
  map_vadd' := λ p v, rfl }

/-- The identity affine map acts as the identity. -/
@[simp] lemma coe_id : ⇑(id k P1) = _root_.id := rfl

@[simp] lemma id_linear : (id k P1).linear = linear_map.id := rfl

variable {P1}

/-- The identity affine map acts as the identity. -/
lemma id_apply (p : P1) : id k P1 p = p := rfl

variables {k P1}

instance : inhabited (P1 →ᵃ[k] P1) := ⟨id k P1⟩

include V2 V3

/-- Composition of affine maps. -/
def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 :=
{ to_fun := f ∘ g,
  linear := f.linear.comp g.linear,
  map_vadd' := begin
    intros p v,
    rw [function.comp_app, g.map_vadd, f.map_vadd],
    refl
  end }

/-- Composition of affine maps acts as applying the two functions. -/
@[simp] lemma coe_comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) :
  ⇑(f.comp g) = f ∘ g := rfl

/-- Composition of affine maps acts as applying the two functions. -/
lemma comp_apply (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) (p : P1) :
  f.comp g p = f (g p) := rfl

omit V3

@[simp] lemma comp_id (f : P1 →ᵃ[k] P2) : f.comp (id k P1) = f := ext $ λ p, rfl

@[simp] lemma id_comp (f : P1 →ᵃ[k] P2) : (id k P2).comp f = f := ext $ λ p, rfl

include V3 V4

lemma comp_assoc (f₃₄ : P3 →ᵃ[k] P4) (f₂₃ : P2 →ᵃ[k] P3) (f₁₂ : P1 →ᵃ[k] P2) :
  (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
rfl

omit V2 V3 V4

instance : monoid (P1 →ᵃ[k] P1) :=
{ one := id k P1,
  mul := comp,
  one_mul := id_comp,
  mul_one := comp_id,
  mul_assoc := comp_assoc }

@[simp] lemma coe_mul (f g : P1 →ᵃ[k] P1) : ⇑(f * g) = f ∘ g := rfl
@[simp] lemma coe_one : ⇑(1 : P1 →ᵃ[k] P1) = _root_.id := rfl

/-! ### Definition of `affine_map.line_map` and lemmas about it -/

/-- The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`. -/
def line_map (p₀ p₁ : P1) : k →ᵃ[k] P1 :=
((linear_map.id : k →ₗ[k] k).smul_right (p₁ -ᵥ p₀)).to_affine_map +ᵥ const k k p₀

lemma coe_line_map (p₀ p₁ : P1) : (line_map p₀ p₁ : k → P1) = λ c, c • (p₁ -ᵥ p₀) +ᵥ p₀ := rfl

lemma line_map_apply (p₀ p₁ : P1) (c : k) : line_map p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀ := rfl

lemma line_map_apply_module' (p₀ p₁ : V1) (c : k) : line_map p₀ p₁ c = c • (p₁ - p₀) + p₀ := rfl

lemma line_map_apply_module (p₀ p₁ : V1) (c : k) : line_map p₀ p₁ c = (1 - c) • p₀ + c • p₁ :=
by simp [line_map_apply_module', smul_sub, sub_smul]; abel

omit V1

lemma line_map_apply_ring' (a b c : k) : line_map a b c = c * (b - a) + a :=
rfl

lemma line_map_apply_ring (a b c : k) : line_map a b c = (1 - c) * a + c * b :=
line_map_apply_module a b c

include V1

lemma line_map_vadd_apply (p : P1) (v : V1) (c : k) :
  line_map p (v +ᵥ p) c = c • v +ᵥ p :=
by rw [line_map_apply, vadd_vsub]

@[simp] lemma line_map_linear (p₀ p₁ : P1) :
  (line_map p₀ p₁ : k →ᵃ[k] P1).linear = linear_map.id.smul_right (p₁ -ᵥ p₀) :=
add_zero _

lemma line_map_same_apply (p : P1) (c : k) : line_map p p c = p := by simp [line_map_apply]

@[simp] lemma line_map_same (p : P1) : line_map p p = const k k p :=
ext $ line_map_same_apply p

@[simp] lemma line_map_apply_zero (p₀ p₁ : P1) : line_map p₀ p₁ (0:k) = p₀ :=
by simp [line_map_apply]

@[simp] lemma line_map_apply_one (p₀ p₁ : P1) : line_map p₀ p₁ (1:k) = p₁ :=
by simp [line_map_apply]

include V2

@[simp] lemma apply_line_map (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
  f (line_map p₀ p₁ c) = line_map (f p₀) (f p₁) c :=
by simp [line_map_apply]

@[simp] lemma comp_line_map (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) :
  f.comp (line_map p₀ p₁) = line_map (f p₀) (f p₁) :=
ext $ f.apply_line_map p₀ p₁

@[simp] lemma fst_line_map (p₀ p₁ : P1 × P2) (c : k) :
  (line_map p₀ p₁ c).1 = line_map p₀.1 p₁.1 c :=
fst.apply_line_map p₀ p₁ c

@[simp] lemma snd_line_map (p₀ p₁ : P1 × P2) (c : k) :
  (line_map p₀ p₁ c).2 = line_map p₀.2 p₁.2 c :=
snd.apply_line_map p₀ p₁ c

omit V2

lemma line_map_symm (p₀ p₁ : P1) :
  line_map p₀ p₁ = (line_map p₁ p₀).comp (line_map (1:k) (0:k)) :=
by { rw [comp_line_map], simp }

lemma line_map_apply_one_sub (p₀ p₁ : P1) (c : k) :
  line_map p₀ p₁ (1 - c) = line_map p₁ p₀ c :=
by { rw [line_map_symm p₀, comp_apply], congr, simp [line_map_apply] }

@[simp] lemma line_map_vsub_left (p₀ p₁ : P1) (c : k) :
  line_map p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀) :=
vadd_vsub _ _

@[simp] lemma left_vsub_line_map (p₀ p₁ : P1) (c : k) :
  p₀ -ᵥ line_map p₀ p₁ c = c • (p₀ -ᵥ p₁) :=
by rw [← neg_vsub_eq_vsub_rev, line_map_vsub_left, ← smul_neg, neg_vsub_eq_vsub_rev]

@[simp] lemma line_map_vsub_right (p₀ p₁ : P1) (c : k) :
  line_map p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁) :=
by rw [← line_map_apply_one_sub, line_map_vsub_left]

@[simp] lemma right_vsub_line_map (p₀ p₁ : P1) (c : k) :
  p₁ -ᵥ line_map p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀) :=
by rw [← line_map_apply_one_sub, left_vsub_line_map]

lemma line_map_vadd_line_map (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) :
  line_map v₁ v₂ c +ᵥ line_map p₁ p₂ c = line_map (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c :=
((fst : V1 × P1 →ᵃ[k] V1) +ᵥ snd).apply_line_map  (v₁, p₁) (v₂, p₂) c

lemma line_map_vsub_line_map (p₁ p₂ p₃ p₄ : P1) (c : k) :
  line_map p₁ p₂ c -ᵥ line_map p₃ p₄ c = line_map (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c :=
-- Why Lean fails to find this instance without a hint?
by letI : affine_space (V1 × V1) (P1 × P1) := prod.add_torsor; exact
((fst : P1 × P1 →ᵃ[k] P1) -ᵥ (snd : P1 × P1 →ᵃ[k] P1)).apply_line_map (_, _) (_, _) c

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
lemma decomp (f : V1 →ᵃ[k] V2) : (f : V1 → V2) = f.linear + (λ z, f 0) :=
begin
  ext x,
  calc
    f x = f.linear x +ᵥ f 0                      : by simp [← f.map_vadd]
    ... = (f.linear.to_fun + λ (z : V1), f 0) x  : by simp
end

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
lemma decomp' (f : V1 →ᵃ[k] V2) : (f.linear : V1 → V2) = f - (λ z, f 0) :=
by rw decomp ; simp only [linear_map.map_zero, pi.add_apply, add_sub_cancel, zero_add]

omit V1

lemma image_interval {k : Type*} [linear_ordered_field k] (f : k →ᵃ[k] k)
  (a b : k) :
  f '' set.interval a b = set.interval (f a) (f b) :=
begin
  have : ⇑f = (λ x, x + f 0) ∘ λ x, x * (f 1 - f 0),
  { ext x,
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0,
    rw [← f.linear_map_vsub, ← f.linear.map_smul, ← f.map_vadd],
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul] },
  rw [this, set.image_comp],
  simp only [set.image_add_const_interval, set.image_mul_const_interval]
end

section

variables {ι : Type*} {V : Π i : ι, Type*} {P : Π i : ι, Type*} [Π i, add_comm_group (V i)]
  [Π i, semimodule k (V i)] [Π i, add_torsor (V i) (P i)]

include V

/-- Evaluation at a point as an affine map. -/
def proj (i : ι) : (Π i : ι, P i) →ᵃ[k] P i :=
{ to_fun := λ f, f i,
  linear := @linear_map.proj k ι _ V _ _ i,
  map_vadd' := λ p v, rfl }

@[simp] lemma proj_apply (i : ι) (f : Π i, P i) : @proj k _ ι V P _ _ _ i f = f i := rfl

@[simp] lemma proj_linear (i : ι) :
   (@proj k _ ι V P _ _ _ i).linear = @linear_map.proj k ι _ V _ _ i := rfl

lemma pi_line_map_apply (f g : Π i, P i) (c : k) (i : ι) :
  line_map f g c i = line_map (f i) (g i) c :=
(proj i : (Π i, P i) →ᵃ[k] P i).apply_line_map f g c

end

end affine_map

namespace affine_map

variables {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} [comm_ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1] [add_comm_group V2] [module k V2]
include V1

/-- If `k` is a commutative ring, then the set of affine maps with codomain in a `k`-module
is a `k`-module. -/
instance : module k (P1 →ᵃ[k] V2) :=
{ smul := λ c f, ⟨c • f, c • f.linear, λ p v, by simp [smul_add]⟩,
  one_smul := λ f, ext $ λ p, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ p, mul_smul _ _ _,
  smul_add := λ c f g, ext $ λ p, smul_add _ _ _,
  smul_zero := λ c, ext $ λ p, smul_zero _,
  add_smul := λ c₁ c₂ f, ext $ λ p, add_smul _ _ _,
  zero_smul := λ f, ext $ λ p, zero_smul _ _ }

@[simp] lemma coe_smul (c : k) (f : P1 →ᵃ[k] V2) : ⇑(c • f) = c • f := rfl

/-- `homothety c r` is the homothety about `c` with scale factor `r`. -/
def homothety (c : P1) (r : k) : P1 →ᵃ[k] P1 :=
r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c

lemma homothety_def (c : P1) (r : k) :
  homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
rfl

lemma homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c : V1) +ᵥ c := rfl

lemma homothety_eq_line_map (c : P1) (r : k) (p : P1) : homothety c r p = line_map c p r := rfl

@[simp] lemma homothety_one (c : P1) : homothety c (1:k) = id k P1 :=
by { ext p, simp [homothety_apply] }

lemma homothety_mul (c : P1) (r₁ r₂ : k) :
  homothety c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂) :=
by { ext p, simp [homothety_apply, mul_smul] }

@[simp] lemma homothety_zero (c : P1) : homothety c (0:k) = const k P1 c :=
by { ext p, simp [homothety_apply] }

@[simp] lemma homothety_add (c : P1) (r₁ r₂ : k) :
  homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ :=
by simp only [homothety_def, add_smul, vadd_assoc]

/-- `homothety` as a multiplicative monoid homomorphism. -/
def homothety_hom (c : P1) : k →* P1 →ᵃ[k] P1 :=
⟨homothety c, homothety_one c, homothety_mul c⟩

@[simp] lemma coe_homothety_hom (c : P1) : ⇑(homothety_hom c : k →* _) = homothety c := rfl

/-- `homothety` as an affine map. -/
def homothety_affine (c : P1) : k →ᵃ[k] (P1 →ᵃ[k] P1) :=
⟨homothety c, (linear_map.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
  function.swap (homothety_add c)⟩

@[simp] lemma coe_homothety_affine (c : P1) :
  ⇑(homothety_affine c : k →ᵃ[k] _) = homothety c :=
rfl

end affine_map
