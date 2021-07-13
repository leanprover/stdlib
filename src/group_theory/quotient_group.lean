/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import group_theory.coset

/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main definitions

* `mk'`: the canonical group homomorphism `G →* G/N` given a normal subgroup `N` of `G`.
* `lift φ`: the group homomorphism `G/N →* H` given a group homomorphism `φ : G →* H` such that
  `N ⊆ ker φ`.
* `map f`: the group homomorphism `G/N →* H/M` given a group homomorphism `f : G →* H` such that
  `N ⊆ f⁻¹(M)`.

## Main statements

* `quotient_ker_equiv_range`: Noether's first isomorphism theorem, an explicit isomorphism
  `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `quotient_inf_equiv_prod_normal_quotient`: Noether's second isomorphism theorem, an explicit
  isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H` and a normal subgroup `N` of a
  group `G`.
* `quotient_group.quotient_quotient_equiv_quotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / M) / (M / N)` and `G / N`, where `N ≤ M`.

## Tags

isomorphism theorems, quotient groups
-/

universes u v

namespace quotient_group

variables {G : Type u} [group G] (N : subgroup G) [nN : N.normal] {H : Type v} [group H]
include nN

-- Define the `div_inv_monoid` before the `group` structure,
-- to make sure we have `inv` fully defined before we show `mul_left_inv`.
-- TODO: is there a non-invasive way of defining this in one declaration?
@[to_additive quotient_add_group.div_inv_monoid]
instance : div_inv_monoid (quotient N) :=
{ one := (1 : G),
  mul := quotient.map₂' (*)
  (λ a₁ b₁ hab₁ a₂ b₂ hab₂,
    ((N.mul_mem_cancel_right (N.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact nN.conj_mem _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c
    (λ a b c, congr_arg mk (mul_assoc a b c)),
  one_mul := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (one_mul a)),
  mul_one := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_one a)),
  inv := λ a, quotient.lift_on' a (λ a, ((a⁻¹ : G) : quotient N))
    (λ a b hab, quotient.sound' begin
      show a⁻¹⁻¹ * b⁻¹ ∈ N,
      rw ← mul_inv_rev,
      exact N.inv_mem (nN.mem_comm hab)
    end) }

@[to_additive quotient_add_group.add_group]
instance : group (quotient N) :=
{ mul_left_inv := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_left_inv a)),
 .. quotient.div_inv_monoid _ }

/-- The group homomorphism from `G` to `G/N`. -/
@[to_additive quotient_add_group.mk' "The additive group homomorphism from `G` to `G/N`."]
def mk' : G →* quotient N := monoid_hom.mk' (quotient_group.mk) (λ _ _, rfl)

@[to_additive, simp]
lemma coe_mk' : (mk' N : G → quotient N) = coe := rfl

@[to_additive, simp]
lemma mk'_apply (x : G) : mk' N x = x := rfl

@[simp, to_additive quotient_add_group.eq_zero_iff]
lemma eq_one_iff {N : subgroup G} [nN : N.normal] (x : G) : (x : quotient N) = 1 ↔ x ∈ N :=
begin
  refine quotient_group.eq.trans _,
  rw [mul_one, subgroup.inv_mem_iff],
end

@[simp, to_additive quotient_add_group.ker_mk]
lemma ker_mk :
  monoid_hom.ker (quotient_group.mk' N : G →* quotient_group.quotient N) = N :=
subgroup.ext eq_one_iff

@[to_additive quotient_add_group.eq_iff_sub_mem]
lemma eq_iff_div_mem {N : subgroup G} [nN : N.normal] {x y : G} :
  (x : quotient N) = y ↔ x / y ∈ N :=
begin
  refine eq_comm.trans (quotient_group.eq.trans _),
  rw [nN.mem_comm_iff, div_eq_mul_inv]
end

-- for commutative groups we don't need normality assumption
omit nN

@[to_additive quotient_add_group.add_comm_group]
instance {G : Type*} [comm_group G] (N : subgroup G) : comm_group (quotient N) :=
{ mul_comm := λ a b, quotient.induction_on₂' a b
    (λ a b, congr_arg mk (mul_comm a b)),
  .. @quotient_group.quotient.group _ _ N N.normal_of_comm }

include nN

local notation ` Q ` := quotient N

@[simp, to_additive quotient_add_group.coe_zero]
lemma coe_one : ((1 : G) : Q) = 1 := rfl

@[simp, to_additive quotient_add_group.coe_add]
lemma coe_mul (a b : G) : ((a * b : G) : Q) = a * b := rfl

@[simp, to_additive quotient_add_group.coe_neg]
lemma coe_inv (a : G) : ((a⁻¹ : G) : Q) = a⁻¹ := rfl

@[simp] lemma coe_pow (a : G) (n : ℕ) : ((a ^ n : G) : Q) = a ^ n :=
(mk' N).map_pow a n

@[simp] lemma coe_gpow (a : G) (n : ℤ) : ((a ^ n : G) : Q) = a ^ n :=
(mk' N).map_gpow a n

/-- A group homomorphism `φ : G →* H` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* H`. -/
@[to_additive quotient_add_group.lift "An `add_group` homomorphism `φ : G →+ H` with `N ⊆ ker(φ)`
descends (i.e. `lift`s) to a group homomorphism `G/N →* H`."]
def lift (φ : G →* H) (HN : ∀x∈N, φ x = 1) : Q →* H :=
monoid_hom.mk'
  (λ q : Q, q.lift_on' φ $ assume a b (hab : a⁻¹ * b ∈ N),
  (calc φ a = φ a * 1           : (mul_one _).symm
  ...       = φ a * φ (a⁻¹ * b) : HN (a⁻¹ * b) hab ▸ rfl
  ...       = φ (a * (a⁻¹ * b)) : (φ.map_mul a (a⁻¹ * b)).symm
  ...       = φ b               : by rw mul_inv_cancel_left))
  (λ q r, quotient.induction_on₂' q r $ φ.map_mul)

@[simp, to_additive quotient_add_group.lift_mk]
lemma lift_mk {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_mk']
lemma lift_mk' {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (mk g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_quot_mk]
lemma lift_quot_mk {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (quot.mk _ g : Q) = φ g := rfl

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
@[to_additive quotient_add_group.map "An `add_group` homomorphism `f : G →+ H` induces a map
`G/N →+ H/M` if `N ⊆ f⁻¹(M)`."]
def map (M : subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) :
  quotient N →* quotient M :=
begin
  refine quotient_group.lift N ((mk' M).comp f) _,
  assume x hx,
  refine quotient_group.eq.2 _,
  rw [mul_one, subgroup.inv_mem_iff],
  exact h hx,
end

@[simp, to_additive quotient_add_group.map_coe] lemma map_coe
  (M : subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
  map N M f h ↑x = ↑(f x) :=
lift_mk' _ _ x

@[to_additive quotient_add_group.map_mk'] lemma map_mk'
  (M : subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
  map N M f h (mk' _ x) = ↑(f x) :=
quotient_group.lift_mk' _ _ x

omit nN
variables (φ : G →* H)

open function monoid_hom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive quotient_add_group.ker_lift "The induced map from the quotient by the kernel to the
codomain."]
def ker_lift : quotient (ker φ) →* H :=
lift _ φ $ λ g, φ.mem_ker.mp

@[simp, to_additive quotient_add_group.ker_lift_mk]
lemma ker_lift_mk (g : G) : (ker_lift φ) g = φ g :=
lift_mk _ _ _

@[simp, to_additive quotient_add_group.ker_lift_mk']
lemma ker_lift_mk' (g : G) : (ker_lift φ) (mk g) = φ g :=
lift_mk' _ _ _

@[to_additive quotient_add_group.injective_ker_lift]
lemma ker_lift_injective : injective (ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [mem_ker,
  φ.map_mul, ← h, φ.map_inv, inv_mul_self]

-- Note that `ker φ` isn't definitionally `ker (φ.range_restrict)`
-- so there is a bit of annoying code duplication here

/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive quotient_add_group.range_ker_lift "The induced map from the quotient by the kernel to
the range."]
def range_ker_lift : quotient (ker φ) →* φ.range :=
lift _ φ.range_restrict $ λ g hg, (mem_ker _).mp $ by rwa range_restrict_ker

@[to_additive quotient_add_group.range_ker_lift_injective]
lemma range_ker_lift_injective : injective (range_ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : φ.range_restrict a = φ.range_restrict b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [←range_restrict_ker, mem_ker,
  φ.range_restrict.map_mul, ← h, φ.range_restrict.map_inv, inv_mul_self]

@[to_additive quotient_add_group.range_ker_lift_surjective]
lemma range_ker_lift_surjective : surjective (range_ker_lift φ) :=
begin
  rintro ⟨_, g, rfl⟩,
  use mk g,
  refl,
end

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive quotient_add_group.quotient_ker_equiv_range "The first isomorphism theorem
(a definition): the canonical isomorphism between `G/(ker φ)` to `range φ`."]
noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃* range φ :=
mul_equiv.of_bijective (range_ker_lift φ) ⟨range_ker_lift_injective φ, range_ker_lift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive quotient_add_group.quotient_ker_equiv_of_right_inverse "The canonical isomorphism
`G/(ker φ) ≃+ H` induced by a homomorphism `φ : G →+ H` with a right inverse `ψ : H → G`.",
  simps]
def quotient_ker_equiv_of_right_inverse (ψ : H → G) (hφ : function.right_inverse ψ φ) :
  quotient (ker φ) ≃* H :=
{ to_fun := ker_lift φ,
  inv_fun := mk ∘ ψ,
  left_inv := λ x, ker_lift_injective φ (by rw [function.comp_app, ker_lift_mk', hφ]),
  right_inv := hφ,
  .. ker_lift φ }

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `quotient_group.quotient_ker_equiv_of_right_inverse`.
-/
@[to_additive quotient_add_group.quotient_ker_equiv_of_surjective "The canonical isomorphism
`G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.

For a `computable` version, see `quotient_add_group.quotient_ker_equiv_of_right_inverse`."]
noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  quotient (ker φ) ≃* H :=
quotient_ker_equiv_of_right_inverse φ _ hφ.has_right_inverse.some_spec

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive "If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic."]
def equiv_quotient_of_eq {M N : subgroup G} [M.normal] [N.normal] (h : M = N) :
  quotient M ≃* quotient N :=
{ to_fun := (lift M (mk' N) (λ m hm, quotient_group.eq.mpr (by simpa [← h] using M.inv_mem hm))),
  inv_fun := (lift N (mk' M) (λ n hn, quotient_group.eq.mpr (by simpa [← h] using N.inv_mem hn))),
  left_inv := λ x, x.induction_on' $ by { intro, refl },
  right_inv := λ x, x.induction_on' $ by { intro, refl },
  map_mul' := λ x y, by rw map_mul }

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[to_additive "Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions."]
def quotient_map_subgroup_of_of_le {A' A B' B : subgroup G}
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal]
  (h' : A' ≤ B') (h : A ≤ B) :
  quotient (A'.subgroup_of A) →* quotient (B'.subgroup_of B) :=
map _ _ (subgroup.inclusion h) $
  by simp [subgroup.subgroup_of, subgroup.comap_comap]; exact subgroup.comap_mono h'

/-- Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic. 

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.subgroup_of A : subgroup A)` depends on on `A`.
-/
@[to_additive "Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.add_subgroup_of A : add_subgroup A)` depends on on `A`.
"]
def equiv_quotient_subgroup_of_of_eq {A' A B' B : subgroup G}
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal]
  (h' : A' = B') (h : A = B) :
  quotient (A'.subgroup_of A) ≃* quotient (B'.subgroup_of B) :=
by apply monoid_hom.to_mul_equiv
    (quotient_map_subgroup_of_of_le h'.le h.le) (quotient_map_subgroup_of_of_le h'.ge h.ge);
  { ext ⟨x⟩, simp [quotient_map_subgroup_of_of_le, map, lift, mk', subgroup.inclusion], refl }

section snd_isomorphism_thm

open subgroup

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`, where
`N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive "The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`,
where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`"]
noncomputable def quotient_inf_equiv_prod_normal_quotient (H N : subgroup G) [N.normal] :
  quotient ((H ⊓ N).comap H.subtype) ≃* quotient (N.comap (H ⊔ N).subtype) :=
/- φ is the natural homomorphism H →* (HN)/N. -/
let φ : H →* quotient (N.comap (H ⊔ N).subtype) :=
  (mk' $ N.comap (H ⊔ N).subtype).comp (inclusion le_sup_left) in
have φ_surjective : function.surjective φ := λ x, x.induction_on' $
  begin
    rintro ⟨y, (hy : y ∈ ↑(H ⊔ N))⟩, rw mul_normal H N at hy,
    rcases hy with ⟨h, n, hh, hn, rfl⟩,
    use [h, hh], apply quotient.eq.mpr, change h⁻¹ * (h * n) ∈ N,
    rwa [←mul_assoc, inv_mul_self, one_mul],
  end,
(equiv_quotient_of_eq (by simp [comap_comap, ←comap_ker])).trans
  (quotient_ker_equiv_of_surjective φ φ_surjective)

end snd_isomorphism_thm

section third_iso_thm

variables (M : subgroup G) [nM : M.normal]

include nM nN

@[to_additive quotient_add_group.map_normal]
instance map_normal : (M.map (quotient_group.mk' N)).normal :=
{ conj_mem := begin
    rintro _ ⟨x, hx, rfl⟩ y,
    refine induction_on' y (λ y, ⟨y * x * y⁻¹, subgroup.normal.conj_mem nM x hx y, _⟩),
    simp only [mk'_apply, coe_mul, coe_inv]
  end }

variables (h : N ≤ M)

/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive quotient_add_group.quotient_quotient_equiv_quotient_aux
"The map from the third isomorphism theorem for additive groups: `(A / N) / (M / N) → A / M`."]
def quotient_quotient_equiv_quotient_aux :
  quotient (M.map (mk' N)) →* quotient M :=
lift (M.map (mk' N))
  (map N M (monoid_hom.id G) h)
  (by { rintro _ ⟨x, hx, rfl⟩, rw map_mk' N M _ _ x,
        exact (quotient_group.eq_one_iff _).mpr hx })

@[simp, to_additive quotient_add_group.quotient_quotient_equiv_quotient_aux_coe]
lemma quotient_quotient_equiv_quotient_aux_coe (x : quotient_group.quotient N) :
  quotient_quotient_equiv_quotient_aux N M h x = quotient_group.map N M (monoid_hom.id G) h x :=
quotient_group.lift_mk' _ _ x

@[to_additive quotient_add_group.quotient_quotient_equiv_quotient_aux_coe_coe]
lemma quotient_quotient_equiv_quotient_aux_coe_coe (x : G) :
  quotient_quotient_equiv_quotient_aux N M h (x : quotient_group.quotient N) =
    x :=
quotient_group.lift_mk' _ _ x

/-- **Noether's third isomorphism theorem** for groups: `(G / N) / (M / N) ≃ G / M`. -/
@[to_additive quotient_add_group.quotient_quotient_equiv_quotient
"**Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃ A / M`."]
def quotient_quotient_equiv_quotient :
  quotient_group.quotient (M.map (quotient_group.mk' N)) ≃* quotient_group.quotient M :=
{ to_fun := quotient_quotient_equiv_quotient_aux N M h,
  inv_fun := quotient_group.map _ _ (quotient_group.mk' N) (subgroup.le_comap_map _ _),
  left_inv := λ x, quotient_group.induction_on' x $ λ x, quotient_group.induction_on' x $
    λ x, by simp,
  right_inv := λ x, quotient_group.induction_on' x $ λ x, by simp,
  map_mul' := monoid_hom.map_mul _ }

end third_iso_thm

end quotient_group
