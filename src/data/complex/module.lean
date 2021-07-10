/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import data.complex.basic
import algebra.algebra.ordered
import data.matrix.notation
import field_theory.tower
import linear_algebra.finite_dimensional

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`has_scalar`, `mul_action`, `distrib_mul_action`, `module`, `algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `complex.re_lm` (`ℝ`-linear map);
* `complex.im_lm` (`ℝ`-linear map);
* `complex.of_real_am` (`ℝ`-algebra (homo)morphism);
* `complex.conj_ae` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

-/

namespace complex

variables {R : Type*} {S : Type*}

section

variables [has_scalar R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`restrict_scalars.module ℝ ℂ ℂ  = complex.module` definitionally. -/
instance : has_scalar R ℂ :=
{ smul := λ r x, ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩ }

lemma smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(•)]
lemma smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(•)]

@[simp] lemma smul_coe {x : ℝ} {z : ℂ} : x • z = x * z :=
by ext; simp [smul_re, smul_im]

end

instance [has_scalar R ℝ] [has_scalar S ℝ] [smul_comm_class R S ℝ] : smul_comm_class R S ℂ :=
{ smul_comm := λ r s x, by ext; simp [smul_re, smul_im, smul_comm] }

instance [has_scalar R S] [has_scalar R ℝ] [has_scalar S ℝ] [is_scalar_tower R S ℝ] :
  is_scalar_tower R S ℂ :=
{ smul_assoc := λ r s x, by ext; simp [smul_re, smul_im, smul_assoc] }

instance [monoid R] [mul_action R ℝ] : mul_action R ℂ :=
{ one_smul := λ x, by ext; simp [smul_re, smul_im, one_smul],
  mul_smul := λ r s x, by ext; simp  [smul_re, smul_im, mul_smul] }

instance [semiring R] [distrib_mul_action R ℝ] : distrib_mul_action R ℂ :=
{ smul_add := λ r x y, by ext; simp [smul_re, smul_im, smul_add],
  smul_zero := λ r, by ext; simp [smul_re, smul_im, smul_zero] }

instance [semiring R] [module R ℝ] : module R ℂ :=
{ add_smul := λ r s x, by ext; simp [smul_re, smul_im, add_smul],
  zero_smul := λ r, by ext; simp [smul_re, smul_im, zero_smul] }

instance [comm_semiring R] [algebra R ℝ] : algebra R ℂ :=
{ smul := (•),
  smul_def' := λ r x, by ext; simp [smul_re, smul_im, algebra.smul_def],
  commutes' := λ r ⟨xr, xi⟩, by ext; simp [smul_re, smul_im, algebra.commutes],
  ..complex.of_real.comp (algebra_map R ℝ) }

/-- Note that when applied the RHS is further simplified by `complex.of_real_eq_coe`. -/
@[simp] lemma coe_algebra_map : ⇑(algebra_map ℝ ℂ) = complex.of_real := rfl

section
variables {A : Type*} [semiring A] [algebra ℝ A]

/-- We need this lemma since `complex.coe_algebra_map` diverts the simp-normal form away from
`alg_hom.commutes`. -/
@[simp] lemma _root_.alg_hom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) :
  f x = algebra_map ℝ A x :=
f.commutes x

/-- Two `ℝ`-algebra homomorphisms from ℂ are equal if they agree on `complex.I`. -/
@[ext]
lemma alg_hom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f I = g I) : f = g :=
begin
  ext ⟨x, y⟩,
  simp only [mk_eq_add_mul_I, alg_hom.map_add, alg_hom.map_coe_real_complex, alg_hom.map_mul, h]
end

end

section
open_locale complex_order

lemma complex_ordered_module : ordered_module ℝ ℂ :=
{ smul_lt_smul_of_pos := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, rfl⟩ := lt_def.mp h₁,
    refine lt_def.mpr ⟨x * y, _, _⟩,
    exact mul_pos h₂ l,
    ext; simp [mul_add],
  end,
  lt_of_smul_lt_smul_of_pos := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, e⟩ := lt_def.mp h₁,
    by_cases h : x = 0,
    { subst h, exfalso, apply lt_irrefl 0 h₂, },
    { refine lt_def.mpr ⟨y / x, div_pos l h₂, _⟩,
      replace e := congr_arg (λ z, (x⁻¹ : ℂ) * z) e,
      simp only [mul_add, ←mul_assoc, h, one_mul, of_real_eq_zero, smul_coe, ne.def,
        not_false_iff, inv_mul_cancel] at e,
      convert e,
      simp only [div_eq_iff_mul_eq, h, of_real_eq_zero, of_real_div, ne.def, not_false_iff],
      norm_cast,
      simp [mul_comm _ y, mul_assoc, h],
    },
  end }

localized "attribute [instance] complex_ordered_module" in complex_order

end


open submodule finite_dimensional

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basis_one_I : basis (fin 2) ℝ ℂ :=
basis.of_equiv_fun
{ to_fun := λ z, ![z.re, z.im],
  inv_fun := λ c, c 0 + c 1 • I,
  left_inv := λ z, by simp,
  right_inv := λ c, by { ext i, fin_cases i; simp },
  map_add' := λ z z', by simp,
  map_smul' := λ c z, by simp }

@[simp] lemma coe_basis_one_I_repr (z : ℂ) : ⇑(basis_one_I.repr z) = ![z.re, z.im] := rfl

@[simp] lemma coe_basis_one_I : ⇑basis_one_I = ![1, I] :=
funext $ λ i, basis.apply_eq_iff.mpr $ finsupp.ext $ λ j,
by fin_cases i; fin_cases j;
    simp only [coe_basis_one_I_repr, finsupp.single_eq_same, finsupp.single_eq_of_ne,
              matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
              nat.one_ne_zero, fin.one_eq_zero_iff, fin.zero_eq_one_iff, ne.def, not_false_iff,
              one_re, one_im, I_re, I_im]

instance : finite_dimensional ℝ ℂ := of_fintype_basis basis_one_I

@[simp] lemma finrank_real_complex : finite_dimensional.finrank ℝ ℂ = 2 :=
by rw [finrank_eq_card_basis basis_one_I, fintype.card_fin]

@[simp] lemma dim_real_complex : module.rank ℝ ℂ = 2 :=
by simp [← finrank_eq_dim, finrank_real_complex]

lemma {u} dim_real_complex' : cardinal.lift.{0 u} (module.rank ℝ ℂ) = 2 :=
by simp [← finrank_eq_dim, finrank_real_complex, bit0]

/-- `fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
lemma finrank_real_complex_fact : fact (finrank ℝ ℂ = 2) := ⟨finrank_real_complex⟩

end complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
@[priority 900]
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
restrict_scalars.module ℝ ℂ E

instance module.real_complex_tower (E : Type*) [add_comm_group E] [module ℂ E] :
  is_scalar_tower ℝ ℂ E :=
restrict_scalars.is_scalar_tower ℝ ℂ E

@[priority 100]
instance finite_dimensional.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E]
  [finite_dimensional ℂ E] : finite_dimensional ℝ E :=
finite_dimensional.trans ℝ ℂ E

lemma dim_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  module.rank ℝ E = 2 * module.rank ℂ E :=
cardinal.lift_inj.1 $
  by { rw [← dim_mul_dim' ℝ ℂ E, complex.dim_real_complex], simp [bit0] }

lemma finrank_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  finite_dimensional.finrank ℝ E = 2 * finite_dimensional.finrank ℂ E :=
by rw [← finite_dimensional.finrank_mul_finrank ℝ ℂ E, complex.finrank_real_complex]

namespace complex

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_lm : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  map_add' := add_re,
  map_smul' := by simp, }

@[simp] lemma re_lm_coe : ⇑re_lm = re := rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def im_lm : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  map_add' := add_im,
  map_smul' := by simp, }

@[simp] lemma im_lm_coe : ⇑im_lm = im := rfl

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_am : ℝ →ₐ[ℝ] ℂ := algebra.of_id ℝ ℂ

@[simp] lemma of_real_am_coe : ⇑of_real_am = coe := rfl

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conj_ae : ℂ ≃ₐ[ℝ] ℂ :=
{ inv_fun := conj,
  left_inv := conj_conj,
  right_inv := conj_conj,
  commutes' := conj_of_real,
  .. conj }

@[simp] lemma conj_ae_coe : ⇑conj_ae = conj := rfl

section lift

variables {A : Type*} [ring A] [algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `complex.lift` for this as an equiv. -/
def lift_aux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
alg_hom.of_linear_map
  ((algebra.of_id ℝ A).to_linear_map.comp re_lm + (linear_map.to_span_singleton _ _ I').comp im_lm)
  (show algebra_map ℝ A 1 + (0 : ℝ) • I' = 1,
    by rw [ring_hom.map_one, zero_smul, add_zero])
  (λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩, show algebra_map ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I'
                          = (algebra_map ℝ A x₁ + y₁ • I') * (algebra_map ℝ A x₂ + y₂ • I'),
    begin
      rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm],
      congr' 1, -- equate "real" and "imaginary" parts
      { rw [smul_mul_smul, hf, smul_neg, ←algebra.algebra_map_eq_smul_one, ←sub_eq_add_neg,
          ←ring_hom.map_mul, ←ring_hom.map_sub], },
      { rw [algebra.smul_def, algebra.smul_def, algebra.smul_def, ←algebra.right_comm _ x₂,
          ←mul_assoc, ←add_mul, ←ring_hom.map_mul, ←ring_hom.map_mul, ←ring_hom.map_add] }
    end)

@[simp]
lemma lift_aux_apply (I' : A) (hI') (z : ℂ) :
 lift_aux I' hI' z = algebra_map ℝ A z.re + z.im • I' := rfl

lemma lift_aux_apply_I (I' : A) (hI') : lift_aux I' hI' I = I' := by simp

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `quaternion`s.

This isomorphism is named to match the very similar `zsqrtd.lift`. -/
@[simps {simp_rhs := tt}]
def lift : {I' : A // I' * I' = -1} ≃ (ℂ →ₐ[ℝ] A) :=
{ to_fun := λ I', lift_aux I' I'.prop,
  inv_fun := λ F, ⟨F I, by rw [←F.map_mul, I_mul_I, alg_hom.map_neg, alg_hom.map_one]⟩,
  left_inv := λ I', subtype.ext $ lift_aux_apply_I I' I'.prop,
  right_inv := λ F, alg_hom_ext $ lift_aux_apply_I _ _, }

/- When applied to `complex.I` itself, `lift` is the identity. -/
@[simp]
lemma lift_aux_I : lift_aux I I_mul_I = alg_hom.id ℝ ℂ :=
alg_hom_ext $ lift_aux_apply_I _ _

/- When applied to `-complex.I`, `lift` is conjugation, `conj`. -/
@[simp]
lemma lift_aux_neg_I : lift_aux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conj_ae :=
alg_hom_ext $ (lift_aux_apply_I _ _).trans conj_I.symm

end lift

end complex
