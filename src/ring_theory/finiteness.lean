/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.noetherian
import ring_theory.ideal.operations
import ring_theory.algebra_tower
import group_theory.finiteness

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `module.finite`, `algebra.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `algebra.finite_presentation`, `ring_hom.finite_presentation`, `alg_hom.finite_presentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/

open function (surjective)
open_locale big_operators

section module_and_algebra

variables (R A B M N : Type*) [comm_ring R]
variables [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

/-- A module over a commutative ring is `finite` if it is finitely generated as a module. -/
class module.finite (R : Type*) (M : Type*) [semiring R] [add_comm_monoid M] [module R M] :
  Prop := (out : (⊤ : submodule R M).fg)

/-- An algebra over a commutative ring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
class algebra.finite_type : Prop := (out : (⊤ : subalgebra R A).fg)

/-- An algebra over a commutative ring is `finite_presentation` if it is the quotient of a
polynomial ring in `n` variables by a finitely generated ideal. -/
def algebra.finite_presentation : Prop :=
∃ (n : ℕ) (f : mv_polynomial (fin n) R →ₐ[R] A),
  surjective f ∧ f.to_ring_hom.ker.fg

namespace module

lemma finite_def {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [module R M] :
  finite R M ↔ (⊤ : submodule R M).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance is_noetherian.finite [is_noetherian R M] : finite R M :=
⟨is_noetherian.noetherian ⊤⟩

namespace finite
open submodule set

lemma iff_add_monoid_fg {M : Type*} [add_comm_monoid M] : module.finite ℕ M ↔ add_monoid.fg M :=
⟨λ h, add_monoid.fg_def.2 $ (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h),
  λ h, finite_def.2 $ (fg_iff_add_submonoid_fg ⊤).2 (add_monoid.fg_def.1 h)⟩

lemma iff_add_group_fg {G : Type*} [add_comm_group G] : module.finite ℤ G ↔ add_group.fg G :=
⟨λ h, add_group.fg_def.2 $ (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h),
  λ h, finite_def.2 $ (fg_iff_add_subgroup_fg ⊤).2 (add_group.fg_def.1 h)⟩

variables {R M N}

lemma exists_fin [finite R M] : ∃ (n : ℕ) (s : fin n → M), span R (range s) = ⊤ :=
submodule.fg_iff_exists_fin_generating_family.mp out

lemma of_surjective [hM : finite R M] (f : M →ₗ[R] N) (hf : surjective f) :
  finite R N :=
⟨begin
  rw [← linear_map.range_eq_top.2 hf, ← submodule.map_top],
  exact submodule.fg_map hM.1
end⟩

lemma of_injective [is_noetherian R N] (f : M →ₗ[R] N)
  (hf : function.injective f) : finite R M :=
⟨fg_of_injective f $ linear_map.ker_eq_bot.2 hf⟩

variables (R)

instance self : finite R R :=
⟨⟨{1}, by simpa only [finset.coe_singleton] using ideal.span_singleton_one⟩⟩

variables {R}

instance prod [hM : finite R M] [hN : finite R N] : finite R (M × N) :=
⟨begin
  rw ← submodule.prod_top,
  exact submodule.fg_prod hM.1 hN.1
end⟩

lemma equiv [hM : finite R M] (e : M ≃ₗ[R] N) : finite R N :=
of_surjective (e : M →ₗ[R] N) e.surjective

section algebra

lemma trans [algebra A B] [is_scalar_tower R A B] :
  ∀ [finite R A] [finite A B], finite R B
| ⟨⟨s, hs⟩⟩ ⟨⟨t, ht⟩⟩ := ⟨submodule.fg_def.2
  ⟨set.image2 (•) (↑s : set A) (↑t : set B),
    set.finite.image2 _ s.finite_to_set t.finite_to_set,
    by rw [set.image2_smul, submodule.span_smul hs (↑t : set B),
      ht, submodule.restrict_scalars_top]⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance finite_type [hRA : finite R A] : algebra.finite_type R A :=
⟨subalgebra.fg_of_submodule_fg hRA.1⟩

end algebra

end finite

end module

namespace algebra

namespace finite_type

lemma self : finite_type R R := ⟨⟨{1}, subsingleton.elim _ _⟩⟩

section
open_locale classical

protected lemma mv_polynomial (ι : Type*) [fintype ι] : finite_type R (mv_polynomial ι R) :=
⟨⟨finset.univ.image mv_polynomial.X, begin
  rw eq_top_iff, refine λ p, mv_polynomial.induction_on' p
    (λ u x, finsupp.induction u (subalgebra.algebra_map_mem _ x)
      (λ i n f hif hn ih, _))
    (λ p q ihp ihq, subalgebra.add_mem _ ihp ihq),
  rw [add_comm, mv_polynomial.monomial_add_single],
  exact subalgebra.mul_mem _ ih
    (subalgebra.pow_mem _ (subset_adjoin $ finset.mem_image_of_mem _ $ finset.mem_univ _) _)
end⟩⟩
end

variables {R A B}

lemma of_surjective (hRA : finite_type R A) (f : A →ₐ[R] B) (hf : surjective f) :
  finite_type R B :=
⟨begin
  convert subalgebra.fg_map _ f hRA.1,
  simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, alg_hom.mem_range] using hf
end⟩

lemma equiv (hRA : finite_type R A) (e : A ≃ₐ[R] B) : finite_type R B :=
hRA.of_surjective e e.surjective

lemma trans [algebra A B] [is_scalar_tower R A B] (hRA : finite_type R A) (hAB : finite_type A B) :
  finite_type R B :=
⟨fg_trans' hRA.1 hAB.1⟩

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
lemma iff_quotient_mv_polynomial : (finite_type R A) ↔ ∃ (s : finset A)
  (f : (mv_polynomial {x // x ∈ s} R) →ₐ[R] A), (surjective f) :=
begin
  split,
  { rintro ⟨s, hs⟩,
    use [s, mv_polynomial.aeval coe],
    intro x,
    have hrw : (↑s : set A) = (λ (x : A), x ∈ s.val) := rfl,
    rw [← set.mem_range, ← alg_hom.coe_range, ← adjoin_eq_range, ← hrw, hs],
    exact set.mem_univ x },
  { rintro ⟨s, ⟨f, hsur⟩⟩,
    exact finite_type.of_surjective (finite_type.mv_polynomial R {x // x ∈ s}) f hsur }
end

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
lemma iff_quotient_mv_polynomial' : (finite_type R A) ↔ ∃ (ι : Type u_2) [fintype ι]
  (f : (mv_polynomial ι R) →ₐ[R] A), (surjective f) :=
begin
  split,
  { rw iff_quotient_mv_polynomial,
    rintro ⟨s, ⟨f, hsur⟩⟩,
    use [{x // x ∈ s}, by apply_instance, f, hsur] },
  { rintro ⟨ι, ⟨hfintype, ⟨f, hsur⟩⟩⟩,
    letI : fintype ι := hfintype,
    exact finite_type.of_surjective (finite_type.mv_polynomial R ι) f hsur }
end

/-- An algebra is finitely generated if and only if it is a quotient of a polynomial ring in `n`
variables. -/
lemma iff_quotient_mv_polynomial'' : (finite_type R A) ↔ ∃ (n : ℕ)
  (f : (mv_polynomial (fin n) R) →ₐ[R] A), (surjective f) :=
begin
  split,
  { rw iff_quotient_mv_polynomial',
    rintro ⟨ι, hfintype, ⟨f, hsur⟩⟩,
    letI := hfintype,
    obtain ⟨equiv⟩ := @fintype.trunc_equiv_fin ι (classical.dec_eq ι) hfintype,
    replace equiv := mv_polynomial.rename_equiv R equiv,
    exact ⟨fintype.card ι, alg_hom.comp f equiv.symm, function.surjective.comp hsur
      (alg_equiv.symm equiv).surjective⟩ },
  { rintro ⟨n, ⟨f, hsur⟩⟩,
    exact finite_type.of_surjective (finite_type.mv_polynomial R (fin n)) f hsur }
end

/-- A finitely presented algebra is of finite type. -/
lemma of_finite_presentation : finite_presentation R A → finite_type R A :=
begin
  rintro ⟨n, f, hf⟩,
  apply (finite_type.iff_quotient_mv_polynomial'').2,
  exact ⟨n, f, hf.1⟩
end

instance prod [hA : finite_type R A] [hB : finite_type R B] : finite_type R (A × B) :=
⟨begin
  rw ← subalgebra.prod_top,
  exact subalgebra.fg_prod hA.1 hB.1
end⟩

end finite_type

namespace finite_presentation

variables {R A B}

/-- An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/
lemma of_finite_type [is_noetherian_ring R] : finite_type R A ↔ finite_presentation R A :=
begin
  refine ⟨λ h, _, algebra.finite_type.of_finite_presentation⟩,
  obtain ⟨n, f, hf⟩ := algebra.finite_type.iff_quotient_mv_polynomial''.1 h,
  refine ⟨n, f, hf, _⟩,
  have hnoet : is_noetherian_ring (mv_polynomial (fin n) R) := by apply_instance,
  replace hnoet := (is_noetherian_ring_iff.1 hnoet).noetherian,
  exact hnoet f.to_ring_hom.ker,
end

/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
lemma equiv (hfp : finite_presentation R A) (e : A ≃ₐ[R] B) : finite_presentation R B :=
begin
  obtain ⟨n, f, hf⟩ := hfp,
  use [n, alg_hom.comp ↑e f],
  split,
  { exact function.surjective.comp e.surjective hf.1 },
  suffices hker : (alg_hom.comp ↑e f).to_ring_hom.ker = f.to_ring_hom.ker,
  { rw hker, exact hf.2 },
  { have hco : (alg_hom.comp ↑e f).to_ring_hom = ring_hom.comp ↑e.to_ring_equiv f.to_ring_hom,
    { have h : (alg_hom.comp ↑e f).to_ring_hom = e.to_alg_hom.to_ring_hom.comp f.to_ring_hom := rfl,
      have h1 : ↑(e.to_ring_equiv) = (e.to_alg_hom).to_ring_hom := rfl,
      rw [h, h1] },
    rw [ring_hom.ker_eq_comap_bot, hco, ← ideal.comap_comap, ← ring_hom.ker_eq_comap_bot,
      ring_hom.ker_coe_equiv (alg_equiv.to_ring_equiv e), ring_hom.ker_eq_comap_bot] }
end

variable (R)

/-- The ring of polynomials in finitely many variables is finitely presented. -/
lemma mv_polynomial (ι : Type u_2) [fintype ι] : finite_presentation R (mv_polynomial ι R) :=
begin
  obtain ⟨equiv⟩ := @fintype.trunc_equiv_fin ι (classical.dec_eq ι) _,
  replace equiv := mv_polynomial.rename_equiv R equiv,
  refine ⟨_, alg_equiv.to_alg_hom equiv.symm, _⟩,
  split,
  { exact (alg_equiv.symm equiv).surjective },
  suffices hinj : function.injective equiv.symm.to_alg_hom.to_ring_hom,
  { rw [(ring_hom.injective_iff_ker_eq_bot _).1 hinj],
    exact submodule.fg_bot },
  exact (alg_equiv.symm equiv).injective
end

/-- `R` is finitely presented as `R`-algebra. -/
lemma self : finite_presentation R R :=
equiv (mv_polynomial R pempty) (mv_polynomial.pempty_alg_equiv R)

variable {R}

/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
lemma quotient {I : ideal A} (h : submodule.fg I) (hfp : finite_presentation R A) :
  finite_presentation R I.quotient :=
begin
  obtain ⟨n, f, hf⟩ := hfp,
  refine ⟨n, (ideal.quotient.mkₐ R I).comp f, _, _⟩,
  { exact (ideal.quotient.mkₐ_surjective R I).comp hf.1 },
  { refine submodule.fg_ker_ring_hom_comp _ _ hf.2 _ hf.1,
    simp [h] }
end

/-- If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
lemma of_surjective {f : A →ₐ[R] B} (hf : function.surjective f) (hker : f.to_ring_hom.ker.fg)
  (hfp : finite_presentation R A) : finite_presentation R B :=
equiv (quotient hker hfp) (ideal.quotient_ker_alg_equiv_of_surjective hf)

lemma iff : finite_presentation R A ↔
  ∃ n (I : ideal (_root_.mv_polynomial (fin n) R)) (e : I.quotient ≃ₐ[R] A), I.fg :=
begin
  refine ⟨λ h,_, λ h, _⟩,
  { obtain ⟨n, f, hf⟩ := h,
    use [n, f.to_ring_hom.ker, ideal.quotient_ker_alg_equiv_of_surjective hf.1, hf.2] },
  { obtain ⟨n, I, e, hfg⟩ := h,
    exact equiv (quotient hfg (mv_polynomial R _)) e }
end

/-- An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
lemma iff_quotient_mv_polynomial' : finite_presentation R A ↔ ∃ (ι : Type u_2) [fintype ι]
  (f : (_root_.mv_polynomial ι R) →ₐ[R] A), (surjective f) ∧ f.to_ring_hom.ker.fg :=
begin
  split,
  { rintro ⟨n, f, hfs, hfk⟩,
    set ulift_var := mv_polynomial.rename_equiv R equiv.ulift,
    refine ⟨ulift (fin n), infer_instance, f.comp ulift_var.to_alg_hom,
      hfs.comp ulift_var.surjective,
      submodule.fg_ker_ring_hom_comp _ _ _ hfk ulift_var.surjective⟩,
    convert submodule.fg_bot,
    exact ring_hom.ker_coe_equiv ulift_var.to_ring_equiv, },
  { rintro ⟨ι, hfintype, f, hf⟩,
    haveI : fintype ι := hfintype,
    obtain ⟨equiv⟩ := @fintype.trunc_equiv_fin ι (classical.dec_eq ι) _,
    replace equiv := mv_polynomial.rename_equiv R equiv,
    refine ⟨fintype.card ι, f.comp equiv.symm,
      hf.1.comp (alg_equiv.symm equiv).surjective,
      submodule.fg_ker_ring_hom_comp _ f _ hf.2 equiv.symm.surjective⟩,
    convert submodule.fg_bot,
    exact ring_hom.ker_coe_equiv (equiv.symm.to_ring_equiv), }
end

/-- If `A` is a finitely presented `R`-algebra, then `mv_polynomial (fin n) A` is finitely presented
as `R`-algebra. -/
lemma mv_polynomial_of_finite_presentation (hfp : finite_presentation R A) (ι : Type*)
  [fintype ι] : finite_presentation R (_root_.mv_polynomial ι A) :=
begin
  classical,
  let n := fintype.card ι,
  obtain ⟨e⟩ := fintype.trunc_equiv_fin ι,
  replace e := (mv_polynomial.rename_equiv A e).restrict_scalars R,
  refine equiv _ e.symm,
  obtain ⟨m, I, e, hfg⟩ := iff.1 hfp,
  refine equiv _ (mv_polynomial.map_alg_equiv (fin n) e),
  -- typeclass inference seems to struggle to find this path
  letI : is_scalar_tower R
    (_root_.mv_polynomial (fin m) R) (_root_.mv_polynomial (fin m) R) :=
      is_scalar_tower.right,
  letI : is_scalar_tower R
    (_root_.mv_polynomial (fin m) R)
    (_root_.mv_polynomial (fin n) (_root_.mv_polynomial (fin m) R)) :=
      mv_polynomial.is_scalar_tower,

  refine equiv _ ((@mv_polynomial.quotient_equiv_quotient_mv_polynomial
    _ (fin n) _ I).restrict_scalars R).symm,
  refine quotient (submodule.map_fg_of_fg I hfg _) _,
  let := mv_polynomial.sum_alg_equiv R (fin n) (fin m),
  refine equiv _ this,
  exact equiv (mv_polynomial R (fin (n + m))) (mv_polynomial.rename_equiv R fin_sum_fin_equiv).symm
end


/-- If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
lemma trans [algebra A B] [is_scalar_tower R A B] (hfpA : finite_presentation R A)
  (hfpB : finite_presentation A B) : finite_presentation R B :=
begin
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB,
  exact equiv (quotient hfg (mv_polynomial_of_finite_presentation hfpA _)) (e.restrict_scalars R)
end

end finite_presentation

end algebra

end module_and_algebra

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite (f : A →+* B) : Prop :=
by letI : algebra A B := f.to_algebra; exact module.finite A B

/-- A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →+* B) : Prop := @algebra.finite_type A B _ _ f.to_algebra

/-- A ring morphism `A →+* B` is of `finite_presentation` if `B` is finitely presented as
`A`-algebra. -/
def finite_presentation (f : A →+* B) : Prop := @algebra.finite_presentation A B _ _ f.to_algebra

namespace finite

variables (A)

lemma id : finite (ring_hom.id A) := module.finite.self A

variables {A}

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite :=
begin
  letI := f.to_algebra,
  exact module.finite.of_surjective (algebra.of_id A B).to_linear_map hf
end

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
@module.finite.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

lemma finite_type {f : A →+* B} (hf : f.finite) : finite_type f :=
@module.finite.finite_type _ _ _ _ f.to_algebra hf

end finite

namespace finite_type

variables (A)

lemma id : finite_type (ring_hom.id A) := algebra.finite_type.self A

variables {A}

lemma comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
@algebra.finite_type.of_surjective A B C _ _ f.to_algebra _ (g.comp f).to_algebra hf
{ to_fun := g, commutes' := λ a, rfl, .. g } hg

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite_type :=
by { rw ← f.comp_id, exact (id A).comp_surjective hf }

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
@algebra.finite_type.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

lemma of_finite_presentation {f : A →+* B} (hf : f.finite_presentation) : f.finite_type :=
@algebra.finite_type.of_finite_presentation A B _ _ f.to_algebra hf

end finite_type

namespace finite_presentation

variables (A)

lemma id : finite_presentation (ring_hom.id A) := algebra.finite_presentation.self A

variables {A}

lemma comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_presentation) (hg : surjective g)
  (hker : g.ker.fg) :  (g.comp f).finite_presentation :=
@algebra.finite_presentation.of_surjective A B C _ _ f.to_algebra _ (g.comp f).to_algebra
{ to_fun := g, commutes' := λ a, rfl, .. g } hg hker hf

lemma of_surjective (f : A →+* B) (hf : surjective f) (hker : f.ker.fg) : f.finite_presentation :=
by { rw ← f.comp_id, exact (id A).comp_surjective hf hker}

lemma of_finite_type [is_noetherian_ring A] {f : A →+* B} : f.finite_type ↔ f.finite_presentation :=
@algebra.finite_presentation.of_finite_type A B _ _ f.to_algebra _

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite_presentation) (hf : f.finite_presentation) :
  (g.comp f).finite_presentation :=
@algebra.finite_presentation.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
{ smul_assoc := λ a b c, begin
    simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
    refl
  end }
hf hg

end finite_presentation

end ring_hom

namespace alg_hom

variables {R A B C : Type*} [comm_ring R]
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra R A] [algebra R B] [algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite

/-- An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite_type

/-- An algebra morphism `A →ₐ[R] B` is of `finite_presentation` if it is of finite presentation as
ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
def finite_presentation (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite_presentation

namespace finite

variables (R A)

lemma id : finite (alg_hom.id R A) := ring_hom.finite.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
ring_hom.finite.comp hg hf

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite :=
ring_hom.finite.of_surjective f hf

lemma finite_type {f : A →ₐ[R] B} (hf : f.finite) : finite_type f :=
ring_hom.finite.finite_type hf

end finite

namespace finite_type

variables (R A)

lemma id : finite_type (alg_hom.id R A) := ring_hom.finite_type.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp hg hf

lemma comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp_surjective hf hg

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite_type :=
ring_hom.finite_type.of_surjective f hf

lemma of_finite_presentation {f : A →ₐ[R] B} (hf : f.finite_presentation) : f.finite_type :=
ring_hom.finite_type.of_finite_presentation hf

end finite_type

namespace finite_presentation

variables (R A)

lemma id : finite_presentation (alg_hom.id R A) := ring_hom.finite_presentation.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_presentation)
  (hf : f.finite_presentation) : (g.comp f).finite_presentation :=
ring_hom.finite_presentation.comp hg hf

lemma comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_presentation)
  (hg : surjective g) (hker : g.to_ring_hom.ker.fg) : (g.comp f).finite_presentation :=
ring_hom.finite_presentation.comp_surjective hf hg hker

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) (hker : f.to_ring_hom.ker.fg) :
  f.finite_presentation :=
ring_hom.finite_presentation.of_surjective f hf hker

lemma of_finite_type [is_noetherian_ring A] {f : A →ₐ[R] B} :
  f.finite_type ↔ f.finite_presentation :=
ring_hom.finite_presentation.of_finite_type

end finite_presentation

end alg_hom

section monoid_algebra

variables {R : Type*} {M : Type*}

namespace add_monoid_algebra

open algebra add_submonoid submodule

section span

section semiring

variables [comm_semiring R] [add_monoid M]

/-- An element of `add_monoid_algebra R M` is in the subalgebra generated by its support. -/
lemma mem_adjoin_support (f : add_monoid_algebra R M) : f ∈ adjoin R (of' R M '' f.support) :=
begin
  suffices : span R (of' R M '' f.support) ≤ (adjoin R (of' R M '' f.support)).to_submodule,
  { exact this (mem_span_support f) },
  rw submodule.span_le,
  exact subset_adjoin
end

/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the set of supports of
elements of `S` generates `add_monoid_algebra R M`. -/
lemma support_gen_of_gen {S : set (add_monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (⋃ f ∈ S, (of' R M '' (f.support : set M))) = ⊤ :=
begin
  refine le_antisymm le_top _,
  rw [← hS, adjoin_le_iff],
  intros f hf,
  have hincl : of' R M '' f.support ⊆
    ⋃ (g : add_monoid_algebra R M) (H : g ∈ S), of' R M '' g.support,
  { intros s hs,
    exact set.mem_bUnion_iff.2 ⟨f, ⟨hf, hs⟩⟩ },
  exact adjoin_mono hincl (mem_adjoin_support f)
end

/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the image of the union of
the supports of elements of `S` generates `add_monoid_algebra R M`. -/
lemma support_gen_of_gen' {S : set (add_monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (of' R M '' (⋃ f ∈ S, (f.support : set M))) = ⊤ :=
begin
  suffices : of' R M '' (⋃ f ∈ S, (f.support : set M)) = ⋃ f ∈ S, (of' R M '' (f.support : set M)),
  { rw this,
    exact support_gen_of_gen hS },
  simp only [set.image_Union]
end

end semiring

section ring

variables [comm_ring R] [add_comm_monoid M]

/-- If `add_monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its
image generates, as algera, `add_monoid_algebra R M`. -/
lemma exists_finset_adjoin_eq_top [h : finite_type R (add_monoid_algebra R M)] :
  ∃ G : finset M, algebra.adjoin R (of' R M '' G) = ⊤ :=
begin
  unfreezingI { obtain ⟨S, hS⟩ := h },
  letI : decidable_eq M := classical.dec_eq M,
  use finset.bUnion S (λ f, f.support),
  have : (finset.bUnion S (λ f, f.support) : set M) = ⋃ f ∈ S, (f.support : set M),
  { simp only [finset.set_bUnion_coe, finset.coe_bUnion] },
  rw [this],
  exact support_gen_of_gen' hS
end

/-- The image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
lemma of'_mem_span [nontrivial R] {m : M} {S : set M} :
  of' R M m ∈ span R (of' R M '' S) ↔ m ∈ S :=
begin
  refine ⟨λ h, _, λ h, submodule.subset_span $ set.mem_image_of_mem (of R M) h⟩,
  rw [of', ← finsupp.supported_eq_span_single, finsupp.mem_supported,
    finsupp.support_single_ne_zero (@one_ne_zero R _ (by apply_instance))] at h,
  simpa using h
end

/--If the image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
the closure of some `S : set M` then `m ∈ closure S`. -/
lemma mem_closure_of_mem_span_closure [nontrivial R] {m : M} {S : set M}
  (h : of' R M m ∈ span R (submonoid.closure (of' R M '' S) : set (add_monoid_algebra R M))) :
  m ∈ closure S :=
begin
  suffices : multiplicative.of_add m ∈ submonoid.closure (multiplicative.to_add ⁻¹' S),
  { simpa [← to_submonoid_closure] },
  rw [set.image_congr' (show ∀ x, of' R M x = of R M x, from λ x, of'_eq_of x),
    ← monoid_hom.map_mclosure] at h,
  simpa using of'_mem_span.1 h
end

end ring

end span

variables [add_comm_monoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`add_monoid_algebra R M`. -/
lemma mv_polynomial_aeval_of_surjective_of_closure [comm_semiring R] {S : set M}
  (hS : closure S = ⊤) : function.surjective (mv_polynomial.aeval
  (λ (s : S), of' R M ↑s) : mv_polynomial S R → add_monoid_algebra R M) :=
begin
  refine λ f, induction_on f (λ m, _) _ _,
  { have : m ∈ closure S := hS.symm ▸ mem_top _,
    refine closure_induction this (λ m hm, _) _ _,
    { exact ⟨mv_polynomial.X ⟨m, hm⟩, mv_polynomial.aeval_X _ _⟩ },
    { exact ⟨1, alg_hom.map_one _⟩ },
    { rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩,
      exact ⟨P₁ * P₂, by rw [alg_hom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply,
        single_mul_single, one_mul]; refl⟩ } },
  { rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩,
    exact ⟨P + Q, alg_hom.map_add _ _ _⟩ },
  { rintro r f ⟨P, rfl⟩,
    exact ⟨r • P, alg_hom.map_smul _ _ _⟩ }
end

/-- If an additive monoid `M` is finitely generated then `add_monoid_algebra R M` is of finite
type. -/
instance finite_type_of_fg [comm_ring R] [h : add_monoid.fg M] :
  finite_type R (add_monoid_algebra R M) :=
begin
  obtain ⟨S, hS⟩ := h.out,
  exact (finite_type.mv_polynomial R (S : set M)).of_surjective (mv_polynomial.aeval
    (λ (s : (S : set M)), of' R M ↑s)) (mv_polynomial_aeval_of_surjective_of_closure hS)
end

/-- An additive monoid `M` is finitely generated if and only if `add_monoid_algebra R M` is of
finite type. -/
lemma finite_type_iff_fg [comm_ring R] [nontrivial R] :
  finite_type R (add_monoid_algebra R M) ↔ add_monoid.fg M :=
begin
  refine ⟨λ h, _, λ h, @add_monoid_algebra.finite_type_of_fg _ _ _ _ h⟩,
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h,
  refine add_monoid.fg_def.2 ⟨S, (eq_top_iff' _).2 (λ m, _)⟩,
  have hm : of' R M m ∈ (adjoin R (of' R M '' ↑S)).to_submodule,
  { simp only [hS, top_to_submodule, submodule.mem_top], },
  rw [adjoin_eq_span] at hm,
  exact mem_closure_of_mem_span_closure hm
end

/-- If `add_monoid_algebra R M` is of finite type then `M` is finitely generated. -/
lemma fg_of_finite_type [comm_ring R] [nontrivial R] [h : finite_type R (add_monoid_algebra R M)] :
  add_monoid.fg M :=
finite_type_iff_fg.1 h

/-- An additive group `G` is finitely generated if and only if `add_monoid_algebra R G` is of
finite type. -/
lemma finite_type_iff_group_fg {G : Type*} [add_comm_group G] [comm_ring R] [nontrivial R] :
  finite_type R (add_monoid_algebra R G) ↔ add_group.fg G :=
by simpa [add_group.fg_iff_add_monoid.fg] using finite_type_iff_fg

end add_monoid_algebra

namespace monoid_algebra

open algebra submonoid submodule

section span

section semiring

variables [comm_semiring R] [monoid M]

/-- An element of `monoid_algebra R M` is in the subalgebra generated by its support. -/
lemma mem_adjoint_support (f : monoid_algebra R M) : f ∈ adjoin R (of R M '' f.support) :=
begin
  suffices : span R (of R M '' f.support) ≤ (adjoin R (of R M '' f.support)).to_submodule,
  { exact this (mem_span_support f) },
  rw submodule.span_le,
  exact subset_adjoin
end

/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the set of supports of elements
of `S` generates `monoid_algebra R M`. -/
lemma support_gen_of_gen {S : set (monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (⋃ f ∈ S, (of R M '' (f.support : set M))) = ⊤ :=
begin
  refine le_antisymm le_top _,
  rw [← hS, adjoin_le_iff],
  intros f hf,
  have hincl : (of R M) '' f.support ⊆
    ⋃ (g : monoid_algebra R M) (H : g ∈ S), of R M '' g.support,
  { intros s hs,
    exact set.mem_bUnion_iff.2 ⟨f, ⟨hf, hs⟩⟩ },
  exact adjoin_mono hincl (mem_adjoint_support f)
end

/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the image of the union of the
supports of elements of `S` generates `monoid_algebra R M`. -/
lemma support_gen_of_gen' {S : set (monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (of R M '' (⋃ f ∈ S, (f.support : set M))) = ⊤ :=
begin
  suffices : of R M '' (⋃ f ∈ S, (f.support : set M)) = ⋃ f ∈ S, (of R M '' (f.support : set M)),
  { rw this,
    exact support_gen_of_gen hS },
  simp only [set.image_Union]
end

end semiring

section ring

variables [comm_ring R] [comm_monoid M]

/-- If `monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its image
generates, as algera, `monoid_algebra R M`. -/
lemma exists_finset_adjoin_eq_top [h :finite_type R (monoid_algebra R M)] :
  ∃ G : finset M, algebra.adjoin R (of R M '' G) = ⊤ :=
begin
  unfreezingI { obtain ⟨S, hS⟩ := h },
  letI : decidable_eq M := classical.dec_eq M,
  use finset.bUnion S (λ f, f.support),
  have : (finset.bUnion S (λ f, f.support) : set M) = ⋃ f ∈ S, (f.support : set M),
  { simp only [finset.set_bUnion_coe, finset.coe_bUnion] },
  rw [this],
  exact support_gen_of_gen' hS
end

/-- The image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
lemma of_mem_span_of_iff [nontrivial R] {m : M} {S : set M} :
  of R M m ∈ span R (of R M '' S) ↔ m ∈ S :=
begin
  refine ⟨λ h, _, λ h, submodule.subset_span $ set.mem_image_of_mem (of R M) h⟩,
  rw [of, monoid_hom.coe_mk, ← finsupp.supported_eq_span_single, finsupp.mem_supported,
    finsupp.support_single_ne_zero (@one_ne_zero R _ (by apply_instance))] at h,
  simpa using h
end

/--If the image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by the
closure of some `S : set M` then `m ∈ closure S`. -/
lemma mem_closure_of_mem_span_closure [nontrivial R] {m : M} {S : set M}
  (h : of R M m ∈ span R (submonoid.closure (of R M '' S) : set (monoid_algebra R M))) :
  m ∈ closure S :=
begin
  rw ← monoid_hom.map_mclosure at h,
  simpa using of_mem_span_of_iff.1 h
end

end ring

end span

variables [comm_monoid M]

/-- If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`monoid_algebra R M`. -/
lemma mv_polynomial_aeval_of_surjective_of_closure [comm_semiring R] {S : set M}
  (hS : closure S = ⊤) : function.surjective (mv_polynomial.aeval
  (λ (s : S), of R M ↑s) : mv_polynomial S R → monoid_algebra R M) :=
begin
  refine λ f, induction_on f (λ m, _) _ _,
  { have : m ∈ closure S := hS.symm ▸ mem_top _,
    refine closure_induction this (λ m hm, _) _ _,
    { exact ⟨mv_polynomial.X ⟨m, hm⟩, mv_polynomial.aeval_X _ _⟩ },
    { exact ⟨1, alg_hom.map_one _⟩ },
    { rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩,
      exact ⟨P₁ * P₂, by rw [alg_hom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply,
        single_mul_single, one_mul]⟩ } },
  { rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩,
    exact ⟨P + Q, alg_hom.map_add _ _ _⟩ },
  { rintro r f ⟨P, rfl⟩,
    exact ⟨r • P, alg_hom.map_smul _ _ _⟩ }
end

/-- If a monoid `M` is finitely generated then `monoid_algebra R M` is of finite type. -/
instance finite_type_of_fg [comm_ring R] [monoid.fg M] : finite_type R (monoid_algebra R M) :=
add_monoid_algebra.finite_type_of_fg.equiv (to_additive_alg_equiv R M).symm

/-- A monoid `M` is finitely generated if and only if `monoid_algebra R M` is of finite type. -/
lemma finite_type_iff_fg [comm_ring R] [nontrivial R] :
  finite_type R (monoid_algebra R M) ↔ monoid.fg M :=
⟨λ h, monoid.fg_iff_add_fg.2 $ add_monoid_algebra.finite_type_iff_fg.1 $ h.equiv $
  to_additive_alg_equiv R M, λ h, @monoid_algebra.finite_type_of_fg _ _ _ _ h⟩

/-- If `monoid_algebra R M` is of finite type then `M` is finitely generated. -/
lemma fg_of_finite_type [comm_ring R] [nontrivial R] [h : finite_type R (monoid_algebra R M)] :
  monoid.fg M :=
finite_type_iff_fg.1 h

/-- A group `G` is finitely generated if and only if `add_monoid_algebra R G` is of finite type. -/
lemma finite_type_iff_group_fg {G : Type*} [comm_group G] [comm_ring R] [nontrivial R] :
  finite_type R (monoid_algebra R G) ↔ group.fg G :=
by simpa [group.fg_iff_monoid.fg] using finite_type_iff_fg

end monoid_algebra

end monoid_algebra
