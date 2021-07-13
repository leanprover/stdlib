import linear_algebra.basic
import data.nat.basic
import tactic.apply
import tactic.omega
import tactic.subtype_instance
import ring_theory.noetherian
import ring_theory.adjoin
import data.matrix.basic
import order.order_iso_nat

namespace dedekind_finite

section

variables (R : Type*)

class is_dedekind_finite_ring [ring R] :=
(inv_comm : ∀ a b : R, a * b = 1 → b * a = 1)

--class dedekind_finite extends ring R, right_inv_is_left_inv R

@[priority 100]
instance is_dedekind_finite_ring_of_comm_ring [comm_ring R] : is_dedekind_finite_ring R :=
⟨λ a b h, h ▸ mul_comm b a⟩

end
section

instance is_dedekind_finite_ring_pi {ι : Type*} {α : ι → Type*}
  [∀ i, ring $ α i] [∀ i, is_dedekind_finite_ring $ α i] : is_dedekind_finite_ring (Π i, α i) := by pi_instance

end

section
variables (R : Type*)

--instance subring.is_dedekind_finite_ring [ring R] [is_dedekind_finite_ring R] (S : set R) [is_subring S] : is_dedekind_finite_ring S :=
--by subtype_instance

def is_nilpotent {R : Type*} [ring R] (a : R) := ∃ n : ℕ, a^n = 0
def nilpotents [ring R] := { a : R | is_nilpotent a }
-- TODO would be nice to set this up as the radical of the zero ideal but currently there doesn't seem to be much about one-sided ideals in non-comm rings

class is_reduced_ring [ring R] :=
(no_nilpotents : ∀ a : R, ∀ n : ℕ, a^n = 0 → a = 0)

lemma zero_nilpotent [ring R] : is_nilpotent (0 : R) := ⟨1, pow_one 0⟩
lemma zero_in_nilpotents [ring R] : (0 : R) ∈ nilpotents R := zero_nilpotent R

lemma nilpotents_of_reduced [ring R] [is_reduced_ring R] : nilpotents R = {0} :=
begin
apply' set.eq_of_subset_of_subset,
{
    rintros x ⟨n, hn⟩,
    rw set.mem_singleton_iff,
    exact is_reduced_ring.no_nilpotents _ n hn,
},
{
    rw set.singleton_subset_iff,
    exact zero_in_nilpotents R,
}
end

class is_reversible_ring [ring R] :=
(zero_div_comm : ∀ a b : R, a * b = 0 → b * a = 0)

@[priority 100]
instance is_reversible_ring_of_domain [domain R] : is_reversible_ring R :=
⟨λ a b h,
begin
    cases domain.eq_zero_or_eq_zero_of_mul_eq_zero a b h,
    { rw h_1, rw [mul_zero], },
    { rw h_1, rw [zero_mul], },
end⟩


@[priority 100]
instance reversible_of_reduced [ring R] [is_reduced_ring R] : is_reversible_ring R :=
⟨λ a b h,
begin
    apply is_reduced_ring.no_nilpotents (b * a) 2,
    rw [pow_two, ← mul_assoc, mul_assoc b, h, mul_zero, zero_mul],
end⟩

@[priority 100]
instance reversible_of_comm_ring [comm_ring R] : is_reversible_ring R :=
⟨λ a b h, h ▸ mul_comm b a⟩

@[priority 100]
instance is_dedekind_finite_ring_of_reversible [ring R] [is_reversible_ring R] : is_dedekind_finite_ring R :=
⟨λ a b h,
begin
    have :=
    calc (b * a - 1) * b = b * (a * b) - b : by rw [sub_mul, one_mul, mul_assoc]
                    ...  = 0               : by rw [h, mul_one, sub_self],
    have : b * (b * a - 1) = 0 := is_reversible_ring.zero_div_comm _ _ this,
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, sub_eq_zero] at this,
    have abba_eq_one := congr_arg ((*) a) this,
    rw [h] at abba_eq_one,
    calc b * a = (a * (b^2 * a)) * b * a : by simp [abba_eq_one]
        ...    = (a * b^2) * (a * b) * a : by simp [mul_assoc] -- I feel like ac_refl should do this
        ...    = (a * b^2 * a)           : by simp [h]
        ...    = 1                       : by assoc_rw [abba_eq_one],
end⟩

@[priority 100]
instance is_dedekind_finite_ring_of_reduced [ring R] [is_reduced_ring R] : is_dedekind_finite_ring R := by apply_instance


variable [ring R]

open linear_map
open function


variables {γ : Type*} [preorder γ] [decidable_rel ((≤) : γ → γ → Prop)]

def strict_monotone_inc_subseq {f : ℕ → γ} (h : ∀ n, ∃ m, f n < f (n + m)) : ℕ → ℕ
| 0       := 0
| (n + 1) := (strict_monotone_inc_subseq n) + nat.find (h (strict_monotone_inc_subseq n))

lemma strict_monotone_inc_subseq_spec (f : ℕ → γ) (h : ∀ n, ∃ m, f n < f (n + m)) :
  strict_mono (f ∘ (strict_monotone_inc_subseq h)) := strict_mono.nat (λ n, nat.find_spec (h (strict_monotone_inc_subseq h n)))





-- TODO artinian version of ring stuff?


open_locale classical

theorem noeth_mod_surj_inj {R : Type*} [ring R] {M : Type*} [add_comm_group M] [module R M] [is_noetherian R M] {f : M →ₗ[R] M} (f_surj : function.surjective f) : function.injective f :=
begin
    have := well_founded_submodule_gt R M,
    rw rel_embedding.well_founded_iff_no_descending_seq at this,
    set ordf : ℕ → submodule R M := λ n, linear_map.ker (f ^ n),
    suffices : ∃ n (h : n ≠ 0), ∀ m, ordf n = ordf (n + m),
    begin
        obtain ⟨n, hne, hn⟩ := this,
        have pow_surj := iterate_surjective f_surj n,
        have : ordf n ⊓ linear_map.range (f ^ n) = ⊥ :=
        begin
            ext,
            rw [submodule.mem_inf, mem_ker, mem_range, submodule.mem_bot],
            split,
            {
                rintro ⟨h₁, ⟨y, h₂⟩⟩,
                rw ← h₂ at h₁, rw ← linear_map.comp_apply at h₁,
                have : f * f = f.comp f := mul_eq_comp f f,
                rw [← mul_eq_comp, ←pow_add] at h₁, rw ← mem_ker at h₁,
                have : ker (f ^ n) = ker (f ^ (n + n)) := hn n,
                rw ← this at h₁, rw mem_ker at h₁,
                rw h₁ at h₂, exact h₂.symm,
            },
            intro a,
            rw [a, map_zero],
            use 0,
            rw map_zero,

        end,
        have range_eq_top : range (f ^ n) = ⊤ := range_eq_top.mpr pow_surj,
        have : ordf n = ⊥ := by simpa [range_eq_top] using this,
        have : function.injective ⇑(f ^ n) := ker_eq_bot.mp this,
        exact injective_of_iterate_injective hne this,
    end,
    contrapose! this,
    refine nonempty.intro _,
    have bbbb : ∀ n, ∃ (m : ℕ), (λ (n : ℕ), ordf (n + 1)) n < (λ (n : ℕ), ordf (n + 1)) (n + m) :=
    (λ n, (begin
        have aaaaa : ∀ n m, ordf (n + 1) ≤ ordf (n + m + 1) :=
        λ n m x hx,
        begin
            simp only [ordf, mem_ker, submodule.mem_coe, add_comm, add_left_comm] at hx ⊢,
            rw [add_comm m, ←add_assoc, add_comm, pow_add, mul_eq_comp, linear_map.comp_apply,
              hx, map_zero]
        end,
        have := (this (n + 1) (nat.succ_ne_zero n)),
        cases this with m hm,
        use m,
        simp only [],
        refine lt_of_le_of_ne _ _,
        exact (aaaaa n m),
        rw add_assoc, rw add_comm m, rw ← add_assoc,
        exact hm,
    end)),
    refine rel_embedding.of_monotone ((λ (n : ℕ), ordf (n + 1)) ∘ strict_monotone_inc_subseq bbbb) _,
    intros a b hab,
    exact strict_monotone_inc_subseq_spec (λ n, ordf (n + 1)) bbbb hab,
end


@[priority 100]
instance is_dedekind_finite_ring_of_noetherian [is_noetherian_ring R] : is_dedekind_finite_ring R :=
⟨λ a b h,
begin
    have : is_linear_map R _ := is_linear_map.is_linear_map_smul' b,
    set f : R →ₗ[R] R := is_linear_map.mk' _ this,
    have f_surj : function.surjective f := λ x, ⟨x * a, by simp [mul_assoc, h]⟩,
    have f_inj := noeth_mod_surj_inj f_surj,
    exact sub_eq_zero.mp (f_inj (
        calc f (b * a - 1) = (b * a - 1) * b : by simp only [is_linear_map.mk'_apply, smul_eq_mul, sub_eq_add_neg]
                       ... = b * a * b - b   : by rw [sub_mul, one_mul]
                       ... = 0               : by rw [mul_assoc, h, mul_one, sub_self]
                       ... = f 0             : by simp only [zero_mul, is_linear_map.mk'_apply, smul_eq_mul])),
    /-
    have := well_founded_submodule_gt R R,
    rw order_embedding.well_founded_iff_no_descending_seq at this,
    set ordf : ℕ → submodule R R := λ n, linear_map.ker (iterate f n),

    suffices : ∃ n, ordf n = ordf (n + 1),
    begin
        obtain ⟨n, hn⟩ := this,
        have pow_surj := iterate_surj f_surj n,
        obtain ⟨c, hc⟩ := pow_surj (b * a - 1),
        have :=
        calc iterate f (n + 1) c = f (b * a - 1)   : by rw [iterate_succ', comp_apply, hc]
                            ...  = (b * a - 1) * b : by simp [f]
                            ...  = 0               : by rw [sub_mul, one_mul, mul_assoc, h, mul_one, sub_self],
        rw ← linear_map.mem_ker at this,
        dsimp only [ordf] at hn,
        rw ← hn at this,
        rw linear_map.mem_ker at this,
        rw this at hc,
        exact sub_eq_zero.mp (eq.symm hc),
    end,

    by_contradiction ho,
    apply this,
    push_neg at ho,
    have : ∀ n, ordf n ≤ ordf (n + 1) := λ n x hx, begin simp [ordf, iterate_succ'] at hx ⊢, rw [hx, zero_mul], end,
    have : ∀ n, ordf (n + 1) > ordf n := λ n, lt_of_le_of_ne (this n) (ho n),
    have := order_embedding.nat_gt _ this,
    exact nonempty.intro this,-/
end⟩

@[priority 100]
instance is_dedekind_finite_ring_of_finite [fintype R] : is_dedekind_finite_ring R := begin
    --TODO why is this needed?
    haveI inst : is_noetherian R R := ring.is_noetherian_of_fintype R R,
    haveI := is_noetherian_ring_iff.mpr inst,
    exactI dedekind_finite.is_dedekind_finite_ring_of_noetherian R,
end
end

section

private lemma aux1 {i j : ℕ} : j - i = j + 1 - (i + 1) := by omega

variable {R : Type*}

lemma mul_eq_one_pow_mul_pow_eq [ring R] {a b : R} (hab : a * b = 1) : ∀ (i j : ℕ), a^i * b^j = if i ≤ j then b^(j - i) else a^(i - j)
| 0       0       := by simp
| (i + 1) 0       := by simp only [mul_one, nat.zero_sub, nat.le_zero_iff,
                        add_eq_zero_iff, if_false, nat.sub_zero, one_ne_zero,
                        pow_zero, and_false]
| 0       (j + 1) := by simp only [one_mul, if_true, nat.zero_sub, zero_le,
                        nat.sub_zero, pow_zero]
| (i + 1) (j + 1) := begin
        rw pow_succ', rw pow_succ, assoc_rw hab,
        rw mul_one, rw mul_eq_one_pow_mul_pow_eq i j,
        apply' if_congr (iff.symm nat.lt_succ_iff),
        apply' congr_arg ((^) b),
        exact aux1,
        apply' congr_arg ((^) a),
        exact aux1,
    end

private lemma aux3 {j k : ℕ}
  (H : k < j) (hjk : ¬j = k + 1) : ¬j ≤ k + 1 :=
by omega

private lemma aux4 {j k l : ℕ}
  (H : k < j)  :
 j - (k + 1) + (l + 1) = j - k + l :=
 by omega

private lemma aux5 {j k l : ℕ}
  (H : k < j)  :
  j + 1 - (k + 1) + (l + 1) = j + 1 - k + l :=
 by omega

private def e (a b : R) [ring R] (i j : ℕ) : R := b^i * a^j - b^(i + 1) * a^(j + 1)

lemma e_orthogonal [ring R] {a b : R} (hab : a * b = 1) :
∀ {i j k l : ℕ},
(e a b i j) * (e a b k l) = if j = k then e a b i l else (0 : R) :=
begin
    intros,
    rw [e,e,e], rw [mul_sub, sub_mul, sub_mul], rw sub_right_comm,
    rw mul_assoc, rw mul_assoc, rw mul_assoc, rw mul_assoc,
    rw ← sub_add, rw ← mul_sub (b ^ i), rw ← sub_sub_assoc_swap,
    rw ← mul_sub (b ^ (i + 1)), rw ← mul_assoc, rw ← mul_assoc, rw ← mul_assoc,
    rw ← mul_assoc,
    rw mul_eq_one_pow_mul_pow_eq hab j k,
    rw mul_eq_one_pow_mul_pow_eq hab j (k + 1),
    rw mul_eq_one_pow_mul_pow_eq hab (j + 1) k,
    rw mul_eq_one_pow_mul_pow_eq hab (j + 1) (k + 1),
    rcases lt_trichotomy j k with H | rfl | H,
    {
        conv_rhs {rw if_neg (ne_of_lt H),},

        -- TODO omega gets stuck on instances
        rw if_pos (le_of_lt H),
        rw if_pos,
        rw if_pos,
        swap, exact H,
        rw if_pos,
        swap, exact le_add_right H,
        rw ← nat.succ_pred_eq_of_pos (nat.lt_sub_left_of_add_lt H : k - j > 0),
        rw ← nat.succ_pred_eq_of_pos (_ : k + 1 - j > 0),
        rw pow_succ, rw pow_succ, rw mul_assoc, rw mul_assoc,
        rw ← mul_sub b, rw ← mul_assoc, rw ← pow_succ',
        rw ← mul_sub (b ^ (i + 1)),
        convert mul_zero _,
        rw nat.pred_eq_sub_one, rw nat.pred_eq_sub_one,
        rw sub_sub_assoc_swap, rw (nat.succ_sub_succ k j : k + 1 - j - 1 = k - j),
        rw (_ : k + 1 - j - 1 = k - j),
        swap,
        exact nat.succ_sub_succ k j,
        rw nat.sub_sub, rw add_comm j 1,
        rw ← nat.sub_sub,
        abel,
        any_goals {linarith,},
        {apply nat.sub_pos_of_lt,
        transitivity k,
        exact H,
        exact lt_add_one k,},
    },
    {
        conv_rhs {rw if_pos,},

        rw if_pos (le_refl j), rw if_pos (nat.le_succ j),
        rw if_neg,
        swap,
        exact nat.lt_irrefl j,
        rw if_pos (le_refl (j + 1)),

        rw nat.sub_self, rw pow_zero, rw one_mul,
        rw (nat.sub_eq_of_eq_add rfl : j + 1 - j = 1),
        rw ← pow_add, rw pow_one, rw nat.sub_self, rw pow_zero,
        rw one_mul, rw add_comm,
        rw sub_self, rw mul_zero, rw sub_zero, rw mul_sub,
        rw ← mul_assoc, rw ← pow_succ',
    },
    {
        conv_rhs {rw if_neg (ne_of_gt H),},

        rw if_neg (not_le.mpr H),
        have : ite (j ≤ k + 1) (b ^ (k + 1 - j)) (a ^ (j - (k + 1))) = a ^ (j - (k + 1)) :=
        begin
            by_cases hjk : j = k + 1,
            {
                rw if_pos (le_of_eq hjk), rw [← hjk],
                rw nat.sub_self, refl,
            },
            {
                rw if_neg, exact aux3 H hjk,
            }
        end,
        rw this, rw if_neg,
        swap,
        exact (nat.lt_asymm H),
        rw if_neg,
        swap,
        exact nat.le_lt_antisymm H,
        rw ← pow_add, rw ← pow_add, rw ← pow_add, rw ← pow_add,
        rw (aux4 H : j - (k + 1) + (l + 1) = j - k + l),
        rw sub_self, rw mul_zero, rw zero_sub,
        rw (aux5 H : j + 1 - (k + 1) + (l + 1) = j + 1 - k + l),
        rw sub_self, rw mul_zero, rw neg_zero,
    }
end

lemma e_ne_pow_two [ring R] {a b : R} (hab : a * b = 1) {i j : ℕ} (hij : i ≠ j) : (e a b i j) ^ 2 = (0 : R) :=
begin
    rw [pow_two],
    rw e_orthogonal hab,
    rw if_neg (ne.symm hij),
end

open_locale classical

@[priority 100]
instance is_dedekind_finite_ring_of_fin_nilpotents (R : Type*) [ring R] (h : (nilpotents R).finite) : is_dedekind_finite_ring R :=
⟨begin
    tactic.unfreeze_local_instances,
    contrapose! h,
    rcases h with ⟨a, b, hab, hba⟩,
    haveI : infinite (nilpotents R) :=
    begin
        let e1 : ℕ → nilpotents R := (λ n, ⟨e a b 0 (n + 1), 2, e_ne_pow_two hab (ne.symm (nat.succ_ne_zero n)) ⟩),
        refine infinite.of_injective e1 _,
        intros n m hnm,
        by_contradiction h,
        simp [e1] at hnm,
        have :=
        calc 1 - b * a = e a b 0 0                         : by simp [e]
                  ...  = e a b 0 (n + 1) * e a b (n + 1) 0 : by rw [e_orthogonal hab, if_pos (rfl)]
                  ...  = e a b 0 (m + 1) * e a b (n + 1) 0 : by rw hnm
                  ...  = 0                                 : by { rw [e_orthogonal hab, if_neg], intro a_2, exact h ((add_left_inj 1).mp (eq.symm a_2)) },
        rw sub_eq_zero at this,
        exact absurd (eq.symm this) hba,
    end,

    intro hinf,
    exact infinite.not_fintype (set.finite.fintype hinf),
end⟩

end
end dedekind_finite
section
variables  {R : Type*} [comm_ring R] [nontrivial R] {M : Type*} [add_comm_group M] [module R M] (f : M →ₗ[R] M)

noncomputable theory



-- if I dont have this some nat decidable instances crop up later and make some "same" finsets different
local attribute [instance, priority 1000] classical.prop_decidable


set_option pp.all false
instance module_polynomial_ring_endo : module (polynomial R) M := { smul := λ r m, r.support.sum (λ i, r.coeff i • (f ^ i) m),
  one_smul := λ b, begin
    simp only [polynomial.coeff_one],
    have : (1 : polynomial R).support = {0} := finsupp.support_single_ne_zero (zero_ne_one.symm),
    simp only [this, finset.sum_singleton, eq_self_iff_true, if_true, pow_zero,
        linear_map.one_apply, one_smul],
    end,
  mul_smul := λ x y b, begin simp, sorry, end,
  smul_add := λ x m n, begin
    simp only [linear_map.one_apply, if_true, eq_self_iff_true, one_smul, linear_map.pow_apply,
      finset.sum_singleton, zero_ne_one, pow_zero],
    rw ←finset.sum_add_distrib,
    congr,
    funext i,
    rw [←linear_map.coe_pow, linear_map.map_add, smul_add]
  end,
  smul_zero := λ r, begin
    simp only [linear_map.one_apply, if_true, eq_self_iff_true, one_smul, linear_map.pow_apply,
        finset.sum_singleton, zero_ne_one, pow_zero],
    apply finset.sum_eq_zero,
    intros x hx,
    rw [←linear_map.coe_pow, linear_map.map_zero, smul_zero]
  end,
  add_smul := λ x y m, begin
    simp only [smul_add, linear_map.map_zero, linear_map.one_apply, if_true, polynomial.coeff_add,
      eq_self_iff_true, one_smul, linear_map.pow_apply, finset.sum_singleton, zero_ne_one,
      linear_map.map_add, smul_zero, pow_zero],
    have := @finset.sum_subset _ _ (x + y).support (x.support ∪ y.support) _ _ finsupp.support_add _,
    rw this,
    conv_lhs{congr,skip, funext,
    rw add_smul,},
    rw finset.sum_add_distrib,
    rw finset.sum_subset (finset.subset_union_left x.support y.support),
    rw finset.sum_subset (finset.subset_union_right x.support y.support),

    rintros x_1 - a,
    have : polynomial.coeff y x_1 = 0 := finsupp.not_mem_support_iff.mp a,
    rw this,
    rw zero_smul,

    rintros x_1 - a,
    have : polynomial.coeff x x_1 = 0 := finsupp.not_mem_support_iff.mp a,
    rw this,
    rw zero_smul,

    rintros x_1 - a,
    rw ← polynomial.coeff_add,
    have : polynomial.coeff (x + y) x_1 = 0 := finsupp.not_mem_support_iff.mp a,
    rw this,
    rw zero_smul,
   end,
  zero_smul := λ m, begin simp, end }



theorem fg_comm_mod_surj_inj (hfg : (⊤ : submodule R M).fg) (f_surj : function.surjective f)
: function.injective f :=
begin
    letI := module_polynomial_ring_endo f,
    let I : ideal (polynomial R) := ideal.span {polynomial.X},
    have supp_X : (polynomial.X : polynomial R).support ⊆ {1} := finsupp.support_single_subset,
    have X_mul : ∀ o, (polynomial.X : polynomial R) • o = f o := begin
        intro,
        simp only [(•)],
        rw finset.sum_subset supp_X,
        {simp only [polynomial.coeff_X_one, one_smul, finset.sum_singleton, pow_one]},
        rintros x - a,
        have : polynomial.coeff (polynomial.X : polynomial R) x = 0 := finsupp.not_mem_support_iff.mp a,
        rw this,
        rw zero_smul,
    end,
    have : (⊤ : submodule (polynomial R) M) ≤ I • (⊤ : submodule (polynomial R) M) := begin
        intros a ha,
        obtain ⟨y, rfl⟩ := f_surj a,
        simp only [(X_mul y).symm, submodule.mem_coe],
        have xmem : polynomial.X ∈ I := ideal.mem_span_singleton.mpr (dvd_refl _),
        exact submodule.smul_mem_smul xmem trivial,
    end,
    have hfgpoly : (⊤ : submodule (polynomial R) M).fg :=
    begin
        obtain ⟨S, hS⟩ := hfg,
        refine submodule.fg_def.mpr _,
        use ↑ S,
        split,
        exact finset.finite_to_set S,
        rw submodule.span_eq_of_le,
        {simp},
        intros a ha,
        have : a ∈ submodule.span R ↑S := set.mem_of_eq_of_mem hS trivial,
        rw submodule.mem_span at *,
        intros p hp,
        --have := this (begin suggest, end),
sorry

    end,
    obtain ⟨F, ⟨hFa,hFb⟩⟩ := submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (⊤ : submodule (polynomial R) M) hfgpoly this,
    rw  ← linear_map.ker_eq_bot,
    rw linear_map.ker_eq_bot',
    intros m hm,
    have Fmzero := hFb m (by simp),
    have : F = F - 1 + 1 := by simp only [neg_add_cancel_right, sub_eq_add_neg],
    rw this at Fmzero,
    rw add_smul at Fmzero,
    simp only [add_comm, one_smul] at Fmzero,
    suffices : (F - 1) • m = 0,
        by rwa [this, add_zero] at Fmzero,
    simp only [I] at hFa,
    rw ideal.mem_span_singleton' at hFa,
    obtain ⟨G, hG⟩ := hFa,
    rw ← hG,
    rw mul_smul,

    rw X_mul m,
    rw hm,
    rw smul_zero,
end

#lint
end
