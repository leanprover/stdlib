import ring_theory.algebra_operations
import ring_theory.localization

open localization

set_option class.instance_max_depth 75

universes u v w

namespace ring

section defs

variables (R : Type u) [integral_domain R] (S : set R) [is_submonoid S]

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def is_fractional (I : submodule R (localization R S)) :=
∃ a ≠ (0 : R), ∀ b ∈ I, is_integer R S (a • b)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `R'` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ R'` is an `R`-submodule of `R'`,
  such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def fractional_ideal := { I : submodule R (localization R S) // is_fractional R S I }

end defs

namespace fractional_ideal

open set
open submodule

variables {R : Type u} [integral_domain R] {S : set R} [is_submonoid S]

instance : has_mem (localization R S) (fractional_ideal R S) := ⟨λ x I, x ∈ I.1⟩

/-- Fractional ideals are equal if their submodules are equal.

  Combined with `submodule.ext` this gives that fractional ideals are equal if
  they have the same elements.
-/
@[ext]
lemma ext {I J : fractional_ideal R S} : I.1 = J.1 → I = J :=
subtype.ext.mpr

lemma fractional_of_subset_one (I : submodule R (localization R S)) (h : I ≤ 1) :
  is_fractional R S I :=
begin
  use 1,
  use one_ne_zero,
  intros b hb,
  obtain ⟨b', b'_mem, b'_eq_b⟩ := h hb,
  convert is_integer_coe R b',
  simp [b'_eq_b.symm]
end

instance coe_to_fractional_ideal : has_coe (ideal R) (fractional_ideal R S) :=
⟨ λ I, ⟨ ↑I, fractional_of_subset_one _ (image_subset _ (subset_univ _)) ⟩ ⟩

instance : has_zero (fractional_ideal R S) := ⟨(0 : ideal R)⟩

@[simp]
lemma mem_zero_iff {x : localization R S} : x ∈ (0 : fractional_ideal R S) ↔ x = 0 :=
⟨ (λ ⟨x', x'_mem_zero, x'_eq_x⟩,
    have x'_eq_zero : x' = 0 := (or_false _).mp x'_mem_zero,
    by simp [x'_eq_x.symm, x'_eq_zero]),
  (λ hx, ⟨0, or.inl rfl, by simp [hx]⟩) ⟩

@[simp] lemma val_zero : (0 : fractional_ideal R S).1 = 0 :=
begin
  ext,
  split; intro h; convert submodule.zero _,
  { rw [mem_zero_iff.mp h] },
  { exact (or_false _).mp h }
end

lemma nonzero_iff_val_nonzero {I : fractional_ideal R S} : I.1 ≠ 0 ↔ I ≠ 0 :=
⟨ λ h h', h (by simp [h']),
  λ h h', h (ext (by simp [h'])) ⟩

instance : inhabited (fractional_ideal R S) := ⟨0⟩

instance : has_one (fractional_ideal R S) :=
⟨(1 : ideal R)⟩

lemma mem_one_iff {x : localization R S} : x ∈ (1 : fractional_ideal R S) ↔ ∃ x' : R, ↑x' = x :=
iff.intro (λ ⟨x', _, h⟩, ⟨x', h⟩) (λ ⟨x', h⟩, ⟨x', ⟨x', set.mem_univ _, rfl⟩, h⟩)

lemma coe_mem_one (x : R) : (x : localization R S) ∈ (1 : fractional_ideal R S) :=
mem_one_iff.mpr ⟨x, rfl⟩

section lattice

/-! ### `lattice` section

  Defines the order on fractional ideals as inclusion of their underlying sets,
  and the lattice structure.
-/

open lattice

instance : partial_order (fractional_ideal R S) :=
{ le := λ I J, I.1 ≤ J.1,
  le_refl := λ I, le_refl I.1,
  le_antisymm := λ ⟨I, hI⟩ ⟨J, hJ⟩ hIJ hJI, by { congr, exact le_antisymm hIJ hJI },
  le_trans := λ _ _ _ hIJ hJK, le_trans hIJ hJK }

lemma le_iff {I J : fractional_ideal R S} : I ≤ J ↔ (∀ x ∈ I, x ∈ J) := iff.refl _

lemma zero_le (I : fractional_ideal R S) : 0 ≤ I :=
begin
  intros x hx,
  convert submodule.zero _,
  simpa using hx
end

instance order_bot : order_bot (fractional_ideal R S) :=
{ bot := 0,
  bot_le := zero_le,
  ..fractional_ideal.partial_order }

@[simp] lemma bot_eq_zero : (⊥ : fractional_ideal R S) = 0 :=
rfl

lemma eq_zero_iff {I : fractional_ideal R S} : I = 0 ↔ (∀ x ∈ I, x = (0 : localization R S)) :=
⟨ (λ h x hx, by simpa [h, mem_zero_iff] using hx),
  (λ h, le_bot_iff.mp (λ x hx, mem_zero_iff.mpr (h x hx))) ⟩

lemma fractional_sup (I J : fractional_ideal R S) : is_fractional R S (I.1 ⊔ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  rcases J.2 with ⟨aJ, haJ, hJ⟩,
  use aI * aJ,
  use mul_ne_zero haI haJ,
  intros b hb,
  rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, hbIJ⟩,
  rw [←hbIJ, smul_add],
  apply is_integer_add,
  { rw [mul_comm, mul_smul],
    apply is_integer_smul _ (hI bI hbI) },
  { rw [mul_smul],
    apply is_integer_smul _ (hJ bJ hbJ) }
end

lemma fractional_inf (I J : fractional_ideal R S) : is_fractional R S (I.1 ⊓ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  use aI,
  use haI,
  intros b hb,
  rcases mem_inf.mp hb with ⟨hbI, hbJ⟩,
  exact (hI b hbI)
end

instance lattice : lattice (fractional_ideal R S) :=
{ inf := λ I J, ⟨I.1 ⊓ J.1, fractional_inf I J⟩,
  sup := λ I J, ⟨I.1 ⊔ J.1, fractional_sup I J⟩,
  inf_le_left := λ I J, show I.1 ⊓ J.1 ≤ I.1, from inf_le_left,
  inf_le_right := λ I J, show I.1 ⊓ J.1 ≤ J.1, from inf_le_right,
  le_inf := λ I J K hIJ hIK, show I.1 ≤ (J.1 ⊓ K.1), from le_inf hIJ hIK,
  le_sup_left := λ I J, show I.1 ≤ I.1 ⊔ J.1, from le_sup_left,
  le_sup_right := λ I J, show J.1 ≤ I.1 ⊔ J.1, from le_sup_right,
  sup_le := λ I J K hIK hJK, show (I.1 ⊔ J.1) ≤ K.1, from sup_le hIK hJK,
  ..fractional_ideal.partial_order }

instance : semilattice_sup_bot (fractional_ideal R S) :=
{ ..fractional_ideal.order_bot, ..fractional_ideal.lattice }

end lattice

section semiring

instance : has_add (fractional_ideal R S) := ⟨(⊔)⟩

@[simp]
lemma sup_eq_add (I J : fractional_ideal R S) : I ⊔ J = I + J := rfl

@[simp]
lemma val_add (I J : fractional_ideal R S) : (I + J).1 = I.1 + J.1 := rfl

instance : has_mul (fractional_ideal R S) :=
⟨ λ I J, ⟨
  I.1 * J.1,
  begin
    rcases I with ⟨I, aI, haI, hI⟩,
    rcases J with ⟨I, aJ, haJ, hJ⟩,
    use aI * aJ,
    use mul_ne_zero haI haJ,
    intros b hb,
    apply submodule.mul_induction_on hb,
    { intros m hm n hn,
      obtain ⟨n', hn', n'_eq⟩ := hJ n hn,
      rw [mul_smul, ←algebra.mul_smul_comm, ←n'_eq, mul_comm],
      apply hI,
      exact submodule.smul _ _ hm },
    { rw [smul_zero],
      apply is_integer_coe },
    { intros x y hx hy,
      rw [smul_add],
      apply is_integer_add _ hx hy },
    { intros r x hx,
      rw [←mul_smul, mul_comm, mul_smul],
      apply is_integer_smul _ hx },
  end ⟩ ⟩

@[simp]
lemma val_mul (I J : fractional_ideal R S) : (I * J).1 = I.1 * J.1 := rfl

lemma mul_left_mono (I : fractional_ideal R S) : monotone ((*) I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul hx (h hy))

lemma mul_right_mono (I : fractional_ideal R S) : monotone (λ J, J * I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul (h hx) hy)

instance add_comm_monoid : add_comm_monoid (fractional_ideal R S) :=
{ add_assoc := λ I J K, lattice.sup_assoc,
  add_comm := λ I J, lattice.sup_comm,
  add_zero := λ I, lattice.sup_bot_eq,
  zero_add := λ I, lattice.bot_sup_eq,
  ..fractional_ideal.has_zero,
  ..fractional_ideal.has_add }

instance comm_monoid : comm_monoid (fractional_ideal R S) :=
{ mul_assoc := λ I J K, ext (submodule.mul_assoc _ _ _),
  mul_comm := λ I J, ext (mul_comm _ _),
  mul_one := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x hx y ⟨y', y'_mem_R, y'_eq_y⟩,
      erw [←y'_eq_y, mul_comm, coe_mul_eq_smul],
      exact submodule.smul _ _ hx },
    { have : x * 1 ∈ (I * 1) := mul_mem_mul h (coe_mem_one _),
      simpa }
  end,
  one_mul := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x ⟨x', x'_mem_R, x'_eq_x⟩ y hy,
      erw [←x'_eq_x, coe_mul_eq_smul],
      exact submodule.smul _ _ hy },
    { have : 1 * x ∈ (1 * I) := mul_mem_mul (coe_mem_one _) h,
      simpa }
  end,
  ..fractional_ideal.has_mul,
  ..fractional_ideal.has_one }

instance comm_semiring : comm_semiring (fractional_ideal R S) :=
{ mul_zero := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hy])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  zero_mul := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hx])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  left_distrib := λ I J K, ext (mul_add _ _ _),
  right_distrib := λ I J K, ext (add_mul _ _ _),
  ..fractional_ideal.add_comm_monoid,
  ..fractional_ideal.comm_monoid }
end semiring

section
variables {M : Type v} [ring M] [algebra R M]

/-- The elements of `I / J` are the `x` such that `x J ⊆ I`.

  This is the general form of the ideal quotient, traditionally written $I : J$.
-/
instance : has_div (submodule R M) :=
⟨ λ I J, {
  carrier := { x | ∀ y ∈ J, x * y ∈ I },
  zero := λ y hy, by { rw zero_mul, apply submodule.zero },
  add := λ a b ha hb y hy, by { rw add_mul, exact submodule.add _ (ha _ hy) (hb _ hy) },
  smul := λ r x hx y hy, by { rw algebra.smul_mul_assoc, exact submodule.smul _ _ (hx _ hy) } } ⟩

lemma mem_div_iff {x : M} {I J : submodule R M} : x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I := iff.refl _

lemma le_div_iff {I J K : submodule R M} : I ≤ J / K ↔ ∀ (x ∈ I) (z ∈ K), x * z ∈ J := iff.refl _

end

section quotient
open_locale classical

instance : zero_ne_one_class (fractional_ideal R (non_zero_divisors R)) :=
{ zero_ne_one := λ h,
  have this : (1 : localization _ _) ∈ (0 : fractional_ideal R (non_zero_divisors R)) :=
    by convert coe_mem_one _,
  one_ne_zero (mem_zero_iff.mp this),
  ..fractional_ideal.has_one,
  ..fractional_ideal.has_zero }

lemma fractional_div_of_nonzero {I J : fractional_ideal R (non_zero_divisors R)} (h : J ≠ 0) :
  is_fractional R (non_zero_divisors R) (I.1 / J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨J, aJ, haJ, hJ⟩,
  obtain ⟨y, mem_J, not_mem_zero⟩ := exists_of_lt (lattice.bot_lt_iff_ne_bot.mpr h),
  obtain ⟨y', _, hy'⟩ := hJ y mem_J,
  use (aI * y'),
  split,
  { apply mul_ne_zero haI,
    intro y'_eq_zero,
    have : ↑aJ * y = 0 := by rw [coe_mul_eq_smul, ←hy', y'_eq_zero, localization.coe_zero],
    obtain aJ_zero | y_zero := mul_eq_zero.mp this,
    { have : aJ = 0 := fraction_ring.of.injective (trans aJ_zero (of_zero _ _).symm),
      contradiction },
    { exact not_mem_zero (mem_zero_iff.mpr y_zero) } },
  intros b hb,
  rw [mul_smul],
  convert hI _ (hb _ (submodule.smul_mem _ aJ mem_J)),
  rw [←hy', mul_coe_eq_smul]
end 

noncomputable instance fractional_ideal_has_div :
  has_div (fractional_ideal R (non_zero_divisors R)) :=
⟨ λ I J, if h : J = 0 then 0 else ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ ⟩

@[simp]
lemma div_nonzero {I J : fractional_ideal R (non_zero_divisors R)} (h : J ≠ 0) :
  (I / J) = ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ :=
dif_neg h

lemma div_one {I : fractional_ideal R (non_zero_divisors R)} : I / 1 = I :=
begin
  rw [div_nonzero (@one_ne_zero (fractional_ideal R _) _)],
  ext,
  split; intro h,
  { convert mem_div_iff.mp h 1 (coe_mem_one 1), simp },
  { apply mem_div_iff.mpr,
    rintros y ⟨y', _, y_eq_y'⟩,
    rw [mul_comm],
    convert submodule.smul _ y' h,
    simp [y_eq_y'.symm] }
end

lemma unique_right_inverse {α} [comm_monoid α] {i j j' : α} :
  i * j = 1 → i * j' = 1 → j = j' :=
λ h h', congr_arg units.inv $
  @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl

theorem right_inverse_eq (I J : fractional_ideal R (non_zero_divisors R)) (h : I * J = 1) :
  J = (1 / I) :=
begin
  have hI : I ≠ 0,
  { intro hI,
    apply @zero_ne_one (fractional_ideal R (non_zero_divisors R)),
    convert h,
    simp [hI] },
  apply unique_right_inverse h,
  rw [div_nonzero hI],
  apply le_antisymm,
  { apply submodule.mul_le.mpr _,
    intros x hx y hy,
    rw [mul_comm],
    exact mem_div_iff.mpr hy x hx },
  rw [←h],
  apply mul_left_mono I,
  apply le_div_iff.mpr _,
  intros y hy x hx,
  rw [mul_comm],
  exact submodule.mul_mem_mul hx hy
end

end quotient

end fractional_ideal

end ring

#lint
