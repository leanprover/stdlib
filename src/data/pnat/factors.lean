/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import data.pnat.prime
import data.multiset.sort
import data.int.gcd
import algebra.group

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `prime_multiset`: Type of multisets of prime numbers.
* `factor_multiset n`: Multiset of prime factors of `n`.
-/

/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/
def prime_multiset := multiset nat.primes

namespace prime_multiset

instance : inhabited prime_multiset :=
by unfold prime_multiset; apply_instance

instance : has_repr prime_multiset :=
by { dsimp [prime_multiset], apply_instance }

instance : canonically_ordered_add_monoid prime_multiset :=
by { dsimp [prime_multiset], apply_instance }

instance : distrib_lattice prime_multiset :=
by { dsimp [prime_multiset], apply_instance }

instance : semilattice_sup_bot prime_multiset :=
by { dsimp [prime_multiset], apply_instance }

instance : has_sub prime_multiset :=
by { dsimp [prime_multiset], apply_instance }

theorem add_sub_of_le {u v : prime_multiset} : u ≤ v → u + (v - u) = v :=
multiset.add_sub_of_le

/-- The multiset consisting of a single prime -/
def of_prime (p : nat.primes) : prime_multiset := (p ::ₘ 0)

theorem card_of_prime (p : nat.primes) : multiset.card (of_prime p) = 1 := rfl

/-- We can forget the primality property and regard a multiset
 of primes as just a multiset of positive integers, or a multiset
 of natural numbers.  In the opposite direction, if we have a
 multiset of positive integers or natural numbers, together with
 a proof that all the elements are prime, then we can regard it
 as a multiset of primes.  The next block of results records
 obvious properties of these coercions.
-/
def to_nat_multiset : prime_multiset → multiset ℕ :=
λ v, v.map (λ p, (p : ℕ))

instance coe_nat : has_coe prime_multiset (multiset ℕ) := ⟨to_nat_multiset⟩

instance coe_nat_hom : is_add_monoid_hom (coe : prime_multiset → multiset ℕ) :=
by { unfold_coes, dsimp [to_nat_multiset], apply_instance }

theorem coe_nat_injective : function.injective (coe : prime_multiset → multiset ℕ) :=
multiset.map_injective nat.primes.coe_nat_inj

theorem coe_nat_of_prime (p : nat.primes) :
((of_prime p) : multiset ℕ) = (p : ℕ) ::ₘ 0 := rfl

theorem coe_nat_prime (v : prime_multiset)
(p : ℕ) (h : p ∈ (v : multiset ℕ)) : p.prime :=
by { rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩,
     exact h_eq ▸ hp' }

/-- Converts a `prime_multiset` to a `multiset ℕ+`. -/
def to_pnat_multiset : prime_multiset → multiset ℕ+ :=
λ v, v.map (λ p, (p : ℕ+))

instance coe_pnat : has_coe prime_multiset (multiset ℕ+) := ⟨to_pnat_multiset⟩

instance coe_pnat_hom : is_add_monoid_hom (coe : prime_multiset → multiset ℕ+) :=
by { unfold_coes, dsimp [to_pnat_multiset], apply_instance }

theorem coe_pnat_injective : function.injective (coe : prime_multiset → multiset ℕ+) :=
multiset.map_injective nat.primes.coe_pnat_inj

theorem coe_pnat_of_prime (p : nat.primes) :
((of_prime p) : multiset ℕ+) = (p : ℕ+) ::ₘ 0 := rfl

theorem coe_pnat_prime (v : prime_multiset)
  (p : ℕ+) (h : p ∈ (v : multiset ℕ+)) : p.prime :=
by { rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩,
     exact h_eq ▸ hp' }

instance coe_multiset_pnat_nat : has_coe (multiset ℕ+) (multiset ℕ) :=
⟨λ v, v.map (λ n, (n : ℕ))⟩

theorem coe_pnat_nat (v : prime_multiset) :
  ((v : (multiset ℕ+)) : (multiset ℕ)) = (v : multiset ℕ) :=
by { change (v.map (coe : nat.primes → ℕ+)).map subtype.val = v.map subtype.val,
     rw [multiset.map_map], congr }

/-- The product of a `prime_multiset`, as a `ℕ+`. -/
def prod (v : prime_multiset) : ℕ+ := (v : multiset pnat).prod

theorem coe_prod (v : prime_multiset) : (v.prod : ℕ) = (v : multiset ℕ).prod :=
begin
  let h : (v.prod : ℕ) = ((v.map coe).map coe).prod :=
    ((monoid_hom.of coe).map_multiset_prod v.to_pnat_multiset),
  rw [multiset.map_map] at h,
  have : (coe : ℕ+ → ℕ) ∘ (coe : nat.primes → ℕ+) = coe := funext (λ p, rfl),
  rw[this] at h, exact h,
end

theorem prod_of_prime (p : nat.primes) : (of_prime p).prod = (p : ℕ+) :=
by { change multiset.prod ((p : ℕ+) ::ₘ 0) = (p : ℕ+),
     rw [multiset.prod_cons, multiset.prod_zero, mul_one] }

/-- If a `multiset ℕ` consists only of primes, it can be recast as a `prime_multiset`. -/
def of_nat_multiset
  (v : multiset ℕ) (h : ∀ (p : ℕ), p ∈ v → p.prime) : prime_multiset :=
@multiset.pmap ℕ nat.primes nat.prime (λ p hp, ⟨p, hp⟩) v h

theorem to_of_nat_multiset (v : multiset ℕ) (h) :
  ((of_nat_multiset v h) : multiset ℕ) = v :=
begin
  unfold_coes,
  dsimp [of_nat_multiset, to_nat_multiset],
  have : (λ (p : ℕ) (h : p.prime), ((⟨p, h⟩ : nat.primes) : ℕ)) = (λ p h, id p) :=
    by {funext p h, refl},
  rw [multiset.map_pmap, this, multiset.pmap_eq_map, multiset.map_id]
end

theorem prod_of_nat_multiset (v : multiset ℕ) (h) :
  ((of_nat_multiset v h).prod : ℕ) = (v.prod : ℕ) :=
by rw[coe_prod, to_of_nat_multiset]

/-- If a `multiset ℕ+` consists only of primes, it can be recast as a `prime_multiset`. -/
def of_pnat_multiset
  (v : multiset ℕ+) (h : ∀ (p : ℕ+), p ∈ v → p.prime) : prime_multiset :=
@multiset.pmap ℕ+ nat.primes pnat.prime (λ p hp, ⟨(p : ℕ), hp⟩) v h

theorem to_of_pnat_multiset (v : multiset ℕ+) (h) :
 ((of_pnat_multiset v h) : multiset ℕ+) = v :=
begin
  unfold_coes, dsimp[of_pnat_multiset, to_pnat_multiset],
  have : (λ (p : ℕ+) (h : p.prime), ((coe : nat.primes → ℕ+) ⟨p, h⟩)) = (λ p h, id p) :=
    by {funext p h, apply subtype.eq, refl},
  rw[multiset.map_pmap, this, multiset.pmap_eq_map, multiset.map_id]
end

theorem prod_of_pnat_multiset (v : multiset ℕ+) (h) :
 ((of_pnat_multiset v h).prod : ℕ+) = v.prod :=
by { dsimp [prod], rw [to_of_pnat_multiset] }

/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
def of_nat_list (l : list ℕ) (h : ∀ (p : ℕ), p ∈ l → p.prime) : prime_multiset :=
of_nat_multiset (l : multiset ℕ) h

theorem prod_of_nat_list (l : list ℕ) (h) : ((of_nat_list l h).prod : ℕ) = l.prod :=
by { have := prod_of_nat_multiset (l : multiset ℕ) h,
     rw [multiset.coe_prod] at this, exact this }

/-- If a `list ℕ+` consists only of primes, it can be recast as a `prime_multiset` with
the coercion from lists to multisets. -/
def of_pnat_list (l : list ℕ+) (h : ∀ (p : ℕ+), p ∈ l → p.prime) : prime_multiset :=
of_pnat_multiset (l : multiset ℕ+) h

theorem prod_of_pnat_list (l : list ℕ+) (h) : (of_pnat_list l h).prod = l.prod :=
by { have := prod_of_pnat_multiset (l : multiset ℕ+) h,
     rw [multiset.coe_prod] at this, exact this }

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
theorem prod_zero : (0 : prime_multiset).prod = 1 :=
by { dsimp [prod], exact multiset.prod_zero }

theorem prod_add (u v : prime_multiset) : (u + v).prod = u.prod * v.prod :=
by { dsimp [prod],
     rw [is_add_monoid_hom.map_add (coe : prime_multiset → multiset ℕ+)],
     rw [multiset.prod_add] }

theorem prod_smul (d : ℕ) (u : prime_multiset) :
 (d • u).prod = u.prod ^ d :=
by { induction d with d ih, refl,
     rw [succ_nsmul, prod_add, ih, nat.succ_eq_add_one, pow_succ, mul_comm] }

end prime_multiset

namespace pnat

/-- The prime factors of n, regarded as a multiset -/
def factor_multiset (n : ℕ+) : prime_multiset :=
prime_multiset.of_nat_list (nat.factors n) (@nat.prime_of_mem_factors n)

/-- The product of the factors is the original number -/
theorem prod_factor_multiset (n : ℕ+) : (factor_multiset n).prod = n :=
eq $ by { dsimp [factor_multiset],
          rw [prime_multiset.prod_of_nat_list],
          exact nat.prod_factors n.pos }

theorem coe_nat_factor_multiset (n : ℕ+) :
  ((factor_multiset n) : (multiset ℕ)) = ((nat.factors n) : multiset ℕ) :=
prime_multiset.to_of_nat_multiset (nat.factors n) (@nat.prime_of_mem_factors n)

end pnat

namespace prime_multiset

/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factor_multiset_prod (v : prime_multiset) :
  v.prod.factor_multiset = v :=
begin
  apply prime_multiset.coe_nat_injective,
  rw [v.prod.coe_nat_factor_multiset, prime_multiset.coe_prod],
  rcases v with ⟨l⟩,
  unfold_coes,
  dsimp [prime_multiset.to_nat_multiset],
  rw [multiset.coe_prod],
  let l' := l.map (coe : nat.primes → ℕ),
  have : ∀ (p : ℕ), p ∈ l' → p.prime :=
    λ p hp, by {rcases list.mem_map.mp hp with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩,
                exact h_eq ▸ hp'},
  exact multiset.coe_eq_coe.mpr (@nat.factors_unique _ l' rfl this).symm,
end

end prime_multiset

namespace pnat

/-- Positive integers biject with multisets of primes. -/
def factor_multiset_equiv : ℕ+ ≃ prime_multiset :=
{ to_fun    := factor_multiset,
  inv_fun   := prime_multiset.prod,
  left_inv  := prod_factor_multiset,
  right_inv := prime_multiset.factor_multiset_prod }

/-- Factoring gives a homomorphism from the multiplicative
 monoid ℕ+ to the additive monoid of multisets. -/
theorem factor_multiset_one : factor_multiset 1 = 0 :=
by simp [factor_multiset, prime_multiset.of_nat_list, prime_multiset.of_nat_multiset]

theorem factor_multiset_mul (n m : ℕ+) :
  factor_multiset (n * m) = (factor_multiset n) + (factor_multiset m) :=
begin
  let u := factor_multiset n,
  let v := factor_multiset m,
  have : n = u.prod := (prod_factor_multiset n).symm, rw[this],
  have : m = v.prod := (prod_factor_multiset m).symm, rw[this],
  rw[← prime_multiset.prod_add],
  repeat {rw[prime_multiset.factor_multiset_prod]},
end

theorem factor_multiset_pow (n : ℕ+) (m : ℕ) :
  factor_multiset (n ^ m) = m • (factor_multiset n) :=
begin
  let u := factor_multiset n,
  have : n = u.prod := (prod_factor_multiset n).symm,
  rw[this, ← prime_multiset.prod_smul],
  repeat {rw[prime_multiset.factor_multiset_prod]},
end

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factor_multiset_of_prime (p : nat.primes) :
  (p : ℕ+).factor_multiset = prime_multiset.of_prime p :=
begin
  apply factor_multiset_equiv.symm.injective,
  change (p : ℕ+).factor_multiset.prod = (prime_multiset.of_prime p).prod,
  rw[(p : ℕ+).prod_factor_multiset, prime_multiset.prod_of_prime],
end

/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factor_multiset_le_iff {m n : ℕ+} :
  factor_multiset m ≤ factor_multiset n ↔ m ∣ n :=
begin
  split,
  { intro h,
    rw [← prod_factor_multiset m, ← prod_factor_multiset m],
    apply dvd.intro (n.factor_multiset - m.factor_multiset).prod,
    rw [← prime_multiset.prod_add, prime_multiset.factor_multiset_prod,
        prime_multiset.add_sub_of_le h, prod_factor_multiset] },
  { intro  h,
    rw [← mul_div_exact h, factor_multiset_mul],
    exact le_self_add }
end

theorem factor_multiset_le_iff' {m : ℕ+} {v : prime_multiset}:
 factor_multiset m ≤ v ↔ m ∣ v.prod :=
by { let h := @factor_multiset_le_iff m v.prod,
     rw [v.factor_multiset_prod] at h, exact h }

end pnat

namespace prime_multiset

theorem prod_dvd_iff {u v : prime_multiset} : u.prod ∣ v.prod ↔ u ≤ v :=
by { let h := @pnat.factor_multiset_le_iff' u.prod v,
     rw [u.factor_multiset_prod] at h, exact h.symm }

theorem prod_dvd_iff' {u : prime_multiset} {n : ℕ+} : u.prod ∣ n ↔ u ≤ n.factor_multiset :=
by { let h := @prod_dvd_iff u n.factor_multiset,
     rw [n.prod_factor_multiset] at h, exact h }

end prime_multiset

namespace pnat

/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets. -/
theorem factor_multiset_gcd (m n : ℕ+) :
 factor_multiset (gcd m n) = (factor_multiset m) ⊓ (factor_multiset n) :=
begin
  apply le_antisymm,
  { apply le_inf_iff.mpr; split; apply factor_multiset_le_iff.mpr,
    exact gcd_dvd_left m n, exact gcd_dvd_right m n},
  { rw[← prime_multiset.prod_dvd_iff, prod_factor_multiset],
    apply dvd_gcd; rw[prime_multiset.prod_dvd_iff'],
    exact inf_le_left, exact inf_le_right}
end

theorem factor_multiset_lcm (m n : ℕ+) :
 factor_multiset (lcm m n) = (factor_multiset m) ⊔ (factor_multiset n) :=
begin
  apply le_antisymm,
  { rw[← prime_multiset.prod_dvd_iff, prod_factor_multiset],
    apply lcm_dvd; rw[← factor_multiset_le_iff'],
    exact le_sup_left, exact le_sup_right},
  { apply sup_le_iff.mpr; split; apply factor_multiset_le_iff.mpr,
    exact dvd_lcm_left m n, exact dvd_lcm_right m n },
end

/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factor_multiset (m : ℕ+) (p : nat.primes) (k : ℕ) :
 (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factor_multiset.count p :=
begin
  intros,
  rw [multiset.le_count_iff_repeat_le],
  rw [← factor_multiset_le_iff, factor_multiset_pow, factor_multiset_of_prime],
  congr' 2,
  apply multiset.eq_repeat.mpr,
  split,
  { rw [multiset.card_nsmul, prime_multiset.card_of_prime, mul_one] },
  { have : ∀ (m : ℕ), m • (p ::ₘ 0) = multiset.repeat p m :=
    λ m, by {induction m with m ih, { refl },
             rw [succ_nsmul, multiset.repeat_succ, ih],
             rw[multiset.cons_add, zero_add] },
    intros q h, rw [prime_multiset.of_prime, this k] at h,
    exact multiset.eq_of_mem_repeat h }
end

end pnat

namespace prime_multiset

theorem prod_inf (u v : prime_multiset) :
 (u ⊓ v).prod = pnat.gcd u.prod v.prod :=
begin
  let n := u.prod,
  let m := v.prod,
  change (u ⊓ v).prod = pnat.gcd n m,
  have : u = n.factor_multiset := u.factor_multiset_prod.symm, rw [this],
  have : v = m.factor_multiset := v.factor_multiset_prod.symm, rw [this],
  rw [← pnat.factor_multiset_gcd n m, pnat.prod_factor_multiset]
end

theorem prod_sup (u v : prime_multiset) :
 (u ⊔ v).prod = pnat.lcm u.prod v.prod :=
begin
  let n := u.prod,
  let m := v.prod,
  change (u ⊔ v).prod = pnat.lcm n m,
  have : u = n.factor_multiset := u.factor_multiset_prod.symm, rw [this],
  have : v = m.factor_multiset := v.factor_multiset_prod.symm, rw [this],
  rw[← pnat.factor_multiset_lcm n m, pnat.prod_factor_multiset]
end

end prime_multiset
