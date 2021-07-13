import data.dfinsupp
import tactic

universes u v w

namespace dfinsupp.prod

variables {ii : Type u} {jj : Type v} [decidable_eq ii] [decidable_eq jj]
variables {β : ii → jj → Type w} [Π i j, has_zero (β i j)]

-- this definition is complete, and looks fairly readable - although there may be a shorter way
def prod_to_nested (f : Π₀ (ij : ii × jj), β ij.1 ij.2) : Π₀ i, Π₀ j, β i j := begin
  fapply quotient.lift_on f,
  exact λ fij, ⟦{
    to_fun := λ i, ⟦ {
      to_fun := λ j, fij.to_fun (i, j),
      pre_support := fij.pre_support.map prod.snd,
      zero := λ j, begin
        obtain hin | h0 := fij.zero (i, j),
        {apply or.inl, rw multiset.mem_map, use (i, j), simp only [hin, eq_self_iff_true, and_self]},
        {exact or.inr h0},
      end
    } ⟧,
    pre_support := fij.pre_support.map prod.fst,
    zero := λ i, begin
      unfold has_zero.zero,
      rw quotient.eq,
      unfold has_equiv.equiv setoid.r dfinsupp.pre.to_fun,
      rw ← forall_or_distrib_left,
      exact λ j, begin
        obtain hin | h0 := fij.zero (i, j),
        {apply or.inl, rw multiset.mem_map, use (i, j), simp only [hin, eq_self_iff_true, and_self]},
        {exact or.inr h0},
      end
    end
  }⟧,
  exact λ a b H, quotient.sound $ λ i, by {
    simp [H (i, _)],
    exact λ j, by simp [H (i, j)]
  },
end

-- this was my first attempt, which requires me to prove untrue statements
def nested_to_prod (f : Π₀ i j, β i j) : Π₀ (ij : ii × jj), β ij.1 ij.2 := begin
  fapply quotient.lift_on f,
  exact λ fi, ⟦{
    to_fun := λ ij, fi.to_fun ij.fst ij.snd,
    pre_support := fi.pre_support.bind (λ i, begin
      let js : multiset jj := quotient.lift_on (fi.to_fun i)
        dfinsupp.pre.pre_support
        (λ a b H, begin
          /- This is unprovable, I think lift_on is the wrong approach, or I need to return a clever quotient -/
          sorry
        end),
      exact js.map (prod.mk i)
    end),
    zero := λ ij, begin
      rw multiset.mem_bind,
      cases fi.zero ij.fst,
      { left, use ij.fst, simp [h], use ij.snd, simp,
        sorry},
      { right, simp [h] }
    end
  }⟧,
  exact λ a b H, quotient.sound $ λ ij, by simp [H ij.fst],
end

-- second attempt, by rewriting the inner function into a product function first.
def nested_to_prod2 (f : Π₀ i j, β i j) : Π₀ (ij : ii × jj), β ij.1 ij.2 := begin
  fapply quotient.lift_on f,
  exact λ fi, by {
    -- build a set of functions, each non-zero for a single i
    let fij : multiset (Π₀ (ij : ii × jj), β ij.fst ij.snd) := fi.pre_support.map (λ i, begin
      fapply quotient.lift_on (fi.to_fun i),
      exact λ fij, begin
        exact ⟦{
          to_fun := λ ij, dite (ij.fst = i) (λ h, begin
            rw h,
            exact fij.to_fun ij.snd,
          end) (λ nh, 0),
          pre_support := fij.pre_support.map (prod.mk i),
          zero := λ ij, begin
            by_cases (i = ij.fst),
            {
              obtain hin | h0 := fij.zero ij.snd,
              {apply or.inl, rw multiset.mem_map, use ij.snd, simp only [hin, h, prod.mk.eta, eq_self_iff_true, and_self] },
              {
                apply or.inr,
                simp only [],
                split_ifs with heq,
                {simp [h0], induction heq, refl},
                {refl},
              }
            },
            {
              apply or.inr,
              simp only [],
              split_ifs,
              exfalso, exact h h_1.symm,
              refl,
            }
          end,
        }⟧,
      end,
      exact λ a b H, quotient.sound $ λ ij, begin
        simp [H],
        split_ifs,
        rw H, refl,
      end,
    end),
    -- I don't know whether I can actual build something useful out of this multiset of functions now...
    sorry,
  },
  -- this can't be filled in until the above sorry is
  exact λ a b H, sorry,
end

lemma is_right_inverse  (f : Π₀ i j, β i j) : prod_to_nested(nested_to_prod(f)) = f := begin
  unfold prod_to_nested nested_to_prod,
  simp,
  -- irrelevant until `nested_to_prod` is fixed
  sorry
end

lemma is_left_inverse (f : Π₀ (ij : ii × jj), β ij.1 ij.2) : nested_to_prod(prod_to_nested(f)) = f := begin
  unfold prod_to_nested nested_to_prod,
  simp,
  -- irrelevant until `nested_to_prod` is fixed
  sorry
end

-- the sole purpose of this file
def eqv : (Π₀ (ij : ii × jj), β ij.1 ij.2) ≃ (Π₀ i j, β i j) := {
  to_fun := prod_to_nested,
  inv_fun := nested_to_prod,
  left_inv := is_left_inverse,
  right_inv := is_right_inverse }

end dfinsupp.prod
