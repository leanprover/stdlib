
import tactic.chain_trans
import tactic.interactive

/-- long chain of inequalities with a mix of `≤`, `<` and `=` -/
example {x y z w u v : ℕ} {a b : ℤ} (h₀ : x ≤ y) (h₁ : y < z) (h : y < u) (h₂ : z < w) (h₃ : w = u) (h₄ : u < v) : x ≤ u :=
begin
  chain_trans,
end

/-- error message when `≤` can be proved but not `<` -/
example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : true :=
begin
  have : w < w,
  { success_if_fail_with_msg
    { chain_trans }
    "`w < w` cannot be proved from `w ≤ w`",
    admit },
  triv
end

/-- error message when no proof is found -/
example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : true :=
begin
  have : x < w,
  { success_if_fail_with_msg
    { chain_trans }
    "no appropriate chain of inequalities can be found between `x` and `w`",
    admit },
  triv
end

/-- simple example -/
example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : w < z :=
begin
  chain_trans,
end

/-- there exists a proof of `w ≤ z` and one of `w < z`. `chain_trans` should prefer `w < z` -/
example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : y = z) (h₃ : x ≤ y) (h₂ : x < y) (h₃ : x ≤ y) : w < z :=
begin
  chain_trans,
end

/-- normalize vertices using `whnf` to recognize definitionally equal terms -/
example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : y = id z) (h₃ : x ≤ y) (h₂ : id x < y) (h₃ : x ≤ y) : w < z :=
begin
  chain_trans,
end

variables {α : Type} [preorder α]

/-- long chain of inequalities with a mix of `≤`, `<` and `=` -/
example {x y z w u v : α} (h₀ : x ≤ y) (h₁ : y < z) (h : y < u) (h₂ : z < w) (h₃ : w = u) (h₄ : u < v) : x ≤ u :=
begin
  chain_trans,
end
