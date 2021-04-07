import analysis.special_functions.trigonometric

namespace real

example : differentiable ℝ (λ (x : ℝ), exp x) :=
by simp

example : differentiable ℝ (λ (x : ℝ), exp ((sin x)^2) - exp (exp (cos (x - 3)))) :=
by simp

example (x : ℝ) : deriv (λ (x : ℝ), (cos x)^2 + 1 + (sin x)^2) x = 0 :=
by { simp, ring }

example (x : ℝ) : deriv (λ (x : ℝ), (1+x)^3 - x^3 - 3 * x^2 - 3 * x - 4) x = 0 :=
by { simp, ring }

example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }

example (x : ℝ) : differentiable_at ℝ (λ x, (cos x, x)) x := by simp

example (x : ℝ) (h : 1 + sin x ≠ 0) : deriv (λ x, exp (cos x) / (1 + sin x)) x =
  (-(exp (cos x) * sin x * (1 + sin x)) - exp (cos x) * cos x) / (1 + sin x) ^ 2 :=
by simp [h]

example (x : ℝ) : differentiable_at ℝ (λ x, (sin x) / (exp x)) x :=
by simp [exp_ne_zero]

example : differentiable ℝ (λ x, (sin x) / (exp x)) :=
by simp [exp_ne_zero]

example (x : ℝ) (h : x ≠ 0) : deriv (λ x, x * (log x - 1)) x = log x :=
by simp [h]

example (x : ℝ) : deriv (deriv log) x ≤ 0 := by simp [pow_two_nonneg]

end real


namespace complex

example : differentiable ℂ  (λ (x : ℂ), exp x) :=
by simp

example : differentiable ℂ (λ (x : ℂ), exp ((sin x)^2) - exp (exp (cos (x - 3)))) :=
by simp

example (x : ℂ) : deriv (λ (x : ℂ), (cos x)^2 + I + (sin x)^2) x = 0 :=
by { simp, ring }

example (x : ℂ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }

example (x : ℂ) : differentiable_at ℂ (λ x, (cos x, x)) x := by simp

example (x : ℂ) (h : 1 + sin x ≠ 0) : deriv (λ x, exp (cos x) / (1 + sin x)) x =
  (-(exp (cos x) * sin x * (1 + sin x)) - exp (cos x) * cos x) / (1 + sin x) ^ 2 :=
by simp [h]

example (x : ℂ) : differentiable_at ℂ (λ x, (sin x) / (exp x)) x :=
by simp [exp_ne_zero]

example : differentiable ℂ (λ x, (sin x) / (exp x)) :=
by simp [exp_ne_zero]

example (x : ℂ) : deriv (λ x, x ^ (-4:ℤ)) x = - 4 * x ^ (-5:ℤ) :=
by norm_num [-fpow_neg]

end complex

namespace polynomial

variables {R : Type*} [comm_semiring R]

example : (2 : polynomial R).derivative = 0 :=
by conv_lhs { simp }

example : (3 + X : polynomial R).derivative = 1 :=
by conv_lhs { simp }

example : (2 * X ^ 2 : polynomial R).derivative = 4 * X :=
by conv_lhs { simp, ring_nf, }

example : (X ^ 2 : polynomial R).derivative = 2 * X :=
by conv_lhs { simp }

example : ((C 2 * X ^ 3).derivative : polynomial R) = 6 * X ^ 2 :=
by conv_lhs { simp, ring_nf, }

end polynomial
