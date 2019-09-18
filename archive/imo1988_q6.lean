import data.rat.basic
import tactic

local attribute [instance] classical.prop_decidable
local attribute [simp] nat.pow_two

/- Vieta's formula for a quadratic equation -/
lemma Vieta_formula_quadratic {α} [comm_ring α] {b c x : α}
  (h : x * x - b * x + c = 0) : ∃ y : α,
    y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
begin
  have : c = b * x - x * x, { apply eq_of_sub_eq_zero, simpa using h },
  use b - x, simp [left_distrib, right_distrib, mul_comm, this],
end

/-
We need a long list of assumptions for the following lemma.
The upside is that it takes care of a bunch of annoying edge cases.
First of all, the user should provide $x$ and $y$
that satisfy the predicate $H(x,y)$.
The functions $B(x)$ and $C(x)$ give the coefficient of the quadratic equation
$y^2 - B(x) * y + C(x) = 0$.
The predicate `base` allows the user to specify a locus of base cases
that will be proven apart from the descent step `H_desc`.
This is the end of the input data. What follows are proof obligations.
In `H_quad` the user must supply a proof that $H(x,y)$ is satisfied
if and only if the quadratic equation $y^2 - B(x) * y + C(x) = 0$ is satisfied.
Next the user should prove that $H$ is symmetric in `H_symm`.
Then the user should prove $H(x,0)$ and $H(x,x)$ for every $x$,
in `H_zero` and `H_diag` respectively.
Finally, the user should prove the descent step in `H_desc`,
and the remaining bases cases in `H_base`.
-/

lemma constant_descent_vieta_jumping (x y : ℕ) {claim : Prop} {H : ℕ → ℕ → Prop}
  (h₀ : H x y) (B : ℕ → ℤ) (C : ℕ → ℤ) (base : ℕ → ℕ → Prop)
  (H_quad : ∀ {x y}, H x y ↔ (y:ℤ) * y - B x * y + C x = 0) (H_symm : ∀ {x y}, H x y ↔ H y x)
  (H_zero : ∀ {x}, H x 0 → claim) (H_diag : ∀ {x}, H x x → claim)
  (H_desc : ∀ {x y}, x < y → x > 0 → ¬base x y → H x y →
    ∀ y', y' * y' - B x * y' + C x = 0 → y' = B x - y → y' * y = C x → y' ≥ 0 ∧ y' ≤ x)
  (H_base : ∀ {x y}, H x y → base x y → claim) :
  claim :=
begin
  -- First of all, we may assume that $x ≤ y$.
  -- We justify this using H_symm.
  wlog hxy : x ≤ y, swap, { rw H_symm at h₀, solve_by_elim },
  -- In fact, we can easily deal with the case $x = y$.
  by_cases x_eq_y : x = y, {subst x_eq_y, exact H_diag h₀},
  -- Hence we may assume that $x < y$.
  replace hxy : x < y := lt_of_le_of_ne hxy x_eq_y, clear x_eq_y,
  -- Consider the upper branch of the hyperbola defined by $H$.
  let upper_branch : set (ℕ × ℕ) := {p | H p.1 p.2 ∧ p.1 < p.2},
  -- Note that the point $p = (x,y)$ lies on the upper branch.
  let p : ℕ × ℕ := ⟨x,y⟩,
  have hp : p ∈ upper_branch := ⟨h₀, hxy⟩,
  -- We also consider the exceptional set of solutions $(a,b)$ that satisfy
  -- $a = 0$ or $a = b$ or $B a = b$ or $B a = b + a$.
  let exceptional  : set (ℕ × ℕ) := {p | H p.1 p.2 ∧ (base p.1 p.2 ∨ p.1 = 0 ∨ p.1 = p.2 ∨ B p.1 = p.2 ∨ B p.1 = p.2 + p.1) },
  -- Let $S$ be the projection on to the $y$-axis of the upper branch after removing the exceptional locus.
  let S : set ℕ := prod.snd '' (upper_branch \ exceptional),
  -- The strategy is to show that the exceptional locus in nonempty.
  -- We first show that this is sufficient.
  suffices exc : exceptional ≠ ∅,
  { -- Suppose that there exists an element in the exceptional locus.
    rw set.ne_empty_iff_exists_mem at exc,
    simp [exceptional, -add_comm] at exc,
    -- Let $(a,b)$ be such an element, and consider all the possible cases.
    rcases exc with ⟨a, b, hH, hb⟩, rcases hb with _|rfl|rfl|hB|hB,
    -- The first three cases are rather easy to solve.
    { solve_by_elim },
    { rw H_symm at hH, solve_by_elim },
    { solve_by_elim },
    -- The final two cases are very similar.
    all_goals {
      -- Consider the quadratic equation that $(a,b)$ satisfies.
      rw H_quad at hH,
      -- We find the other root of the equation, and Vieta's formulas.
      rcases Vieta_formula_quadratic hH with ⟨c, h_root, hV₁, hV₂⟩,
      -- By substitutions we find that $b = 0$ or $b = a$.
      simp [hB] at hV₁, subst hV₁,
      rw [← int.coe_nat_zero] at *,
      rw ← H_quad at h_root,
      -- And hence we are done by H_zero and H_diag.
      solve_by_elim } },
  -- Now assume that the exceptional locus is empty.
  assume exceptional_empty,
  -- Observe that $S$ is nonempty.
  have S_ne_empty : S ≠ ∅,
  { rw set.ne_empty_iff_exists_mem,
    -- It contains the image of $p$.
    use p.2,
    apply set.mem_image_of_mem,
    -- After all, we assumed that the exceptional locus is empty.
    rwa [exceptional_empty, set.diff_empty], },
  -- We are now set for an infinite descent argument.
  -- Let $m$ be the smallest element of the nonempty set $S$.
  let  m     : ℕ                := well_founded.min     nat.lt_wf S S_ne_empty,
  have m_mem : m ∈ S            := well_founded.min_mem nat.lt_wf S S_ne_empty,
  have m_min : ∀ k ∈ S, ¬ k < m := λ k hk, well_founded.not_lt_min nat.lt_wf S S_ne_empty hk,
  -- It suffices to show that there is point $(a,b)$ with $b ∈ S$ and $b < m$.
  suffices hp' : ∃ p' : ℕ × ℕ, p'.2 ∈ S ∧ p'.2 < m,
  { rcases hp' with ⟨p', p'_mem, p'_small⟩, solve_by_elim },
  -- Let $(m_x, m_y)$ be a point on the upper branch that projects to $m ∈ S$
  -- and that does not lie in the exceptional locus.
  rcases m_mem with ⟨⟨mx, my⟩, ⟨⟨hHm, mx_lt_my⟩, h_base⟩, m_eq⟩,
  -- This means that $m_y = m$,
  -- and the conditions $H(m_x, m_y)$ and $m_x < m_y$ are satisfied.
  simp only at hHm,
  simp [exceptional, hHm] at mx_lt_my h_base m_eq,
  push_neg at h_base,
  -- Finally, it also means that $(m_x, m_y)$ does not lie in the base locus,
  -- that $m_x ≠ 0$, $m_x ≠ m_y$, $B(m_x) ≠ m_y$, and $B(m_x) ≠ m_x + m_y$.
  rcases h_base with ⟨h_base, hmx, hm_diag, hm_B₁, hm_B₂⟩,
  replace hmx : mx > 0 := nat.pos_iff_ne_zero.mpr hmx,
  -- Consider the quadratic equation that $(m_x, m_y)$ satisfies.
  have h_quad := hHm, rw H_quad at h_quad,
  -- We find the other root of the equation, and Vieta's formulas.
  rcases Vieta_formula_quadratic h_quad with ⟨c, h_root, hV₁, hV₂⟩,
  -- Recall that we are trying find a point $(a,b)$ such that $b ∈ S$ and $b < m$.
  -- We claim that $p' = (|c|, m_x)$ does the job.
  let p' : ℕ × ℕ := ⟨c.nat_abs, mx⟩,
  use p',
  -- The second condition is rather easy to check, so we do that first.
  split, swap,
  { rwa m_eq at mx_lt_my },
  -- Now we need to show that $p'$ projects onto $S$.
  -- In other words, that $|c| ∈ S$.
  -- We do that, by showing that it lies in the upper branch
  -- (which is sufficient, because we assumed that the exceptional locus is empty).
  apply set.mem_image_of_mem,
  rw [exceptional_empty, set.diff_empty],
  -- To see that this is true, we first rewrite Vietas formulas a bit,
  -- and apply the descent step.
  replace hV₁ : c = B mx - my := eq_sub_of_add_eq' hV₁,
  rw mul_comm at hV₂,
  have Hc := H_desc mx_lt_my hmx h_base hHm c h_root hV₁ hV₂,
  -- This means that we may assume that $c ≥ 0$ and $c ≤ m_x$.
  cases Hc with c_nonneg c_lt,
  -- Now we are ready to prove that $p' = (|c|, m_x)$ lies on the upper branch.
  -- We need to check two conditions: $H(|c|, m_x)$ and $|c| < m_x$.
  split; dsimp,
  { -- The first condition is not so hard.
    -- After all, $c$ was the other root of the quadratic equation,
    -- and since $c ≥ 0$ we know that $c = |c|$.
    rw [H_symm, H_quad],
    simpa [int.nat_abs_of_nonneg c_nonneg] using h_root, },
  { -- For the second condition, we note that it suffices to check that $c ≠ m_x$.
    suffices hc : c ≠ mx,
    { rw [← int.coe_nat_lt],
      simp [int.nat_abs_of_nonneg c_nonneg],
      apply lt_of_le_of_ne c_lt hc },
    -- However, recall that $B(m_x) ≠ m_x + m_y$.
    -- If $c = m_x$, we can prove $B(m_x) = m_x + m_y$.
    contrapose! hm_B₂, subst c,
    rw ← hm_B₂,
    simp, }
    -- Hence $p' = (|c|, m_x)$ lies on the upper branch, and we are done.
end

lemma imo1988_q6 {a b : ℕ} (h : (a*b+1) ∣ a^2 + b^2) :
  ∃ d, d^2 = (a^2 + b^2)/(a*b + 1) :=
begin
  rcases h with ⟨k, hk⟩,
  rw [hk, nat.mul_div_cancel_left _ (nat.succ_pos (a*b))],
  simp only [nat.pow_two] at hk,
  apply constant_descent_vieta_jumping a b hk (λ x, k * x) (λ x, x*x - k) (λ x y, false),
  { intros x y, dsimp,
    rw [← int.coe_nat_inj', ← sub_eq_zero],
    apply eq_iff_eq_cancel_right,
    simp, ring, },
  { intros x y, simp [add_comm (x*x), mul_comm x], },
  { simp, rintros x rfl, use x },
  { intros x hx,
    suffices : k ≤ 1,
    { rcases nat.le_one_cases k this with rfl|rfl,
      { use 0, simp },
      { use 1, simp } },
    contrapose! hx with k_lt_one,
    apply ne_of_lt,
    calc x*x + x*x = x*x * 2       : by rw mul_two
               ... ≤ x*x * k       : nat.mul_le_mul_left (x*x) k_lt_one
               ... < (x*x + 1) * k : by apply mul_lt_mul; linarith },
  { clear hk a b,
    intros x y x_lt_y hx hxky h z h_root hV₁ hV₀,
    split,
    { dsimp [-sub_eq_add_neg] at *,
      have hpos : z*z + x*x > 0,
      { apply add_pos_of_nonneg_of_pos,
        { apply mul_self_nonneg },
        { apply mul_pos; exact_mod_cast hx }, },
      have hzx : z*z + x*x = (z * x + 1) * k,
      { rw [← sub_eq_zero, ← h_root],
        simp, ring, },
      rw hzx at hpos,
      replace hpos : z * x + 1 > 0 := pos_of_mul_pos_right hpos (int.coe_zero_le k),
      replace hpos : z * x ≥ 0 := int.le_of_lt_add_one hpos,
      apply nonneg_of_mul_nonneg_right hpos (by exact_mod_cast hx), },
    { contrapose! hV₀ with x_lt_z,
      apply ne_of_gt,
      calc z * y > x*x     : by apply mul_lt_mul'; linarith
             ... ≥ x*x - k : sub_le_self _ (int.coe_zero_le k) }, },
  { simp },
end

example {a b : ℕ} (h : a*b ∣ a^2 + b^2 + 1) :
  3*a*b = a^2 + b^2 + 1 :=
begin
  rcases h with ⟨k, hk⟩,
  suffices : k = 3, { simp * at *, ring, },
  simp only [nat.pow_two] at hk,
  apply constant_descent_vieta_jumping a b hk (λ x, k * x) (λ x, x*x + 1) (λ x y, x ≤ 1),
  { intros x y, dsimp,
    rw [← int.coe_nat_inj', ← sub_eq_zero],
    apply eq_iff_eq_cancel_right,
    simp, ring, },
  { intros x y, simp, apply eq_iff_eq_cancel_left, ring },
  { simp },
  { clear hk a b, intros x hx,
    have x_sq_dvd : x*x ∣ x*x*k := dvd_mul_right (x*x) k,
    rw ← hx at x_sq_dvd,
    simp only [nat.dvd_add_self_left, add_assoc] at x_sq_dvd,
    rcases x_sq_dvd with ⟨y, hy⟩,
    rw eq_comm at hy,
    simp [nat.mul_eq_one_iff] at hy,
    rcases hy with ⟨rfl,rfl⟩,
    simpa using hx.symm, },
  { clear hk a b,
    intros x y x_lt_y hx h_base h z h_root hV₁ hV₀,
    split,
    { have zy_pos : z * y ≥ 0,
      { rw hV₀, exact_mod_cast (nat.zero_le _) },
      apply nonneg_of_mul_nonneg_right zy_pos,
      linarith },
    { contrapose! hV₀ with x_lt_z,
      apply ne_of_gt,
      push_neg at h_base,
      calc z * y > x * y       : by apply mul_lt_mul_of_pos_right; linarith
             ... ≥ x * (x + 1) : by apply mul_le_mul; linarith
             ... > x * x + 1   :
        begin
          rw [mul_add, mul_one],
          apply add_lt_add_left,
          assumption_mod_cast
        end, } },
  { intros x y h h_base,
    rcases nat.le_one_cases x h_base with rfl|rfl,
    { simp at h, contradiction },
    { simp at h,
      have y_dvd : y ∣ y * k := dvd_mul_right y k,
      rw [← h, ← add_assoc, nat.dvd_add_left (dvd_mul_left y y)] at y_dvd,
      have y_eq : y = 1 ∨ y = 2 := nat.prime_two.2 y y_dvd,
      rcases y_eq with rfl|rfl,
      { simpa using h.symm, },
      { replace h : 2 * k = 2 * 3 := h.symm,
        apply nat.eq_of_mul_eq_mul_left _ h,
        exact (nat.succ_pos _), } } }
end
