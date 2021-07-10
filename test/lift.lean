import tactic.lift
import data.set.basic
import data.int.basic

/-! Some tests of the `lift` tactic. -/

example (n m k x z u : ℤ) (hn : 0 < n) (hk : 0 ≤ k + n) (hu : 0 ≤ u)
  (h : k + n = 2 + x) (f : false) :
  k + n = m + x :=
begin
  lift n to ℕ using le_of_lt hn,
    guard_target (k + ↑n = m + x), guard_hyp hn : (0 : ℤ) < ↑n,
  lift m to ℕ,
    guard_target (k + ↑n = ↑m + x), tactic.swap, guard_target (0 ≤ m), tactic.swap,
    tactic.num_goals >>= λ n, guard (n = 2),
  lift (k + n) to ℕ using hk with l hl,
    guard_hyp l : ℕ, guard_hyp hl : ↑l = k + ↑n, guard_target (↑l = ↑m + x),
    tactic.success_if_fail (tactic.get_local `hk),
  lift x to ℕ with y hy,
    guard_hyp y : ℕ, guard_hyp hy : ↑y = x, guard_target (↑l = ↑m + x),
  lift z to ℕ with w,
    guard_hyp w : ℕ, tactic.success_if_fail (tactic.get_local `z),
  lift u to ℕ using hu with u rfl hu,
    guard_hyp hu : (0 : ℤ) ≤ ↑u,

  all_goals { exfalso, assumption },
end

-- test lift of functions
example (α : Type*) (f : α → ℤ) (hf : ∀ a, 0 ≤ f a) (hf' : ∀ a, f a < 1) (a : α) : 0 ≤ 2 * f a :=
begin
  lift f to α → ℕ using hf,
    guard_target ((0:ℤ) ≤ 2 * (λ i : α, (f i : ℤ)) a),
    guard_hyp hf' : ∀ a, ((λ i : α, (f i:ℤ)) a) < 1,
  exact int.coe_nat_nonneg _
end

-- fail gracefully when the lifted variable is a local definition
example : let n : ℤ := 3 in n = n :=
begin
  intro n,
  success_if_fail_with_msg { lift n to ℕ }
    ("Cannot substitute variable n, it is a local definition. " ++
    "If you really want to do this, use `clear_value` first."),
  refl
end

instance can_lift_unit : can_lift unit unit :=
⟨id, λ x, true, λ x _, ⟨x, rfl⟩⟩

/- test whether new instances of `can_lift` are added as simp lemmas -/
run_cmd do l ← can_lift_attr.get_cache, guard (`can_lift_unit ∈ l)

/- test error messages -/
example (n : ℤ) (hn : 0 < n) : true :=
begin
  success_if_fail_with_msg {lift n to ℕ using hn} "lift tactic failed.
invalid type ascription, term has type\n  0 < n\nbut is expected to have type\n  0 ≤ n",
  success_if_fail_with_msg {lift (n : option ℤ) to ℕ}
    "Failed to find a lift from option ℤ to ℕ. Provide an instance of\n  can_lift (option ℤ) ℕ",
  trivial
end

example (n : ℤ) : ℕ :=
begin
  success_if_fail_with_msg {lift n to ℕ}
    "lift tactic failed. Tactic is only applicable when the target is a proposition.",
  exact 0
end

instance can_lift_subtype (R : Type*) (P : R → Prop) : can_lift R {x // P x} :=
{ coe := coe,
  cond := λ x, P x,
  prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }

instance can_lift_set (R : Type*) (s : set R) : can_lift R s :=
{ coe := coe,
  cond := λ x, x ∈ s,
  prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }

example {R : Type*} {P : R → Prop} (x : R) (hx : P x) : true :=
by { lift x to {x // P x} using hx with y, trivial }

/-! Test that `lift` elaborates `s` as a type, not as a set. -/
example {R : Type*} {s : set R} (x : R) (hx : x ∈ s) : true :=
by { lift x to s using hx with y, trivial }

example (n : ℤ) (hn : 0 ≤ n) : true :=
by { lift n to ℕ, trivial, exact hn }

example (n : ℤ) (hn : 0 ≤ n) : true :=
by { lift n to ℕ using hn, trivial }

example (n : ℤ) (hn : n ≥ 0) : true :=
by { lift n to ℕ using ge.le _, trivial, guard_target (n ≥ 0), exact hn }

example (n : ℤ) (hn : 0 ≤ 1 * n) : true :=
begin
  lift n to ℕ using by { simpa [int.one_mul] using hn } with k,
  -- the above braces are optional, but it would be bad style to remove them (see next example)
  guard_hyp hn : 0 ≤ 1 * ((k : ℕ) : ℤ),
  trivial
end

example (n : ℤ) (hn : 0 ≤ n ↔ true) : true :=
begin
  lift n to ℕ using by { simp [hn] } with k, -- the braces are not optional here
  trivial
end
