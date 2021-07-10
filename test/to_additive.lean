import algebra.group.to_additive

@[to_additive bar0]
def foo0 {α} [has_mul α] [has_one α] (x y : α) : α := x * y * 1

class {u v} my_has_pow (α : Type u) (β : Type v) :=
(pow : α → β → α)

class my_has_scalar (M : Type*) (α : Type*) := (smul : M → α → α)

attribute [to_additive_reorder 1] my_has_pow
attribute [to_additive_reorder 1 4] my_has_pow.pow
attribute [to_additive my_has_scalar] my_has_pow
attribute [to_additive my_has_scalar.smul] my_has_pow.pow

-- set_option pp.universes true
-- set_option pp.implicit true
-- set_option pp.notation false

@[priority 10000]
local infix ` ^ `:80 := my_has_pow.pow

@[to_additive bar1]
def foo1 {α} [my_has_pow α ℕ] (x : α) (n : ℕ) : α := @my_has_pow.pow α ℕ _ x n

instance dummy : my_has_pow ℕ $ plift ℤ := ⟨λ _ _, 0⟩

set_option pp.universes true
@[to_additive bar2]
def foo2 {α} [my_has_pow α ℕ] (x : α) (n : ℕ) (m : plift ℤ) : α := x ^ (n ^ m)

@[to_additive bar3]
def foo3 {α} [my_has_pow α ℕ] (x : α) : ℕ → α := @my_has_pow.pow α ℕ _ x

@[to_additive bar4]
def {a b} foo4 {α : Type a} : Type b → Type (max a b) := @my_has_pow α

@[to_additive bar4_test]
lemma foo4_test {α β : Type*} : @foo4 α β = @my_has_pow α β := rfl

@[to_additive bar5]
def foo5 {α} [my_has_pow α ℕ] [my_has_pow ℕ ℤ] : true := trivial

@[to_additive bar6]
def foo6 {α} [my_has_pow α ℕ] : α → ℕ → α := @my_has_pow.pow α ℕ _

@[to_additive bar7]
def foo7 := @my_has_pow.pow

open tactic
/- test the eta-expansion applied on `foo6`. -/
run_cmd do
env ← get_env,
reorder ← to_additive.reorder_attr.get_cache,
d ← get_decl `foo6,
let e := d.value.eta_expand env reorder,
let t := d.type.eta_expand env reorder,
let decl := declaration.defn `barr6 d.univ_params t e d.reducibility_hints d.is_trusted,
add_decl decl,
skip
