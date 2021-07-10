/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.linarith.elimination
import tactic.linarith.parsing

/-!
# Deriving a proof of false

`linarith` uses an untrusted oracle to produce a certificate of unsatisfiability.
It needs to do some proof reconstruction work to turn this into a proof term.
This file implements the reconstruction.

## Main declarations

The public facing declaration in this file is `prove_false_by_linarith`.
-/

namespace linarith

open ineq tactic native

/-! ### Auxiliary functions for assembling proofs -/

/--
`mul_expr n e` creates a `pexpr` representing `n*e`.
When elaborated, the coefficient will be a native numeral of the same type as `e`.
-/
meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
if n = 1 then ``(%%e) else
``(%%(nat.to_pexpr n) * %%e)

private meta def add_exprs_aux : pexpr → list pexpr → pexpr
| p [] := p
| p [a] := ``(%%p + %%a)
| p (h::t) := add_exprs_aux ``(%%p + %%h) t

/--
`add_exprs l` creates a `pexpr` representing the sum of the elements of `l`, associated left.
If `l` is empty, it will be the `pexpr` 0. Otherwise, it does not include 0 in the sum.
-/
meta def add_exprs : list pexpr → pexpr
| [] := ``(0)
| (h::t) := add_exprs_aux h t

/--
If our goal is to add together two inequalities `t1 R1 0` and `t2 R2 0`,
`ineq_const_nm R1 R2` produces the strength of the inequality in the sum `R`,
along with the name of a lemma to apply in order to conclude `t1 + t2 R 0`.
-/
meta def ineq_const_nm : ineq → ineq → (name × ineq)
| eq eq := (``eq_of_eq_of_eq, eq)
| eq le := (``le_of_eq_of_le, le)
| eq lt := (``lt_of_eq_of_lt, lt)
| le eq := (``le_of_le_of_eq, le)
| le le := (`add_nonpos, le)
| le lt := (`add_lt_of_le_of_neg, lt)
| lt eq := (``lt_of_lt_of_eq, lt)
| lt le := (`add_lt_of_neg_of_le, lt)
| lt lt := (`left.add_neg, lt)

/--
`mk_lt_zero_pf_aux c pf npf coeff` assumes that `pf` is a proof of `t1 R1 0` and `npf` is a proof
of `t2 R2 0`. It uses `mk_single_comp_zero_pf` to prove `t1 + coeff*t2 R 0`, and returns `R`
along with this proof.
-/
meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do (iq, h') ← mk_single_comp_zero_pf coeff npf,
   let (nm, niq) := ineq_const_nm c iq,
   prod.mk niq <$> mk_app nm [pf, h']

/--
`mk_lt_zero_pf coeffs pfs` takes a list of proofs of the form `tᵢ Rᵢ 0`,
paired with coefficients `cᵢ`.
It produces a proof that `∑cᵢ * tᵢ R 0`, where `R` is as strong as possible.
-/
meta def mk_lt_zero_pf : list (expr × ℕ) → tactic expr
| [] := fail "no linear hypotheses found"
| [(h, c)] := prod.snd <$> mk_single_comp_zero_pf c h
| ((h, c)::t) :=
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> t.mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.1 ce.2) (iq, h')

/-- If `prf` is a proof of `t R s`, `term_of_ineq_prf prf` returns `t`. -/
meta def term_of_ineq_prf (prf : expr) : tactic expr :=
prod.fst <$> (infer_type prf >>= get_rel_sides)

/-- If `prf` is a proof of `t R s`, `ineq_prf_tp prf` returns the type of `t`. -/
meta def ineq_prf_tp (prf : expr) : tactic expr :=
term_of_ineq_prf prf >>= infer_type

/--
`mk_neg_one_lt_zero_pf tp` returns a proof of `-1 < 0`,
where the numerals are natively of type `tp`.
-/
meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
do zero_lt_one ← mk_mapp `zero_lt_one [tp, none, none],
   mk_app `neg_neg_of_pos [zero_lt_one]

/--
If `e` is a proof that `t = 0`, `mk_neg_eq_zero_pf e` returns a proof that `-t = 0`.
-/
meta def mk_neg_eq_zero_pf (e : expr) : tactic expr :=
to_expr ``(neg_eq_zero.mpr %%e)

/--
`prove_eq_zero_using tac e` tries to use `tac` to construct a proof of `e = 0`.
-/
meta def prove_eq_zero_using (tac : tactic unit) (e : expr) : tactic expr :=
do tgt ← to_expr ``(%%e = 0),
   prod.snd <$> solve_aux tgt (tac >> done)

/--
`add_neg_eq_pfs l` inspects the list of proofs `l` for proofs of the form `t = 0`. For each such
proof, it adds a proof of `-t = 0` to the list.
-/
meta def add_neg_eq_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  do some (iq, tp) ← parse_into_comp_and_expr <$> infer_type h,
  match iq with
  | ineq.eq := do nep ← mk_neg_eq_zero_pf h, tl ← add_neg_eq_pfs t, return $ h::nep::tl
  | _ := list.cons h <$> add_neg_eq_pfs t
  end

/-! #### The main method -/

/--
`prove_false_by_linarith` is the main workhorse of `linarith`.
Given a list `l` of proofs of `tᵢ Rᵢ 0`,
it tries to derive a contradiction from `l` and use this to produce a proof of `false`.

An oracle is used to search for a certificate of unsatisfiability.
In the current implementation, this is the Fourier Motzkin elimination routine in
`elimination.lean`, but other oracles could easily be swapped in.

The returned certificate is a map `m` from hypothesis indices to natural number coefficients.
If our set of hypotheses has the form  `{tᵢ Rᵢ 0}`,
then the elimination process should have guaranteed that
1.\ `∑ (m i)*tᵢ = 0`,
with at least one `i` such that `m i > 0` and `Rᵢ` is `<`.

We have also that
2.\ `∑ (m i)*tᵢ < 0`,
since for each `i`, `(m i)*tᵢ ≤ 0` and at least one is strictly negative.
So we conclude a contradiction `0 < 0`.

It remains to produce proofs of (1) and (2). (1) is verified by calling the `discharger` tactic
of the `linarith_config` object, which is typically `ring`. We prove (2) by folding over the
set of hypotheses.
-/
meta def prove_false_by_linarith (cfg : linarith_config) : list expr → tactic expr
| [] := fail "no args to linarith"
| l@(h::t) := do
    -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
    -- along with negated equality proofs.
    l' ← add_neg_eq_pfs l,
    hz ← ineq_prf_tp h >>= mk_neg_one_lt_zero_pf,
    let inputs := hz::l',
    -- perform the elimination and fail if no contradiction is found.
    (comps, max_var) ← linear_forms_and_max_var cfg.transparency inputs,
    certificate ← cfg.oracle.get_or_else fourier_motzkin.produce_certificate comps max_var
      <|> fail "linarith failed to find a contradiction",
    linarith_trace "linarith has found a contradiction",
    let enum_inputs := inputs.enum,
    -- construct a list pairing nonzero coeffs with the proof of their corresponding comparison
    let zip := enum_inputs.filter_map $ λ ⟨n, e⟩, prod.mk e <$> certificate.find n,
    mls ← zip.mmap (λ ⟨e, n⟩, do e ← term_of_ineq_prf e, return (mul_expr n e)),
    -- `sm` is the sum of input terms, scaled to cancel out all variables.
    sm ← to_expr $ add_exprs mls,
    pformat! "The expression\n  {sm}\nshould be both 0 and negative" >>= linarith_trace,
    -- we prove that `sm = 0`, typically with `ring`.
    sm_eq_zero ← prove_eq_zero_using cfg.discharger sm,
    linarith_trace "We have proved that it is zero",
    -- we also prove that `sm < 0`.
    sm_lt_zero ← mk_lt_zero_pf zip,
    linarith_trace "We have proved that it is negative",
    -- this is a contradiction.
    pftp ← infer_type sm_lt_zero,
    (_, nep, _) ← rewrite_core sm_eq_zero pftp,
    pf' ← mk_eq_mp nep sm_lt_zero,
    mk_app `lt_irrefl [pf']

end linarith
