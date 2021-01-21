/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.basic
import algebra.archimedean
/-!
# Computable Continued Fractions

## Summary

We formalise the standard computation of (regular) continued fractions for linear ordered floor
fields. The algorithm is rather simple. Here is an outline of the procedure adapted from Wikipedia:

Take a value `v`. We call `⌊v⌋` the *integer part* of `v` and `v − ⌊v⌋` the *fractional part* of
`v`.  A continued fraction representation of `v` can then be given by `[⌊v⌋; b₀, b₁, b₂,...]`, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v − ⌊v⌋)`.  This
process stops when the fractional part hits 0.

In other words: to calculate a continued fraction representation of a number `v`, write down the
integer part (i.e. the floor) of `v`. Subtract this integer part from `v`. If the difference is 0,
stop; otherwise find the reciprocal of the difference and repeat. The procedure will terminate if
and only if `v` is rational.

For an example, refer to `int_fract_pair.stream`.

## Main definitions

- `generalized_continued_fraction.int_fract_pair.stream`: computes the stream of integer and
  fractional parts of a given value as described in the summary.
- `generalized_continued_fraction.of`: computes the generalised continued fraction of a value `v`.
  In fact, it computes a regular continued fraction that terminates if and only if `v` is rational
  (those proofs will be added in a future commit).

## Implementation Notes

There is an intermediate definition `generalized_continued_fraction.int_fract_pair.seq1` between
`generalized_continued_fraction.int_fract_pair.stream` and `generalized_continued_fraction.of`
to wire up things. User should not (need to) directly interact with it.

The computation of the integer and fractional pairs of a value can elegantly be
captured by a recursive computation of a stream of option pairs. This is done in
`int_fract_pair.stream`. However, the type then does not guarantee the first pair to always be
`some` value, as expected by a continued fraction.

To separate concerns, we first compute a single head term that always exists in
`generalized_continued_fraction.int_fract_pair.seq1` followed by the remaining stream of option
pairs. This sequence with a head term (`seq1`) is then transformed to a generalized continued
fraction in `generalized_continued_fraction.of` by extracting the wanted integer parts of the
head term and the stream.

## References

- https://en.wikipedia.org/wiki/Continued_fraction

## Tags

numerics, number theory, approximations, fractions
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf

-- Fix a carrier `K`.
variable (K : Type*)

/--
We collect an integer part `b = ⌊v⌋` and fractional part `fr = v - ⌊v⌋` of a value `v` in a pair
`⟨b, fr⟩`.
-/
structure int_fract_pair := (b : ℤ) (fr : K)

/-! Interlude: define some expected coercions and instances. -/
namespace int_fract_pair

/-- Make an `int_fract_pair` printable. -/
instance [has_repr K] : has_repr (int_fract_pair K) :=
⟨λ p, "(b : " ++ (repr p.b) ++ ", fract : " ++ (repr p.fr) ++ ")"⟩

instance inhabited [inhabited K] : inhabited (int_fract_pair K) := ⟨⟨0, (default _)⟩⟩

variable {K}

section coe
/-! Interlude: define some expected coercions. -/
/- Fix another type `β` and assume `K` can be converted to `β`. -/
variables {β : Type*} [has_coe K β]

/-- Coerce a pair by coercing the fractional component. -/
instance has_coe_to_int_fract_pair : has_coe (int_fract_pair K) (int_fract_pair β) :=
⟨λ ⟨b, fr⟩, ⟨b, (fr : β)⟩⟩


@[simp, norm_cast]
lemma coe_to_int_fract_pair {b : ℤ} {fr : K} :
  (↑(int_fract_pair.mk b fr) : int_fract_pair β) = int_fract_pair.mk b (↑fr : β) :=
rfl

end coe

-- Note: this could be relaxed to something like `linear_ordered_division_ring` in the
-- future.
/- Fix a discrete linear ordered field with `floor` function. -/
variables [linear_ordered_field K] [floor_ring K]

/-- Creates the integer and fractional part of a value `v`, i.e. `⟨⌊v⌋, v - ⌊v⌋⟩`. -/
protected def of (v : K) : int_fract_pair K := ⟨⌊v⌋, fract v⟩

/--
Creates the stream of integer and fractional parts of a value `v` needed to obtain the continued
fraction representation of `v` in `generalized_continued_fraction.of`. More precisely, given a value
`v : K`, it recursively computes a stream of option `ℤ × K` pairs as follows:
- `stream v 0 = some ⟨⌊v⌋, v - ⌊v⌋⟩`
- `stream v (n + 1) = some ⟨⌊frₙ⁻¹⌋, frₙ⁻¹ - ⌊frₙ⁻¹⌋⟩`,
    if `stream v n = some ⟨_, frₙ⟩` and `frₙ ≠ 0`
- `stream v (n + 1) = none`, otherwise

For example, let `(v : ℚ) := 3.4`. The process goes as follows:
- `stream v 0 = some ⟨⌊v⌋, v - ⌊v⌋⟩ = some ⟨3, 0.4⟩`
- `stream v 1 = some ⟨⌊0.4⁻¹⌋, 0.4⁻¹ - ⌊0.4⁻¹⌋⟩ = some ⟨⌊2.5⌋, 2.5 - ⌊2.5⌋⟩ = some ⟨2, 0.5⟩`
- `stream v 2 = some ⟨⌊0.5⁻¹⌋, 0.5⁻¹ - ⌊0.5⁻¹⌋⟩ = some ⟨⌊2⌋, 2 - ⌊2⌋⟩ = some ⟨2, 0⟩`
- `stream v n = none`, for `n ≥ 3`
-/
protected def stream (v : K) : stream $ option (int_fract_pair K)
| 0 := some (int_fract_pair.of v)
| (n + 1) := do ap_n ← stream n,
  if ap_n.fr = 0 then none else int_fract_pair.of ap_n.fr⁻¹

/--
Shows that `int_fract_pair.stream` has the sequence property, that is once we return `none` at
position `n`, we also return `none` at `n + 1`.
-/
lemma stream_is_seq (v : K) : (int_fract_pair.stream v).is_seq :=
by { assume _ hyp, simp [int_fract_pair.stream, hyp] }

/--
Uses `int_fract_pair.stream` to create a sequence with head (i.e. `seq1`) of integer and fractional
parts of a value `v`. The first value of `int_fract_pair.stream` is never `none`, so we can safely
extract it and put the tail of the stream in the sequence part.

This is just an intermediate representation and users should not (need to) directly interact with
it. The setup of rewriting/simplification lemmas that make the definitions easy to use is done in
`algebra.continued_fractions.computation.translations`.
-/
protected def seq1 (v : K) : seq1 $ int_fract_pair K :=
⟨ int_fract_pair.of v,--the head
  seq.tail -- take the tail of `int_fract_pair.stream` since the first element is already in the
  -- head create a sequence from `int_fract_pair.stream`
  ⟨ int_fract_pair.stream v, -- the underlying stream
    @stream_is_seq _ _ _ v ⟩ ⟩ -- the proof that the stream is a sequence

end int_fract_pair

variable {K}

/--
Returns the `generalized_continued_fraction` of a value. In fact, the returned gcf is also
a `continued_fraction` that terminates if and only if `v` is rational (those proofs will be
added in a future commit).

The continued fraction representation of `v` is given by `[⌊v⌋; b₀, b₁, b₂,...]`, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v − ⌊v⌋)`. This
process stops when the fractional part `v- ⌊v⌋` hits 0 at some step.

The implementation uses `int_fract_pair.stream` to obtain the partial denominators of the continued
fraction. Refer to said function for more details about the computation process.
-/
protected def of [linear_ordered_field K] [floor_ring K] (v : K) : gcf K :=
let ⟨h, s⟩ := int_fract_pair.seq1 v in -- get the sequence of integer and fractional parts.
⟨ h.b, -- the head is just the first integer part
  s.map (λ p, ⟨1, p.b⟩) ⟩ -- the sequence consists of the remaining integer parts as the partial
                          -- denominators; all partial numerators are simply 1


end generalized_continued_fraction
