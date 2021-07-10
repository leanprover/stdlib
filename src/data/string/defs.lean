/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Keeley Hoek, Floris van Doorn
-/
import data.list.defs

/-!
# Definitions for `string`

This file defines a bunch of functions for the `string` datatype.
-/

namespace string

/-- `s.split_on c` tokenizes `s : string` on `c : char`. -/
def split_on (s : string) (c : char) : list string :=
split (= c) s

/-- `string.map_tokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def map_tokens (c : char) (f : string → string) : string → string :=
intercalate (singleton c) ∘ list.map f ∘ split (= c)

/-- Tests whether the first string is a prefix of the second string. -/
def is_prefix_of (x y : string) : bool :=
x.to_list.is_prefix_of y.to_list

/-- Tests whether the first string is a suffix of the second string. -/
def is_suffix_of (x y : string) : bool :=
x.to_list.is_suffix_of y.to_list

/-- `x.starts_with y` is true if `y` is a prefix of `x`, and is false otherwise. -/
abbreviation starts_with (x y : string) : bool :=
y.is_prefix_of x

/-- `x.ends_with y` is true if `y` is a suffix of `x`, and is false otherwise. -/
abbreviation ends_with (x y : string) : bool :=
y.is_suffix_of x

/-- `get_rest s t` returns `some r` if `s = t ++ r`.
  If `t` is not a prefix of `s`, returns `none` -/
def get_rest (s t : string) : option string :=
list.as_string <$> s.to_list.get_rest t.to_list

/-- Removes the first `n` elements from the string `s` -/
def popn (s : string) (n : nat) : string :=
(s.mk_iterator.nextn n).next_to_string

/-- `is_nat s` is true iff `s` is a nonempty sequence of digits. -/
def is_nat (s : string) : bool :=
¬ s.is_empty ∧ s.to_list.all (λ c, to_bool c.is_digit)

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise 'A'. -/
def head (s : string) : char :=
s.mk_iterator.curr

end string
