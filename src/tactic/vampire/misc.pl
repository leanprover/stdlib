join_string([], _, "").

join_string([Str], _, Str).

join_string([Str | Strs], Jn, Rst) :-
  string_concat(Str, Jn, Str1),
  join_string(Strs, Jn, Str2),
  string_concat(Str1, Str2, Rst).

join_string(Strs, Str) :-
  join_string(Strs, "", Str).

is_digit(Cd) :- 47 < Cd, Cd < 58.

head_is_digit([Cd | _]) :- is_digit(Cd).

split_string_at(Str, Sep, Fst, Snd) :-
  string_concat(Fst, Tmp, Str),
  string_concat(Sep, Snd, Tmp).

number_binstr(0, "0").
number_binstr(1, "1").
number_binstr(Num, Str) :-
  Num > 1,
  Mod is Num mod 2,
  Quo is Num // 2,
  number_binstr(Quo, Str1),
  number_binstr(Mod, Str2),
  string_concat(Str1, Str2, Str).

max(Num1, Num2, Num1) :- Num1 >= Num2.
max(Num1, Num2, Num2) :- Num1 < Num2.

union([], []).

union([Lst | Lsts], Un) :-
  union(Lsts, Tmp),
  union(Lst, Tmp, Un).

break_list(0, Lst, [], Lst).

break_list(Num, [Elm | Lst], [Elm | Fst], Snd) :-
  0 < Num,
  NewNum is Num - 1,
  break_list(NewNum, Lst, Fst, Snd).

break_string(Num, Str, Fst, Snd) :-
  string_codes(Str, Cds),
  break_list(Num, Cds, FstCds, SndCds),
  string_codes(Fst, FstCds),
  string_codes(Snd, SndCds).

break_string(Num, Str, [Str]) :-
  string_length(Str, Lth),
  Lth =< Num.

break_string(Num, Str, [Hd | Tl]) :-
  break_string(Num, Str, Hd, Rem),
  break_string(Num, Rem, Tl).

tor([Hd | Tl], 0, [Hd | Tl]).

tor([Hd | Tl], Idx, [HdA, Hd | TlA]) :-
  tor(Tl, IdxA, [HdA | TlA]),
  Idx is IdxA + 1.

rot(0, [Hd | Tl], [Hd | Tl]).

rot(Idx, [Hd | Tl], [NewHd, Hd | NewTl]) :-
  0 < Idx,
  NewIdx is Idx - 1,
  rot(NewIdx, Tl, [NewHd | NewTl]).
