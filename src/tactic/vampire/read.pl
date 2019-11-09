:- [misc].

read_lines(Out, []) :-
  read_line_to_string(Out, end_of_file), !.

read_lines(Out, Cdss) :-
  read_line_to_codes(Out, Cds),
  read_lines(Cds, Out, Cdss).

read_lines(end_of_file, _, []) :- !.

read_lines(Cds, Out, [Cds | Cdss]) :-
        read_line_to_codes(Out, Tmp),
        read_lines(Tmp, Out, Cdss).

vampire(Loc, Cdss) :-
  setup_call_cleanup(
    process_create(
      path(vampire),
      ["--avatar", "off", Loc],
      [stdout(pipe(Out))]
    ),
    read_lines(Out, Cdss),
    close(Out)
  ).

parse_rul("input", asm).

parse_rul(Str, map(Idx)) :-
  ( string_concat("factoring ", NumStr, Str) ;
    string_concat("duplicate literal removal ", NumStr, Str) ),
  number_string(Num, NumStr),
  Idx is Num - 1.

parse_rul(Str, trv(Idx)) :-
  string_concat("trivial inequality removal ", NumStr, Str),
  number_string(Num, NumStr),
  Idx is Num - 1.

parse_rul(Str, eqres(Idx)) :-
  string_concat("equality resolution ", NumStr, Str),
  number_string(Num, NumStr),
  Idx is Num - 1.

parse_rul(Str, rsl(Idx1, Idx2)) :-
  ( string_concat("resolution ", Tmp, Str) ;
    string_concat("subsumption resolution ", Tmp, Str) ),
  split_string(Tmp, ",", "", [NumStr1, NumStr2]),
  number_string(Num1, NumStr1),
  Idx1 is Num1 - 1,
  number_string(Num2, NumStr2),
  Idx2 is Num2 - 1.


parse_rul(Str, rep(Idx1, Idx2)) :-
  ( string_concat("superposition ", Tmp, Str) ;
    string_concat("forward demodulation ", Tmp, Str) ;
    string_concat("definition unfolding ", Tmp, Str) ),
  split_string(Tmp, ",", "", [NumStr1, NumStr2]),
  number_string(Num1, NumStr1),
  Idx1 is Num1 - 1,
  number_string(Num2, NumStr2),
  Idx2 is Num2 - 1.

parse_num(Acc, [Cd | Cds], Num, Rem) :-
  is_digit(Cd),
  parse_num([Cd | Acc], Cds, Num, Rem).

parse_num(Acc, Cds, Num, Cds) :-
  ( ( Cds = [Hd | _],
      not(is_digit(Hd)) ) ;
    ( Cds = [] ) ),
  reverse(Acc, Tmp),
  number_codes(Num, Tmp).

parse_num(Str, Num, Rem) :-
  string_codes(Str, Cds),
  parse_num([], Cds, Num, Tmp),
  string_codes(Rem, Tmp).

parse_args_core(Str, [], Rem) :-
  string_concat(")", Rem, Str).

parse_args_core(Str, Args, Rem) :-
  string_concat(",", Str1, Str),
  parse_args_core(Str1, Args, Rem).

parse_args_core(Str, [Arg | Args], Rem) :-
  parse_trm(Str, Arg, Str1),
  parse_args_core(Str1, Args, Rem).

parse_args(Str, [], Str) :-
  not(string_concat("(", _, Str)).

parse_args(Str, Args, Rem) :-
  string_concat("(", Str1, Str),
  parse_args_core(Str1, Args, Rem).

parse_trm(Str, fn(Num, Trms), Rem) :-
  string_concat("f", Str1, Str),
  parse_num(Str1, Num, Str2),
  parse_args(Str2, Trms, Rem).

parse_trm(Str, var(Num), Rem) :-
  string_concat("X", Str1, Str),
  parse_num(Str1, Num, Rem).

parse_atm(Str, rl(Num, Trms), Rem) :-
  string_concat("r", Str1, Str), 
  parse_num(Str1, Num, Str2),
  parse_args(Str2, Trms, Rem).

parse_atm(Str, eq(TrmA, TrmB), Rem) :-
  parse_trm(Str, TrmA, Str1), 
  string_concat(" = ", Str2, Str1),
  parse_trm(Str2, TrmB, Rem). 

parse_atm(Str, ne(TrmA, TrmB), Rem) :-
  parse_trm(Str, TrmA, Str1), 
  string_concat(" != ", Str2, Str1),
  parse_trm(Str2, TrmB, Rem). 

parse_lit_core(Str, lit(neg, Atm)) :-
  string_concat("~", Tmp, Str),
  parse_atm(Tmp, Atm, "").

parse_lit_core(Str, lit(pos, Atm)) :-
  parse_atm(Str, Atm, "").

negate(neg, pos).
negate(pos, neg).

rmv_ne(TmpPol, ne(TrmA, TrmB), Pol, eq(TrmA, TrmB)) :- 
  !, negate(TmpPol, Pol).

rmv_ne(Pol, Atm, Pol, Atm). 

parse_lit(Str, lit(Pol, Atm)) :-
  parse_lit_core(Str, lit(TmpPol, TmpAtm)),
  rmv_ne(TmpPol, TmpAtm, Pol, Atm). 

parse_cla("$false", []) :- !.

parse_cla(Str, Cla) :-
  split_string(Str, "|", " ", LitStrs),
  maplist(parse_lit, LitStrs, Cla).

parse_line(Str, line(Idx, Cla, Rul)) :-
  split_string(Str, ".[", "] ", [NumStr, ClaStr, RulStr]),
  number_string(Num, NumStr),
  Idx is Num - 1,
  parse_cla(ClaStr, Cla),
  parse_rul(RulStr, Rul).

read_proof(Loc, Lns) :-
  vampire(Loc, Cds),
  include(head_is_digit, Cds, Tmp),
  maplist(string_codes, Strs, Tmp),
  maplist(parse_line, Strs, Lns).

read_test(Loc, Strs) :-
  vampire(Loc, Cds),
  include(head_is_digit, Cds, Tmp),
  maplist(string_codes, Strs, Tmp).
