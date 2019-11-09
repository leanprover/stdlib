:- [misc].

subst_trms(Maps, Trms, NewTrms) :-
  maplist(subst_trm(Maps), Trms, NewTrms).

subst_trm(Maps, var(Num), var(Num)) :-
  not(member(map(Num, _), Maps)).

subst_trm(Maps, var(Num), Trm) :-
  member(map(Num, Trm), Maps), !.

subst_trm(Maps, fn(Num, Trms), fn(Num, NewTrms)) :-
  subst_trms(Maps, Trms, NewTrms).

subst_atm(Maps, eq(SrcTrmA, SrcTrmB), eq(TgtTrmA, TgtTrmB)) :-
  subst_trm(Maps, SrcTrmA, TgtTrmA),
  subst_trm(Maps, SrcTrmB, TgtTrmB).

subst_atm(Maps, rl(Num, Trms), rl(Num, NewTrms)) :-
  subst_trms(Maps, Trms, NewTrms).

subst_lit(Map, lit(Pol, SrcAtm), lit(Pol, TgtAtm)) :-
  subst_atm(Map, SrcAtm, TgtAtm).

subst_cla(Maps, Cla, NewCla) :-
  maplist(subst_lit(Maps), Cla, NewCla).

/* 
check(Mat, LPrf, success) :-
  string_codes(LPrf, Prf),
  check(Mat, [], Prf).

check(Mat, LPrf, fail(Mat, LPrf)).

check(_, [cla([])], []).

check(Mat, Stk, [110 | Prf]) :-
  check(Mat, [num(0) | Stk], Prf).

check(Mat, [num(Num) | Stk], [48 | Prf]) :-
  NumA is Num * 2,
  check(Mat, [num(NumA) | Stk], Prf).

check(Mat, [num(Num) | Stk], [49 | Prf]) :-
  NumA is ((Num * 2) + 1),
  check(Mat, [num(NumA) | Stk], Prf).

check(Mat, [maps(Maps), num(Num) | Stk], [97 | Prf]) :-
  nth0(Num, Mat, Cla),
  subst(Maps, Cla, Cnc),
  check(Mat, [cla(Cnc) | Stk], Prf).

check(Mat, [cla([lit(pos, Trm) | ClaB]), cla([lit(neg, Trm) | ClaA]) | Stk], [114 | Prf]) :-
  append(ClaA, ClaB, Cnc),
  check(Mat, [cla(Cnc) | Stk], Prf).

check(Mat, [cla(Cla), num(Num) | Stk], [116 | Prf]) :-
  rot(Num, Cla, Cnc),
  check(Mat, [cla(Cnc) | Stk], Prf).

check(Mat, [cla([Lit, Lit | Cla]) | Stk], [99 | Prf]) :-
  check(Mat, [cla([Lit | Cla]) | Stk], Prf).

check(Mat, Stk, [101 | Prf]) :-
  check(Mat, [maps([]) | Stk], Prf).

check(Mat, [num(Num) | Stk], [115 | Prf]) :-
  check(Mat, [trm(sym(Num)) | Stk], Prf).

check(Mat, [trm(TrmB), trm(TrmA) | Stk], [112 | Prf]) :-
  check(Mat, [trm(app(TrmA, TrmB)) | Stk], Prf).

check(Mat, [trm(Trm), num(Num), maps(Maps) | Stk], [109 | Prf]) :-
  check(Mat, [maps([map(Num, Trm) | Maps]) | Stk], Prf).
*/

