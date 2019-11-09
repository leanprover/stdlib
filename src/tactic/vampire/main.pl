#!/usr/bin/env swipl

:- initialization(main, main).

:- [write, read, check].

parse_inp([Num | Stk], ['v' | Chs], Mat) :-
  parse_inp([var(Num) | Stk], Chs, Mat).

parse_inp([Num, Trms | Stk], ['f' | Chs], Mat) :-
  parse_inp([fn(Num, Trms) | Stk], Chs, Mat).

parse_inp([Num, Trms | Stk], ['r' | Chs], Mat) :-
  parse_inp([rl(Num, Trms) | Stk], Chs, Mat).

parse_inp([TrmB, TrmA | Stk], ['e' | Tks], Mat) :-
  parse_inp([eq(TrmA, TrmB) | Stk], Tks, Mat).

parse_inp([Atm | Stk], ['-' | Tks], Mat) :-
  parse_inp([lit(neg, Atm) | Stk], Tks, Mat).

parse_inp([Atm | Stk], ['+' | Tks], Mat) :-
  parse_inp([lit(pos, Atm) | Stk], Tks, Mat).

parse_inp(Stk, ['n' | Chs], Mat) :-
  parse_inp([[] | Stk], Chs, Mat).

parse_inp([Hd, Tl | Stk], ['c' | Chs], Mat) :-
  parse_inp([[Hd | Tl] | Stk], Chs, Mat).

parse_inp(Stk, ['b' | Chs], Mat) :-
  parse_inp([0 | Stk], Chs, Mat).

parse_inp([Num | Stk], ['0' | Chs], Mat) :-
  NewNum is Num * 2,
  parse_inp([NewNum | Stk], Chs, Mat).

parse_inp([Num | Stk], ['1' | Chs], Mat) :-
  NewNum is (Num * 2) + 1,
  parse_inp([NewNum | Stk], Chs, Mat).

parse_inp([Mat], [], Mat).

vnew_trm(var(NumA), NumB) :-
  NumB is NumA + 1.

vnew_trm(fn(_, Trms), Num) :-
  maplist(vnew_trm, Trms, Nums),
  max_list([0 | Nums], Num).

vnew_atm(rl(_, Trms), Num) :-
  maplist(vnew_trm, Trms, Nums),
  max_list([0 | Nums], Num).

vnew_atm(eq(TrmA, TrmB), Num) :-
  vnew_trm(TrmA, NumA),
  vnew_trm(TrmB, NumB),
  max(NumA, NumB, Num).

vnew_lit(lit(_, Atm), Num) :-
  vnew_atm(Atm, Num).

vnew_cla(Cla, Num) :-
  maplist(vnew_lit, Cla, Nums),
  max_list([0 | Nums], Num).

offset(Ofs, Src, map(Src, var(Tgt))) :-
  Tgt is Src + Ofs.

union_list([], []).

union_list([Lst | Lsts], Un) :-
  union_list(Lsts, Tmp),
  union(Lst, Tmp, Un).

vars_trm(var(Num), [Num]).

vars_trm(fn(_, Trms), Nums) :-
  maplist(vars_trm, Trms, Numss),
  union_list(Numss, Nums).
  
vars_atm(rl(_, Trms), Nums) :-
  maplist(vars_trm, Trms, Numss),
  union_list(Numss, Nums).

vars_atm(eq(TrmA, TrmB), Nums) :-
  vars_trm(TrmA, NumsA),
  vars_trm(TrmB, NumsB),
  union(NumsA, NumsB, Nums).

vars_lit(lit(_, Atm), Nums) :-
  vars_atm(Atm, Nums).

vars_cla(Cla, Nums) :-
  maplist(vars_lit, Cla, Numss),
  union(Numss, Nums).

disjoiner(Cla1, Cla2, Dsj) :-
  vnew_cla(Cla2, Num),
  vars_cla(Cla1, Nums),
  maplist(offset(Num), Nums, Dsj).

compose_maps(FstMaps, SndMaps, Maps) :-
  update_maps(FstMaps, SndMaps, NewFstMaps),
  append(NewFstMaps, SndMaps, Maps).

src(Num, map(Num, _)).

rm_red_maps([], []).

rm_red_maps([map(Num, Trm) | Maps], [map(Num, Trm) | NewMaps]) :- 
  exclude(src(Num), Maps, TmpMaps),
  rm_red_maps(TmpMaps, NewMaps).

idmap(map(Num, var(Num))).

compress_maps(Maps, NewMaps) :-
  rm_red_maps(Maps, TmpMaps),
  exclude(idmap, TmpMaps, NewMaps).

update_map(Map, map(Src, Tgt), map(Src, NewTgt)) :-
  subst_trm(Map, Tgt, NewTgt).

update_maps(FstMaps, SndMaps, NewFstMaps) :-
  maplist(update_map(SndMaps), FstMaps, NewFstMaps).

rep_trm(SrcTrm, TrmA, TrmB, TgtTrm, Rpl) :-
  unif_trm(SrcTrm, TrmA, RplA),
  subst_trm(RplA, TrmB, TrmB1),
  inst_trm(TrmB1, TgtTrm, RplB),
  compose_maps(RplA, RplB, Rpl).

rep_trm(var(Num), _, _, TgtTrm, [map(Num, TgtTrm)]).

rep_trm(fn(Num, SrcTrms), TrmA, TrmB, fn(Num, TgtTrms), Rpl) :- 
  rep_trms(SrcTrms, TrmA, TrmB, TgtTrms, Rpl).

rep_trms([], _, _, [], []).

rep_trms([SrcTrm | SrcTrms], TrmA, TrmB, [TgtTrm | TgtTrms], Rpl) :- 
  rep_trm(SrcTrm, TrmA, TrmB, TgtTrm, Rpl1), 
  maplist(subst_trm(Rpl1), SrcTrms, SrcTrms1),
  subst_trm(Rpl1, TrmA, TrmA1),
  subst_trm(Rpl1, TrmB, TrmB1),
  rep_trms(SrcTrms1, TrmA1, TrmB1, TgtTrms, Rpl2), 
  compose_maps(Rpl1, Rpl2, Rpl).

rep_atm(eq(SrcTrmA, SrcTrmB), TrmA, TrmB, eq(TgtTrmA, TgtTrmB), Rpl) :- 
  rep_trm(SrcTrmA, TrmA, TrmB, TgtTrmA, RplA), 
  subst_trm(RplA, SrcTrmB, SrcTrmB1),
  subst_trm(RplA, TrmA, TrmA1),
  subst_trm(RplA, TrmB, TrmB1),
  rep_trm(SrcTrmB1, TrmA1, TrmB1, TgtTrmB, RplB), 
  compose_maps(RplA, RplB, Rpl).

rep_atm(rl(Num, SrcTrms), TrmA, TrmB, rl(Num, TgtTrms), Rpl) :- 
  rep_trms(SrcTrms, TrmA, TrmB, TgtTrms, Rpl).

unif_trms([], [], []).

unif_trms([TrmA | TrmsA], [TrmB | TrmsB], Maps) :-
  unif_trm(TrmA, TrmB, FstMaps),
  subst_trms(FstMaps, TrmsA, TrmsA1),
  subst_trms(FstMaps, TrmsB, TrmsB1),
  unif_trms(TrmsA1, TrmsB1, SndMaps),
  compose_maps(FstMaps, SndMaps, Maps).

unif_trm(var(Num), Trm, [map(Num, Trm)]).

unif_trm(Trm, var(Num), [map(Num, Trm)]).

unif_trm(fn(Num, TrmsA), fn(Num, TrmsB), Maps) :- 
  unif_trms(TrmsA, TrmsB, Maps).

unif_atm(rl(Num, TrmsA), rl(Num, TrmsB), Maps) :- 
  unif_trms(TrmsA, TrmsB, Maps).

unif_atm(eq(TrmAL, TrmAR), eq(TrmBL, TrmBR), Maps) :-
  unif_trm(TrmAL, TrmBL, FstMaps),
  subst_trm(FstMaps, TrmAR, TrmAR1),
  subst_trm(FstMaps, TrmBR, TrmBR1),
  unif_trm(TrmAR1, TrmBR1, SndMaps),
  compose_maps(FstMaps, SndMaps, Maps).

range(0, Acc, Acc).

range(Num, Acc, Nums) :-
  0 < Num,
  NewNum is Num - 1,
  range(NewNum, [NewNum | Acc], Nums).

range(Num, Nums) :-
  range(Num, [], Nums).

member_rev(Lst, Elm) :- member(Elm, Lst).

merge_instantiators([], Inst, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, Inst) :-
  member(map(Idx, Tgt), Inst2),
  merge_instantiators(Inst1, Inst2, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, [map(Idx, Tgt) | Inst]) :-
  not(member(map(Idx, _), Inst2)),
  merge_instantiators(Inst1, Inst2, Inst).

inst_trms([], [], []).

inst_trms([SrcTrm | SrcTrms], [TgtTrm | TgtTrms], Maps) :-
  inst_trm(SrcTrm, TgtTrm, Maps1),
  inst_trms(SrcTrms, TgtTrms, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

inst_trm(var(Num), Trm, [map(Num, Trm)]).

inst_trm(fn(Num, SrcTrms), fn(Num, TgtTrms), Maps) :-
  inst_trms(SrcTrms, TgtTrms, Maps).

inst_atm(rl(Num, SrcTrms), rl(Num, TgtTrms), Maps) :-
  inst_trms(SrcTrms, TgtTrms, Maps).

inst_atm(eq(SrcTrmA, SrcTrmB), eq(TgtTrmA, TgtTrmB), Maps) :-
  inst_trm(SrcTrmA, TgtTrmA, Maps1),
  inst_trm(SrcTrmB, TgtTrmB, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

choose_map_atm(SrcAtm, TgtAtm, Maps) :- 
  inst_atm(SrcAtm, TgtAtm, Maps).

choose_map_atm(eq(TrmA, TrmB), TgtAtm, Maps) :- 
  inst_atm(eq(TrmB, TrmA), TgtAtm, Maps).

choose_map_lit(lit(Pol, SrcAtm), lit(Pol, TgtAtm), Maps) :-
  choose_map_atm(SrcAtm, TgtAtm, Maps).

choose_map_cla([], _, [], []).

choose_map_cla([Lit | Cla], Tgt, Maps, [LitNum | ClaNums]) :-
  nth0(LitNum, Tgt, TgtLit),
  choose_map_lit(Lit, TgtLit, LitMaps),
  choose_map_cla(Cla, Tgt, ClaMaps, ClaNums),
  merge_instantiators(LitMaps, ClaMaps, Maps).

surjective(Ran, Nums) :-
  length(Ran, Lth),
  range(Lth, Idxs),
  subset(Idxs, Nums).

count(_, [], 0).

count(Elm, [Elm | Lst], Cnt) :-
  count(Elm, Lst, Tmp),
  Cnt is Tmp + 1.

count(Elm, [Hd | Lst], Cnt) :-
  not(Elm = Hd),
  count(Elm, Lst, Cnt).

dup_idxs([Hd | Tl], 0, Idx) :-
  nth1(Idx, Tl, Hd).

dup_idxs([_ | Tl], IdxA, IdxB) :-
  dup_idxs(Tl, SubIdxA, SubIdxB),
  IdxA is SubIdxA + 1,
  IdxB is SubIdxB + 1.

conc(asm(_, Cnc), Cnc).
conc(rsl(_, _, Cnc), Cnc).
conc(rtt(_, _, Cnc), Cnc).
conc(cnt(_, Cnc), Cnc).
conc(sub(_, _, Cnc), Cnc).
conc(rep(_, _, Cnc), Cnc).
conc(sym(_, Cnc), Cnc).
conc(trv(_, Cnc), Cnc).

allign_eq(Prf, Prf) :-
  conc(Prf, [Lit, Lit | _]).

allign_eq(SubPrf, Prf) :-
  conc(SubPrf, [lit(Pol, eq(TrmA, TrmB)), lit(Pol, eq(TrmB, TrmA)) | Cnc]),
  Prf = sym(SubPrf, [lit(Pol, eq(TrmB, TrmA)), lit(Pol, eq(TrmB, TrmA)) | Cnc]).

compile_cnts(Prf, Dsts, Prf) :-
  not(dup_idxs(Dsts, _, _)).

compile_cnts(SubPrf, Dsts, Prf) :-
  dup_idxs(Dsts, IdxA, IdxB),
  conc(SubPrf, SubCnc),
  tor(SubCnc, IdxA, SubCnc1),
  SubPrf1 = rtt(IdxA, SubPrf, SubCnc1),
  tor(SubCnc1, IdxB, [Lit1, Lit2 | SubCnc2]),
  SubPrf2 = rtt(IdxB, SubPrf1, [Lit1, Lit2 | SubCnc2]),
  allign_eq(SubPrf2, SubPrf3),
  conc(SubPrf3, [Lit, Lit | SubCnc3]),
  SubPrf4 = cnt(SubPrf3, [Lit | SubCnc3]),
  tor(Dsts,  IdxA, Dsts1),
  tor(Dsts1, IdxB, [Dst, Dst | Dsts2]),
  compile_cnts(SubPrf4, [Dst | Dsts2], Prf).

compute_maps(Cla, Tgt, Maps, Nums) :-
  choose_map_cla(Cla, Tgt, Maps, Nums),
  surjective(Tgt, Nums).

compile_map(SubPrf, Tgt, Prf) :-
  conc(SubPrf, SubCnc),
  compute_maps(SubCnc, Tgt, Inst, Nums),
  subst_cla(Inst, SubCnc, SubCnc1),
  compile_cnts(sub(Inst, SubPrf, SubCnc1), Nums, Prf).

rep_lit(lit(Pol, SrcAtm), TrmA, TrmB, lit(Pol, TgtAtm), Rpl) :-
  rep_atm(SrcAtm, TrmA, TrmB, TgtAtm, Rpl). 

compile_rep_core(PrfA, PrfB, Tgt, Prf) :-
  conc(PrfA, CncA),
  CncA = [LitA | _],
  conc(PrfB, CncB),
  CncB = [lit(pos, eq(TrmA, TrmB)) | _],
  member(LitB, Tgt),
  rep_lit(LitA, TrmA, TrmB, LitB, Rpl), 
  subst_cla(Rpl, CncA, CncA1),
  PrfA1 = sub(Rpl, PrfA, CncA1),
  subst_cla(Rpl, CncB, CncB1),
  PrfB1 = sub(Rpl, PrfB, CncB1),
  CncA1 = [_ | TlA],
  CncB1 = [_ | TlB],
  append(TlA, TlB, Tl),
  compile_map(rep(PrfA1, PrfB1, [LitB | Tl]), Tgt, Prf).

select_dir(Prf, Prf).

select_dir(Prf, sym(Prf, [lit(Pol, eq(TrmB, TrmA)) | Cnc])) :-
  conc(Prf, [lit(Pol, eq(TrmA, TrmB)) | Cnc]).

select_rot(Prf, rtt(Num, Prf, NewCnc)) :- 
  conc(Prf, Cnc),
  tor(Cnc, Num, NewCnc).

select_lit(Prf, NewPrf) :-
  select_rot(Prf, TmpPrf),
  select_dir(TmpPrf, NewPrf).

compile_rep(PrfA, PrfB, Tgt, Prf) :-
  conc(PrfA, CncA),
  conc(PrfB, CncB),
  disjoiner(CncB, Tgt, DsjB),
  subst_cla(DsjB, CncB, CncB1),
  PrfB1 = sub(DsjB, PrfB, CncB1),
  disjoiner(CncA, CncB1, DsjA),
  subst_cla(DsjA, CncA, CncA1),
  PrfA1 = sub(DsjA, PrfA, CncA1),
  select_lit(PrfA1, PrfA2), 
  select_lit(PrfB1, PrfB2), 
  compile_rep_core(PrfA2, PrfB2, Tgt, Prf).

compile_rsl(PrfA, PrfB, rsl(PrfA2, PrfB1, Cnc)) :-
  conc(PrfA, CncA),
  CncA = [lit(neg, _) | _],
  conc(PrfB, CncB),
  CncB = [lit(pos, AtmB) | _],
  disjoiner(CncA, CncB, Dsj),
  subst_cla(Dsj, CncA, CncA1),
  CncA1 = [lit(neg, AtmA) | _],
  PrfA1 = sub(Dsj, PrfA, CncA1),
  unif_atm(AtmA, AtmB, Unf),
  subst_cla(Unf, CncA1, CncA2),
  CncA2 = [lit(neg, Atm) | ClaA2],
  PrfA2 = sub(Unf, PrfA1, CncA2),
  subst_cla(Unf, CncB, CncB1),
  CncB1 = [lit(pos, Atm) | ClaB1],
  PrfB1 = sub(Unf, PrfB, CncB1),
  append(ClaA2, ClaB1, Cnc).

compile(Mat, _, Tgt, asm, Prf) :-
  nth0(Num, Mat, Cla),
  compile_map(asm(Num, Cla), Tgt, Prf).

compile(Mat, Lns, Tgt, rsl(NumA, NumB), Prf) :-
  compile(Mat, Lns, NumA, PrfA),
  compile(Mat, Lns, NumB, PrfB),
  conc(PrfA, CncA),
  conc(PrfB, CncB),
  tor(CncA, IdxA, CncA1),
  tor(CncB, IdxB, CncB1),
  PrfA1 = rtt(IdxA, PrfA, CncA1),
  PrfB1 = rtt(IdxB, PrfB, CncB1),
  ( compile_rsl(PrfA1, PrfB1, SubPrf) ;
    compile_rsl(PrfB1, PrfA1, SubPrf) ),
  compile_map(SubPrf, Tgt, Prf).

compile(Mat, Lns, Tgt, rep(NumA, NumB), Prf) :-
  compile(Mat, Lns, NumA, PrfA),
  compile(Mat, Lns, NumB, PrfB),
  compile_rep(PrfA, PrfB, Tgt, Prf).

compile(Mat, Lns, Tgt, eqres(Num), Prf) :-
  compile(Mat, Lns, Num, Prf1),
  conc(Prf1, Cnc1),
  tor(Cnc1, Idx, Cnc2), 
  Cnc2 = [lit(neg, eq(TrmA, TrmB)) | _],
  Prf2 = rtt(Idx, Prf1, Cnc2),
  unif_trm(TrmA, TrmB, Unf),
  subst_cla(Unf, Cnc2, Cnc3),
  Cnc3 = [lit(neg, eq(Trm, Trm)) | Tl],
  Prf3 = sub(Unf, Prf2, Cnc3),
  Prf4 = trv(Prf3, Tl),
  compile_map(Prf4, Tgt, Prf).

compile(Mat, Lns, Tgt, trv(Num), trv(Prf, Tgt)) :-
  compile(Mat, Lns, Num, Prf),
  conc(Prf, [lit(neg, eq(Trm, Trm)) | Tgt]).

compile(Mat, Lns, Tgt, map(Num), Prf) :-
  compile(Mat, Lns, Num, SubPrf),
  compile_map(SubPrf, Tgt, Prf).

compile(Mat, Lns, Num, Prf) :-
  member(line(Num, Tgt, Rul), Lns),
  compile(Mat, Lns, Tgt, Rul, Prf).

compress(asm(Num, Cla), asm(Num, Cla)).

compress(rtt(0, Prf, _), NewPrf) :-
  compress(Prf, NewPrf).

compress(rtt(Num, Prf, Cla), rtt(Num, NewPrf, Cla)) :-
  0 < Num,
  compress(Prf, NewPrf).

compress(rsl(PrfA, PrfB, Cla), rsl(NewPrfA, NewPrfB, Cla)) :-
  compress(PrfA, NewPrfA),
  compress(PrfB, NewPrfB).

compress(sub(Maps, Prf, Cla), NewPrf) :-
  ( compress_maps(Maps, []), compress(Prf, NewPrf) ) ; 
  ( compress_maps(Maps, NewMaps), 
    compress(Prf, TmpPrf), 
    NewPrf = sub(NewMaps, TmpPrf, Cla) ).

compress(rep(PrfA, PrfB, Cla), rep(NewPrfA, NewPrfB, Cla)) :-
  compress(PrfA, NewPrfA),
  compress(PrfB, NewPrfB).

compress(trv(Prf, Cla), trv(NewPrf, Cla)) :-
  compress(Prf, NewPrf).

compress(sym(Prf, Cla), sym(NewPrf, Cla)) :-
  compress(Prf, NewPrf).

compress(cnt(Prf, Cla), cnt(NewPrf, Cla)) :-
  compress(Prf, NewPrf).

relevant(Vars, map(Num, _)) :-
  member(Num, Vars).

filter_maps(Prf, Maps, NewMaps) :-
  conc(Prf, Cnc),
  vars_cla(Cnc, Vars),
  include(relevant(Vars), Maps, NewMaps).

compile(Mat, Lns, Prf) :-
  length(Lns, Lth),
  Idx is Lth - 1,
  nth0(Idx, Lns, line(_, [], Rul)),
  compile(Mat, Lns, [], Rul, Prf).

compile(Mat, Lns, compile_error(Mat, Lns)).

string_block(Str, Blk) :-
  break_string(60, Str, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Blk).

trms_string(Trms, Str) :-
  maplist(trm_string, Trms, TrmStrs),
  tuple_string(TrmStrs, Str).

trm_string(var(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("X", NumStr, Str).

trm_string(fn(Num, Trms), Str) :-
  number_string(Num, NumStr),
  trms_string(Trms, TrmsStr),
  join_string(["f", NumStr, TrmsStr], Str).

atm_string(rl(Num, Trms), Str) :-
  number_string(Num, NumStr),
  trms_string(Trms, TrmsStr),
  join_string(["r", NumStr, TrmsStr], Str).

atm_string(eq(TrmA, TrmB), Str) :-
  trm_string(TrmA, StrA),
  trm_string(TrmB, StrB),
  join_string(["(", StrA, " = ", StrB, ")"], Str).

lit_string(lit(pos, Atm), Str) :-
  atm_string(Atm, Str).

lit_string(lit(neg, Trm), Str) :-
  trm_string(Trm, Str1),
  string_concat("-", Str1, Str).

map_string(map(Num, Trm), Str) :-
  number_string(Num, NumStr),
  trm_string(Trm, TrmStr),
  join_string([NumStr, " |-> ", TrmStr], Str).

list_string(ItemString, Lst, Str) :-
  maplist(ItemString, Lst, Strs),
  join_string(Strs, ", ", TmpStr),
  join_string(["[", TmpStr, "]"], Str).

cla_string(Cla, Str) :-
  list_string(lit_string, Cla, Str).

maps_string(Maps, Str) :-
  list_string(map_string, Maps, Str).

proof_string(Spcs, asm(Num, Cnc), Str) :-
  number_string(Num, NumStr),
  cla_string(Cnc, CncStr),
  join_string([Spcs, "asm ", NumStr, " : ", CncStr], Str).

proof_string(Spcs, rsl(PrfA, PrfB, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  proof_string(NewSpcs, PrfB, StrB),
  string_codes(Nl, [10]),
  join_string([Spcs, "rsl : ", CncStr, Nl, StrA, Nl, StrB], Str).

proof_string(Spcs, sub(Maps, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  maps_string(Maps, MapsStr),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  string_codes(Nl, [10]),
  join_string([Spcs, "sub : ", CncStr, Nl, NewSpcs, MapsStr, Nl, StrA], Str).

proof_string(Spcs, rtt(Num, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  number_string(Num, NumStr),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rtt ", NumStr, " : ", CncStr, Nl, StrA], Str).

proof_string(Spcs, cnt(PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "cnt : ", CncStr, Nl, StrA], Str).

proof_string(Prf, Str) :-
  proof_string("", Prf, Str).

proof_string(Prf, print_error(Prf)).

temp_loc("/var/tmp/temp_goal_file").

line_string(line(Num, Cla, Rul), Str) :-
  number_string(Num, NumStr),
  cla_string(Cla, ClaStr),
  term_string(Rul, RulStr),
  join_string([NumStr, ". ", ClaStr, " [", RulStr, "]"], Str).

lines_string(Lns, Str) :-
  maplist(line_string, Lns, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Str).

linearize_trms([], "n").

linearize_trms([Trm | Trms], Str) :-
  linearize_trms(Trms, TrmsStr),
  linearize_trm(Trm, TrmStr),
  join_string([TrmsStr, TrmStr, "c"], Str).

linearize_trm(var(Num), Str) :-
  number_binstr(Num, NumStr),
  join_string(["b", NumStr, "v"], Str).

linearize_trm(fn(Num, Trms), Str) :-
  number_binstr(Num, NumStr),
  linearize_trms(Trms, TrmsStr), 
  join_string([TrmsStr, "b", NumStr, "f"], Str).

linearize_maps([], "n").

linearize_maps([map(Num, Trm) | Maps], Str) :-
  number_binstr(Num, NumStr),
  linearize_trm(Trm, TrmStr),
  linearize_maps(Maps, SubStr),
  join_string([SubStr, TrmStr, "b", NumStr, "mc"], Str).

linearize_prf(asm(Num, _), Str) :-
  number_binstr(Num, NumStr),
  join_string(["b", NumStr, "H"], Str).

linearize_prf(rsl(PrfA, PrfB, _), Str) :-
  linearize_prf(PrfA, StrA),
  linearize_prf(PrfB, StrB),
  join_string([StrA, StrB, "R"], Str).

linearize_prf(rep(PrfA, PrfB, _), Str) :-
  linearize_prf(PrfA, StrA),
  linearize_prf(PrfB, StrB),
  join_string([StrA, StrB, "P"], Str).

linearize_prf(rtt(Num, Prf, _), Str) :-
  number_binstr(Num, NumStr),
  linearize_prf(Prf, PrfStr),
  join_string([PrfStr, "b", NumStr, "T"], Str).

linearize_prf(sub(Maps, Prf, _), Str) :-
  linearize_maps(Maps, MapsStr),
  linearize_prf(Prf, PrfStr),
  join_string([PrfStr, MapsStr, "S"], Str).

linearize_prf(sym(Prf, _), Str) :-
  linearize_prf(Prf, PrfStr),
  join_string([PrfStr, "Y"], Str).

linearize_prf(trv(Prf, _), Str) :-
  linearize_prf(Prf, PrfStr),
  join_string([PrfStr, "V"], Str).

linearize_prf(cnt(Prf, _), Str) :-
  linearize_prf(Prf, PrfStr),
  join_string([PrfStr, "C"], Str).

linearize_prf(_, "linearize_error").
 
main([Argv]) :-
  string_chars(Argv, Chs),
  parse_inp([], Chs, Mat),
  temp_loc(Loc),
  write_goal(Loc, Mat),
  read_proof(Loc, Lns),
  compile(Mat, Lns, RawPrf),
  compress(RawPrf, Prf),
  linearize_prf(Prf, RawStr),
  string_block(RawStr, Str),
  write(Str).
