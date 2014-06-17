% Implements an engine with parallel saturation construction.

:- module(par,
	  [
	   runParLgg/1
	  ]
	 ).

% import needed modules from GILPS
:- use_module('common', [generate_incremental_HypothesesAndTheory/1]).
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [id2example/2, exampleIDsWeights/2]).
:- use_module('../bottom clause/bottom_clause', [parallel_sat/7]).
:- use_module('../utils/list', [elemsAtPos/3, firstNElemsOf/3, n_randomElems/3, randomPairs/3, custom_qsort/3, numbersList/3]).
:- use_module('../messages/messages', [message/2]).
:- use_module('../bottom clause/lgg', [all_lgg/5]).
:- use_module('../bottom clause/clause_reduce', [negative_clause_reduce/8]).
:- use_module('progolem', [coverage_computation/11, best_clauses/2]).

% YAP modules
:- use_module(library(random), [randseq/3]).
:- use_module(library(lists), [nth/3, nth/4, reverse/2, flatten/2]).
:- use_module(library(apply_macros), [convlist/3, maplist/3]).
:- use_module(library(ordsets), [ord_subtract/3, ord_insert/3, ord_union/3]).

runParLgg( FileName) :-
    generate_incremental_HypothesesAndTheory(genHypFromExamples_incremental).

genHypFromExamples_incremental(PosEIDs, NegEIDs, APosEIDs, _TestFold, BestHyp) :-
    generate_parallel_seeds(PosEIDs, APosEIDs, NegEIDs, Seeds),
    best_clauses(Seeds, BestHyps),
%    BestHyps = [BestHyp | OtherHyps].
    iterate_until_best_clause(1, BestHyps, PosEIDs, APosEIDs, NegEIDs, (Score, NumLit, PosIdCov, NegIdCov, rlgg(core(_, _, _), clause(Clause, ClauseSig)))),
    BestHyp = (Score, Clause, ClauseSig, NumLit, PosIdCov, NegIdCov).

generate_parallel_seeds(TPosIds, APosIds, TNegIds, SeedClauses) :-
    setting(progolem_initial_pairs_sample, NumPairs),
    randomPairs(NumPairs, APosIds, Pairs),
    convlist(computePairedSat(TPosIds, TNegIds), Pairs, SeedClauses).

computePairedSat(PosEIDs, NegEIDs, (E1, E2), (Score, NumLits, PosIDCov, NegIDCov, rlgg(core(E1, [E2], Indexes), clause(RedClause, RedClauseSig)))) :-
    id2example(E1, Example1),
    id2example(E2, Example2),
    parallel_sat(Example1, Example2, mode(ground, *), Bottom1, Bottom2, Signature1, Signature2),
    all_lgg(Bottom1, Signature1, Bottom2, Clause, ClauseSig),
    !,
    sort([E1, E2], GenCPosEIDs),
    negative_clause_reduce(Clause, ClauseSig, PosEIDs, NegEIDs, RedClause, RedClauseSig, FPosIDCov, FNegIDCov),
%    trace,
    coverage_computation(0, RedClause, RedClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosIDCov, NegIDCov, _HypInfo, NumLits, Score),
    length(RedClause, NumLiterals),
    numbersList(1, NumLiterals, Indexes).

% TODO: THIS WILL NEED TO BE EXTENDED
extend_lgg(Iter, PosExampleIDs, APosEIDs, NegExampleIDs, ScoreThreshold, NumLits, ClauseInfo, NClauseTuples):-
  setting(progolem_iteration_sample_size, NumExamples),
  ClauseInfo=(_,_,PosIDsCov,_,rlgg(core(_,GenClausePosEIDs,_),clause(_,_))), % we only want to consider positive examples that are not already covered by the ARMG
  ord_union(PosIDsCov, GenClausePosEIDs, DisregardPosEIDs), % GenClausePosEIDs should be a subset of PosIDsCov but may not be if min_resolutions is low
  %DisregardPosEIDs=GenClausePosEIDs,
  ord_subtract(PosExampleIDs, DisregardPosEIDs, ExtendARMGPosIDs), % determine pos examples that may be used to extend the ARMG  
  n_randomElems(ExtendARMGPosIDs, NumExamples, SelectedARMGPosIDs),
  convlist(pos_clause_reduce(Iter, ScoreThreshold, NumLits, APosEIDs, NegExampleIDs, ClauseInfo), SelectedARMGPosIDs, NClauseTuples).

iterate_until_best_clause(Iter, CurrentClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, BestClauseInfo):-
  CurrentClausesInfo=[CurBestInfo|_],
  CurBestInfo=(Score, _NumLiterals, PosIDsCov, NegIDsCov, ARMG),
%  trace,
  message(best_rmg, [Iter, Score, ARMG, PosIDsCov, NegIDsCov]), %% UPDATE THIS, clause, GenPosEIDs by ARMG
  nextClauses(Iter, CurrentClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, NextClausesInfo),
  (NextClausesInfo=[] -> % no further best clauses
     BestClauseInfo=CurBestInfo
   ;
     Iter1 is Iter+1,
     iterate_until_best_clause(Iter1, NextClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, BestClauseInfo)
  ).

nextClauses(Iter, Clauses, TPosEIDs, APosEIDs, TNegEIDs, NClauses):-
	NClauses = [].
  % Clauses=[(HighestScore, NumLiterals, _, _, _)|_],%
  % maplist(extend_lgg(Iter, TPosEIDs, APosEIDs, TNegEIDs, HighestScore, NumLiterals), Clauses, SuccessorClauses),
  % flatten(SuccessorClauses, AllSuccessorClauses),
  % best_clauses(AllSuccessorClauses, NClauses).
