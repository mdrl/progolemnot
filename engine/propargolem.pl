%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-05-11
%
% Adaptations by Miha Drole.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Types:
%    ARMG: armg(core(SeedID, Ordered list of example ids used in its construction, % includes SeedID
%                    ListOfIndexs from  bottom clause of SeedID that constitute clause),
%               clause(Clause, ClauseSig))
%  ClauseInfo: tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(engine_propargolem,
           [
             runPropargolem/1
           ]
         ).

% GILPS modules
:- use_module('common', [generate_global_HypothesesAndTheory/2, generate_incremental_HypothesesAndTheory/1]).
:- use_module('../settings/settings', [setting/2, set/2]). % because of 'n' and 'k'
:- use_module('../bottom clause/bottom_clause', [sat/3, parallel_sat/7]).
:- use_module('../bottom clause/clause_reduce', [positive_clause_reduce/3, positiveClauseReduce/6, negative_clause_reduce/8, negative_clause_reduce/10, negative_clause_reduce_with_neg/8]).
:- use_module('../bottom clause/common_clause', [commonClause/4]).
:- use_module('../bottom clause/srmg', [create_srmg_heuristic_term/2, srmg/5, srmg/6, srmg/7]).
:- use_module('../examples/examples', [id2example/2, exampleIDsWeights/2, invertExamples/1]).
:- use_module('../hypotheses/score', [hypothesis_info/5, stop_score/1, score/3, verifies_partial_metrics/2, verifies_full_metrics/2]).
:- use_module('../hypotheses/coverage', [full_hypothesis_coverage/6, hypothesis_coverage/6]).
:- use_module('../utils/list', [elemsAtPos/3, firstNElemsOf/3, n_randomElems/3, randomPairs/3, custom_qsort/3, numbersList/3]).
:- use_module('../messages/messages', [message/2]).
:- use_module('../utils/clause', [prettyPrintLiterals/1, hypothesisBody/2, hypothesisHead/2]).
:- use_module('../theory/theory_constructor', [construct_incremental_theory/7, construct_incremental_theory/8]).

% YAP modules
:- use_module(library(lists), [nth/3, nth/4, reverse/2, flatten/2, append/3]).
:- use_module(library(apply_macros), [convlist/3, maplist/3]).
:- use_module(library(ordsets), [ord_subtract/3, ord_insert/3, ord_union/3]).
:- use_module(library(random), [randseq/3, setrand/1]).
:- use_module(library(rbtrees), [rb_new/1, rb_insert/4, rb_lookup/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_armg(+ExampleID, -ARMG)
%
% Given:
%  ExampleID: the example id to compute the starting ARMG)
% 
% Returns:
%  ARMG: the resulting armg, see armg type above
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_armg(ExampleID, armg(core(ExampleID, [ExampleID], Indexs), clause(Bottom, BottomSig))):-
  id2example(ExampleID, Example),
  sat(Example, Bottom, BottomSig),
  length(Bottom, NumLiterals),
  numbersList(1, NumLiterals, Indexs).

create_parsat(ExampleID, Example2ID, armg(core(ExampleID, [ExampleID], Indexs), clause(Bottom, BottomSig))):-
  id2example(ExampleID, Example),
  id2example(Example2ID, Example2),
  parallel_sat(Example, Example2, mode(variablized, default), Bottom, Example2Sat, BottomSig,  Example2Sig),
  length(Bottom, NumLiterals),
  numbersList(1, NumLiterals, Indexs).

%armg_core_to_clause(+core(SeedID, Remaining examples used in its construction, ListOfIndexs from SeedID), -Clause, -ClauseSig)
armg_core_to_clause(core(SeedID, _OtherConsIDs, IndexsFromSeed), Clause, ClauseSig):-
  id2example(SeedID, Example),
  sat(Example, Bottom, BottomSig), % this can be expensive if done often...
  elemsAtPos(Bottom, IndexsFromSeed, Clause),
  elemsAtPos(BottomSig, IndexsFromSeed, ClauseSig).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% runProgolem(+FileName)
%
% Given:
%   FileName: the filename to store the rated hypotheses and their coverages. If it's a variable it's ignored
%
% Displays the outcome of running Progolem in standard output, possibly saving the hypotheses (but not the theory)
% in FileName
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

runPropargolem(FileName):-
  (setting(theory_construction, global) ->
    generate_global_HypothesesAndTheory(genHypFromExample_global, FileName)
%    format("Progolem can only be executed in incremental theory construction mode.~n", [])
   ;
  %setting(theory_construction, incremental)
    generate_incremental_HypothesesAndTheory(genHypFromExample_incremental)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% genHypFromExample_global(+ExampleID, +TPosEIDs, +APosEIDs, +ANegEIDs, +MaxHypothesesPerExample, -Hypotheses)
%
% Given:
%   ExampleID: example id to process now
%   TPosEIDs: ordered list of positive example ids remaining (i.e. the subset from APosEIDs not yet considered)
%   APosEIDs: ordered list of all positive example ids (to possibly test for coverage)
%   ANegEIDs: ordered list of all negative example ids (to possibly test for coverage)
%   MaxHypothesesPerExample: maximum number of hypotheses an example may generate
%
% Returns:
%   Hypotheses: a list of tuples (hypothesis, hypothesis signature)
%
% Notes:
%   This is the main distinguisher between ILP systems: the way hypotheses are generated
%   Notice that Progolem only outputs one hypothesis per example!
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_global(ExampleID, _TPosEIDs, APosEIDs, ANegEIDs, _MaxHypothesesPerExample, Result):-
  create_armg(ExampleID, armg(Core, clause(Bottom, BottomSig))),
  %id2example(ExampleID, Example),
  %sat(Example, Bottom, BottomSig),
  write(Bottom),
  (hypothesis_score(Bottom, BottomSig, APosEIDs, ANegEIDs, NumLits, PosEIDsCov, NegEIDsCov, _HypInfo, Score) ->
     BottomClauseInfo=(Score, NumLits, PosEIDsCov, NegEIDsCov, armg(Core, clause(Bottom, BottomSig))),
     (setting(progolem_mode, reduce) ->
       ClauseInfo=BottomClauseInfo
      ;
       iterate_until_best_clause(1, [BottomClauseInfo], APosEIDs, APosEIDs, ANegEIDs, ClauseInfo)
     ),
     (negative_reduce(ClauseInfo, APosEIDs, ANegEIDs, BestHypothesis) ->
       BestHypothesis=(_Score, Hyp, HypSig, _NumLiterals, _PosIDsCov, _NegIDsCov),
       Result=[(Hyp,HypSig)]
     ;
       format("No compressive hypothesis~n",[]),
       Result=[] % no compressive hypothesis was found, don't waste time adding it
     )
   ;
    format("Bottom clause covers negatives~n",[]),%halt,
    Result=[] % bottom clause already covers negatives or no positives (may happen with noise, low recall or if min_resolutions is low)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% genHypFromExample_incremental(+TPosEIDs, +TNegEIDs, +APosEIDs, +TestFold, -BestHypothesis)
%
% Given:
%  TPosEIDs: ordered list of train positive examples id to generate best hypothesis from
%  TNegEIDs: ordered list of train negative examples id to generate best hypothesis from
%  APosEIDs: ordered list of all positive example ids of the current fold not yet entailed
%            (i.e. TPosEIDs plus the positive examples where one couldn't find compressive clauses)
%  TestFold: test fold
%
% Returns:
%   BestHypothesis: a tuple of the form (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                   (Hypothesis as a list of literals)
%
% Notes:
%   APosEIDs and ANegEIDs not strictly needed. Consider not using them later (they are here just because
%   the way theories are shown. they require the coverage to be known for train and test)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_incremental(TPosEIDs, TNegEIDs, APosEIDs, _TestFold, % review later the need for TestFold
                              BestHypothesis):-
    setting(max_neg_depth, MD),
    genHypFromExample_incremental(TPosEIDs, TNegEIDs, APosEIDs, _TestFold, BestHypothesis, MD).

genHypFromExample_incremental(TPosEIDs, TNegEIDs, APosEIDs, _TestFold, % review later the need for TestFold
                              BestHypothesis, Depth):-
  generate_seed_clauses(TPosEIDs, APosEIDs, TNegEIDs, SeedClauses, Depth),
  (setting(progolem_mode, reduce)->
      SeedClauses=[ClauseInfo]
    ;
      iterate_until_best_clause(1, SeedClauses, TPosEIDs, APosEIDs, TNegEIDs, ClauseInfo)
  ),
  negative_reduce(ClauseInfo, APosEIDs, TNegEIDs, BestHypothesis).


%generate_seed_clauses(+TPosEIDs, +APosEIDs, +TNegEIDs, -SeedClauses)
generate_seed_clauses(_, APosEIDs, TNegEIDs, SeedClauses, Depth):-
  setting(theory_construction, incremental),% pairs mode only applicable in incremental theory construction
  setting(progolem_mode, pairs),!,
  setting(progolem_initial_pairs_sample, NumPairs),
  message(compute_rmg_pairs, []),
  randomPairs(NumPairs, APosEIDs, Pairs),  
  convlist(rmg_pair_info(APosEIDs, TNegEIDs, Depth), Pairs, AllClausesInfo),
  best_clauses(AllClausesInfo, SeedClauses).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% rmg_pair_info(+PosExampleIDs, +NegExampleIDs, +(ExID1, ExID2), -ClauseInfo)
%
% Given:
%  PosExampleIDs: ordered list of positive example ids to consider for coverage
%  NegExampleIDs: ordered list of negative example ids to consider for coverage
%  ExID1: first example ID
%  ExID2: second example ID
%
% Returns:
%  ClauseInfo: tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% With negation enabled
rmg_pair_info(PosEIDs, NegEIDs, Depth, (ExID1, ExID2), (Score, NumLits, PosEIDsCov, NegEIDsCov, armg(Core, clause(Clause, ClauseSig), NewPredicate))):-
  Depth >= 0, % Check the depth / has it bottomed-out?
  ND is Depth - 1,
  setting(useneg, true),
  id2example(ExID1, Example1),
  id2example(ExID2, Example2),
  (setting(progolem_refinement_operator, armg) -> % This could be simplified
     create_parsat(ExID1, ExID2, ARMG1),
     positive_clause_reduce(ARMG1, ExID2, armg(CoreT, clause(ClauseT, ClauseSigT))) % = Compute the ARMG
  ;
     format("SRMGs not yet supported when we represent a clause as a list of indexs from the bottom~n", []),halt,
     create_srmg_heuristic_term(NegEIDs, SRMG_Heuristic),
     srmg(Example1, Example2, SRMG_Heuristic, Clause, ClauseSig)
  ),
  sort([ExID1, ExID2], GenCPosEIDs),
  coverage_computation_only(0, ClauseT, ClauseSigT, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCovT, NegEIDsCovT),
  length(NegEIDsCovT, NegCoverage),
  ((NegCoverage > 1) ->  % If it covers > 1 negative examples, do cws 
  (
    cws(ClauseT, ClauseSigT, GenCPosEIDs, PosEIDsCovT, NegEIDsCovT, PosEIDs, NegEIDs, [Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score], NewPredicate, ND)
   ;
   %NEGATION FAILED (!)
   [Clause, ClauseSig] = [ClauseT, ClauseSigT],
   coverage_computation(0, Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score)
   )
   ;
   % Not enough negative examples to negate.
   [Clause, ClauseSig] = [ClauseT, ClauseSigT],
   coverage_computation(0, Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score)
  ),
  message(rmg_pair, [Clause, Example1, Example2, ExID1, ExID2, (Score, NumLits, PosEIDsCov, NegEIDsCov)]).


%Without use of negation
rmg_pair_info(PosEIDs, NegEIDs, _, (ExID1, ExID2), (Score, NumLits, PosEIDsCov, NegEIDsCov, armg(Core, clause(Clause, ClauseSig), []))):-
  id2example(ExID1, Example1),
  id2example(ExID2, Example2),
  (setting(progolem_refinement_operator, armg) ->
     create_parsat(ExID1, ExID2, ARMG1),
     positive_clause_reduce(ARMG1, ExID2, armg(Core, clause(Clause, ClauseSig)))
  ;
     format("SRMGs not yet supported when we represent a clause as a list of indexs from the bottom~n", []),halt,
     create_srmg_heuristic_term(NegEIDs, SRMG_Heuristic),
     srmg(Example1, Example2, SRMG_Heuristic, Clause, ClauseSig)
  ),
  sort([ExID1, ExID2], GenCPosEIDs),
  coverage_computation(0, Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score),
  message(rmg_pair, [Clause, Example1, Example2, ExID1, ExID2, (Score, NumLits, PosEIDsCov, NegEIDsCov)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% coverage_computation(+IterationNum, +Clause, +ClauseSig, +GenCPosEIDs, +PosEIDs, +NegEIDs,
%                      -PosEIDsCov, -NegEIDsCov, -HypInfo, -NumLits, -Score)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

coverage_computation(IterNum, Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs,
                     PosEIDsCov, NegEIDsCov, HypInfo, NumLits, Score):-
  setting(progolem_bypass_coverage_iters, ByPassN),
  clauseLength(Clause, NumLits),
  (ByPassN>IterNum ->
     PosEIDsCov=GenCPosEIDs, NegEIDsCov=[],
     hypothesis_score_aux(PosEIDs, NegEIDs, NumLits, PosEIDsCov, NegEIDsCov, HypInfo, Score)
    ;
     hypothesis_score(Clause, ClauseSig, PosEIDs, NegEIDs, NumLits, PosEIDsCov, NegEIDsCov, HypInfo, Score)
  ).

coverage_computation_only(IterNum, Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs,
                     PosEIDsCov, NegEIDsCov):-
     hypothesis_coverage(Clause, ClauseSig, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% negative_reduce(+ClauseInfo, +TPosEIDs, +TNegEIDs, -BestHypothesis)
%
% Given:
%  ClauseInfo: a term of the form (CScore, CNumLiterals, CPosIDsCov, CNegIDsCov, ARMG)
%  TPosEIDs: ordered list of train positive example ids to consider for reduction
%  TNegEIDs: ordered list of train negative example ids to consider for reduction
%
% Returns:
%   BestHypothesis: a tuple of the form (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                   (Hypothesis as a list of literals)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

negative_reduce((CScore, _CNumLiterals, CPosIDsCov, CNegIDsCov, armg(_Core, clause(CClause, CClauseSig), _AuxClauses)),
                TPosEIDs, TNegEIDs,
                (FScore, FClause, FClauseSig, FNumLiterals, FPosEIDsCov, FNegEIDsCov, _AuxClauses)):-
  message(before_neg_reduction, [CClause, CClauseSig, CScore, CPosIDsCov, CNegIDsCov]),
%  negative_clause_reduce_with_neg(CClause, CClauseSig, TPosEIDs, TNegEIDs, FClause, FClauseSig, FPosEIDsCov, FNegEIDsCov)
  negative_clause_reduce(CClause, CClauseSig, TPosEIDs, TNegEIDs, FClause, FClauseSig, FPosEIDsCov, FNegEIDsCov),
  hypothesis_info(FPosEIDsCov, FNegEIDsCov, TPosEIDs, TNegEIDs, HypInfo),
  clauseLength(FClause, FNumLiterals),
  stop_criteria(FClause, FClauseSig, FNumLiterals, HypInfo, FScore).

negative_reduce((CScore, _CNumLiterals, CPosIDsCov, CNegIDsCov, armg(_Core, clause(CClause, CClauseSig))),
                TPosEIDs, TNegEIDs,
                (FScore, FClause, FClauseSig, FNumLiterals, FPosEIDsCov, FNegEIDsCov)):-
  message(before_neg_reduction, [CClause, CClauseSig, CScore, CPosIDsCov, CNegIDsCov]),
%  negative_clause_reduce_with_neg(CClause, CClauseSig, TPosEIDs, TNegEIDs, FClause, FClauseSig, FPosEIDsCov, FNegEIDsCov),
  negative_clause_reduce(CClause, CClauseSig, TPosEIDs, TNegEIDs, FClause, FClauseSig, FPosEIDsCov, FNegEIDsCov),
  hypothesis_info(FPosEIDsCov, FNegEIDsCov, TPosEIDs, TNegEIDs, HypInfo),
  clauseLength(FClause, FNumLiterals),
  stop_criteria(FClause, FClauseSig, FNumLiterals, HypInfo, FScore).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% stop_criteria(+Clause, +ClauseSig, +NumLiterals, +HypInfo, -Score)
%
% Given:
%   Clause: as a list of literals
%   ClauseSig: Clause's signature
%   NumLiterals: an integer
%   HypInfo: a list with 4 integers: [TP, FP, FN, TN]
%
% Succeeds if clause has positive compression, otherwise fails
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

stop_criteria(Clause, ClauseSig, NumLiterals, [TP, FP, FN, TN], Score):-
  score(NumLiterals, [TP, FP, FN, TN], Score),
  message(after_neg_reduction, [Clause, ClauseSig, Score, NumLiterals, TP, FP]),
  (verifies_full_metrics(NumLiterals, [TP, FP, FN, TN]) ->
    true
   ;
    message(no_good_clause, [TP, FP, FN, TN, Score]),
    fail
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% iterate_until_best_clause(+Iteration, +CurrentClausesInfo, +TPosEIDs, +APosEIDs, +TNegEIDs, -BestClauseInfo)
%
% Given:
%   Iteration: an integer specifying the current iteration
%   CurrentClausesInfo: list of tuples (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%   TPosEIDs: ordered list of train positive example ids available for ARMG
%   APosEIDs: ordered list of train positive example ids available for coverage (same as above, plus non
%              compressive ones from previous iterations)
%   TNegEIDs: ordered list of train negative example ids
%
% Returns:
%   BestClauseInfo: the highest scoring clause info (no further refinement yields a better one)
%                   It's a tuple of the form (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

iterate_until_best_clause(Iter, CurrentClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, BestClauseInfo):-
  CurrentClausesInfo=[CurBestInfo|_],
  CurBestInfo=(Score, _NumLiterals, PosIDsCov, NegIDsCov, ARMG),
  message(best_rmg, [Iter, Score, ARMG, PosIDsCov, NegIDsCov]), %% UPDATE THIS, clause, GenPosEIDs by ARMG
  nextClauses(Iter, CurrentClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, NextClausesInfo),
  (NextClausesInfo=[] -> % no further best clauses
     BestClauseInfo=CurBestInfo
   ;
     Iter1 is Iter+1,
     iterate_until_best_clause(Iter1, NextClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, BestClauseInfo)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% nextClauses(+Iter, +ClausesInfo, +TPosEIDs, +APosEIDs, +TNegEIDs, -NextClausesInfo)
%
% Given:
%   Iter: iteration number
%   ClausesInfo: a list of up to 'n' (user parameter) clauses info. Each is a tuple of the form
%            (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%   TPosEIDs: ordered list of positive examples used for training (i.e. considered for extending ARMG and coverage)
%   APosEIDs: ordered list of train positive example ids available for coverage (same as above, plus non
%              compressive ones from previous iterations)
%   TNegEIDs: ordered list of negative examples used for training (i.e. considered for coverage)
%
% Returns:
%   NextClauses: a list of up to 'n' clauses (ClausesInfo format). Each clause must have higher score than
%                the highest score in ClausesInfo
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

nextClauses(Iter, Clauses, TPosEIDs, APosEIDs, TNegEIDs, NClauses):-
  Clauses=[(HighestScore, NumLiterals, _, _, _ARMG)|_],%
  maplist(extend_clause_rmg(Iter, TPosEIDs, APosEIDs, TNegEIDs, HighestScore, NumLiterals), Clauses, SuccessorClauses),
  flatten(SuccessorClauses, AllSuccessorClauses),
  best_clauses(AllSuccessorClauses, NClauses).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% extend_clause_rmg(+Iter, +PosEIDs, +APosEIDs, +NegEIDs, +ScoreThreshold, +NumLiterals, +ClauseInfo, -NClauseTuples)
%
% Given:
%  Iter: iteration number
%  PosEIDs: list of positive example ids to consider for coverage
%  APosEIDs: ordered list of train positive example ids available for coverage (same as above, plus non
%            compressive ones from previous iterations)
%  NegEIDs: list of negative example ids to consider for coverage
%  ScoreThreshold: all NClauseTuples must be above this score
%  NumLiterals: number of literals of the score with score ScoreThreshold
%  ClauseInfo: tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
% Returns:
%  NClauseTuple: successors of ClauseInfo, each of the same form as ClauseInfo
%                they are ClauseTuple with ARMG extended by one extra positive example from PosExampleIDs but
%                not in GenClausePosEIDs
%
% Notes:
%  Only clauses with scores higher than the highest in ClauseTuples appear in NClauseTuple
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

extend_clause_rmg(Iter, PosExampleIDs, APosEIDs, NegExampleIDs, ScoreThreshold, NumLits, ClauseInfo, NClauseTuples):-
  setting(progolem_iteration_sample_size, NumExamples),
  ClauseInfo=(_,_,PosIDsCov,_,armg(core(_,GenClausePosEIDs,_),clause(_,_),_)), % we only want to consider positive examples that are not already covered by the ARMG
  ord_union(PosIDsCov, GenClausePosEIDs, DisregardPosEIDs), % GenClausePosEIDs should be a subset of PosIDsCov but may not be if min_resolutions is low
  %DisregardPosEIDs=GenClausePosEIDs,
  ord_subtract(PosExampleIDs, DisregardPosEIDs, ExtendARMGPosIDs), % determine pos examples that may be used to extend the ARMG  
  n_randomElems(ExtendARMGPosIDs, NumExamples, SelectedARMGPosIDs),
  convlist(pos_clause_reduce(Iter, ScoreThreshold, NumLits, APosEIDs, NegExampleIDs, ClauseInfo), SelectedARMGPosIDs, NClauseTuples).

%pos_clause_reduce(+IterNum, +ScoreThreshold, +NumLitsThreshold, +PosExampleIDs, +NegExampleIDs, +ClauseInfo, +PosEID2Reduce,
%                  -NextClauseInfo)
pos_clause_reduce(Iter, ScoreThreshold, NumLitsThreshold, PosEIDs, NegEIDs, (_, _, _, _, ARMG),
                  PosEID2Reduce, (Score, NumLiterals, PosEIDsCov, NegEIDsCov, NARMG)):-
  ARMG=armg(core(_, GenEIDs, _), clause(Clause, ClauseSignature), _AuxClause),
  id2example(PosEID2Reduce, PosExample),
  (setting(progolem_refinement_operator, armg) ->
     positive_clause_reduce(ARMG, PosEID2Reduce, armg(core(SeedID, NGenEIDs, Indexs), clause(Clause1, Clause1Sig))),
     %positiveClauseReduce(Clause, ClauseSignature, PosEID2Reduce, _FailProfile, NClause1, NClauseSignature1),
     setting(progolem_negative_sample_per_iteration, NegSample),
     (NegSample=0 ->
       NClause=Clause1,
       NClauseSignature=Clause1Sig,
       NARMG=armg(core(SeedID, NGenEIDs, Indexs), clause(NClause, NClauseSignature), _AuxClause)
      ;
       n_randomElems(NegEIDs, NegSample, SampleNegEIDs),
% negative_reduce(+ClauseInfo, TPosEIDs, +TNegEIDs, -BestHypothesis)
%
% Given:
%  ClauseInfo: a term of the form (CScore, CNumLiterals, CPosIDsCov, CNegIDsCov, ARMG)
       format("Negative reduction at each iteration is not yet supported when we represent a clause as a list of indexs from the bottom~n", []),halt,
       negative_clause_reduce(NClause1, NClauseSignature1, PosEIDs, SampleNegEIDs, NClause, NClauseSignature, _PosEIDsCov, _NegEIDsCov),
       NARMG=armg(core(SeedID, NGenEIDs, Indexs), clause(NClause1, NClauseSignature1), _AuxClause)
       %Note: when we do negative reduction of a small sample it is possible that we prune away more literals than we should
       % and thus getting an inconsistent clause with respect to the noise setting
     )     
   ;
     format("SRMGs are not yet supported when we represent a clause as a list of indexs from the bottom~n", []),halt,
     create_srmg_heuristic_term(NegEIDs, SRMG_Heuristic),
     srmg(Clause, ClauseSignature, PosExample, SRMG_Heuristic, NClause, NClauseSignature),
     ord_insert(GenEIDs, PosEID2Reduce, NGenEIDs),
     NARMG=armg(core(SeedID, NGenEIDs, Indexs), clause(NClause, NClauseSignature), _AuxClause)
  ),
%  format("PosEIDs:~w, NegEIDs:~w~n", [PosEIDs, NegEIDs]),
  coverage_computation(Iter, NClause, NClauseSignature, NGenEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov,
                       HypInfo, NumLiterals, Score),
  message(extended_rmg, [PosExample, PosEID2Reduce, GenEIDs, NumLiterals, Score, HypInfo]),
  compareClause(>, (Score, NumLiterals, _, _, _), (ScoreThreshold, NumLitsThreshold, _, _, _)).
%  format("Score: ~w NumLiterals: ~w Threshold: ~w~n", [Score, NumLiterals, ScoreThreshold]),

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compareClause(-Compare, +ClauseScoreInfo1, -ClauseScoreInfo2)
%
% Given:
%  ClauseScoreInfo1: a tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%  ClauseScoreInfo2: a tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
% Returns:
%  Compare: either '=' if the ClauseScores are identical
%                  '>' if first score is better than second
%                  '<' if second score is better than first
%
% Notes:
%   A ClauseScore is better than other if the score is higher, or if is equal but has less literals
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compareClause(>, (S1, _, _, _, _), (S2, _, _, _, _)):- S1>S2,!.
compareClause(>, (S, L1, _, _, _), (S, L2, _, _, _)):-
  ( (setting(evalfn, compression);setting(evalfn, compression_ratio)) ->
       L1>L2 % if compression or compression ratio are the metrics then, for the same score, we prefer longer clauses
     ;
       L1<L2 % otherwise, for the same score, we prefer shorter clauses
  ),
  !.
% we want to remove clauses if they have the same score and same length (are likely to be equivalent or even the same!,
% we are unlikely gain much in keeping both), so we say that two such clauses are equal
compareClause(=, (S, L, _, _, _), (S, L, _, _, _)):- !.
%compareClause(=, (S, L, A, B, C, D, E), (S, L, A, B, C, D, E)):- !. % with this we would keep both if they are distinct (that's what sort/2) does
compareClause(<, _, _):- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% best_clauses(+ClauseScores, -BestClauses)
%
% Given:
%  Clauses: a list of tuples of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
% Returns:
%  BestClauses: the top 'n' highest scoring clauses
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

best_clauses(ClauseScores, BestClauses):-
  setting(progolem_beam_width, NumBestClauses),
  (setting(progolem_stochastic_beam, true) ->
    do_tournament(ClauseScores, NumBestClauses, BestClauses)
   ;
    custom_qsort(ClauseScores, compareClause, SClauses), %clauses sorted according to score (ascending)
    % note that if we used sort(ClauseScores, SClauses) we would be prefering longer literals
    %sort(ClauseScores, SClauses), %clauses sorted according to score (ascending)
    reverse(SClauses, SClauses1), % reverse the clause to have clauses descendingly sorted by score
    firstNElemsOf(SClauses1, NumBestClauses, BestClauses)
  ).
  %maplist(removeU, BestClauses, SClauses2), write(SClauses2),nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% do_tournament(+Clauses, +N, -SelectedClauses)
%
% Given:
%  Clauses: a list of tuples of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%  N: Number of clauses to select for next iteration
%
% Returns:
%  SelectedClauses: the N clauses selected for the next iteration in no particular order
%                              This is sub list of Clauses
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

do_tournament([], _N, []):-!.
do_tournament(ClauseScores, N, BestClauses):-
  length(ClauseScores, NumClauses),
  setting(progolem_tournament_size, K), %  K=TournamentSize: see description in settings file
  (K>NumClauses ->
     do_tournament_aux(N, ClauseScores, NumClauses, NumClauses, BestClauses)    
    ;
     do_tournament_aux(N, ClauseScores, K, NumClauses, BestClauses)
  ).
  
do_tournament_aux(0, _, _, _, []):-!.
do_tournament_aux(N, ClauseScores, K, NumClauses, [WinnerC|RemainClauses]):-
  randseq(K, NumClauses, TournamentClausesIDs),
  sort(TournamentClausesIDs, STournamentClausesIDs),
  elemsAtPos(ClauseScores, STournamentClausesIDs, TournamentClauses),
  find_max_score(TournamentClauses, WinnerC),
  N1 is N-1,
  do_tournament_aux(N1, ClauseScores, K, NumClauses, RemainClauses).

%find_max_score(+TournamentClauses, -WinnerClause)
find_max_score([Clause|RClauses], WinnerClause):-
  find_max_score_aux(RClauses, Clause, WinnerClause).

%find_max_score_aux(+RemainClauses, +BestClauseSoFar, -WinnerClause)
find_max_score_aux([], WinnerClause, WinnerClause).
find_max_score_aux([CurClause|Cs], BestClauseSoFar, WinnerClause):-
  CurClause=(Score1, _, _, _, _),
  BestClauseSoFar=(Score2, _, _, _, _),
  (Score1>Score2 ->
      find_max_score_aux(Cs, CurClause, WinnerClause)    
    ;
      find_max_score_aux(Cs, BestClauseSoFar, WinnerClause)
  ).

removeU((S, L, _, _, _), (S,L)).

%hypothesis_score(+Clause, +ClauseSig, +PosEIDs, +NegEIDs, -NumLiterals, -PosEIDsCov, -NegEIDsCov, -HypInfo, -Score)
hypothesis_score(Clause, ClauseSig, PosEIDs, NegEIDs, NumLiterals, PosEIDsCov, NegEIDsCov, HypInfo, Score):-
  hypothesis_coverage(Clause, ClauseSig, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov),
  clauseLength(Clause, NumLiterals),
  hypothesis_score_aux(PosEIDs, NegEIDs, NumLiterals, PosEIDsCov, NegEIDsCov, HypInfo, Score).

%hypothesis_score_aux(+PosEIDs, +NegEIDs, +NumLiterals, +PosEIDsCov, +NegEIDsCov, -HypInfo,  -Score)
hypothesis_score_aux(PosEIDs, NegEIDs, NumLiterals, PosEIDsCov, NegEIDsCov, HypInfo, Score):-
  hypothesis_info(PosEIDsCov, NegEIDsCov, PosEIDs, NegEIDs, HypInfo),
  verifies_partial_metrics(NumLiterals, HypInfo),
  score(NumLiterals, HypInfo, Score).


%
%
% Unify vars in the head throughout the body.
%
%

unifyHead(OrigHead, [ClauseH | ClauseB], UnifClause) :-
    createVarMap(OrigHead, ClauseH, VarMap),
    applyVarMap(ClauseB, VarMap, UnifClause).

createVarMap(L1, L2, VarMap) :-
    functor(L1, _, NArgs),
    N is NArgs + 1,
    rb_new(TVarMap),
    addMappings(L1, L2, TVarMap, VarMap, 1, N).

addMappings(L1, L2, Map, Map, N, N) :- !. %Cut so that alternatives are not tested... another possibility: add LN >= N in second clause

addMappings(L1, L2, Map, NMap, N, LN) :-
    N1 is N + 1,
    addMappings(L1, L2, Map, TMap, N1, LN),
    arg(N, L1, A1),
    arg(N, L2, A2),
    rb_insert(TMap, A2, A1, NMap).

applyVarMap([], _, []).

applyVarMap([H | T], VarMap, [NH | NT]) :-
    applyVarMap(T, VarMap, NT),
    applyVarMapToLiteral(H, VarMap, NH).

applyVarMapToLiteral(Lit, VarMap, NewLit) :-
    Lit =.. [H|T],
    convlist(mapValue(VarMap), T, NT),
    append([H], NT, NewLitParts),
    NewLit =.. NewLitParts.

mapValue(RBMap, Val, OutVal) :-
    rb_lookup(Val, OutVal, RBMap), !.

mapValue(RBMap, Val, Val).

%
%
% Transforms a list [...] into a (...) structure
%
%

listToParenth([], []).

listToParenth([H], H).

listToParenth([H | T], (H, TT)) :-
    listToParenth(T, TT).

%
%
% Compute the clause length --- TODO: This will need to be fixed once predicates are negated
%
%

clauseLength([], 0) :- !.
clauseLength([\+ H | T], L) :-
    !,
    parenthToList(H, NH),
    clauseLength(NH, L1),
    clauseLength(T, L2),
    L is L1 + L2.

clauseLength([\+H | T], L) :-
    !,
    parenthToList(H, NH),
    clauseLength(NH, L1),
    clauseLength(T, L2),
    L is L1 + L2.

clauseLength([H | T], L) :-
    !,
    clauseLength(T, L1), 
    L is L1 + 1.

clauseLength(A, 1) :- !.

parenthToList((H, T), [H | TT]) :-
    !,
    parenthToList(T, TT).

parenthToList((A), [A]).    


extractAuxPredicates( [], []).

extractAuxPredicates( [T|TT], AuxPreds) :-
    extractAuxPredicates(TT, OAuxPreds),
    T = (_, _, _, _, _, _, _, CAuxPred),
    append(CAuxPred, OAuxPreds, AuxPreds).

%
%
% Computes the CWS of the input.
%
%

cws(InitialClause, InitialClauseSig, GenCPosEID, CoveredPos, CoveredNeg, AllPos, AllNeg, [Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score], TheoryDefinition, ND) :-
   invertExamples(CoveredNeg),
   invertExamples(CoveredPos),
   % Try to generate the negated part
%   (genHypFromExample_incremental(CoveredNeg, CoveredPos, CoveredNeg, _, (NegClauseScore, NegClause, NegClauseSig, NegClauseLen, NegClauseNegCoverage, NegClausePosCoverage), ND) ->

   (construct_incremental_theory(CoveredNeg, CoveredPos, CoveredNeg, CoveredPos, genHypFromExample_incremental, -1, Theory, ND), Theory \= (0, _, _, _), Theory \= (1, _, _, _) ->
	
	assertTheory( Theory, NegPredicateName, TheoryDefinitionTemp2),
	appendNegatedCall( InitialClause, InitialClauseSig, NegPredicateName, ClauseWithNeg, ClauseWithNegSig),
	Theory = (_, _, _, TheoryClauses),
	extractAuxPredicates(TheoryClauses, OtherAux),
	append(TheoryDefinitionTemp2, OtherAux, TheoryDefinitionTemp)
            ;
	%In case when hypothesis generation fails -- if the returned hypothesis is void
	invertExamples(CoveredNeg),
	invertExamples(CoveredPos),
	fail),

   invertExamples(CoveredNeg),
   invertExamples(CoveredPos), !,

   % Compute the score for the clause with negation
   coverage_computation(0, InitialClause, InitialClauseSig, GenCPosEIDs, AllPos, AllNeg, PosEIDsCovP, NegEIDsCovP, _HypInfoP, NumLitsP, ScoreP),
   coverage_computation(0, ClauseWithNeg, ClauseWithNegSig, GenCPosEIDs, AllPos, AllNeg, PosEIDsCovN, NegEIDsCovN, _HypInfoN, NumLitsNTemp, ScoreNTemp),
   (setting(evalfn, compression) ->
    	Theory = (TotLit, _),
	% The score needs to be fixed more in-depth.
    	ScoreN is ScoreNTemp - TotLit,
	NumLitsN is NumLitsNTemp + TotLit
      ; 
	ScoreN = ScoreNTemp,
	NumLitsN = NumLitsTemp),
   % Send the best hypothesis onwards (with or without negation)
   ((ScoreN > ScoreP, verifies_partial_metrics(NumLitsN, _HypInfoN)) ->
       [Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score] = [ClauseWithNeg, ClauseWithNegSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCovN, NegEIDsCovN, _HypInfoN, NumLitsN, ScoreN],
       TheoryDefinition = TheoryDefinitionTemp
       ; 
       [Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score] = [InitialClause, InitialClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCovP, NegEIDsCovP, _HypInfoP, NumLitsP, ScoreP],
       TheoryDefinition = []
   ).

%
%
% Adds a negated call to the hypothesis
%
%

appendNegatedCall( [InitialHead | InitialBody], [InitialHeadSig | InitialBodySig], NegPredicateName, NewClause, NewClauseSig) :-
    % extract the arguments from head
    InitialHead =.. [HeadName | HeadArguments],
    InitialHeadSig =.. [HeadNameSig | HeadSigArguments],
    AddedCall =.. [NegPredicateName | HeadArguments],
    AddedCallSig =.. [NegPredicateName | HeadSigArguments],
    append([InitialHead | InitialBody], [\+ AddedCall], NewClause),
    append([InitialHeadSig | InitialBodySig], [\+ AddedCallSig], NewClauseSig).


%
%
% Asserts the theory
%
%
:- dynamic negPredNo/1.

% Counter that ensures that introduced "negated" predicates have different names
negPredNo( 1).

nextPredNo( A) :-
    negPredNo(A),
    retract(negPredNo(A)),
    NA is A + 1,
    assert(negPredNo(NA)).

% Construct a name for a new "negated" predicate
new_predicate_name( PredicateName) :-
    nextPredNo( PredNumber),
    atomic_concat( [negPred, PredNumber], PredicateName).

assertTheory((TotLit, PosCov, NegCov, Hypotheses), PredicateName, Definition) :-
    new_predicate_name( PredicateName),
    assertTheory( Hypotheses, PredicateName, Definition).

assertTheory([], _, []).

assertTheory([(Hypothesis, _, _, _, _, _) | OtherTheories], PredHead, [[NewHead | HypothesisBody] | OtherClauses]) :-
    % Rename the head
    Hypothesis = [HypothesisHead | HypothesisBody],
    HypothesisHead =.. [LiteralName | LiteralArgs],
    NewHead =.. [PredHead | LiteralArgs],
    listToParenth(HypothesisBody, HypothesisBodyParenth),
    % Assert the hypothesis
    asserta(user:(:-(NewHead, HypothesisBodyParenth))),
    assertTheory(OtherTheories, PredHead, OtherClauses).
