:- consult(gilps).

:- set(engine, propargolem).
:- set(theory_construction, incremental).
:- set(clause_evaluation, left_to_right).
:- set(progolem_mode, pairs).
:- set(useneg, true).
:- set(max_neg_depth, 1). %counting begins with 0 -- i.e. value 0 will induce one level of exceptions
:- set(noise, 1). %workaround so that gilps does not reject clauses before cws is performed

:- read_problem('datasets/testML.pl').


