progolemnot
===========

The GILPS system with added ProGolemNot classifier. The GILPS system was developed by José Carlos Almeida Santos [http://www.doc.ic.ac.uk/~jcs06/](http://www.doc.ic.ac.uk/~jcs06/). The original system is available at [http://www.doc.ic.ac.uk/~jcs06/GILPS/](http://www.doc.ic.ac.uk/~jcs06/GILPS/).


Usage:

:- consult(gilps). %load gilps

% required settings

:- set(engine, propargolem).

:- set(theory_construction, incremental).

:- set(clause_evaluation, left_to_right).

:- set(progolem_mode, pairs).

:- set(useneg, true).

:- set(max_neg_depth, 1). % Counting starts from 0, so in this case two levels of exceptions will be considered.

:- set(noise, 1).

:- read_problem('datasets/testML.pl').

:- build_theory.

This sequence can also be executed by loading progolemnot.pl.
