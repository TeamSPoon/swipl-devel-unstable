add_to_global_worklist(TableIdentifier) :-
  hprolog_nb_getval(globalWorklist,L1),
  hprolog_nb_setval(globalWorklist,[TableIdentifier|L1]).

worklist_empty :-
  hprolog_nb_getval(globalWorklist,[]).

pop_worklist(TableIdentifier) :-
  hprolog_nb_getval(globalWorklist,L1),
  L1 = [TableIdentifier|L2],
  hprolog_nb_setval(globalWorklist,L2).

