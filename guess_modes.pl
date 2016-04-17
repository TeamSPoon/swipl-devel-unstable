
:- use_module(library(pldoc/doc_library)).
:-  doc_load_library.

 current_module(M),catch(M:'$pldoc'(F/A, Loc,Text,I),_,fail), functor(Head,F,A), \+ catch(M:'$mode'(Head, Det),_,fail),
   format('~q.~n',[M:'$pldoc'(F/A, Loc,Text)]),
   format('~q.~n',[M:'$mode'(Head, Det)]).

 current_module(M),catch(M:'$pldoc'(F//A, Det,O,I),_,fail),format('~q.~n',[M:'$pldoc'(F//A, Det,I)]) 
 ,fail.
 current_module(M),catch(M:'$mode'(Head, Det),_,fail),format('~q.~n',[M:'$mode'(Head, Det)]),fail.


