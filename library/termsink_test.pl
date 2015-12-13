/*  Part of (HACKED!) SWI-Prolog

    Author:        Douglas R. Miles
    E-mail:        logicmoo@gmail.com 
    WWW:           http://www.swi-prolog.org http://www.prologmoo.com
    Copyright (C): naw...

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/
:- module(termsink,[memory_var/1,memberchk_same_q/2,mvar_set/2, mvar_getsink/2,mvar_set/2,dont_care/1,
          wno_mvars/1,w_mvars/1,w_mvars/2,
          wno_dmvars/1,w_dmvars/1,
          wno_debug/1,w_debug/1,
  termsink/1,termsource/1,
  memory_sink/1,counter_var/1,sinkbits_to_number/2,  
  anything_once/1,termfilter/1,subsumer_var/1,plvar/1]).

:- meta_predicate wno_mvars(+).
:- meta_predicate wno_dmvars(+).
:- meta_predicate wno_debug(+).
:- meta_predicate w_mvars(+).
:- meta_predicate w_dmvars(+).
:- meta_predicate w_debug(+).

:- module_trasparent((
  wno_mvars/1,w_mvars/1,w_mvars/2,
  wno_dmvars/1,w_dmvars/1,
  wno_debug/1,w_debug/1))

:- '$sinkmode'(W,4096), asserta(t_l:save_sinkmode(W)).
 
% /devel/LogicmooDeveloperFramework/swipl-devel/library/termsink
/** <module> Dict utilities

   Some experiments ongoing

   O_TERMSINK
         Without this set #define the 
          Attributed variables call $wakeup basically after their identities (the tagged variable) has been 
         removed from the current call (destroyed until unwind).
         So this prevents their destuction until code in $wakeup/3 destroys them
          So the wakeups in attrib_unify_hook/2 decides  (the effective binding)
          Thus code has the option to keep the attributed variable unbound despite laws of "Prolog physics"..
          (This is what Tarau''s EmtpySinks do!)
         requires O_ATTVAR

   O_ATTVAR_EAGER
         Notice potential wakeups eagerly, for example instead of being put into Variables.. 
        in do_unify(..)  the L or R side of the unify might decide.. or Before/After.
        So the above wakeups decide maybe if a binding will put into the variable instead of the attributed variable
         (Maybe allow to run code early enough the attributed variables binding is decided by attrib_unify_hook  )

   O_DONTCARE_TAGS
       We can test the implications of using variables that need no trail/undo/copy_term that claim to 
       unify with everything and remains free afterwards Currently this is implemented 
        poorly to see if it is correctly operating (semantically as well).  
       eventually this would not be an attributed variable but 
        a single variable in the system that (effectively could be a constant) or *_TAG'ed if we had any space for it

   With any of the above set the system still operates as normal
              until the user invokes  '$sinkmode'/2 to 

   None of these option being enabled will cost more than 
              if( (LD->attrvar.gsinkmode & SOME_OPTION) != 0) ...
  
    
*/

:- meta_predicate w_mvars(+,0),do_test_type(1),wno_mvars(0),must_ts(0),test(?).
:- discontiguous(test/1).
:- nodebug(termsinks).

%% depth_of_var(+Var,-FrameCount) is det.
%
%  if the Variable is on the local stack, FrameCount will tell you for
%  how many levels it has been levels it is away from the creation frame
%
%  This can be a powerfull heuristic in inference engines and 
%  Sat solvers to *help* judge when they are being unproductive.
%  (The example bellow is a loop ... but another idea is that we 
%    can iteratively lengthen the depth allowance of each variable
%   (variable to survive for deeper ))
%
% Example of a different use:
% ==
% q :- q(X), writeln(X).
% q(X) :- depth_of_var(X, D), format('Depth = ~w~n', [D]), D < 5, q(X), notail.
% notail.
% ==
% 
% Running this says:
% ==
% 1 ?- q.
% Depth = 1
% Depth = 2
% Depth = 3
% Depth = 4
% Depth = 5
% false.
% ==
% 

%% anything_once(+Var) is det.
%
% An attributed variable to never be bound to the same value twice
%
%  ==
%  ?- anything_once(X),member(X,[1,2,3,3,3,1,2,3]).
%  X = 1;
%  X = 2;
%  X = 3;
%  No.
%  ==
anything_once(Var):- nonvar(Var) ->true; (get_attr(Var,nr,_)->true;put_attr(Var,nr,old_vals([]))).

nr:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz), \+ memberchk_same_q(VarValue,Waz),nb_setarg(1,AttValue,[VarValue|Waz]).


%% termsink(-X) is det.
%
% Base class of var that consumes terms 
%
termsink(X):-mvar_set(X,+termsink).


%% termsource(-X) is det.
%
% Base class of var that may have a value
%
termsource(X):-mvar_set(X,+termsource),put_attr(X,'$ident',X).

%% termfilter(-X) is det.
%
% Filter that may produce a term (termsource/1)
%
termfilter(X):-mvar_set(X,+wakeAssigns+remainVar).

%% nb_termfilter(-X) is det.
%
% Filters terms but stays unbound even after filtering
%
nb_termfilter(X):-mvar_set(X,+wakeAssigns+remainVar-dontTrail).

%% dont_care(-X) is det.
%
% nb_termfilter term filter that will bind with anything and call no wakeups
%
dont_care(X):-mvar_set(X,skipWakeup+wakeAssigns+remainVar-scheduleOther+evenDuringWakeup).


%% plvar(-X) is det.
%
% Example of the well known "Prolog" variable!
%
% Using a term sink to emulate a current prolog variable (note we cannot use remainVar)
%
% the code:
% ==
% /* if the new value is the same as the old value accept the unification*/
% plvar(X):- termsource(X),put_attr(X,plvar,binding(X,_)).
% plvar:attrib_unify_hook(binding(Var,Prev),Value):-  Value=Prev,put_attr(Var,plvar,binding(Var,Value)).
% ==
%
% ==
% ?- plvar(X), X = 1.
% X = 1.
%
% ?- plvar(X), X = 1, X = 2.
% false.
% ==
%
/* if the new value is the same as the old value accept the unification*/
plvar(X):- termsource(X),put_attr(X,plvar,binding(X,_)).
plvar:attrib_unify_hook(binding(Var,Prev),Value):-  Value=Prev,put_attr(Var,plvar,binding(Var,Value)).


%% subsumer_var(-X) is det.
%
% Example of:
%
%  Each time it is bound, it potentially becomes less bound!
%
% ==
% subsumer_var(X):- termsource(X),init_accumulate(X,subsumer_var,term_subsumer).
% ==
%
% ==
%  ?-  subsumer_var(X), X= a(1), X = a(2).
%  X = a(_).
% ==
%
subsumer_var(X):- termsource(X),init_accumulate(X,pattern,term_subsumer).


%% counter_var(-X) is det.
%
% Example of:
%
% Using a term sink to add numbers together
%
% ==
% counter_var(X):- termsource(X),init_accumulate(X,numeric,plus).
% ==
% 
% ==
%  ?-  counter_var(X), X= 1, X = 1.
%  X = 2.
% ==
%
counter_var(X):- termsource(X),init_accumulate(X,counter_var,plus).


%% nb_var(+X) is det.
%
% Using prolog variable that is stored as a global (for later use)
%
% nb_var/1 code above doesnt call nb_var/2 (since termsource/1 needs called before call we call format/3 .. promotes a _L666 varable to _G666 )
nb_var(X):- termsource(X), format(atom(N),'~q',[X]),nb_linkval(N,X),put_attr(X,nb_var,N),nb_linkval(N,V).
nb_var:attrib_unify_hook(N,V):-
       nb_getval(N,Prev),
       ( % This is how we produce a binding for +termsource "iterator"
          (var(Value),nonvar(Prev)) ->  Value=Prev;
         % same binding (effectively)
             Value==Prev->true;
         % On unification we will update the internal value
             Value=Prev->nb_setval(N,Prev)).

%%  nb_var(+Name,+X) is det.
%
% Using prolog variable that is stored as a global Name (for later use)
% 
%  like nb_linkvar(+Name,+X)
%
%  with the difference that more complex operations are now available at the address 
%  (Like fifdling with the sinkvar props)
%
% ==
%  ?-  nb_var('ForLater',X), member(X,[1,2,3]).
%  X = 1.
%
%  ?- nb_var('ForLater',X).
%  X = 1.
%
%  
% ==
nb_var(N, X):- termsource(X), nb_linkval(N,X),put_attr(X,nb_var,N),nb_linkval(N,V).


%% debug_sinks is det.
%
% Turn on extreme debugging
%
debug_sinks:- sinkmode(+debugSink),!.


%% sinkmode(+Set) is det.
%
% Set system wide sink modes
%
% == 
%      remainVar =bit(0), /* survive bindings to even constants */
%      wakeAssigns =bit(1), /* let $wakeup do our value settings */
%      dontTrail =bit(2), /* dontTrail we are a constant */
%      trailOther =bit(3), /* tail any assignment we are about to make on others */
%      skipWakeup =bit(4), /* we dont need wakeups called */
%      scheduleOther =bit(5), /* schedule wakeup on other attvars */
%      takeOverReferences =bit(6), /* attempt to linkval to what we unify */
%      iteratorVar =bit(7), /* call wakeup to deteremine effective values */
%      replaceVars =bit(8), /* when unifying with a variable attempt to replace it  */
%      containsSlowUnify =bit(9), /* direct LD->slow_unify to be true */
%      dontSlowUnify =bit(10), /* direct LD->slow_unify to be optional */
%      evenDuringWakeup =bit(11), /*  if off (default .. term sinking disabled durring calls to $wakeup/=bit(3), ) */
%      disableTermSink =bit(12), /*  */
%      disabledAll =bit(12), /*  */
%      eagerALL =bit(13), /* call assignAttVar for all value setting  */
%      eagerSome =bit(14), /* call assignAttVar for some unifications with vars */
%      dontCare(unify) =bit(18), /*  dontCare(=) */
%      dontCare(==) =bit(17), /*  dontCare(==) */
%      dontCare(can_unify) =bit(16), /*  dontCare(can_unify) */
%      dontCare(variant) =bit(19), /*  dontCare(=@=) */
%      dontCare(compare) =bit(20), /*  dontCare(compare) */
%      dontInheritGlobal =bit(21),
%      dontTrailAttributes = bit(22),
%      trailAttributes = bit(23),
%      debugSink =bit(24), /*  debugger on  */
%      allAttvarsAreSinks = bit(25),
%         dontCare(copy_term) =bit(26), /*  dontCare(copy_term) */
%         unifyMakesCopy =bit(27), 
%      termsink=(+remainVar+wakeAssigns+dontTrailAttributes+dontInheritGlobal),
%      termsource=(+remainVar+iteratorVar+scheduleOther+wakeAssigns+dontInheritGlobal)
% ==
%
%   more to come...
%
sinkmode(X):- var(X),!,'$sinkmode'(X,X).
sinkmode(X):- '$sinkmode'(M,M),merge_sinkmodes(X,M,XM),must_ts('$sinkmode'(_,XM)),!,sinkmode,!.
bits_for_sinkmode(v(
      remainVar =bit(0), /* survive bindings to even constants */
      wakeAssigns =bit(1), /* let $wakeup do our value settings */
      dontTrail =bit(2), /* dontTrail we are a constant */
      trailOther =bit(3), /* tail any assignment we are about to make on others */
      skipWakeup =bit(4), /* we dont need wakeups called */
      scheduleOther =bit(5), /* schedule wakeup on other attvars */
      takeOverReferences =bit(6), /* attempt to linkval to what we unify */
      iteratorVar =bit(7), /* call wakeup to deteremine effective values */
      replaceVars =bit(8), /* when unifying with a variable attempt to replace it  */
      containsSlowUnify =bit(9), /* direct LD->slow_unify to be true */
      dontSlowUnify =bit(10), /* direct LD->slow_unify to be optional */
      evenDuringWakeup =bit(11), /*  if off (default .. term sinking disabled durring calls to $wakeup/=bit(3), ) */
      disableTermSink =bit(12), /*  */
      disabledAll =bit(12), /*  */
      eagerALL =bit(13), /* call assignAttVar for all value setting  */
      eagerSome =bit(14), /* call assignAttVar for some unifications with vars */
      dontCare(unify) =bit(18), /*  dontCare(=) */
      dontCare(==) =bit(17), /*  dontCare(==) */
      dontCare(can_unify) =bit(16), /*  dontCare(can_unify) */
      dontCare(variant) =bit(19), /*  dontCare(=@=) */
      dontCare(compare) =bit(20), /*  dontCare(compare) */
      dontInheritGlobal =bit(21),
      dontTrailAttributes = bit(22),
      trailAttributes = bit(23),
      debugSink =bit(24), /*  debugger on  */
      allAttvarsAreSinks = bit(25),
         dontCare(copy_term) =bit(26), /*  dontCare(copy_term) */
         unifyMakesCopy =bit(27), 
      termsink=(+remainVar+wakeAssigns+dontTrailAttributes+dontInheritGlobal),
      termsource=(+remainVar+iteratorVar+scheduleOther+wakeAssigns+dontInheritGlobal)

    )). 

%% sinkmode is det.
%
% Print the system global modes
%
sinkmode:-'$sinkmode'(M,M),any_to_sinkbits(M,B),format('~N~q.~n',[sinkmode(M=B)]).


%% early_sinks() is det.
%
% Aggressively make attvars unify with non attvars (instead of the other way arround)
%
early_sinks:- sinkmode(+eagerSome+containsSlowUnify).
eagerALL:- sinkmode(+eagerALL+containsSlowUnify).
pass_ref:- sinkmode(+takeOverReferences).
noearly_sinks:-  sinkmode(-eagerALL-eagerSome).
%% mvar_getsink(Var,BitsOut)
%
% Get a variables sink properties
%
mvar_getsink(Var,BitsOut):- '$mvar_sinkmode'(Var,Mode,Mode),any_to_sinkbits(Mode,BitsOut).


mvar_sinkmode(V,X):-var(X)->mvar_getsink(V,X);mvar_set(V,X).
mvar_sinkmode(V,X,Y):-mvar_getsink(V,X),mvar_set(V,Y).

%% mvar_set(Var,BitsOut)
%
% Set a variables sink properties
%
mvar_set(Var,Modes):-
  wno_dmvars((notrace(( 
   '$mvar_sinkmode'(Var,Was,Was)->
       (merge_sinkmodes(Was,Modes,Change),'$mvar_sinkmode'(Var,_,Change));
   ((must(sinkbits_to_number(Modes,Number)),'$mvar_sinkmode'(Var,att('$ident',Var,[]),_,Number))))))).

%% mvar_set(Var,Bits)
%
% Set a variables sink properties
%
new_mvar(Bits,Var):-mvar_set(Var,Bits).

%  counter_var(X),X=1,X=2,w_mvars(eagerSome+eagerALL+takeOverReferences,X=Y).


must_ts(G):- G*-> true; throw(must_ts_fail(G)).

/*

?-  counter_var(X),X=1,X=2,w_mvars(eagerSome+eagerALL+takeOverReferences+debugSink,X=Y).

vs 

?-  counter_var(X),X=1,X=2,w_mvars(eagerSome+eagerALL+takeOverReferences+debugSink,X=Y).

*/

w_mvars(M,G):- ('$sinkmode'(W,W),merge_sinkmodes(M,W,N),T is N  /\ \ 4096,'$sinkmode'(W,T))->mcc(G,'$sinkmode'(_,W)).

:- module_transparent(w_debug/1).
:- module_transparent(mcc/2).

mcc(G,CU):- !, call_cleanup((G),(CU)).
mcc(G,CU):- G*-> CU ; (once(CU),fail).

wno_dmvars(G):- wno_mvars(wno_debug(G)).
w_dmvars(G):- w_mvars(w_debug(G)).
wno_mvars(G):-  '$sinkmode'(W,W),T is W   /\ \ 4096, '$sinkmode'(_,T), call_cleanup(G,'$sinkmode'(_,W)).
w_mvars(G):-  '$sinkmode'(W,W),T is W   /\ \ 4096, '$sinkmode'(_,T), call_cleanup(G,'$sinkmode'(_,W)).
wno_debug(G):-  '$sinkmode'(W,W), T is W /\ \ 16777216 ,  '$sinkmode'(_,T),  call_cleanup(G,'$sinkmode'(_,W)).
w_debug(G):-  '$sinkmode'(W,W),T is W  \/ 16777216 , '$sinkmode'(_,T), call_cleanup(G,'$sinkmode'(_,W)).

vartypes_to_test(F):-wno_dmvars((current_predicate(termsink:F/1),functor(P,F,1),predicate_property(P,number_of_clauses(_)),termsink:'$pldoc'(F/1,_,_,_),
  clause(P,(A,_BODY)),compound(A),A=mvar_set(_,_))).
vartypes_to_test(new_mvar(Type)):-wno_dmvars(( bits_for_sinkmode(ALL),arg(_,ALL,Type))).

do_test(test_for(Type)):-
  wno_dmvars((vartypes_to_test(Type))) *-> w_debug(ignore((w_mvars(do_test_type(Type)),fail))) ; do_test_type(Type).


init_accumulate(Var,M,P):-put_attr(Var,accume,init_accumulate(Var,M,P)).

accume_unify_hook(init_accumulate(Var,M,P),Value):- nonvar(Value),!,put_attr(Var,accume,accume_value(Var,M,P,Value)).
accume_unify_hook(init_accumulate(_,_,_),Value):- !,var(Value).
accume_unify_hook(accume_value(Var,M,P,Prev),Value):- nonvar(Value),!,show_call(must(call(P, Prev,Value,Combined))),put_attr(Var,accume,accume_value(Var,M,P,Combined)).
accume_unify_hook(accume_value(_Var,_M,P,Prev),Value):- var(Value),!, nonvar(P), must(wno_mvars(Prev=Value)).

accume:attr_unify_hook(Prev,Value):-
 wno_dmvars(( write_term(accume_unify(Prev,Value),[attributes(portray),ignore_ops(true),quoted(true)]),nl,
  accume_unify_hook(Prev,Value))).


% ?- do_test_type(var).


do_test_type(Type):- writeln(maplist_local=Type+X),  
   call(Type,X),
  maplist_local(=(X),[1,2,3,3,3,1,2,3]),
  writeln(value=X),
  writeln(value=X),var_info(X).
  

do_test_type(Type):- 
  once((writeln(vartype=call(Type,X)),  
      call(Type,X),
      ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(Type=X),
      ignore((get_attrs(X,Ats),writeln(Ats=X))),
      fail)),
      writeln(value=X))),var_info(X).

tv123(B):-mvar_set(X,B),t123(X).
t123(X):- print_var(xbefore=X),L=link_term(X,Y,Z),dmsg(before=L),
  ignore((
   X=1,X=1,ignore(show_call(X=2)),w_debug(Y=X),w_debug(X=Z),print_var(x=X),
   print_var(y=Y),print_var(z=Z),ignore(show_call(X=2)),dmsg(each=L),fail)),
   dmsg(after=L).

maplist_local(G,List):-List==[]->!;(List=[H|T],must(call(G,H)),maplist_local(G,T)).

var_info(V):- wno_dmvars(show_var(V)).
print_var(V):-wno_dmvars(show_var(V)).
show_var(E):- wno_dmvars((nonvar(E),(N=V)=E, show_var(N,V))),!.
show_var(V):- wno_dmvars((show_var(var_was,V))).

show_var(N,V):- wno_dmvars(((((\+ attvar(V)) -> dmsg(N=V); (must(('$mvar_sinkmode'(V,Attrs,C,C),any_to_sinkbits(C,Bits))),dmsg(N=(V={Attrs,C,Bits}))))))).


'$source':attr_unify_hook(X,Y):- ignore((debug(termsinks,'~N~q.~n',['$source':attr_unify_hook(X,Y)]))),fail.
'$source':attr_unify_hook(_,Y):- member(Y,[default1,default2,default3])*->true;true.

contains_bit(Var,Bit):- var(Bit),'$mvar_sinkmode'(Var,M,M),any_to_sinkbits(M,Bits),!,member(Bit,Bits).
contains_bit(Var,Bit):-'$mvar_sinkmode'(Var,M,M),sinkbits_to_number(Bit,N),!,N is N /\ M.

'$ident':attr_unify_hook(Var,Value):- var(Var),contains_bit(Var,iteratorVar),var(Value),!,member(Value,[default1,default2,default3]).
'$ident':attr_unify_hook(Var,Value):- 
  wno_dmvars((((ignore((var(Var),get_attrs(Var,Attribs), 
   debug(termsinks,'~N~q.~n',['$ident':attr_unify_hook({var=Var,attribs=Attribs},{value=Value})]))))))).

:-  debug(termsinks).

any_to_sinkbits(BitsIn,BitsOut):-  
 sinkbits_to_number(BitsIn,Mode),
   Bits=[[]],bits_for_sinkmode(MASKS),
 ignore((arg(Arg,MASKS,Mask), 
   (Mask=(N=V)-> (sinkbits_to_number(V,VV) , VV is VV /\ Mode , nb_extend_list(Bits,N),fail) ; 
   (Arg0 is Arg -1, sinkbits_to_number(bit(Arg0),VV) , VV is VV /\ Mode , nb_extend_list(Bits,Mask),fail)))),!,
  BitsOut = Bits.


nb_extend_list(List,E):-arg(2,List,Was),nb_setarg(2,List,[E|Was]).



merge_sinkmodes(V,VV,VVV):-number(V),catch((V < 0),_,fail),!, V0 is - V, merge_sinkmodes(-(V0),VV,VVV),!.
merge_sinkmodes(V,VV,VVV):-number(V),number(VV),VVV is (V \/ VV).
merge_sinkmodes(V,VV,VVV):-var(V),!,V=VV,V=VVV.
merge_sinkmodes(set(V),_,VVV):-sinkbits_to_number(V,VVV),!.
merge_sinkmodes(V,VV,VVV):-var(VV),!, sinkbits_to_number(V,VVV),!.
merge_sinkmodes(+(A),B,VVV):- must_ts((sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V \/ VV))).
merge_sinkmodes(*(A),B,VVV):- sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V /\ VV).
merge_sinkmodes(-(B),A,VVV):- sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V /\ \ VV).
merge_sinkmodes([A],B,VVV):-  must_ts(merge_sinkmodes(A,B,VVV)),!.
merge_sinkmodes([A|B],C,VVV):-merge_sinkmodes(A,C,VV),merge_sinkmodes(B,VV,VVV),!.
merge_sinkmodes(A,C,VVV):-sinkbits_to_number(A,VV),!,must_ts(merge_sinkmodes(VV,C,VVV)),!.


sinkbits_to_number(N,O):-number(N),!,N=O.
sinkbits_to_number(V,O):-var(V),!,V=O.
sinkbits_to_number([],0).
sinkbits_to_number(B+A,VVV):- merge_sinkmodes(+(A),B,VVV),!.
sinkbits_to_number(B*A,VVV):- merge_sinkmodes(*(A),B,VVV),!.
sinkbits_to_number(B-A,VVV):- sinkbits_to_number(B,BB),sinkbits_to_number(A,AA),VVV is (BB /\ \ AA),!.
sinkbits_to_number(+(Bit),VVV):-sinkbits_to_number((Bit),VVV),!.
sinkbits_to_number(-(Bit),VVV):-sinkbits_to_number((Bit),V),!,VVV is ( \ V).
sinkbits_to_number(bit(Bit),VVV):- number(Bit),!,VVV is 2 ^ (Bit).
sinkbits_to_number(bit(Bit),VVV):-bits_for_sinkmode(VV),arg(N,VV,Bit),N0 is N-1,!,sinkbits_to_number(bit(N0),VVV),!.
sinkbits_to_number(set(Bit),VVV):-bits_for_sinkmode(VV),arg(N,VV,Bit),N0 is N-1,!,sinkbits_to_number(bit(N0),VVV),!.
sinkbits_to_number((Name),VVV):-bits_for_sinkmode(VV),arg(_,VV,Name=Bit),!,must_ts(sinkbits_to_number(Bit,VVV)),!.
sinkbits_to_number([A],VVV):-!,sinkbits_to_number(A,VVV).
sinkbits_to_number([A|B],VVV):-!,merge_sinkmodes(B,A,VVV).
sinkbits_to_number(Bit,VVV):-bits_for_sinkmode(VV),arg(N,VV,Bit),N0 is N-1,!,sinkbits_to_number(bit(N0),VVV),!.
sinkbits_to_number(V,VVV) :- catch(( VVV is V),_,fail),!.






%% memberchk_same_q( ?X, :TermY0) is semidet.
%
% Uses =@=/2,  except with variables, it uses ==/2.
%
memberchk_same_q(X, List) :- is_list(List),!, \+ atomic(List), C=..[v|List],!,(var(X)-> (arg(_,C,YY),X==YY) ; (arg(_,C,YY),X =@= YY)),!.
memberchk_same_q(X, Ys) :-  nonvar(Ys), var(X)->memberchk_same0(X, Ys);memberchk_same1(X,Ys).
memberchk_same0(X, [Y|Ys]) :-  X==Y  ; (nonvar(Ys),memberchk_same0(X, Ys)).
memberchk_same1(X, [Y|Ys]) :-  X =@= Y ; (nonvar(Ys),memberchk_same1(X, Ys)).

memberchk_same2(X, List) :- Hold=hold(List), !,
        repeat, (arg(1,Hold,[Y0|Y0s]) ->
          ( X==Y0-> true; (nb_setarg(1,Hold,Y0s),fail)) ; (! , fail)).

memberchk_same3(X, List) :- Hold=hold(List), !,
        repeat, (arg(1,Hold,[Y0|Y0s]) ->
          ( X=@=Y0-> true; (nb_setarg(1,Hold,Y0s),fail)) ; (! , fail)).

memb_r(X, List) :- Hold=hold(List), !, throw(broken_memb_r(X, List)),
         repeat,
          ((arg(1,Hold,[Y|Ys]),nb_setarg(1,Hold,Ys)) -> X=Y ; (! , fail)).



%% memory_var(+Var) is det.
%
% An attributed variable that records it''s past experience
%
% ?- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).
% memory_var=1
% memory_var=2
% memory_var=3
% memory_var=3
% memory_var=3
% memory_var=1
% memory_var=2
% memory_var=3
% get_attrs=att(mv,old_vals([3,2,1,3,3,3,2,1]),[])
%
%  No.
%  ==
mv:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz),nb_setarg(1,AttValue,[VarValue|Waz]).

memory_var(Var):- nonvar(Var) ->true; (get_attr(Var,mv,_)->true;put_attr(Var,mv,old_vals([]))).

test(memory_var):- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).


%% memory_sink(+Var) is det.
%
%  Makes a variable that remembers all of the previous bindings (even the on ..)
%
%  This is strill to be wtritten
%
% "She'll try anything twice"
%
%  ==
%  ?- memory_sink(X),member(X,[1,2,3,3,3,1,2,3]).
%  X = 1;
%  X = 2;
%  X = 3;
%  No.
%  ==
% memory_sink(Var):-mvar_set(Sink,[]), put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.
memory_sink(Var):-mvar_set(Var,[]),put_attr(Var,'_',Var),put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.








/*
:- if((
  exists_source( library(logicmoo_utils)),
  current_predicate(gethostname/1), 
  % fail,
  gethostname(ubuntu))).
*/

:- use_module(library(logicmoo_utils)).

:- debug(_).
% :- debug_sinks.
% :- early_sinks.
:- debug(termsinks).

:-export(demo_nb_linkval/1).
  demo_nb_linkval(T) :-
           T = nice(N),
           (   N = world,
               nb_linkval(myvar, T),
               fail
           ;   nb_getval(myvar, V),
               writeln(V)
           ).
/*
   :- debug(_).
   :- nodebug(http(_)).
   :- debug(mpred).

   % :- begin_file(pl).


   :- dynamic(sk_out/1).
   :- dynamic(sk_in/1).

   :- read_attvars(true).

   sk_in(avar([vn='Ex',sk='SKF-666'])).

   :- listing(sk_in).

   :- must_ts((sk_in(Ex),get_attr(Ex,sk,What),What=='SKF-666')).

*/

v1(X,V) :- mvar_set(V,X),show_var(V).



%:- endif.

:- early_sinks.
% :- early_sinks. 
% :- eagerALL.
:- listing(wno_debug).



% :-'$debuglevel'(_,1).


mvar_call(VarFactory,G):-
   wno_dmvars((term_variables(G,Vs),
   maplist(VarFactory,Vs))),trace,w_dmvars(G).


%% set_unifyp(+Pred,?Var) is det.
%
% Create or alter a Prolog variable to have overloaded unification
%
% Done with these steps:
% 1) +termsink = Allow to remain a variable after binding with a nonvar
% 2) +termsource = Declares the variable to be a value producing iterator
% 3) Set the unifyp attribute to the Pred.
set_unifyp(Pred,Var):- wno_dmvars((trace,termsource(Var),put_attr(Var,unifyp,binding(Pred,Var,_Uknown)))).

% Our implimentation of a unifyp variable
unifyp:attrib_unify_hook(binding(Pred,Var,Prev),Value):-
        % This is how we produce a binding for +termsource "iterator"
          (var(Value),nonvar(Prev)) ->  Value=Prev;
         % same binding (effectively)
             Value==Prev->true;
         % unification we will update the internal value
             Value=Prev->put_attr(Var,plvar,binding(Pred,Var,Value));
         % Check if out overload was ok
             call(Pred,Prev,Value) -> true;
         % Symmetrically if out overload was ok
             call(Pred,Value,Prev)-> true.




ab(a1,b1).
ab(a2,b2).
ab(a3,b3).

xy(x1,y1).
xy(x2,y2).
xy(x3,y3).

equals(a1,x1).
equals(a2,x2).
equals(a3,x3).
equals(b1,y1).
equals(b2,y2).
equals(b3,y3).

q(A,B):-trace,ab(A,B),xy(A,B).

% label_sources

lv:- mvar_call(set_unifyp(equals),q(A,B)),label_sources(A,B),dmsg(q(A,B)).

:- sinkmode.
:- eagerALL.

 
:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),M\=vn,
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A)))),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A)))))).

:- (retract(t_l:save_sinkmode(W))->'$sinkmode'(_,W);true).

