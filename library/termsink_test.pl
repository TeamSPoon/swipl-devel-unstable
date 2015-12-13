/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@cs.vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2015, VU University Amsterdam

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
:- module(termsink_test,[memory_var/1,memberchk_same_q/2,mvar_new/2, mvar_getsink/2,mvar_setsink/2,dont_care/1,
  wno_mvars_tst/1,w_mvars/2,memory_sink/1,termsink/1,counter_var/1,sinkbits_to_number/2,  
   anything_once/1,termsource/1,termfilter/1,subsumer_var/1,plvar/1]).

% /devel/LogicmooDeveloperFramework/swipl-devel/library/termsink
/** <module> Dict utilities

   Some experiments ongoing

   O_TERMSINK
         Attributed variables call $wakeup basically after their identities (the tagged variable) has been 
         removed from the current call So now the wakeups like attrib_unify_hook/2 decide 
        the effective binding of this.  Sometimes keep the attributed variable unbound despite
         being unified with a term?!? (This is what Tarau''s EmtpySinks do!)
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

:- meta_predicate w_mvars(+,0),do_test_type(1),wno_mvars_tst(0),must_ts(0),test(?).
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
% "She'll try anything once"
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
termsink(X):-mvar_new(X,skipAssign).


%% termsource(-X) is det.
%
% Base class of var that may have a value
%
termsource(X):-mvar_new(X,termSource+scheduleOther+skipAssign). % remainVar

%% termfilter(-X) is det.
%
% Filter that may produce a term (termsource/1)
%
termfilter(X):-mvar_new(X,skipAssign+termSource).

%% nb_termfilter(-X) is det.
%
% Filters terms but stays unbound even after filtering
%
nb_termfilter(X):-mvar_new(X,skipAssign+remainVar).

%% dont_care(-X) is det.
%
% nb_termfilter term filter that will bind with anything and call no wakeups
%
dont_care(X):-mvar_new(X,skipWakeup+skipAssign+remainVar-scheduleOther).


%% plvar(-X) is det.
%
% Example of:
%
% Using a term sink to emulate a current prolog variable (note we cannot use remainVar)
%
% ==
% plvar(X):- termsource(X),put_attr(X,plvar,TS),TS=X.
% plvar:attr_unify_hook(_,_).
%  /* if the new value is the same as the old value accept the unification, otherwise fail */
% plvar:early_unify_hook(Var,OldValue,Value):-  OldValue=Value,put_attr(Var,plvar,Value)
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
plvar(X):- termsource(X),put_attr(X,plvar,TS),TS=X.
plvar:attr_unify_hook(_,_).
% if the new value is the same as the old value accept the unification
plvar:early_unify_hook(Var,OldValue,Value):-  OldValue=Value,put_attr(Var,plvar,Value).


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
subsumer_var(X):- termsource(X),init_accumulate(X,subsumer_var,term_subsumer).


%% counter_var(-X) is det.
%
% Example of:
%
% Using a term sink to add numbers together
%
% ==
% counter_var(X):- termsource(X),init_accumulate(X,counter_var,plus).
% ==
% 
% ==
%  ?-  counter_var(X), X= 1, X = 1.
%  X = 2.
% ==
%
counter_var(X):- termsource(X),init_accumulate(X,counter_var,plus).


%% nb_var(-X) is det.
%
% Using prolog variable that is stored in a global variable 
%
nb_var(X):- termsource(X), format(atom(N),'~q',[X]),nb_linkval(N,X),put_attr(X,nb_var,N).
nb_var:attrib_unify_hook(N,V):- nb_linkval(N,V).
nb_var:early_unify_hook(_Var,N,V):- nb_setval(N,V).

%% debug_sinks is det.
%
% Turn on extreme debugging
%
debug_sinks:- set_sinkmode(+debugSink),!.


%% set_sinkmode(+Set) is det.
%
% Set system wide sink modes
%
%      containsSlowUnify = WAM needs our help soemtimes
%      slowUnifyUneeded = If true we dont dont help
%      twoO48 = bit 2048 
%      attrReverseVar = Attvar''s control unification with plain variables (Irregardless to whom was created first)
%      attrBeforeVar  = Attvar''s control unification with plain variables (But abiding by creation order )
%      dontCare(unifiable) = assume we are 
%      dontCare(==)  = assume we are 
%      dontCare(=)   = dont trail undo of some special variables
%      dontCare(=@=)  = assume we are 
%      debugSink=bit(24) = print extra term reference pointer information
%
%   Per variable the default sink modes 
%
%      remainVar = after unification stay a variable (even if if we are bound)
%      skipAssign = allow early_unify_hook/3 to control (instead of =/2)
%      dontTrail = this variable need no trailing (non backtrackable)
%      trailOther =  we anticipate changing something in the value we unify with
%      skipWakeup = this variable need no calls to $wakeup/3
%      scheduleOther =  call $wakeup on other attributed variable who bind with us (overrides the stack priority) 
%      passReferenceToAttvar = this is for when we might create a linkval back to us where unification just happened
%      termSource = on unification ask attr_unify_hook/2 
%
%   more to come...
%
set_sinkmode(X):- '$sinkmode'(M,M),merge_sinkmodes(X,M,XM),must_ts('$sinkmode'(_,XM)),!,sinkmode,!.


%% sinkmode is det.
%
% Print the system global modes
%
sinkmode:-'$sinkmode'(M,M),any_to_sinkbits(M,B),format('~N~q.~n',[sinkmode(M=B)]).


%% early_sinks() is det.
%
% Aggressively make attvars unify with non attvars (instead of the other way arround)
%
early_sinks:- set_sinkmode(+attrReverseVar+attrBeforeVar+containsSlowUnify).

pass_ref:- set_sinkmode(+passReferenceToAttvar).

%% mvar_getsink(Var,BitsOut)
%
% Get a variables sink properties
%
mvar_getsink(Var,BitsOut):- '$mvar_sinkmode'(Var,Mode,Mode),any_to_sinkbits(Mode,BitsOut).


%% mvar_setsink(Var,BitsOut)
%
% Set a variables sink properties
%
mvar_setsink(Var,New):-
   '$mvar_sinkmode'(Var,Was,Was)->
       (merge_sinkmodes(Was,New,Change),'$mvar_sinkmode'(Var,_,Change));
     mvar_new(Var,New).

%% mvar_setsink(Var,BitsOut)
%
% Set a variables sink properties
%
mvar_new(X,Modes):- notrace(( sinkbits_to_number(Modes+debugSink,Number),!, '$mvar_sinkmode'(X,_Attrs,_M,Number))).

%mvar_new(X,V):-wno_mvars_tst((((get_attr(X,'$sink',VV)->(VV==V->true;(merge_sinkmodes(V,VV,VVV),
%   put_attr(X,'$sink',VVV)));((var(V)->V=1;true),(sinkbits_to_number(V,VV),put_attr(X,'$sink',VV)))),put_attr(X,'$ident',X)))),!.

new_mvar(X,V):-mvar_new(V,X).

bits_for_sinkmod(v(
      remainVar, % 1
      skipAssign, % 2
      dontTrail, % 4
      trailOther, % 8
      skipWakeup, % 16
      scheduleOther, % 32
      passReferenceToAttvar, % 64
      termSource, %128
      is256,
      containsSlowUnify, % 512
      slowUnifyUneeded, % 1024
      twoO48, % 
      disabledAll,  % 4096
      attrBeforeVar,  % 8192
      attrReverseVar,  % 
      dontCare(unifiable),
      dontCare(==),
      dontCare(=), 
      dontCare(=@=), 
      debugSink=bit(24)
    )). 


%  counter_var(X),X=1,X=2,w_mvars(attrReverseVar+attrBeforeVar+passReferenceToAttvar,X=Y).


must_ts(G):- G*-> true; throw(must_ts_fail(G)).

:- meta_predicate w_mvars(0).
:- meta_predicate wno_dbg(0).
:- meta_predicate w_dbg(+).

/*

?-  counter_var(X),X=1,X=2,w_mvars(attrReverseVar+attrBeforeVar+passReferenceToAttvar+debugSink,X=Y).

vs 

?-  counter_var(X),X=1,X=2,w_mvars(attrReverseVar+attrBeforeVar+passReferenceToAttvar+debugSink,X=Y).

*/

w_mvars(M,G):- ('$sinkmode'(W,W),merge_sinkmodes(M,W,N),T is N  /\ \ 4096,'$sinkmode'(W,T))->call_cleanup(G,'$sinkmode'(_,W)).

:- module_transparent(w_dbg/1).

wno_mvars_tst(G):-  must('$sinkmode'(W,W)),must((T is W  \/ 4096)), 
 must('$sinkmode'(_,T)), (G*->must('$sinkmode'(_,W));(must('$sinkmode'(_,W)),fail)).

w_mvars(G):-  '$sinkmode'(W,W),T is W   /\ \ 4096, '$sinkmode'(W,T), call_cleanup(G,'$sinkmode'(_,W)).
wno_dbg(G):-  '$sinkmode'(W,W),T is W  /\ \ 16777216 , '$sinkmode'(W,T), call_cleanup(G,'$sinkmode'(_,W)).
w_dbg(G):-  '$sinkmode'(W,W),T is W  \/ 16777216 , '$sinkmode'(W,T), call_cleanup(G,'$sinkmode'(_,W)).

vartypes_to_test(F):-wno_mvars_tst((current_predicate(termsink:F/1),functor(P,F,1),predicate_property(P,number_of_clauses(_)),termsink:'$pldoc'(F/1,_,_,_),
  clause(P,(A,_BODY)),compound(A),A=mvar_new(_,_))).
vartypes_to_test(new_mvar(Type)):-wno_mvars_tst(( bits_for_sinkmod(ALL),arg(_,ALL,Type))).

do_test(test_for(Type)):-
  wno_dbg(wno_mvars_tst(vartypes_to_test(Type))) *-> w_dbg(ignore((w_mvars(do_test_type(Type)),fail))) ; do_test_type(Type).


init_accumulate(Var,M,P):-put_attr(Var,accume,init_accumulate(Var,M,P)).

accume:attr_unify_hook(Prev,Value):-
  writeq(accume_unify(M,Prev,Value)),nl,
  accume_unify_hook(Prev,Value).

accume_unify_hook(init_accumulate(Var,M,P),Value):- nonvar(Value),!,put_attr(Var,accume,accume_value(Var,M,P,Value)).
accume_unify_hook(init_accumulate(Var,M,P),Value):- var(Value),!,Value=_.  
accume_unify_hook(accume_value(Var,M,P,Prev),Value):- nonvar(Value),!,show_call(must(call(P, Prev,Value,Combined))),put_attr(Var,accume,accume_value(Var,M,P,Combined)).
accume_unify_hook(accume_value(Var,_M,P,Prev),Value):- var(Value),!, nonvar(P),
    %% must('$sinkmode'(W,W))),must((T is W  \/ 4096)), must('$sinkmode'(W,T)),
     must(wno_mvars_tst(Prev=Value)).



% ?- do_test_type(var).


do_test_type(Type):- writeln(maplist_local=Type+X),  
   call(Type,X),
  maplist_local(=(X),[1,2,3,3,3,1,2,3]),
  writeln(value=X),
  writeln(value=X),print_varinfo(X).
  

do_test_type(Type):- 
  once((writeln(vartype=call(Type,X)),  
      call(Type,X),
      ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(Type=X),
      ignore((get_attrs(X,Ats),writeln(Ats=X))),
      fail)),
      writeln(value=X))),print_varinfo(X).
      

maplist_local(G,List):-List==[]->!;(List=[H|T],call(G,H),maplist_local(G,T)).

print_varinfo(X):-catch((writeq(print_varinfo=X),get_attrs(X,Attrs),writeln(get_attrs=Attrs)),_,true).

'$sink':call_all_attr_uhooks_early(_,[], _).
'$sink':call_all_attr_uhooks_early(Var,att(Module, AttVal, Rest), Value) :-
        must(( (current_predicate(Module:early_unify_hook/3)->
          Module:early_unify_hook(Var, AttVal, Value);true),
	'$sink':call_all_attr_uhooks_early(Var, Rest, Value))).

'$sink':attr_unify_hook(X,Y):- ignore((debug(termsinks,'~N~q.~n',['$sink':attr_unify_hook(mode=X,value=Y)]))).

'$ident':attr_unify_hook(Var,Value):- 
  wno_mvars_tst((ignore((var(Var),get_attrs(Var,Attribs), 
   debug(termsinks,'~N~q.~n',['$ident':attr_unify_hook(({Var+Attribs}=Value))]),
   '$sink':call_all_attr_uhooks_early(Var,Attribs,Value))))).



any_to_sinkbits(BitsIn,BitsOut):-  
 sinkbits_to_number(BitsIn,Mode),
   Bits=[[]],bits_for_sinkmod(MASKS),
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
sinkbits_to_number(bit(Bit),VVV):-bits_for_sinkmod(VV),arg(N,VV,Bit),N0 is N-1,!,sinkbits_to_number(bit(N0),VVV),!.
sinkbits_to_number(set(Bit),VVV):-bits_for_sinkmod(VV),arg(N,VV,Bit),N0 is N-1,!,sinkbits_to_number(bit(N0),VVV),!.
sinkbits_to_number((Name),VVV):-bits_for_sinkmod(VV),arg(_,VV,Name=Bit),!,must_ts(sinkbits_to_number(Bit,VVV)),!.
sinkbits_to_number([A],VVV):-!,sinkbits_to_number(A,VVV).
sinkbits_to_number([A|B],VVV):-!,merge_sinkmodes(B,A,VVV).
sinkbits_to_number(Bit,VVV):-bits_for_sinkmod(VV),arg(N,VV,Bit),N0 is N-1,!,sinkbits_to_number(bit(N0),VVV),!.
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
% memory_sink(Var):-mvar_new(Sink,[]), put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.
memory_sink(Var):-mvar_new(Var,[]),put_attr(Var,'_',Var),put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.





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

:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A)))),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A)))))).


%:- endif.
% :- set_sinkmode(-disabledAll).
:- debug_sinks.
: -early_sinks.

