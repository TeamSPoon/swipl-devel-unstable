/*

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

:- module(termsink,[memory_var/1,memberchk_same/2,mvar_new/2,mvar_get/2,mvar_set/2,dont_care/1,
  with_mvz/1,with_mv/2,memory_sink/1,termsink/1,counter_var/1,
   anything_once/1,termsource/1,termfilter/1,uvar/1,plvar/1]).
:- meta_predicate with_mv(+,0),test_helper(1),with_mvz(0),must_ts(0).

:- discontiguous(test/1).

:- nodebug(termsinks).

%% depth_of_var(+Var,-FrameCount).
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

nr:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz), \+ memberchk_same(VarValue,Waz),nb_setarg(1,AttValue,[VarValue|Waz]).

test(anything_once):- anything_once(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(anything_once=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).

%% termsink(-X) is det.
%
% Base class of var that consumes terms 
%
termsink(X):-mvar_new(X,skipAssign).

%% termsource(-X) is det.
%
% Base class of var that may have a value
%
termsource(X):-mvar_new(X,termSource+scheduleOther).

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
% plvar:early_unify_hook(Var,OldValue,NewValue):-  OldValue=NewValue,put_attr(Var,plvar,NewValue)
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
plvar:early_unify_hook(Var,OldValue,NewValue):-  OldValue=NewValue,put_attr(Var,plvar,NewValue).


%% uvar(-X) is det.
%
% Example of:
%
%  Each time it is bound, it potentially becomes less bound!
%
% ==
% uvar(X):- termsource(X),put_attr(X,uvar,TS),TS=X.
% uvar:attr_unify_hook(TotalCount,TotalCount).
% uvar:early_unify_hook(Var,PrevValue,NewValue):-  term_subsumer(PrevValue,NewValue,Combined),put_attr(Var,uvar,Combined).
% ==
%
% ==
%  ?-  uvar(X), X= a(1), X = a(2).
%  X = a(_).
% ==
%
uvar(X):- termsource(X),put_attr(X,uvar,TS),TS=X.
uvar:attr_unify_hook(TotalCount,TotalCount).
uvar:early_unify_hook(Var,PrevValue,NewValue):-  term_subsumer(PrevValue,NewValue,Combined),put_attr(Var,uvar,Combined).


%% counter_var(-X) is det.
%
% Example of:
%
% Using a term sink to add numbers together
%
% ==
% counter_var(X):- termsource(X),put_attr(X,counter_var,TS),TS=X.
% counter_var:attr_unify_hook(TotalCount,TotalCount).
% counter_var:early_unify_hook(Var,PrevValue,NewValue):-  plus(PrevValue,NewValue,Combined),put_attr(Var,counter_var,Combined).
% ==
% 
% ==
%  ?-  counter_var(X), X= 1, X = 1.
%  X = 2.
% ==
%
counter_var(X):- termsource(X),put_attr(X,counter_var,TS),TS=X.
counter_var:attr_unify_hook(TotalCount,TotalCount).
counter_var:early_unify_hook(Var,PrevValue,NewValue):-  plus(PrevValue,NewValue,Combined),put_attr(Var,counter_var,Combined).



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
debug_sinks:- set_sinkmode(+sinkDebug),sinkmode.


%% set_sinkmode(+Set) is det.
%
% Set system wide sink modes
%
%      containsSlowUnify = WAM needs our help soemtimes
%      slowUnifyUneeded = If true we dont dont help
%      twoO48 = bit 2048 
%      attrVarBeforeVar = Attvar''s control unification with plain variables (Irregardless to whom was created first)
%      attrVarAfterVar  = Attvar''s control unification with plain variables (But abiding by creation order )
%      dontCare(unifiable) = assume we are 
%      dontCare(==)  = assume we are 
%      dontCare(=)   = dont trail undo of some special variables
%      dontCare(=@=)  = assume we are 
%      sinkDebug=bit(24) = print extra term reference pointer information
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
set_sinkmode(X):- '$sinkmode'(M,M),merge_sinkmodes(X,M,XM),must_ts('$sinkmode'(_,XM)).


%% sinkmode is det.
%
% Print the system global modes
%
sinkmode:-'$sinkmode'(M,M),any_to_sinkbits(M,B),format('~N~q.~n',[sinkmode(M=B)]).


%% early_sinks() is det.
%
% Aggressively make attvars unify with non attvars (instead of the other way arround)
%
early_sinks:- set_sinkmode(+attrVarBeforeVar+attrVarAfterVar+containsSlowUnify),sinkmode.


%% mvar_get(Var,BitsOut)
%
% Get a variables sink properties
%
mvar_get(Var,BitsOut):-get_attr(Var,'$sink',Mode),any_to_sinkbits(Mode,BitsOut).

%% mvar_set(Var,BitsOut)
%
% Set a variables sink properties
%
mvar_set(Var,New):-
   get_attr(Var,'$sink',Was)->
       (merge_sinkmodes(Was,New,Change),put_attr(Var,'$sink',Change));
     mvar_new(Var,New).

%% mvar_set(Var,BitsOut)
%
% Set a variables sink properties
%
mvar_new(X,V):-with_mvz((((get_attr(X,'$sink',VV)->(VV==V->true;(merge_sinkmodes(V,VV,VVV),
   put_attr(X,'$sink',VVV)));((var(V)->V=1;true),(sinkbits_to_number(V,VV),put_attr(X,'$sink',VV)))),put_attr(X,'$ident',X)))),!.

bits_for_sinkmod(v(
      remainVar, % 1
      skipAssign, % 2
      dontTrail, % 4
      trailOther, % 8
      skipWakeup, % 16
      scheduleOther, % 32
      passReferenceToAttvar, % 64
      termSource, %128
      containsSlowUnify, % 512
      slowUnifyUneeded, % 1024
      twoO48, % 
      attrVarAfterVar,  % 4096
      attrVarBeforeVar,  % 8192
      dontCare(unifiable), 
      dontCare(==),
      dontCare(=), 
      dontCare(=@=), 
      sinkDebug=bit(24)
    )). 



with_mvz(G):- '$sinkmode'(W,16777216),call_cleanup(G,'$sinkmode'(_,W)).

with_mv(M,G):- ('$sinkmode'(W,W),merge_sinkmodes(M,W,N),'$sinkmode'(W,N))->call_cleanup(G,'$sinkmode'(_,W)).



'$sink':call_all_attr_uhooks_early(_,[], _).
'$sink':call_all_attr_uhooks_early(Var,att(Module, AttVal, Rest), Value) :-
        (current_predicate(Module:early_unify_hook/3)->Module:early_unify_hook(Var, AttVal, Value);true),
	'$sink':call_all_attr_uhooks_early(Var, Rest, Value).

'$sink':attr_unify_hook(X,Y):- debug(termsinks,'~N~q.~n',['$sink':attr_unify_hook(mode=X,value=Y)]).
'$ident':attr_unify_hook(Var,Value):- assertion(var(Var)),
  ignore(with_mvz((var(Var),get_attrs(Var,Attribs), debug(termsinks,'~N~q.~n',[attr_unify_hook(({Var+Attribs}=Value))])))),
   '$sink':call_all_attr_uhooks_early(Var,Attribs,Value).



test(remainVar) :- mvar_new(V,[remainVar]),V=1,var(V).
test(skipAssign) :- mvar_new(V,[skipAssign]),V=1,var(V).
test(skipWakeup) :- mvar_new(V,[skipWakeup]),V=1,nonvar(V).


any_to_sinkbits(BitsIn,BitsOut):-  
 sinkbits_to_number(BitsIn,Mode),
   Bits=[[]],bits_for_sinkmod(MASKS),
 ignore((arg(Arg,MASKS,Mask), 
   (Mask=(N=V)-> (sinkbits_to_number(V,VV) , VV is VV /\ Mode , nb_extend_list(Bits,N),fail) ; 
   (Arg0 is Arg -1, sinkbits_to_number(bit(Arg0),VV) , VV is VV /\ Mode , nb_extend_list(Bits,Mask),fail)))),!,
  BitsOut = Bits.


nb_extend_list(List,E):-arg(2,List,Was),nb_setarg(2,List,[E|Was]).

must_ts(G):- G*-> true; throw(must_ts_fail(G)).

merge_sinkmodes(V,VV,VVV):-number(V),V<0,!,V0 is -V,merge_sinkmodes(-(V0),VV,VVV),!.
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
sinkbits_to_number(V,VVV) :- catch(( VVV is V),_,fail),!.
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
sinkbits_to_number((Bit),VVV):-bits_for_sinkmod(VV),arg(N,VV,Bit),N0 is N-1,!,sinkbits_to_number(bit(N0),VVV),!.






%% memberchk_same( ?X, :TermY0) is semidet.
%
% Uses =@=/2,  except with variables, it uses ==/2.
%
memberchk_same(X, List) :- is_list(List),!, \+ atomic(List), C=..[v|List],!,(var(X)-> (arg(_,C,YY),X==YY) ; (arg(_,C,YY),X =@= YY)),!.
memberchk_same(X, Ys) :-  nonvar(Ys), var(X)->memberchk_same0(X, Ys);memberchk_same1(X,Ys).
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
% An attributed variable that records it''s experience
%
% "She seems to regret all of her mistakes and continues to make them"
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


test_helper(Type) :- writeln(var=call(Type,X)), call(Type,X),  writeln(Type=X),  ignore((member(X,[1,2,3,3,3,1,2,3]),
   get_attrs(X,Ats),writeln(Ats=X),fail)),
   get_attrs(X,Attrs),writeln(get_attrs=Attrs).

test(plvar):-test_helper(plvar).
test(adder):-test_helper(counter_var).


:- if((
  exists_source( library(logicmoo_utils)),
  current_predicate(gethostname/1), 
  % fail,
  gethostname(ubuntu))).

:- use_module(library(logicmoo_utils)).

:- early_sinks.
:- debug_sinks.
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



:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A)))),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A)))))).

:- endif.

