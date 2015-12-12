% #!/usr/bin/env swipl

/*
This not a library yet .. just a test script

  make ; make install ; clsk ; make ; swipl -f library/sinktest.pl

*/

:- module(sinktest,[memory_var/1,memberchk_same/2,termsink/2,with_smz/1,with_sm/2,memory_sink/1,termsink/1,anonvar/1,anything_once/1,v3/0,v4/0,vt/1,varq/1,plvar/1]).
% :- sinkmode(_,0).
:-  use_module(library(logicmoo_utils)).

:-module_transparent((with_smz/1,with_sm/2)).
with_sm(N,G):- sinkmode(W,N),call_cleanup(G,sinkmode(_,W)).
with_smz(G):- sinkmode(W,16777216),call_cleanup(G,sinkmode(_,W)).


bits_for_sinkmod(v(
    remainVar, % 1
	dontCare, % 2
    dontTrail, % 4
	trailOther, % 8
    skipWakeup, % 16
    scheduleOther, % 32
	passReferenceToAttvar, % 64
    termSource, %128
    containsSlowUnify, % 512
	slowUnifyUneeded, % 1024
	twoO48, % 
    attrVarBeforeVar,  % 4096
	attrVarAfterVar,  % 8192
	dontCare(unifiable),  % 16xxx
	dontCare(==), % 32xxx
	dontCare(=), % do_unify 65536
	dontCare(=@=), % 128xxx
    sinkDebug=bit(24)
    )).

anonvar(X):-termsink(X,dontCare+scheduleOther+dontTrail),!.
termsink(X):-termsink(X,remainVar+scheduleOther),!.
termsource(X):-termsink(X,termSource+remainVar+scheduleOther),!.
plvar(X):-termsink(X,termSource+remainVar+scheduleOther),!.

'$sink':attr_unify_hook(X,Y):- format('~N~q.~n',['$sink':attr_unify_hook(sinkmode=X,value=Y)]).
'$ident':attr_unify_hook(X,Y):- ignore(with_smz((get_attrs(X,Attribs), format('~N~q.~n',[attr_unify_hook(X==(Y+Attribs))])))).
'termsource':attr_unify_hook(Goal,Y):- Call= call(Goal,Y),writeq(Call),with_smz(Call).

gvar:attrib_unify_hook(N,V):-var(V),!,b_getvar(N,V).
gvar:attrib_unify_hook(N,V):-var(V),!,b_setvar(N,V).
gvar(X):- with_smz((format(atom(N),'~q',[X]),nb_linkval(N,X),termsink(X,set(termSource+remainVar)),put_attr(X,gvar,N))).
varq(X):-termsink(X),put_attr(X,varq,X).
varq:attr_unify_hook(_,_).
varq:early_unify_hook(Var,_Attrib,NewValue):- 
   (get_attr(Var,varq,OldValue) -> (OldValue==NewValue,put_attr(Var,varq,NewValue)); put_attr(Var,varq,NewValue)),!.

plvar(X):-termsink(TS),put_attr(X,plvar,TS),TS=X.

plvar:attr_unify_hook(_,_).
plvar:early_unify_hook(Var,_Attrib,NewValue):- 
   (get_attr(Var,plvar,OldValue) -> 
     (OldValue=NewValue,put_attr(Var,plvar,NewValue)); put_attr(Var,plvar,NewValue)).


sinkmode:-sinkmode(M,M),mode_to_bits(M,B),format('~N~q.~n',[sinkmode(M=B)]).
mode_to_bits(Mode,BitsO):- Bits=[[]],bits_for_sinkmod(MASKS),
 ignore((arg(Arg,MASKS,Mask), 
   (Mask=(N=V)-> (to_sink_mode(V,VV) , VV is VV /\ Mode , nb_extend_list(Bits,N),fail) ; 
   (to_sink_mode(bit(Arg),VV) , VV is VV /\ Mode , nb_extend_list(Bits,Mask),fail)))),
  BitsO = Bits.

nb_extend_list(List,E):-arg(2,List,Was),nb_setarg(2,List,[E|Was]).
% passReferenceToAttvar
attrVarBeforeVar:- set_sinkmode(attrVarAfterVar+attrVarBeforeVar+sinkDebug+containsSlowUnify),sinkmode.


merge_sink_modes(V,VV,VVV):-number(V),V<0,!,V0 is -V,merge_sink_modes(-(V0),VV,VVV),!.

merge_sink_modes(V,VV,VVV):-number(V),number(VV),VVV is (V /\ VV).
merge_sink_modes(V,VV,VVV):-var(V),!,V=VV,V=VVV.
merge_sink_modes(set(V),_,VVV):-to_sink_mode(V,VVV),!.
merge_sink_modes(V,VV,VVV):-var(VV),!, to_sink_mode(V,VVV),!.

merge_sink_modes(+(A),B,VVV):- must((to_sink_mode(A,V),to_sink_mode(B,VV),!,VVV is (V \/ VV))).
merge_sink_modes(*(A),B,VVV):- to_sink_mode(A,V),to_sink_mode(B,VV),!,VVV is (V /\ VV).
merge_sink_modes(-(B),A,VVV):- to_sink_mode(A,V),to_sink_mode(B,VV),!,VVV is (V /\ \ VV).
merge_sink_modes([A],B,VVV):-  must(merge_sink_modes(A,B,VVV)),!.
merge_sink_modes([A|B],C,VVV):-merge_sink_modes(A,C,VV),merge_sink_modes(B,VV,VVV),!.
merge_sink_modes(A,C,VVV):-to_sink_mode(A,VV),!,must(merge_sink_modes(VV,C,VVV)),!.


to_sink_mode(V,O):-var(V),!,V=O.
to_sink_mode(N,O):-number(N),!,N=O.
to_sink_mode(V,VVV) :- catch(( VVV is V),_,fail),!.
to_sink_mode(B+A,VVV):- merge_sink_modes(+(A),B,VVV),!.
to_sink_mode(B*A,VVV):- merge_sink_modes(*(A),B,VVV),!.
to_sink_mode(B-A,VVV):- to_sink_mode(B,BB),to_sink_mode(A,AA),VVV is (BB /\ \ AA),!.
to_sink_mode(+(Bit),VVV):-to_sink_mode((Bit),VVV),!.
to_sink_mode(-(Bit),VVV):-to_sink_mode((Bit),V),!,VVV is ( \ V).
to_sink_mode(bit(Bit),VVV):- number(Bit),!,VVV is 2 ^ (Bit).
to_sink_mode(bit(Bit),VVV):-bits_for_sinkmod(VV),arg(N,VV,Bit),N0 is N-1,!,to_sink_mode(bit(N0),VVV),!.
to_sink_mode(set(Bit),VVV):-bits_for_sinkmod(VV),arg(N,VV,Bit),N0 is N-1,!,to_sink_mode(bit(N0),VVV),!.
to_sink_mode((Name),VVV):-bits_for_sinkmod(VV),arg(_,VV,Name=Bit),!,must(to_sink_mode(Bit,VVV)),!.
to_sink_mode([A],VVV):-!,to_sink_mode(A,VVV).
to_sink_mode([A|B],VVV):-!,merge_sink_modes(B,A,VVV).
to_sink_mode((Bit),VVV):-bits_for_sinkmod(VV),arg(N,VV,Bit),N0 is N-1,!,to_sink_mode(bit(N0),VVV),!.

set_sinkmode(X):- sinkmode(M,M),merge_sink_modes(X,M,XM),sinkmode(_,XM).

:- rtrace(attrVarBeforeVar).

termsink(X,V):-with_smz((((get_attr(X,'$sink',VV)->(VV==V->true;(merge_sink_modes(V,VV,VVV),
   put_attr(X,'$sink',VVV)));(to_sink_mode(V,VV),put_attr(X,'$sink',VV)))),put_attr(X,'$ident',X))),!.



termsink:attr_unify_hook(_,_).




uhook_early(Module, Var, AttVal, Value):-  (current_predicate(Module:early_unify_hook/3)->Module:early_unify_hook(Var, AttVal, Value);true).

'$sink':call_all_attr_uhooks_early(_,[], _).
'$sink':call_all_attr_uhooks_early(Var,att(Module, AttVal, Rest), Value) :-
        uhook_early(Module, Var, AttVal, Value),        
	'$sink':call_all_attr_uhooks_early(Var, Rest, Value).




%% memberchk_same( ?X, :TermY0) is semidet.
%
% Memberchk Same.
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

v1 :- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).
:- v1.


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
nr:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz), \+ memberchk_same(VarValue,Waz),nb_setarg(1,AttValue,[VarValue|Waz]).

anything_once(Var):- nonvar(Var) ->true; (get_attr(Var,nr,_)->true;put_attr(Var,nr,old_vals([]))).
v2 :- anything_once(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(anything_once=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).
:- v2.
 

zar:attr_unify_hook(AttValue,VarValue):- writeq(zar:attr_unify_hook(AttValue,VarValue)),nl.

%% memory_sink(+Var) is det.
%
%  Makes a variable that remembers all of the previous bindings (even the on ..)
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
% memory_sink(Var):-termsink(Sink,[]), put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.
memory_sink(Var):-termsink(Var,[]),put_attr(Var,'_',Var),put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.

vt(Type) :- writeln(var=call(Type,X)), call(Type,X),  writeln(Type=X),  ignore((member(X,[1,2,3,3,3,1,2,3]),
   get_attrs(X,Ats),writeln(Ats=X),fail)),
   get_attrs(X,Attrs),writeln(get_attrs=Attrs).

v3:-vt(plvar).
v4:-vt(varq).
% :- sinkmode(_,15).
% :- sinkmode(_,0).
% :- X is 512+1+2+4+8+16+32, sinkmode(_,X).
%:- v3.
%:- v4.
% :- termsink(X),X=1,X=2,Y=X,Z=Y,X=1,T=1,T=X.

:- export(q/0).

q :- q(X), writeln(X).
q(X) :- depth_of_var(X, D), format('Depth = ~w~n', [D]), D < 5, q(X),notail.

notail.


/*

:- ignore(q).

Running this says:

1 ?- q.
Depth = 1
Depth = 2
Depth = 3
Depth = 4
Depth = 5

*/ 


varinfo(X):-depth_of_var(X, D2), format('Depth of ~q = ~w~n', [X,D2]).

:- export(q2/0).

q2 :- q2(X), writeln(X).
q2(X) :- varinfo(X), depth_of_var(X, D), ((integer(D),D < 5) -> (q2(X),notail); true).

%:- q2.


t1 :- plvar(X),X=2,X=3,X=4.

%:- t1.




%:- public ((attr_unify_hook/2,attr_portray_hook/2)).

t2 :- \+ t2f, t2p.

t2f :- writeln(X), X=1,writeln(X=1),
      
      X=2,
      writeln(X).

t2p :- termsink(X), writeln(X), X=1,writeln(X=1),
      
      X=2,
      writeln(X).

%:-t2.


is_term_sink(X):-
   writeln(entry=X),
   varinfo(X), 
   writeln(permsink=X),
   X = 1,
   writeln(X=1),
   X = 2,
   writeln(X=2),
   X = 3,
   writeln(X=3),notail.


with_ps(D,X):- (D < 1 -> fail ; (D2 is D-1, !, with_ps(D2,X))),notail.
with_ps(D,X):- writeln(with_ps(D,X)),termsink(X,_), is_term_sink(X).


t3 :- X=_,with_ps(3,X).

/*

entry=_G844
Depth of _G844 = _G849
permsink=_G844
_G844=1
_G844=2
_G844=3


*/

t4 :- X=_,with_ps(10,X).

:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A)))),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A)))))).





:- termsink(X),X=2,X=3,X=4.

:- termsink(X),
      writeln(X),
      X=1,writeln(X),
      
      X=2,
      writeln(X).



















end_of_file.




% :- use_module(library(logicmoo_utils)).

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

% :- read_attvars(true).

sk_in(avar([vn='Ex',sk='SKF-666'])).

:- listing(sk_in).

% :- must((sk_in(Ex),get_attr(Ex,sk,What),What=='SKF-666')).



/*
Running this says:

1 ?- q.
Depth = 1
Depth = 2
Depth = 3
Depth = 4
Depth = 5

*/



end_of_file.


/*
		if( (LD->attvar.gsinkmode & 1024) != 0 ) {
			bool unifyWasSuccess, assumeAssigned, trailUnneeded, restart;
			if( canUnifyAttVar(ATOM_equals, &unifyWasSuccess, &assumeAssigned, &trailUnneeded, &restart, t1, t2 PASS_LD) ) {

				if( restart ) {
					return(do_unify(t1, t2 PASS_LD));
				}
				if( unifyWasSuccess ) {
					if( assumeAssigned ) {
						continue;
					} else {
						assignThis = TRUE;
					}
				} else {
					goto out_fail;
				}

				if( trailUnneeded ) {
					trailThis = FALSE;
				}
			}
		}
*/

bool
canUnifyAttVar(atom_t uniftype, bool* unifyWasSuccess, bool *assumeAssigned, bool* trailUnneeded, bool* restart, Word av, Word value ARG_LD) {

	*unifyWasSuccess = *assumeAssigned = *trailUnneeded = *restart = FALSE;
	
    if( LD->attvar.sinkdepth > 2) return FALSE;

	wakeup_state wstate;
	if( !saveWakeup(&wstate, TRUE PASS_LD) )
		return(FALSE);

	LD->attvar.sinkdepth++;

	int rc;
	predicate_t  pred;

	fid_t fid;
	if( !(fid = PL_open_foreign_frame()) ) return(FALSE);

	pred = _PL_predicate("unify_attvar", 9, "$attvar",
						 &GD->procedures.unify_attvar6);

	term_t avr = PL_new_term_refs(9);

	deRef(av); 
	deRef(value); 

	PL_put_atom(avr,uniftype);
	*valTermRef(avr+1) = makeRef(av);   
	*valTermRef(avr+2) = makeRef(value);

	qid_t qid;


	if( (qid = PL_open_query(NULL,PL_Q_NODEBUG|PL_Q_PASS_EXCEPTION, pred, avr)) ) {
		rc = PL_next_solution(qid);
		PL_cut_query(qid);
	} else
		rc = FALSE;

	if( rc != TRUE && !PL_exception(0) )
		rc = TRUE;

	if( rc == TRUE ) {

		bool b;
		if( PL_get_bool(avr+5, &b ) ) {
			*unifyWasSuccess = b;
		}
		if( PL_get_bool(avr+6, &b ) ) {
			*assumeAssigned = b;
		}
		if( PL_get_bool(avr+7, &b ) ) {
			*trailUnneeded = b;
		}
		if( PL_get_bool(avr+8, &b ) ) {
			*restart = b;
		}
		if( restart ) {
			*av = *valTermRef(avr+3);
			*value = *valTermRef(avr+4);
		}
	}
	PL_discard_foreign_frame(fid);
	LD->attvar.sinkdepth--;
	restoreWakeup(&wstate PASS_LD);
	return(rc);
}

