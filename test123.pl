
:- use_module(library(logicmoo_webbot)).

end_of_file.



% :- shell('cmd.exe /c mode con: cols=180 lines=78').

% ta:- use_unify_var,lv,!, metaterm_override(X, print : nop), source_fluent(X),sink_fluent(X),print(X).

prolog_temp_debug(Type):- undo(prolog_nodebug(Type)),prolog_debug(Type).

% :- set_prolog_flag(dmiles,true).

% :- wo_metaterm(plvar(_)).


% metaterm_test:- source_fluent(X),metaterm_setval(X,foo),Y=X,Y==foo,meta(X).

%  source_fluent(X),metaterm_copy_var(X),metaterm_setval(X,foo),dmsg( ( x : X , y : Y ) ),trace,Y=X,Y=foo,meta(X).



% :- use_unify_var.




do_metaterm_tests:- forall(clause(metaterm_test,B),(nl,nl,run_b_test(B),nl,nl)).

:- discontiguous(metaterm_test/0).


run_b_test(B):- amsg(run_test(B)),fail.
run_b_test(B):- catch((call((B,deterministic(Det),true)),!,(Det==true->amsg(test_passed(B));amsg(test_warn_nondet(B)))),_,fail),!.
run_b_test(B):- catch((rtrace_each(B),fail),E,amsg(test_error(E,B))),!.
run_b_test(B):- amsg(test_failed(B)),!.

rtrace_each((A,B)):-!,rtrace_each(A),!,rtrace_each(B),!.
rtrace_each(B):-rtrace(B).

mc:- X:=1,prolog_debug('msg_call'),X=1.

prolog_nodebug:- prolog_nodebug('MSG_WAKEUPS'),prolog_nodebug('MSG_METATERM'),prolog_nodebug('MSG_METATERM_VMI'),prolog_nodebug('MSG_DRA').

:- set_prolog_flag(write_attributes, ignore).

test123 :-test123(_X).

test123(plvar_1):- with_metaterm(( plvar(X),X=1,Y=X, wo_metaterm(( var(X),integer(Y), X\==Y, Y==1  )), trace, integer(X),X==1,X==Y )).

% with_metaterm(( plvar(X),X=1,Y=X, wo_metaterm(( var(X),integer(Y), X\==Y, Y==1  )), trace, integer(X),X==1,X==Y )).

:- discontiguous(test123/1).

foo(_):- throw(error).  system:bar(_):- writeln(passed).

% if X is called in foo/1, bar/1 will override it
test123(simple_override):- metaterm_override(X,foo/1=bar/1),foo(X).

test123(simple_override2):- metaterm_override(X,foo/1=bar/1),plvar(X),with_prolog_debug('MSG_VMI',((X=1,foo(X)))).

te:-  prolog_temp_debug('MSG_VMI'),lv.

ta:-test123(simple_override),test123(simple_override2).

metaterm_test:- plvar(X),X=1,Y=X,integer(Y).

metaterm_test:- plvar(X),X=Y,metaterm_getval(X,XX),XX==Y.

ev_integer(X):-metaterm_getval(X,V),integer(V).

metaterm_test:- plvar(X),X=1,_Y=X,metaterm_override(X,integer/1=ev_integer/1), integer(X).

metaterm_test:- plvar(X),_Y=X,metaterm_override(X,integer/1=ev_integer/1), \+ integer(X).

metaterm_test:- plvar(X),X=1,_Y =X,integer(X).

tn:- source_fluent(X),metaterm_setval(X,1),X==1.

coax_int(X):- number(X),!.
coax_int(0).

% if X is called in integer/1, coax_int/1 will override it
t20:- metaterm_override(X,integer/1=coax_int/1),
  must(integer(X)),true.


ta11:- metaterm_override(X,writeln/1=dmsg/1), % ,metaterm_setval(X,foo),
  trace, call(call,writeln,X),true.


ta1:- metaterm_override(X,writeln/1=dmsg/1),metaterm_setval(X,foo),
  prolog_temp_debug('MSG_CALL'),writeln(X).

ta2:- metaterm_override(X,writeln/1=dmsg/1),metaterm_setval(X,foo),
  writeln(X).

ta3:- metaterm_override(X,compare/3=dshow/3), % metaterm_override(X, == : '=='/2),
   trace,prolog_temp_debug('MSG_CALL'),call(writeln(X)), call(X==1).

ta4:- plvar(X),X=999999,Y=X,writeq(x=X),rtrace(Y==X).


% :- Y=_,sink_fluent(X),source_fluent(X),trace,X=1,trace,X=Y.




% :- [src/test_va]. 



/*
:- if((
  exists_source( library(logicmoo_utils)),
  current_predicate(gethostname/1), 
  % fail,
  gethostname(ubuntu))).
*/

:- use_module(library(http/http_path)).
:- use_module(library(http/http_host)).
:- use_module(library(logicmoo_utils)).


:- wo_metaterm(use_listing_vars).

 % :- debug(_).
% :- debug_fluents.
% :- source_fluent.
:- debug(fluents).

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
    % :- debug(_).
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

v1(X,V) :- put_atts(V,X),show_var(V).



%:- endif.


/*



metaterm_test:- 
 put_attr(X, tst, a), X = a.
verifying: _G389386 = a;  (attr: a)
X = a.


metaterm_test:-  put_attr(X,tst, vars(Y)), put_attr(Y,tst, vars(X)), [X,Y] = [x,y(X)].
verifying: _G389483 = x;  (attr: vars(_G389490))
verifying: _G389490 = y(x);  (attr: vars(x))


metaterm_test:- VARS = vars([X,Y,Z]), put_attr(X,tst, VARS), put_attr(Y,tst,VARS), put_attr(Z,tst, VARS), [X,Y,Z]=[0,1,2].
verifying: _G389631 = 0;  (attr: vars([_G389631,_G389638,_G389645]))
verifying: _G389638 = 1;  (attr: vars([0,_G389638,_G389645]))
verifying: _G389645 = 2;  (attr: vars([0,1,_G389645]))
VARS = vars([0, 1, 2]),
X = 0,
Y = 1,
Z = 2.


*/

t12:- must_ts(rtrace((when(nonvar(X),member(X,[a(1),a(2),a(3)])),!,findall(X,X=a(_),List),List==[a(1),a(2),a(3)]))).

t22:- must_ts(rtrace( (freeze(Foo,setarg(1,Foo,cant)),  Foo=break_me(borken), Foo==break_me(cant)))).


:- prolog_temp_debug('MSG_WAKEUPS').
:- prolog_temp_debug('MSG_METATERM').
:- prolog_temp_debug('MSG_METATERM_VMI').
:- prolog_temp_debug('MSG_WAKEUPS').
:- prolog_temp_debug('MSG_DRA').


