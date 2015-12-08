% #!/usr/bin/env swipl

/*
This not a library yet .. just a test script

  make ; make install ; clsk ; make ; swipl -f library/sinktest.pl

*/
:- module(sinktest,[memory_var/1,memberchk_same/2,memory_sink/1,anything_once/1,v3/0]).

% Type can be =,==,=@=,\==, etc
% Result
%  Var -> NewVar
%  Val -> NewVal
% 
%  Result = 
%
%  try_again  = assume either the var or value has been replaced more correctly this time
%  continue
%  completed
%   trail/notrail
%   failed

'$attvar':unify_attvar(Type,Into,With,NewInto,NewWith,Result):- 
  writeq('$attvar':unify_attvar(Type,Into,With)),nl,
   fail,nop(Result),
   (\+ number(With)
    ->((NewWith=With; writeq('$attvar':unify_attvar(Into,With,NewWith))));
      ((NewWith is With * With),writeq('$attvar':unify_attvar(Into,With,NewWith)),( 0 is With div 2))).

'$attvar':unify_nonattvar(Type,Into,With,NewInto,NewWith,Result):- 
  writeq('$attvar':unify_attvar(Type,Into,With)),nl,
   fail,nop(Result),
   (\+ number(With)
    ->((NewWith=With; writeq('$attvar':unify_attvar(Into,With,NewWith))));
      ((NewWith is With * With),writeq('$attvar':unify_attvar(Into,With,NewWith)),( 0 is With div 2))).

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
memory_sink(Var):-termsink(Var,[]), put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.



v3 :- writeln(var=X), memory_sink(X),  writeln(attvar=X),  ignore((member(X,[1,2,3,3,3,1,2,3]),
   get_attrs(X,Ats),writeln(Ats=X),fail)),
   get_attrs(X,Attrs),writeln(get_attrs=Attrs).

:- sinkmode(512,512).
:- v3.

end_of_file.

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

notail.

%:- q2.


t1 :- permsink(X),X=2,X=3,X=4.

%:- t1.




%:- public ((attr_unify_hook/2,attr_portray_hook/2)).



t2 :- writeln(X), X=1,writeln(X=1),
      unset_var(X,D),
      writeln(d=D),
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




























end_of_file.

:- termsink(X),X=2,X=3,X=4.

:- termsink(X),
      writeln(X),
      X=1,writeln(X),
      unset_var(X,D),
      writeln(d=D),
      X=2,
      writeln(X).



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

