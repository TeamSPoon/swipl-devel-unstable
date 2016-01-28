/*  Part of SWI-Prolog

    Author:        Douglas Miles
    E-mail:        logicmoo@gmail.com
    WWW:           http://www.swi-prolog.org
    Copyright (C): Public domain
*/

/** <module> XSB compatibility layer

This file contains some predicates that   are  defined in XSB-prolog and
not in SWI-prolog (or at least not  with   the  same meaning). In case a
predicate has a different meaning in  SWI-prolog   and  in Prolog by XSB
renaming is done.  Remark  that  some   predicates  are  only  partially
covered, feel free to add.

@author  Douglas Miles
       
         logicmoo@gmail.com
*/


:- module(machine,[attv_unify/2]).

/*
Example XSB Support
*/

attv_unify(Var,Value):- '$attvar_assign'(Var,Value).


% Switches us from verify_attributes/3 to verify_attributes/2 support
% This predicate is called whenever an attributed variable Var (which has at least one attribute) 
% is about to be bound to Value (a non-variable term or another attributed variable). 
% When Var is to be bound to Value, a special interrupt called attributed variable 
% interrupt is triggered, and then XSB's interrupt handler (written in Prolog) calls 
% verify_attributes/2. If it fails, the unification is deemed to have failed. 
% It may succeed non-deterministically, in which case the unification 
% might backtrack to give another answer.
:- module_transparent(system:verify_attributes/3).
system:verify_attributes(Var, Value, []):- 
      context_module(Mod),
      Mod:verify_attributes(Var, Value).


end_of_file.


% Working example from XSB docs (that works in SWI-Prolog now)

:- module(fd,[domain/2,show_domain/1]).

%:- import put_atts/2, get_atts/2 from atts.
:- use_module(library(dialect/sicstus/atts)). 
:- use_module(library(dialect/xsb)).
%:- import attv_unify/2 from machine.
%:- import member/2 from basics.

:- attribute dom/1.

verify_attributes(Var, Value) :-
        get_atts(Var, dom(Da)),
        (var(Value)                          % Value is an attributed variable
         -> get_atts(Value, dom(Db)),        % has a domain
            intersection(Da, Db, [E|Es]),    % intersection not empty
            (Es = []                         % exactly one element
             -> attv_unify(Var, Value),      % bind Var to Value
                attv_unify(Var, E)           % bind Var (and Value) to E
             ;  attv_unify(Var, Value),      % bind Var to Value
                put_atts(Value, dom([E|Es])) % update Var's (and Value's)
                                             % attributes
            )
         ;  member(Value, Da),               % is Value a member of Da?
            attv_unify(Var, Value)           % bind Var to Value
        ).

intersection([], _, []).
intersection([H|T], L2, [H|L3]) :-
        member(H, L2), !,
        intersection(T, L2, L3).
intersection([_|T], L2, L3) :-
        intersection(T, L2, L3).

domain(X, Dom) :- 
        var(Dom), !, 
        get_atts(X, dom(Dom)). 
domain(X, List) :- 
        List = [El|Els],                     % at least one element 
        (Els = []                            % exactly one element
         -> X = El                           % implied binding 
         ;  put_atts(Fresh, dom(List)),      % create a new attributed variable
            X = Fresh                        % may call verify_attributes/2
        ).

show_domain(X) :-                            % print out the domain of X
        var(X),                              % X must be a variable
        get_atts(X, dom(D)),
        write('Domain of '), write(X),
        write(' is '), writeln(D).



/*
The output of some example queries are listed below, from 
which we can see how attributed variables are unified using verify_attributes/2:
root@gitlab:~/lib/swipl/pack/fluentvars/prolog# swipl -l fd.P
Welcome to SWI-Prolog (Multi-threaded, 64 bits, Version 7.3.14-41-ga3b985d-DIRTY)
Copyright (c) 1990-2015 University of Amsterdam, VU Amsterdam
SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software,
and you are welcome to redistribute it under certain conditions.
Please visit http://www.swi-prolog.org for details.
For help, use ?- help(Topic). or ?- apropos(Word).
?- domain(X,[5,6,7,1]), domain(Y,[3,4,5,6]), domain(Z,[1,6,7,8]),
|             show_domain(X), show_domain(Y), show_domain(Z).
Domain of _G66 is [5,6,7,1]
Domain of _G81 is [3,4,5,6]
Domain of _G96 is [1,6,7,8]
put_attr(X, fd, [dom([5, 6, 7, 1])]),
put_attr(Y, fd, [dom([3, 4, 5, 6])]),
put_attr(Z, fd, [dom([1, 6, 7, 8])]).
?-  domain(X,[5,6,7,1]), domain(Y,[3,4,5,6]), domain(Z,[1,6,7,8]),
|             X = Y, show_domain(X), show_domain(Y), show_domain(Z).
Domain of _G259 is [5,6]
Domain of _G259 is [5,6]
Domain of _G289 is [1,6,7,8]
X = Y,
put_attr(Y, fd, [dom([5, 6])]),
put_attr(Z, fd, [dom([1, 6, 7, 8])]).
?-  domain(X,[5,6,7,1]), domain(Y,[3,4,5,6]), domain(Z,[1,6,7,8]),
|             X = Y, Y = Z.
X = Y, Y = Z, Z = 6.
*/




