/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2004-2013, University of Amsterdam
			      VU University Amsterdam

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

:- module('$attvar',
	  [ '$wakeup'/1,		% +Wakeup list
            % undo/1,                     % :Goal
            freeze/2,			% +Var, :Goal
	    frozen/2,			% @Var, -Goal
	    call_residue_vars/2,        % :Goal, -Vars
	    copy_term/3                 % +Term, -Copy, -Residue
	  ]).

:- meta_predicate '$wakeup'(0).

/** <module> Attributed variable handling

Attributed  variable  and  coroutining  support    based  on  attributed
variables. This module is complemented with C-defined predicates defined
in pl-attvar.c
*/

%%	'$wakeup'(+List)
%
%	Called from the kernel if assignments have been made to
%	attributed variables.

% each variable will be shut off one at a time and global will be re-enabled once a var is shut off
'$wakeup'(G) :- with_meta_disabled(global,G).


       /*******************************
       *         UTILS    *
       *******************************/

system:goals_with_module([G|Gs], M):- !,
	M:call(G),
	system:goals_with_module(Gs, M).
system:goals_with_module(_,_).

:- meta_predicate(system:ifdef(0,0)).
system:ifdef(IfDef,Else):-'$c_current_predicate'(_, IfDef)->IfDef;Else.


amsg(G):- notrace(
   ignore((current_prolog_flag(dmiles,true),
           ifdef(logicmoo_util_dmsg:dmsg(G),
                  format(user_error,'~N,~q~n',[G]))))).




       /*******************************
       *         PRE_UNIFY        *
       *******************************/

:- meta_predicate(system:pre_unify(+,0,+,+,+)).

% METATERMs
system:pre_unify(att('$atts',_Was,Rest), Next, Var, Value, Atom ):- !,
  writeln(meta_unify(Atom, Var, Value )),
  meta_unify(Rest, Atom, Var, Value),
  call(Next).

% BOUND
system:pre_unify(Atts, Next, Var, Value, Atom ):- \+ attvar(Var),!,
   system:post_unify(Atts, Next, Var, Value, Atom ).

% ATTVARs
system:pre_unify(Atts, Next, Var, Value, Atom ):-
  amsg(Atom:collect_va(Atts, Next, Var, Value )),
  redo_call_cleanup_av(push_attvar_waking(Var),
    collect_va(Atts, Next, Var, Value),pop_attvar_waking(Var)).


      /*******************************
      *         VERIFY_ATTRIBUTES/3    *
      *******************************/

:- meta_predicate(system:collect_va(+,:,+,+)).
system:collect_va(att(Module, _AttVal, Rest), Next, Var, Value ):- !,
        ifdef(Module:verify_attributes(Var, Value, VAGoals),VAGoals=[]),
        collect_va(Rest, Next, Var, Value),
        goals_with_module(VAGoals,Module).

system:collect_va(_,Next,Var,Value):- 
      verify_attributes(Var, Value),
      call(Next).


      /*******************************
      *         VERIFY_ATTRIBUTES/2  *
      *******************************/

system:verify_attributes(Var, Value):- attvar(Var),!,
   '$trail_assignment'(Var),
   ignore(attv_unify(Var,Value)).
   
system:verify_attributes(Value, Value).


     /*******************************
     *	  METATERM UNIFY HOOK	*
     *******************************/

:- meta_predicate(system:meta_unify(+,0,+,+)).
system:meta_unify(att('var_replace', var_replace(Copy,Call), Rest), Atom, _Var, Value):- !,
         call(Call),
         system:pre_unify(Rest,true,Copy,Value,Atom).

system:meta_unify(att('$atts_saved', MV, Rest), Atom, Var, Value ):- !,
      ((var(Var),MV>0)->put_attr(Var,'$atts',MV);true),
      system:meta_unify(Rest,Atom,Var,Value).

system:meta_unify(att(Module, AttVal, Rest), Atom, Var, Value ):- !,
     ifdef(Module:meta_unify_hook(Atom, AttVal, Var, Value),true),
     meta_unify(Rest, Atom, Var, Value).

system:meta_unify(_,_Atom,_Var,_Value).


     /*******************************
     *   C POST UNIFY HOOK	*
     *******************************/

:- meta_predicate(system:post_unify(+,0,+,+,+)).
system:post_unify(Atts, Next, Var, Value, Atom ):-
  amsg(Atom:post_unify(Atts, Next, Var, Value )),
  redo_call_cleanup_av(push_attvar_waking(Var),
    post_unify(Atts, Next, Var, Value),pop_attvar_waking(Var)).


     /*******************************
     *   ATTR UNIFY HOOK	*
     *******************************/

:- meta_predicate(call_uhooks(+,0,+,+)).
call_uhooks(att(Module, AttVal, Rest), Next, Var, Value ):- !,
        ifdef(Module:attr_unify_hook(AttVal, Value),true),
        call_uhooks(Rest, Next, Var, Value).

call_uhooks(_,Next,Var,Value):- nop(verify_attributes(Var, Value)),
        call(Next).



        /*******************************
	 *	      FREEZE		*
         *******************************/

%%	freeze(@Var, :Goal)
%
%	Suspend execution of Goal until Var is bound.

:- meta_predicate
	freeze(?, 0).

freeze(Var, Goal) :-
	'$freeze'(Var, Goal), !.	% Succeeds if delayed
freeze(_, Goal) :-
	call(Goal).

%%	frozen(@Var, -Goals)
%
%	Unify Goals with the goals frozen on Var or true if no
%	goals are grozen on Var.

frozen(Var, Goals) :-
	get_attr(Var, freeze, Goals0), !,
	make_conjunction(Goals0, Goals).
frozen(_, true).

make_conjunction('$and'(A0, B0), (A, B)) :- !,
	make_conjunction(A0, A),
	make_conjunction(B0, B).
make_conjunction(G, G).

/* DM: TODO - Ensure verify_attributes/3 works ! */
freeze:verify_attributes(Var, Other, Gs) :-
	\+ current_prolog_flag(wakeups,va3) -> Gs=[] ;
	(   get_attr(Var, freeze, Goal)
	->  (	attvar(Other)
	    ->	(   get_attr(Other, freeze, G2)
		->  put_attr(Other, freeze, '$and'(G2, Goal))
		;   put_attr(Other, freeze, Goal)
		),
		Gs = []
	    ;	Gs = ['$attvar':unfreeze(Goal)]
	    )
	;   Gs = []
	).


/* DM: TODO - Ensure this would have worked just as well! */
freeze:attr_unify_hook(Goal, Y) :-
	current_prolog_flag(wakeups,va3) -> true ;
	(   attvar(Y)
	->  (   get_attr(Y, freeze, G2)
	    ->	put_attr(Y, freeze, '$and'(G2, Goal))
	    ;	put_attr(Y, freeze, Goal)
	    )
	;   unfreeze(Goal)
	).

%%	unfreeze(+ConjunctionOrGoal)
%
%	Handle  unfreezing  of  conjunctions.  As  meta-calling  control
%	structures is slower than meta-interpreting them   we do this in
%	Prolog. Another advantage is that   having unfreeze/1 in between
%	makes the stacktrace and profiling   easier  to intepret. Please
%	note that we cannot use a direct conjunction as this would break
%	freeze(X, (a, !, b)).

unfreeze('$and'(A,B)) :- !,
	unfreeze(A),
	unfreeze(B).
unfreeze(Goal) :-
	Goal.

		 /*******************************
		 *	       PORTRAY		*
		 *******************************/

%%	portray_attvar(@Var)
%
%	Called from write_term/3 using the option attributes(portray) or
%	when the prolog flag write_attributes   equals portray. Its task
%	is the write the attributes in a human readable format.

:- public
	portray_attvar/1.

portray_attvar(Var) :-
	write('{'),
	get_attrs(Var, Attr),
	portray_attrs(Attr, Var),
	write('}').

portray_attrs([], _).
portray_attrs(att(Name, Value, Rest), Var) :-
	portray_attr(Name, Value, Var),
	(   Rest == []
	->  true
	;   write(', '),
	    portray_attrs(Rest, Var)
	).

portray_attr(freeze, Goal, Var) :- !,
	format('freeze:freeze(~w, ~W)', [ Var, Goal,
				   [ portray(true),
				     quoted(true),
				     attributes(ignore)
				   ]
				 ]).
portray_attr(Name, Value, Var) :-
	G = Name:attr_portray_hook(Value, Var),
	(   '$c_current_predicate'(_, G),
	    G
	->  true
	;  fa(Name,Value)
	).
 
system:attr_portray_hook(Name,Value):- fa(Name,Value).

fa(Name,Value):-
  current_prolog_flag(write_attributes,W),
  set_prolog_flag(write_attributes, ignore),
        format('~q:~W', [Name, Value,
				   [ portray(true),
				     quoted(true),
				     attributes(ignore)
				   ]
        ]),
   set_prolog_flag(write_attributes, W).


		 /*******************************
		 *	    CALL RESIDUE	*
		 *******************************/

%%	call_residue_vars(:Goal, -Vars)
%
%	If Goal is  true,  Vars  is   the  set  of  residual  attributed
%	variables created by Goal. Goal  is   called  as in call/1. This
%	predicate  is  for  debugging  constraint   programs.  Assume  a
%	constraint program that creates  conflicting   constraints  on a
%	variable that is not part of the   result  variables of Goal. If
%	the solver is powerful enough it   will  detect the conflict and
%	fail. If the solver is too  weak   however  it  will succeed and
%	residual attributed variables holding the conflicting constraint
%	form a witness of this problem.

:- meta_predicate
	call_residue_vars(0, -).

call_residue_vars(Goal, Vars) :-
	prolog_current_choice(Chp),
	setup_call_cleanup(
	    '$call_residue_vars_start',
	    run_crv(Goal, Chp, Vars, Det),
	    '$call_residue_vars_end'),
	(   Det == true
	->  !
	;   true
	).
call_residue_vars(_, _) :-
	fail.

run_crv(Goal, Chp, Vars, Det) :-
	with_meta_enabled(global,call(Goal)),
	deterministic(Det),
        '$attvars_after_choicepoint'(Chp, Vars).

%%	copy_term(+Term, -Copy, -Gs) is det.
%
%	Creates a regular term Copy  as  a   copy  of  Term (without any
%	attributes), and a list Gs of goals that when executed reinstate
%	all attributes onto Copy. The nonterminal attribute_goals//1, as
%	defined in the modules the  attributes   stem  from,  is used to
%	convert attributes to lists of goals.

copy_term(Term, Copy, Gs) :-
	term_attvars(Term, Vs),
	(   Vs == []
	->  Gs = [],
	    copy_term(Term, Copy)
	;   findall(Term-Gs,
		    ( phrase(attvars_residuals(Vs), Gs),
		      delete_attributes(Term)
		    ),
		    [Copy-Gs])
	).

attvars_residuals([]) --> [].
attvars_residuals([V|Vs]) -->
	(   { get_attrs(V, As) }
	->  attvar_residuals(As, V)
	;   []
	),
	attvars_residuals(Vs).

attvar_residuals([], _) --> [].
attvar_residuals(att(Module,Value,As), V) -->
	(   { nonvar(V) }
	->  % a previous projection predicate could have instantiated
	    % this variable, for example, to avoid redundant goals
	    []
	;   (	{ Module == freeze }
	    ->	frozen_residuals(Value, V)
	    ;	{ current_predicate(Module:attribute_goals//1) }
	    ->	{ phrase(Module:attribute_goals(V), Goals) },
		list(Goals)
	    ;	[put_attr(V, Module, Value)]
	    )
	),
	attvar_residuals(As, V).

list([])     --> [].
list([L|Ls]) --> [L], list(Ls).

delete_attributes(Term) :-
	term_attvars(Term, Vs),
	delete_attributes_(Vs).

delete_attributes_([]).
delete_attributes_([V|Vs]) :-
	del_attrs(V),
	delete_attributes_(Vs).


%%	frozen_residuals(+FreezeAttr, +Var)// is det.
%
%	Instantiate  a  freeze  goal  for  each    member  of  the  $and
%	conjunction. Note that we cannot  map   this  into a conjunction
%	because  freeze(X,  a),  freeze(X,  !)  would  create  freeze(X,
%	(a,!)),  which  is  fundamentally  different.  We  could  create
%	freeze(X,  (call(a),  call(!)))  or  preform  a  more  eleborate
%	analysis to validate the semantics are not changed.

frozen_residuals('$and'(X,Y), V) --> !,
	frozen_residuals(X, V),
	frozen_residuals(Y, V).
frozen_residuals(X, V) -->
	[ freeze(V, X) ].



end_of_file.



% nop/1 is for disabling code while staying in syntax
system:nop(_).


system:make_var_cookie(Var,VarID:SAtts):- assertion(attvar(Var)),
   del_attr(Var,cookie), get_attrs(Var,Atts),
   format(string(VarID),'~q',[Var]),
   format(string(SAtts),'~q',[attrs(Var,Atts)]),
   put_attr(Var,cookie,VarID).

cookie:verify_attributes(_,_,[]).

check_var_cookie(Var,FirstID:Expect):-
  assertion(get_attr(Var,cookie,LastVarID)), % cookie is missing then something trampled this var (this is to decide how much to panic)
   make_var_cookie(Var,VarID:SAtts),
   nop((Expect==SAtts->true;print_message(trace,format('~N~q~n',[Expect==SAtts])))),
   ((FirstID==VarID)
    ->true;
     (backtrace(30),
      (LastVarID==FirstID-> Type = warning ; Type = error),  % detect between a shifts maybe vs a attvar bwing overwritten 
       print_message(Type,format('~N~q~n',[Expect==SAtts])),
       set_prolog_flag(access_level,system), % ensures trace durring wakeup
       % leaving trace nop'ed out so we can run make check or other things easier
       nop(trace), % someomes can just leap here since there will be false postives
       nop(throw(Expect==SAtts)))),!.


       /*******************************
           *	  VERIFY ATTRIBUTES	* 
       *******************************/

%%	pre_unify(+Att3s, +Next, +Var, +Value)
%
%	Called from the kernel if assignments will be made to attributed
%	variables.
%
%	First calls Module:verify_attributes/3 for each `Module` for which Var
%	has an attribute. During this process,   modules  may remove and
%	change each others attributes.
%
%       If a callee removes the '$unify' property we succeed unconditionally

no_pre_unify:- true.

        

                   /*******************************
                   *	  PEER UNIFY HOOKS	*
                   *******************************/

:- meta_predicate(system:peer_unify(+,0,+,+,-)).

system:peer_unify(att(Module, _AttVal, Rest), Next, Var, Value,(goals_with_module(Goals,Module),G)):- !,
	metaterm_flags(Var,set,0x0060), % no_wake + no_inherit
	system:ifdef(Module:verify_attributes(Var, Value, Goals),Goals=[]),
	system:peer_unify(Rest, Next, Var, Value, G).

system:peer_unify(_,Next,_, _, Next).

%%	wakeup(+Var, +NextOnChain, +Value)
%
%  Calls  Module:verify_attributes/2 on caller Module

:- meta_predicate(wakeup(?,:,?)).
/* durring runtime this seems to be calling in the correct module (clpfd chr_runtime etc etc)  
   next section bellow fills in where term expansion misses things */
wakeup(Var,M:Next, Value):- M:verify_attributes(Var, Value), M:call(Next).

       /*******************************
       *       FOR SISCTUS   *
       *******************************/

/* Note if a user doesnt know how they wished to handle all the properties of a variable
  they may call system:verify_attributes/2 since it will call attv_unify/2  */

system:verify_attributes(Var, Value):-
    get_attrs(Var,Att3s),!,
    pre_unify(Att3s,Var,Value).

