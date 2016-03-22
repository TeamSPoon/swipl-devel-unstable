/*  Part of SWI-Prolog

    Author:        Douglas R. Miles
    E-mail:        logicmoo@gmail.com
    WWW:           http://www.swi-prolog.org http://www.prologmoo.com
    Copyright (C): 2015, University of Amsterdam
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

/* 

*/

:- module(atts,[
      % in init.pl
      % wo_metaterm/2,wo_metaterm/1,  with_metaterm/1,
      wno_dmvars/1,w_dmvars/1,
      wno_debug/1,w_debug/1,
      wnmt/1,
      wi_atts/2,
      wd/1,
      metaterm_create/2,
      was_tracing/1,
      was_access_level_atts/1,
      
      unify_val/2,
      undo/1,
      testfv/0,
      swap_args/3,
      source_fluent/1,sink_fluent/1,empty_fluent/1,
      source_fluent/2,sink_fluent/2,
      set_metaflags/1,
      set_module_metaterm_overriden/2,
      set_dict_attvar_reader/1,
      set_as/4,
      put_atts/3,
      new_meta_attribute/3,
      new_meta/2,
      new_attribute/2,
      nb_extend_list/2,
      metaterm_setval/2,
      metaterm_push/2,
      metaterm_pop/2,
      metaterm_override/3,
      metaterm_override/2,
      metaterm_handler_name/1,
      metaterm_getval/2,
      metaflag_unset/2,
      metaflag_set/2,
      metaflag_get/2,
      merge_fbs/3,
      matts/2,
      matts/1,
      matts/0,
      make_metaterm_override/2,
      is_metaterm_att/1,
      has_hooks/1,
      get_metaflags/1,
      get_handler/4,
      get_attribute/3,
      get_attribute/2,
      fvi_set/2,
      fvi_push/2,
      fvi_pop/2,
      fvi_get/2,
      fbs_to_number/2,
      fbs_for_hooks_default/1,
      export_all/0,
      exec_atts_put/4,
      ensure_meta/1,
      dskip/5,dskip/4,dskip/3,dskip/2,dskip/1,
      dshowf/4,dshowf/3,dshowf/2,dshowf/1,
      dshow/4,dshow/3,dshow/2,dshow/1,
      do_metaterm_hook/4,
      debug_hooks/1,
      copy_var/1,idempotent/1,
      contains_fbs/2,
      compare_to_retcode/2,
      check/1,
      atts_tmpl/2,
      atts_put/4,
      atts_modulize/4,
      atts_module/2,
      atts_get/3,
      atts_exist/2,
      attrs_val/2,
      attrs_to_pairs/2,
      attrs_to_atts/3,
      as_handler/2,
      any_to_fbs/2,
      add_attribute/3, add_attribute/2,
      add_attr/3,
      'meta_attribute'/2,
      'attribute'/1,get_atts/2,put_atts/2,del_atts/2, op(1150, fx, 'attribute'),
      %get_attribute/3,
      %add_attribute/3,
      % TODO remove some of above before master
      attvar_to_dict/2,dict_to_attvar/1,dict_to_attvar/2]).


:- meta_predicate('meta_attribute'(+,:)).
:- meta_predicate(get_atts(+,:)).
:- meta_predicate(put_atts(+,:)).
:- meta_predicate(get_atts(+,:)).
:- meta_predicate(put_atts(+,:)).
:- meta_predicate(dict_to_attvar(:)).
:- meta_predicate(dict_to_attvar(:,-)).
:- meta_predicate wi_atts(+,0).

:- meta_predicate w_dmvars(0).
:- meta_predicate wno_dmvars(0).
:- meta_predicate w_debug(0).
:- meta_predicate wno_debug(0).

:- multifile(atts:metaterm_type/1).
:- discontiguous(atts:metaterm_type/1).
:- dynamic(atts:metaterm_type/1).

:- module_transparent 
      matts/0,
      testfv/0,
      w_debug/1,
      w_dmvars/1,
      wi_atts/2,
      wno_debug/1,
      ensure_meta/1,
      wno_dmvars/1,
      % TODO remove  above before master
      
      'attribute'/1,get_atts/2,put_atts/2,del_atts/2, 
      add_attr/3,
      any_to_fbs/2,
      has_hooks/1,
      matts/1,
      matts/2,
      copy_var/1,idempotent/1,
      metaterm_getval/2,
      metaterm_setval/2,
      source_fluent/1,sink_fluent/1,empty_fluent/1,
      metaterm_override/2,
      add_attribute/2,
      %add_attribute/3,
      get_attribute/2,
      %get_attribute/3,
      get_metaflags/1,
      set_metaflags/1,
      merge_fbs/3,
      new_meta/2,
      fbs_to_number/2,
      'meta_attribute'/2,
      set_dict_attvar_reader/1,
      metaflag_unset/2,
      metaflag_set/2,
      dict_to_attvar/1,
      dict_to_attvar/2.

:- nodebug(fluents).

uses_copy_var(Fluent,Value):- var(Value), get_attr(Fluent,copy_var,[_]).

%%	sink_fluent(-Fluent) is det.
%
% Base class of "SinkFluent" that recieves bindings

sink_fluent(Fluent):- sink_fluent(Fluent,metaterm_setval).
sink_fluent(Fluent,Method):- put_atts(Fluent, +(sink_fluent:Method) +(direction:sink) +no_bind).

sink_fluent:metaterm_unify_hook(_Atom,[Method],Fluent,Value):- \+ uses_copy_var(Fluent,Value),!,must_notrace(nonvar(Value)->call(Method,Fluent,Value);true).
sink_fluent:metaterm_unify_hook(_Atom,_AttVal,_Fluent,_Value).

%%	source_fluent(-Fluent) is det.
%
% Base class of "SourceFluent" that creates bindings
source_fluent(Fluent):- source_fluent(Fluent,metaterm_getval).
source_fluent(Fluent,Method):- put_atts(Fluent,+(source_fluent:Method) +(direction:source), +use_unify_var +no_bind).

source_fluent:metaterm_unify_hook(_Atom,[Method],Fluent,Value):- \+ uses_copy_var(Fluent,Value),!,(call(Method,Fluent,ValueO)*->ValueO=Value;true).
source_fluent:metaterm_unify_hook(_Atom,_AttVal,_Fluent,_Value).


%%	copy_var(-Fluent) is det.
%
% Make a var use idempotent unification
copy_var(Fluent):- copy_var(Fluent,duplicate_term).
copy_var(Fluent,Method):- put_atts(Fluent, +(copy_var:Method) +use_unify_var),exists(Fluent).

copy_var:metaterm_unify_hook(_Atom,[Method],Fluent,Value):- var(Value), !,
                       must_notrace(( \+ attvar(Value) 
                        -> (get_attrs(Fluent,AttsIn),call(Method,AttsIn,AttsOut),put_attrs(Value,AttsOut))
                        ;  (get_atts(Fluent,AttsIn),call(Method,AttsIn,AttsOut),put_atts(Value,AttsOut)))).

copy_var:metaterm_unify_hook(_Atom,_AttVal,_Fluent,_Value).

idempotent(Fluent):- copy_var(Fluent).


%%	empty_fluent(-Fluent) is det.
%
% Create a truely don't care '_' Fluent
% Will unify multiple times and remain a var
% even after binding. At bind with anything and call no wakeups
% peer or otherwise
% Tarau's "EmptySink" matts

empty_fluent(Fluent):- ensure_meta(Fluent),put_atts(Fluent,+no_wakeup+no_bind+no_trail).


get_metaflags(Get):- metaterm_flags(global,Get,Get).
set_metaflags(Set):- metaterm_flags(global,set,Set).
metaflag_unset(V,F):- metaterm_flags(V,~,F).
metaflag_set(V,F) :- metaterm_flags(V,(/\),F).
metaflag_get(Var,Get):- metaterm_flags(Var,Get,Get).

:- meta_predicate('attribute'(:)).
% :- '$set_source_module'(_,'atts').
:- dynamic(was_access_level_atts/1).
:- current_prolog_flag(access_level,Was),asserta(was_access_level_atts(Was)).
:- set_prolog_flag(access_level,user).
:- use_module(library(ordsets)).

% auto-define attributes otherwise signal error is undeclared attributes are used
:- create_prolog_flag(atts_declared,auto,[type(atom),keep(true)]).
% Users might need to read docs to decided they rather have auto?
:- set_prolog_flag(atts_declared,true).
% What is all this fuss about?
% We need some answer to what happens when ?- user:put_atts(Var,+a(1)).
% if attibute a/1 is declared in one module at least we have some sense
% Still doesnt solve the problem when if a/1 is declared in several modules
% Should we use the import_module/2 Dag?
% Still doesnt solve the problem when if a/1 is declared only in one unseen module!
% Though every option is simple to implement, it should be left to programmers to decide with flags/options
% and not left just to those editing these files.  Still we need to pick a default.

%%    attribute(+AttributeSpec).
%
% :- attribute AttributeSpec,..., AttributeSpec.
%
% where each AttributeSpec has the form Functor/Arity.
% Having declared some attribute names, these attributes can be added, 
% updated and deleted from unbound variables using the following two predicates 
%(get_atts/2 and put_atts/2) defined in the module atts. 
% For each declared attribute name, any variable can have at most one such attribute (initially it has none).
'attribute'(M:V):- new_attribute(V,M),!.

new_attribute(V,M) :- var(V), !, throw(error(instantiation_error,'attribute'(M:V))).
new_attribute(Na/Ar,Mod) :- !, functor(At,Na,Ar),new_attribute(At,Mod).
new_attribute(Mod:ANY,_) :- !, new_attribute(ANY,Mod).
new_attribute([],_).
new_attribute((At1,At2),M) :- new_attribute(At1,M), new_attribute(At2,M).
new_attribute([At1|At2],M) :- new_attribute(At1,M), new_attribute(At2,M).
new_attribute(At,Mod) :- dynamic(Mod:protobute/3),
  (Mod:protobute(Mod,At,_) -> true; 
   ((Mod:protobute(Mod,_,Nth)->Nth2 is Nth+1;Nth2=1),asserta(Mod:protobute(Mod,At,Nth2)))).

%%    put_atts(+Var, +AccessSpec)
%
% Sets the attributes of Var according to AccessSpec.
%
% Non-variable terms in Var cause a type error. 
%  if curent_prolog_flag(atts_compat,xsb).
%
% The effect of put_atts/2 are undone on backtracking. 
% (prefix + may be dropped for convenience).
% The prefixes of AccessSpec have the following meaning:
%  +(Attribute):
%     The corresponding actual attribute is set to Attribute. If the actual attribute was already present, it is simply replaced.
%  -(Attribute):
%     The corresponding actual attribute is removed. If the actual attribute is already absent, nothing happens.
%
%  Should we ignore The arguments of Attribute, only the name and arity are relevant? Currently coded to
%
% ==
% ?- m1:put_atts(Var,+a(x1,y1)).
% put_attr(Var, m1, [a(x1, y1)]).
%
% ?- m1:put_atts(V,+a(x1,y1)),m1:put_atts(V,+b(x1,y1)),m1:put_atts(V,-a(_,_)),m2:put_atts(V,+b(x2,y2)).
% put_attr(V, m1, [b(x1, y1)]),
% put_attr(V, m2, [b(x2, y2)]) .


%%    get_atts(+Var, ?AccessSpec) 
%
% Gets the attributes of Var according to AccessSpec. 
%  If AccessSpec is unbound, it will be bound to a list of all set attributes of Var. 
%
% Non-variable terms in Var cause a type error. 
%  if curent_prolog_flag(atts_compat,xsb).
%
% AccessSpec is either +(Attribute), -(Attribute), or a list of such 
% (prefix + may be dropped for convenience).
%
% The prefixes in the AccessSpec have the following meaning:
%  +(Attribute):
%     The corresponding actual attribute must be present and is unified with Attribute.
%  -(Attribute):
%     The corresponding actual attribute must be absent.
%
%  Should we ignore The arguments of Attribute are ignored, only the name and arity are relevant?
%   yes = XSB_compat, no = less control and perf
%
% ==
% ?- m1:put_atts(Var,+a(x1,y1)),m1:get_atts(Var,-missing(x1,y1)).
% put_attr(Var, m1, [a(x1, y1)]).
%
% ?- m1:put_atts(Var,+a(x1,y1)),m1:get_atts(Var,X).
% X=[a(x1, y1)],
% put_attr(Var, m1, [a(x1, y1)]).
% ==
% TODO/QUESTION  user:get_atts(Var,Atts) ->  ??? only attributes in 'user' or all attributes??? Attr=[m1:...]



% TODO BEGIN remove before master

:- meta_predicate tst_det(0).
:- meta_predicate tst(0).

/*

SWI-Prolog fluent patch in implements all of the C support! https://github.com/logicmoo/swipl-devel/

*/

% TODO END remove before master



:- use_module(library(ordsets)).


/*
unify:
the usual unification. The handler procedure is
unify_handler(+Term, ?Attribute [,SuspAttr])
The first argument is the term that was unified with the attributed variable, it is either a non-variable or another attributed variable. The second argument is the contents of the attribute slot corresponding to the extension. Note that, at this point in execution, the orginal attributed variable no longer exists, because it has already been bound to Term. The optional third argument is the suspend-attribute of the former variable; it may be needed to wake the variable's 'constrained' suspension list.
The handler's job is to determine whether the binding is allowed with respect to the attribute. This could for example involve checking whether the bound term is in a domain described by the attribute. For variable-variable bindings, typically the remaining attribute must be updated to reflect the intersection of the two individual attributes. In case of success, suspension lists inside the attributes may need to be scheduled for waking.
If an attributed variable is unified with a standard variable, the variable is bound to the attributed variable and no handlers are invoked. If an attributed variable is unified with another attributed variable or a non-variable, the attributed variable is bound (like a standard variable) to the other term and all handlers for the unify operation are invoked. Note that several attributed variable bindings can occur simultaneously, e.g. during a head unification or during the unification of two compound terms. The handlers are only invoked at certain trigger points (usually before the next regular predicate call). Woken goals will start executing must_notrace all unify-handlers are done.
*/
metaterm_handler_name(unify).

/*
test_unify:   REDIRECT ==  verify_attributes/3 TODO
a unifiability test which is not supposed to trigger constraints propagation. It is used by the not_unify/2 predicate. The handler procedure is
test_unify_handler(+Term, ?Attribute)
where the arguments are the same as for the unify handler. The handler's job is to determine whether Attribute allows unification with Term (not considering effects of woken goals). During the execution of the handler, the attributed variable may be bound to Term, however when all attribute handlers succeed, all bindings are undone again, and no waking occurs.
*/
metaterm_handler_name(test_unify).

/*
compare_instances:  C is done in branch 'eclipse_c' - PROLOG TODO
computation of instance, subsumption and variance relationship, as performed by the built-ins compare_instances/3, instance/2 and variant/2. The handler procedure is
instance_handler(-Res, ?TermL, ?TermR)
and its arguments are similar to the ones of the compare_instances/3 predicate. The handler is invoked with one or both of TermL and TermR being attributed variables. The task of the handler is to examine the two terms, and compute their instance relationship with respect to the extension attribute in question. The handler must bind Res to = iff the terms are variants, < iff TermL is a proper instance of TermR, or > iff TermR is a proper instance of TermL) with respect to the attribute under consideration. If the terms are not unifiable with respect to this attribute, the handler must fail.
Even though one of TermL and TermR is guaranteed to be an attributed variable, they might not have the particular attribute that the handler is concerned with. The handler must therefore be written to correctly deal with all combinations of an attributed (but potentially uninstantiated attribute) variable with any other term.
*/
metaterm_handler_name(compare_instances).
metaterm_handler_name(compare).

/*
copy_term:  C is done in branch 'eclipse_c' - PROLOG TODO
the handler is invoked by either copy_term/2 or copy_term_vars/3. The handler procedure is
copy_handler(?AttrVar, ?Copy)
AttrVar is the attributed variable encountered in the copied term, Copy is its corresponding variable in the copy. All extension handlers receive the same arguments. This means that if the attributed variable should be copied as an attributed variable, the handler must check if Copy is still a free variable or if it was already bound to an attributed variable by a previous handler.
*/
metaterm_handler_name(copy_term).
metaterm_handler_name(copy_term_nat).

/*
suspensions:  REDIRECT ==  attribute_goals//1
this handler is invoked by the suspensions/2 predicate to collect all the suspension lists inside the attribute. The handler call pattern is
suspensions_handler(?AttrVar, -ListOfSuspLists, -Tail)
AttrVar is an attributed variable. The handler should bind ListOfSuspLists to a list containing all the attribute's suspension lists and ending with Tail.
*/
metaterm_handler_name(suspensions).

/*
delayed_goals_number:   REDIRECT ==  attribute_goals//1 (count)
handler is invoked by the delayed_goals_number/2 predicate. The handler call pattern is
delayed_goals_number_handler(?AttrVar, -Number)
AttrVar is the attributed variable encountered in the term, Number is the number of delayed goals occurring in this attribute. Its main purpose is for the first-fail selection predicates, i.e., it should return the number of constraints imposed on the variable.
*/
metaterm_handler_name(delayed_goals_number).

/*
get_bounds:  OUT OF SCOPE (Should be done in CLP)
This handler is used by the predicate get_var_bounds/3 to retrieve information about the lower and upper bound of a numeric variable. The handler should therefore only be defined if the attribute contains that kind of information. The handler call pattern is
get_bounds_handler(?AttrVar, -Lwb, -Upb)
The handler is only invoked if the variable has the corresponding (non-empty) attribute. The handler should bind Lwb and Upb to numbers (any numeric type) reflecting the attribute's information about lower and upper bound of the variable, respectively. If different attributes return different bounds information, get_var_bounds/3 will return the intersection of these bounds. This can be empty (Lwb > Upb).

set_bounds:  OUT OF SCOPE (Should be done in CLP)
This handler is used by the predicate set_var_bounds/3 to distribute information about the lower and upper bound of a numeric variable to all its existing attributes. The handler should therefore only be defined if the attribute can incorporate this kind of information. The handler call pattern is
set_bounds_handler(?AttrVar, +Lwb, +Upb)
The handler is only invoked if the variable has the corresponding (non-empty) attribute. Lwb and Upb are the numbers that were passed to set_var_bounds/3, and the handler is expected to update its own bounds representation accordingly.
*/

/*
print:   REDIRECT ==  portray_attvar/1
attribute printing in write/1,2, writeln/1,2, printf/2,3 when the m option is specified. The handler procedure is
print_handler(?AttrVar, -PrintAttr)
AttrVar is the attributed variable being printed, PrintAttr is the term which will be printed as a value for this attribute, prefixed by the attribute name. If no handler is specified for an attribute, or the print handler fails, the attribute will not be printed.
The following handlers are still supported for compatibility, but their use is not recommened:
*/
metaterm_handler_name(print).

/*
pre_unify:  REDIRECT ==  verify_attributes/3
this is another handler which can be invoked on normal unification, but it is called before the unification itself occurs. The handler procedure is
pre_unify_handler(?AttrVar, +Term)
The first argument is the attributed variable to be unfied, the second argument is the term it is going to be unified with. This handler is provided only for compatibility with SICStus Prolog and its use is not recommended, because it is less efficient than the unify handler and because its semantics is somewhat unclear, there may be cases where changes inside this handler may have unexpected effects.
*/
metaterm_handler_name(pre_unify).

/*
delayed_goals:     REDIRECT == attribute_goals//1
this handler is superseded by the suspensions-handler, which should be preferred. If there is no suspensions- handler, this handler is invoked by the obsolete delayed_goals/2 predicate. The handler procedure is
delayed_goals_handler(?AttrVar, ?GoalList, -GoalCont)
AttrVar is the attributed variable encountered in the term, GoalList is an open-ended list of all delayed goals in this attribute and GoalCont is the tail of this list.
*/
metaterm_handler_name(delayed_goals).


% auto-define attributes otherwise signal error is undeclared attributes are used
:- create_prolog_flag(atts_declared,auto,[type(atom),keep(true)]).
% Users might need to read docs to decided they rather have auto?
:- set_prolog_flag(atts_declared,true).
% What is all this fuss about?
% We need some answer to what happens when ?- user:put_atts(Var,+a(1)).
% if attibute a/1 is declared in one module at least we have some sense
% Still doesnt solve the problem when if a/1 is declared in several modules
% Should we use the import_module/2 Dag?
% Still doesnt solve the problem when if a/1 is declared only in one unseen module!
% Though every option is simple to implement, it should be left to programmers to decide with flags/options
% and not left just to those editing these files.  Still we need to pick a default.

/*
SEE:  http://eclipseclp.org/doc/userman/umsroot100.html 
An attributed variable can have any number of attributes. The attributes are accessed by their name. Before an attribute can be created and used, it must be declared with the predicate meta_attribute/2. The declaration has the format

meta_attribute(Name, HandlerList)  PROLOG TODO
Name is an atom denoting the attribute name and usually it is the name of the module where this attribute is being created and used. HandlerList is a (possibly empty) list of handler specifications for this attribute (see Section 16.7).
*/
%%    meta_attribute(Name,+HandlerList).
%
% :- meta_attribute(Name,[HandlerL,..., List]).
%
% where each HandlerList has the form HookName:Functor/Arity.
% Having declared some meta_attribute names, these attributes can be added, 
% updated and deleted from unbound variables using the following two predicates 
%(get_atts/2 and put_atts/2) defined in the module atts. 
% For each declared meta_attribute name, any variable can have at most one such meta_attribute (initially it has none).
'meta_attribute'(Base,M:V):- new_meta_attribute(Base,V,M),!.

new_meta_attribute(Base,V,M) :- (var(Base);var(M);var(V)), !, throw(error(instantiation_error,'meta_attribute'(Base,M:V))).
new_meta_attribute(Base,Na/Ar,Mod) :- !, functor(At,Na,Ar),new_meta_attribute(Base,At,Mod).
new_meta_attribute(Base,Mod:ANY,_) :- \+ metaterm_handler_name(Mod),!, new_meta_attribute(Base,ANY,Mod).
new_meta_attribute(_,[],_).
new_meta_attribute(Base,(At1,At2),M) :- new_meta_attribute(Base,At1,M), new_meta_attribute(Base,At2,M).
new_meta_attribute(Base,[At1|At2],M) :- new_meta_attribute(Base,At1,M), new_meta_attribute(Base,At2,M).

new_meta_attribute(Base,P:At,Mod) :- assertion(metaterm_handler_name(P)),dynamic(Mod:metaterm_hook/3),
  (Mod:metaterm_hook(Base,P,At) -> true; asserta(Mod:metaterm_hook(Base,P,At))).

new_meta_attribute(Base,At,Mod) :- dynamic(Mod:protobute/3),
  (Mod:protobute(Base,At,_) -> true; 
   ((Mod:protobute(Base,_,Nth)->Nth2 is Nth+1;Nth2=1),asserta(Mod:protobute(Base,At,Nth2)))).


%%    put_atts(+Var, +AccessSpec)
%
% Sets the attributes of Var according to AccessSpec.
%
% Non-variable terms in Var cause a type error. 
%  if curent_prolog_flag(atts_compat,xsb).
%
% The effect of put_atts/2 are undone on backtracking. 
% (prefix + may be dropped for convenience).
% The prefixes of AccessSpec have the following meaning:
%  +(Attribute):
%     The corresponding actual meta_attribute is set to Attribute. If the actual meta_attribute was already present, it is simply replaced.
%  -(Attribute):
%     The corresponding actual meta_attribute is removed. If the actual meta_attribute is already absent, nothing happens.
%
%  Should we ignore The arguments of Attribute, only the name and arity are relevant? Currently coded to
%
% ==
% ?- m1:put_atts(Var,+a(x1,y1)).
% put_attr(Var, m1, [a(x1, y1)]).
%
% ?- m1:put_atts(V,+a(x1,y1)),m1:put_atts(V,+b(x1,y1)),m1:put_atts(V,-a(_,_)),m2:put_atts(V,+b(x2,y2)).
% put_attr(V, m1, [b(x1, y1)]),
% put_attr(V, m2, [b(x2, y2)]) .

put_atts(Var,M:Atts):- must_notrace((wo_metaterm((atts_put(+,Var,M,Atts))),!)).
put_atts(Var,M,Atts):- must_notrace((wo_metaterm((atts_put(+,Var,M,Atts))),!)).
del_atts(Var,M:Atts):- must_notrace((wo_metaterm((atts_put(-,Var,M,Atts))),!)).
get_atts(Var,M:Atts):- must_notrace((atts_get(Var,M,Atts))),!.


%%    get_atts(+Var, ?AccessSpec) 
%
% Gets the attributes of Var according to AccessSpec. 
%  If AccessSpec is unbound, it will be bound to a list of all set attributes of Var. 
%
% Non-variable terms in Var cause a type error. 
%  if curent_prolog_flag(atts_compat,xsb).
%
% AccessSpec is either +(Attribute), -(Attribute), or a list of such 
% (prefix + may be dropped for convenience).
%
% The prefixes in the AccessSpec have the following meaning:
%  +(Attribute):
%     The corresponding actual meta_attribute must be present and is unified with Attribute.
%  -(Attribute):
%     The corresponding actual meta_attribute must be absent.
%
%  Should we ignore The arguments of Attribute are ignored, only the name and arity are relevant?
%   yes = XSB_compat, no = less control and perf
%
% ==
% ?- m1:put_atts(Var,+a(x1,y1)),m1:get_atts(Var,-missing(x1,y1)).
% put_attr(Var, m1, [a(x1, y1)]).
%
% ?- m1:put_atts(Var,+a(x1,y1)),m1:get_atts(Var,X).
% X=[a(x1, y1)],
% put_attr(Var, m1, [a(x1, y1)]).
% ==
% TODO/QUESTION  user:get_atts(Var,Atts) ->  ??? only attributes in 'user' or all attributes??? Attr=[m1:...]



atts_exist(_A,_At):- current_prolog_flag(atts_declared,auto),!.
atts_exist(_A,_At):- current_prolog_flag(set_dict_attvar_reader,true),!.
atts_exist(M,At):- \+ \+ (M:dynamic(protobute/3),assertion(M:protobute(M,At,_))).

atts_module(Var,M):- get_attr(Var,M,Was)->assertion(is_list(Was));put_attr(Var,M,[]).

atts_tmpl(At,Tmpl):- functor(At,F,A),functor(Tmpl,F,A).

to_pind(unify,=(_,_)).
to_pind(FA,PI):- compound(FA),compound_name_arity(FA,F,0),to_pind(F,PI),!.
to_pind(F/A,PI):- atom(F),integer(A),A>0,compound_name_arity(PI,F,A).
to_pind(F,PI):- atom(F),current_predicate( F /A),!,functor(PI,F,A).
to_pind(PI,PI).

system:'$undo_unify'(Var,Value):- dmsg(system:'$undo_unify'(Var,Value)).

%  av(X),metaterm_override_(X, = /2 : unify/2),metaterm_overriding(X,l(_,_),Y).

metaterm_override(X,BPIAPI):-must_notrace((metaterm_override_(X,BPIAPI))).

metaterm_override_(X,BA):-  is_list(BA),!,maplist(metaterm_override_,X,BA).
metaterm_override_(X,Atom):- atomic(Atom),!,metaterm_override_(X,Atom:true([])).
metaterm_override_(X,Atom):- compound_name_arity(Atom,_,0),!,metaterm_override_(X,Atom:true([])).
metaterm_override_(X,B:A):- to_pind(B,BPI),functor(BPI,_,AB),(atom(A)->functor(API,A,AB);to_pind(A,API)),!,metaterm_override_(X,BPI,API).
metaterm_override_(X,B=A):-  metaterm_override_(X,B:A),!.
metaterm_override_(X,What):- put_atts(X,'$meta': + What),put_atts(X,[+use_vmi]).

metaterm_override(X,BPI,API):- must_notrace(metaterm_override_(X,BPI,API)).

metaterm_override_(X,BPI,API):- (get_attr(X,'$meta',W) ->true; W=[]),put_attr(X,'$meta',att(BPI,API,W)),add_overriden(BPI,true),put_atts(X,[+use_vmi]).


make_metaterm_override(X,B=A):- metaterm_override_(X,B:A).


atts_modulize([], _) --> [].
atts_modulize([G|Gs], M) --> !,
    atts_modulize(G, M),
    atts_modulize(Gs, M).
atts_modulize(G,M)-->
 {strip_module(G,_,GS),
     (G == GS -> MG = M:G ; MG = G)},
 [MG]. 


attrs_to_atts([])--> [].
attrs_to_atts(att(M,Att,Rest))-->
   atts_modulize(Att,M),
   attrs_to_atts(Rest).

% ?- put_atts(X,+(unify=write)),!.

add_attr(Var,N,Value):- get_attrs(Var,Was)->put_attrs(Var,att(N,Value,Was));put_attrs(Var,att(N,Value,[])).


% Should 'user' use the import_module/2 Dag? (curretly will just return all)
atts_get(Var,user,Atts):- var(Atts),!,get_attrs(Var,Attr),attrs_to_atts(Attr,Atts,[]).
% atts_get(Var,M,At):- var(At),!,get_attr(Var,M,At).
atts_get(Var,M,List):- is_list(List),!,maplist(atts_get(Var,M),List).
atts_get(Var,M,+At):- !,atts_get(M,Var,At).
atts_get(Var,_,-(M:At)):- \+ metaterm_handler_name(M), !,atts_get(Var,M,-At).
atts_get(Var,_, (M:At)):- \+ metaterm_handler_name(M), !,atts_get(Var,M,At).
atts_get(Var,M, - Pair):- !,
  atts_to_att(Pair,At),
   atts_exist(M,At),
   (get_attr(Var,M,Cur)->
      \+ memberchk(At,Cur) ;
    true).
atts_get(Var,M,Pair):- 
   atts_to_att(Pair,At),
   atts_exist(M,At),
   (get_attr(Var,M,Cur)->
      memberchk(At,Cur) ;
    fail).


invert_pn(+,-).
invert_pn(-,+).

atts_put(+,Var,M,At):- var(At),!,throw(error(instantiation_error, M:put_atts(Var,+At))).
atts_put(PN,Var,M, List):- is_list(List),!,atts_module(Var,M),maplist(atts_put(PN,Var,M),List).
atts_put(PN,Var,M,At):- var(At),!,exec_atts_put(PN,Var,M,At).
atts_put(PN,Var,M, X+Y):- !, atts_put(PN,Var,M, X),atts_put(PN,Var,M,+Y).
atts_put(PN,Var,M, X-Y):- !, atts_put(PN,Var,M, X),atts_put(PN,Var,M,-Y).
atts_put(PN,Var,M, +X+Y):- !, atts_put(PN,Var,M, +X),atts_put(PN,Var,M,+Y).
atts_put(PN,Var,M, +X-Y):- !, atts_put(PN,Var,M, +X),atts_put(PN,Var,M,-Y).
atts_put(_, Var,M,  +At):- !, atts_put(+,Var,M,At).
atts_put(PN,Var,M,  -At):- invert_pn(PN,NP),!,atts_put(NP,Var,M,At).
% atts_put(PN,Var,_,(M:At)):- \+ metaterm_handler_name(M), !,atts_put(PN,Var,M,At).
atts_put(PN,Var,M, Meta):- \+ \+ clause(M:metaterm_hook(Meta,_,_),_), !, forall(M:metaterm_hook(Meta,P,A),atts_put(PN,Var,M,P=A)).
% =(+a,b) -->   +(A=B).
atts_put(PN,Var,M, Pair):- compound(Pair),Pair=..[P,Arg1,Arg2],attsep(P),compound(Arg1),tst((Arg1=..List,append(Head,[Last],List),At=..[P,Last,Arg2],append(Head,[At],ListNew),Try=..ListNew,!,atts_put(PN,Var,M, Try))).
atts_put(PN,Var,user,Atts):- atts_nv(Atts,N,V),atts_put(PN,Var,N,V).
atts_put(PN,Var,atts,Atts):- atts_nv(Atts,N,V),atts_put(PN,Var,N,V).

atts_put(PN,Var,M,Pair):- 
  atts_to_att(Pair,Tmpl),
  atts_exist(PN,Tmpl),
  exec_atts_put(PN,Var,M,Tmpl).

is_metaterm_att(Tmpl):- fbs_for_hooks_default(Comp),arg(_,Comp,Tmpl).


exec_atts_put(Sign,Var,_,NameNV):- nonvar(NameNV),atts_nv(NameNV,Name,Value),is_metaterm_att(Name),!,exec_atts_put(Sign,Var,Name,Value).

exec_atts_put(-,Var,M,Tmpl):- !,
  update_hooks(-,Var,M,Tmpl),!,
   (get_attr(Var,M,Cur)->
     (delete(Cur,Tmpl,Upd),(Upd==[]->del_attr(Var,M);put_attr(Var,M,Upd))) ;
    true).

exec_atts_put(+,Var,M,At):- 
 update_hooks(+,Var,M,At),!,
   (get_attr(Var,M,Cur) ->
    (atts_tmpl(At,Tmpl),
     delete(Cur,Tmpl,Mid), % ord_del_element wont work here because -a(_) stops short of finding a(1).
     ord_add_element(Mid,At,Upd),
     put_attr(Var,M,Upd));
    put_attr(Var,M,[At])).

attsep('=').
attsep(':').
attsep('-').


atts_nv(Var,_N,_V):- var(Var),!,must_be(nonvar,Var),fail.
atts_nv(N:V,N,V):- !.
atts_nv(N-V,N,V):- !.
atts_nv(N=V,N,V):- !.
atts_nv(F/A,N,V):- !,assertion((atom(F),integer(A))),functor(Tmpl,F,A),atts_nv(Tmpl,N,V).
atts_nv(Tmpl,Tmpl,true):-atom(Tmpl),!.
atts_nv(Tmpl,N,V):- !,Tmpl=..[N,V].
atts_nv(Tmpl,N,Tmpl):-functor(Tmpl,N,_),!.


atts_to_att(Var,Var):- var(Var),!.
atts_to_att(N-V,Tmpl):- !,atts_to_att(N=V,Tmpl).
atts_to_att(N:V,Tmpl):- !,atts_to_att(N=V,Tmpl).
atts_to_att(N=V,Tmpl):- !,assertion(atom(N)),!,Tmpl=..[N,V].
atts_to_att(F/A,Tmpl):- !,assertion((atom(F),integer(A))),functor(Tmpl,F,A).
atts_to_att(Tmpl,Tmpl).

update_hooks(PN,Var,Hook,_):- 
  ignore((handler_fbs(+ Hook,Number), Number>0, !,PNHook=..[PN,Hook], put_datts(Var, PNHook))),
  update_hooks1(PN,Var,_,Hook).

update_hooks1(+,Var,At,_):- ignore((compound(At),compound_name_arguments(At,Hook,[_Value]),handler_fbs(Hook,Number),!,Number>0,
   (get_attr(Var,'$atts',Was)-> (New is Was \/ Number,put_attr(Var,'$atts',New));(ensure_meta(Var),put_attr(Var,'$atts',Number))))).
update_hooks1(-,Var,_M,At):- ignore((compound(At),compound_name_arguments(At,Hook,[_Value]),handler_fbs(Hook,Number),!,Number>0,
   (get_attr(Var,'$atts',Was)-> (New is Was /\ \ Number,put_attr(Var,'$atts',New));(ensure_meta(Var),put_attr(Var,'$atts',Number))))).

handler_fbs(Hook,Number):- must_notrace(catch(fbs_to_number(Hook,Number),_,Number=0)).

/*

Eclipse 

where Attr is the value obtained from the handler. If there are several handled attributes, all attributes are qualified like in

X{a:A, b:B, c:C}.

pl_notrace(_)

*/
set_dict_attvar_reader(X):- set_prolog_flag(set_dict_attvar_reader,X).

attvar_to_dict(AttVar,Dict):-
   get_attrs(AttVar,Att3s),
   attrs_to_pairs(Att3s,DictPairs),
   dict_create(Dict,AttVar,DictPairs).

attrs_to_pairs(att(N,V,Att3s),[N=V|DictPairs]):-!,attrs_to_pairs(Att3s,DictPairs).
attrs_to_pairs(DictPairs,DictPairs).

dict_to_attvar(Dict):- dict_to_attvar(Dict,_),!.
dict_to_attvar(_:Dict,Out):- \+ compound(Dict),!,Out=Dict.
dict_to_attvar(Mod:Dict,Out):- 
   is_dict(Dict),dict_pairs(Dict,M,Pairs),
   (atom(M)->atts_put(+,Out,M,Pairs);
   (var(M)-> (M=Out,put_atts(Out,Mod:Pairs)))),!.
dict_to_attvar(Mod:Dict,Out):- 
  compound_name_arguments(Dict,F,Args),
   maplist(Mod:dict_to_attvar,Args,ArgsO),!,
   compound_name_arguments(Out,F,ArgsO).

% This type-checking predicate succeeds iff its argument is an ordinary free variable, it fails if it is an attributed variable.
eclipse:free(X):- var(X),\+attvar(X).

% This type-checking predicate succeeds iff its argument is an attributed variable. For other type testing predicates an attributed variable behaves like a variable.
% eclipse:
system:meta(X):- attvar(X),get_attr(X,'$atts',N),N>0.

% A new attribute can be added to a variable using the tool predicate
% add_attribute(Var, Attr).
% An attribute whose name is not the current module name can be added using add_attribute/3 which is its tool body predicate (exported in sepia_kernel). If Var is a free variable, it will be bound to a new attributed variable whose attribute corresponding to the current module is Attr and all its other attributes are free variables. If Var is already an attributed variable and its attribute is uninstantiated, it will b
:- meta_predicate(add_attribute(+,:)).
add_attribute(Var, M:Attr):- atts_put(+,Var,M, Attr).
add_attribute(Var,M,Attr):- atts_put(+,Var,M, Attr).

:- meta_predicate(get_attribute(+,:)).
get_attribute(Var, M:Attr):- atts_get(Var,M, Attr).
get_attribute(Var, M, Attr):- atts_get(Var,M, Attr).

:- nodebug(matts).

:- multifile('$atts':metaterm_hook/4).
:- dynamic('$atts':metaterm_hook/4).
:- meta_predicate('$atts':metaterm_hook(:,+,+,-)).
'$atts':metaterm_hook(PredIn,Var,Value,RetCode):- strip_module(PredIn,M,Pred), do_metaterm_hook(M,Pred,Var,Value,RetCode),!.

get_handler(M,Var,Hook,M:Handler):- get_attr(Var,M,Handlers),memberchk(Hook:Hndler,Handlers),as_handler(Hndler,Handler).
get_handler(M,Var,Hook,M:Handler):- get_attr(Var,Hook,Hndler),as_handler(Hndler,Handler).
get_handler(M,Var,Hook,M:Handler):- get_attr(Var,tst,Handlers),memberchk(Hook:Hndler,Handlers),as_handler(Hndler,Handler).

as_handler(Handler/_,Handler):- !.
as_handler(M:Handler/_,M:Handler):- !.
as_handler(Handler,Handler).

:- meta_predicate do_metaterm_hook(2,*,?,*).
:- meta_predicate wd(0).
:- meta_predicate(wnmt(:)).
wnmt(G):-  get_metaflags(W),setup_call_cleanup(set_metaflags(0),G,set_metaflags(W)).
:- module_transparent(do_metaterm_hook/4).


% unbind return code
do_metaterm_hook(Pred,Var,Value,RetCode):- nonvar(RetCode),!,do_metaterm_hook(Pred,Var,Value,RetCode0),RetCode0=RetCode.
% print debug
do_metaterm_hook(Pred,Var,Value,RetCode):- must_notrace((dmsg(user:metaterm_hook(Pred,Var,Value,RetCode)),fail)).
% Search for handler PER Var
do_metaterm_hook(Hook,Var,Value,1):- get_handler(user,Var,Hook,Handler),!,call(Handler,Var,Value).

do_metaterm_hook('==',Var,Value, 1):- !, wnmt(Var==Value). % this one ends up calling compare/3 
do_metaterm_hook('==',Var,Value,1):- attrs_val(Value,BA),attrs_val(Var,Cell),!,BA=@=Cell.
do_metaterm_hook('==',Var,Value,1):- attrs_val(Value,BA),attrs_val(Var,Cell),BA==Cell,!.
do_metaterm_hook('=@=', Var, Value, 1):- !, wnmt(Var=@=Value).
do_metaterm_hook('=@=',Var,Value,1):- attrs_val(Value,BA),attrs_val(Var,Cell),!,BA=@=Cell.
do_metaterm_hook(compare, Var, Value, RetCode):- !, wnmt(compare(Cmp,Var,Value)),compare_to_retcode(Cmp,RetCode).
do_metaterm_hook(copy_term, Var, Value, 1):- !, wnmt(copy_term(Var,Value)).
do_metaterm_hook(copy_term_nat, Var, Value, 1):- !, wnmt(copy_term_nat(Var,Value)).
do_metaterm_hook(Hook,Var,Value,1):- metaterm_getval(Var,Cell),with_metaterm(call(Hook,Cell,Value)).
do_metaterm_hook('$undo_unify',Var,_Value,1):- get_attr(Var,'$undo_unify',G),!,G.
% 0: == call handler
do_metaterm_hook(compare,Var,Value,0):- do_metaterm_hook(==,Var,Value,1),!.
% call back
do_metaterm_hook(compare,Var,Value,RetCode):- compare(Res,Value,Var),compare_to_retcode(Res,RetCode),!.

compare_to_retcode(>,1).
compare_to_retcode(<,-1).
compare_to_retcode(==,0).

swap_args(_,_,4).
set_as(N,N,N,4).
attrs_val(Var,AttsO):- '$visible_attrs'(Var,AttsO).

ensure_meta(Fluent):- get_attrs(Fluent,att('$atts',_,_)),!.
ensure_meta(Fluent):- get_attrs(Fluent,Was)->put_attrs(Fluent,att('$atts',0,Was));put_attr(Fluent,'$atts',0).

metaterm_setval(Var,Value):- get_cont(Var,Cont),!,fvi_set(Cont,Value).
metaterm_setval(Var,Value):- put_attr(Var,value,v([Value])).


metaterm_reset(Var,Value):- get_cont(Var,Cont),!,fvi_reset(Cont,Value).
metaterm_reset(Var,Value):- put_attr(Var,value,v([Value])).

unify_val(Var,Value):- metaterm_getval(Var,Cell),!,Cell=Value.
unify_val(Var,Value):- metaterm_setval(Var,Value).

get_cont(Var,Cont):- get_attr(Var,gvar,Cell)->nb_linkval(Cell,Cont);get_attr(Var,value,Cont).

metaterm_getval(Var,Value):- get_cont(Var,Cont),fvi_get(Cont,Value).

metaterm_pop(Var,Value):- get_cont(Var,Cont),fvi_pop(Cont,Value).

metaterm_push(Var,Value):- get_cont(Var,Cont),!,fvi_push(Cont,Value).
metaterm_push(Var,Value):- metaterm_setval(Var,Value).

metaterm_create(Term,Var):- exists(Var),metaterm_reset(Var,Term).
   

fvi_reset(Cont,Value):- compound(Cont),arg(1,Cont,List),assertion(is_list(List)),setarg(1,Cont,[Value]).

fvi_set(Cont,Value):-
     var(Cont)-> Cont=v([Value]);
     (arg(1,Cont,List), (List==[]-> setarg(1,Cont,[Value]); setarg(1,List,Value))).

fvi_push(Cont,Value):- var(Cont)-> Cont=v([Value]); (arg(1,Cont,List),setarg(1,Cont,[Value|List])).

fvi_get(Cont,Value):- compound(Cont),arg(1,Cont,List),assertion(is_list(List)),member(Value,List).

fvi_pop(Cont,Value):- compound(Cont),arg(1,Cont,[Value|List]),assertion(is_list(List)),setarg(1,Cont,List).




         /**************
         *  UNDO HOOK  *
         **************/
/*    
    ?- F='\n',undo(((writeln(F:1);writeln(F:2)),fail)),!,write(before),fail.  % prints: before,1,2
    WAS BUG: ?- undo(((member(F,[1,2,3]),writeln(F),fail))),!,write(before),fail. % crashes ssytem
*/
system:'$meta'('$undo_unify', _, Goal, 1):- !, '$schedule_wakeup'(Goal).

was_tracing(Tracing):-current_prolog_flag(query_debug_settings,debug(_, Tracing)),!.
was_tracing(Tracing):- tracing -> Tracing = true ;   Tracing = false.

:- meta_predicate(system:undo(:)).
system:undo(Goal):-
       was_tracing(Tracing),
       set_prolog_flag(query_debug_settings,debug(true, Tracing)),
        metaterm_flags(current,(\/),use_undo),
        put_attr(Var,'$undo_unify',Goal),
        '$trail_assignment'(Var),
        ( current_prolog_flag(debug, true)  
            -> attv_unify(Var,Goal)
             ; (debug,attv_unify(Var,(Goal,nodebug)))).
        
:- debug.

dshow(X):- dmsg(dshow(X)).
dshow(X,Y):- dmsg(dshow(X,Y)).
dshow(X,Y,Z):- dmsg(dshow(X,Y,Z)).
dshow(S,X,Y,Z):- dmsg(dshow(S,X,Y,Z)).

dshowf(X):- dmsg(dshowf(X)),fail.
dshowf(X,Y):- dmsg(dshowf(X,Y)),fail.
dshowf(X,Y,Z):- dmsg(dshowf(X,Y,Z)),fail.
dshowf(S,X,Y,Z):- dmsg(dshowf(S,X,Y,Z)),fail.


dskip(X):- nop(dshow(X)).
dskip(X,Y):- nop(dshow(X,Y)).
dskip(X,Y,Z):- nop(dshow(X,Y,Z)).
dskip(S,X,Y,Z):- nop(dshow(S,X,Y,Z)).
dskip(S,X,Y,Z,A):- nop(dshow(S,X,Y,Z,A)).

/*
foo(p,a,q).
foo_dra(X,Y,Z):-dra(foo(p,a,q)).
*/

%%	matts(+Get,+Set) is det.
%
% Get/Set system wide matts modes
% Examples:
%
% ==
% ?- matts(_,+disable). % Disable entire system
% ==

matts(Get,Set):- get_metaflags(Get),merge_fbs(Set,Get,XM),tst(set_metaflags(XM)).


%% matts(+Set) is det.
%
% Set system wide matts modes
%
% == 
% ?-listing(fbs_for_hooks_default/1) to see them.
% ==

matts(X):- integer(X),!,set_metaflags(X),matts.
matts(X):- var(X),!,get_metaflags(X).
matts(X):- get_metaflags(M),merge_fbs(X,M,XM),tst(set_metaflags(XM)),!,matts,!.



fbs_for_hooks_default(v(

/* Global bits in an prolog accessable  get_attr/3,putt_attr/3 need it fit in valInt()*/


 sink_fluent,
 attv_bindconst  		," bindconst() " ,
 copy_var       		," unify: assign and wakeup " ,
 attv_will_unbind   , " peer no trail ", 
 
		 /*******************************
		 *	      FVS      	*
		 *******************************/
 metaterm_default,
 source_fluent      , " allow attvar survival ", 
 metaterm_disabled  , " disable all options (allows the options to be saved) ", 
 no_bind, " c should let only prolog do binding ",
 no_inherit, " this fv doest not inherit from 'matts_default' flags (otherwise they are or-ed) ", 
 no_swap, " dont swap attvars", 
 no_wakeup, " dont call wakeup ", 
 no_trail, " do not bother to trail the previous value ", 

 use_wakebinds,
 use_trail_optimize,
 use_no_trail_optimize,
 use_skip_hidden , " dont factor $meta into attvar identity ", 
 use_dra_interp,
 source_fluent,
 disable_vmi , " dont hook wam or cpreds", 
 use_unify_var, " debugging for a moment trying to guage if damaging do_unify() ",
 use_undo , " check attvars for undo hooks (perfomance checking) ",
 use_vmi , " hook wam ", 

 "done"

    )). 



%% matts is det.
%
% Print the system global modes
%
matts:- must_notrace((get_metaflags(M),any_to_fbs(M,B),format('~N~q.~n',[matts(M=B)]))).


%% debug_hooks is det.
%
% Turn on extreme debugging
%
debug_hooks(true):- !, matts(+debug_hooks+debug_extreme).
debug_hooks(_):- matts(-debug_hooks-debug_extreme).

%%    metaterm_override(AttVar,BitsOut)
%
% Set matts properties
%

put_datts(AttVar,Modes):- 
 must_notrace((wo_metaterm((var(AttVar),
  ((
   get_attr(AttVar,'$atts',Was)->
       (merge_fbs(Modes,Was,Change),put_attr(AttVar,'$atts',Change)); 
   (fbs_to_number(Modes,Number),ensure_meta(AttVar),put_attr(AttVar,'$atts',Number)))))))),!.


%%    matts(+AttVar)
%
% Checks to see if a term has matts

has_hooks(AttVar):- wo_metaterm(get_attr(AttVar,'$meta',_)).

%%    new_meta(+Bits,-AttVar) is det.
%
% Create new matts with a given set of Overrides

new_meta(Bits,AttVar):- must_notrace((put_atts(AttVar,'$meta':Bits))).


nb_extend_list(List,E):- arg(2,List,Was),nb_setarg(2,List,[E|Was]).


contains_fbs(AttVar,Bit):- any_to_fbs(AttVar,Bits),!,member(Bit,Bits).

% any_to_fbs(Var,BitsOut):- attvar(Var), get_attr(Var,'$atts',BitsIn),!,any_to_fbs(BitsIn,BitsOut).
any_to_fbs(BitsIn,BitsOut):- must_notrace((
 tst((fbs_to_number(BitsIn,Mode),number(Mode))),
   Bits=[Mode],
   ignore((current_metaterm_mask(N,VV), VV is VV /\ Mode , nb_extend_list(Bits,N),fail)),!,
   BitsOut = Bits)).


tst(G):- G*-> true; throw(tst_fail(G)).

tst_det(G):- G,deterministic(Y),(Y==true->true;throw(tst_fail(G))).


merge_fbs(V,VV,VVV):- number(V),catch((V < 0),_,fail),!, V0 is - V, merge_fbs(-(V0),VV,VVV),!.
merge_fbs(V,VV,VVV):- number(V),number(VV),VVV is (V \/ VV).
merge_fbs(V,VV,VVV):- var(V),!,V=VV,V=VVV.
merge_fbs(set(V),_,VVV):- fbs_to_number(V,VVV),!.
merge_fbs(V,VV,VVV):- var(VV),!, fbs_to_number(V,VVV),!.
merge_fbs(+(A),B,VVV):- tst((fbs_to_number(A,V),fbs_to_number(B,VV),!,VVV is (V \/ VV))).
merge_fbs(*(A),B,VVV):- fbs_to_number(A,V),fbs_to_number(B,VV),!,VVV is (V /\ VV).
merge_fbs(-(B),A,VVV):- fbs_to_number(A,V),fbs_to_number(B,VV),!,VVV is (V /\ \ VV).
merge_fbs([A],B,VVV):-  tst(merge_fbs(A,B,VVV)),!.
merge_fbs([A|B],C,VVV):- merge_fbs(A,C,VV),merge_fbs(B,VV,VVV),!.
merge_fbs(A,C,VVV):- fbs_to_number(A,VV),!,tst(merge_fbs(VV,C,VVV)),!.
merge_fbs(A,C,VVV):- fbs_to_number(override(A),VV),!,tst(merge_fbs(VV,C,VVV)),!.


fbs_to_number(N,O):- number(N),!,N=O.
fbs_to_number(V,VVV):- attvar(V),!,metaflags_get(V,VV),!,fbs_to_number(VV,VVV).
fbs_to_number(V,O):- var(V),!,0=O.
fbs_to_number([],0).
fbs_to_number(B << A,VVV):- !, fbs_to_number(B,VV), VVV is (VV << A).
fbs_to_number(B+A,VVV):- merge_fbs(+(A),B,VVV),!.
fbs_to_number(B*A,VVV):- merge_fbs(*(A),B,VVV),!.
fbs_to_number(B-A,VVV):- fbs_to_number(B,BB),fbs_to_number(A,Cell),VVV is (BB /\ \ Cell),!.
fbs_to_number(+(Bit),VVV):- fbs_to_number((Bit),VVV),!.
fbs_to_number(-(Bit),VVV):- fbs_to_number((Bit),V),!,VVV is ( \ V).
fbs_to_number(~(Bit),VVV):- fbs_to_number((Bit),V),!,VVV is ( \ V).
fbs_to_number( \ (Bit),VVV):- fbs_to_number((Bit),V),!,VVV is ( \ V).
fbs_to_number(bit(Bit),VVV):- number(Bit),!,VVV is 2 ^ (Bit).
fbs_to_number((Name),VVV):-   current_metaterm_mask(Name,VVV),!.
fbs_to_number((Name),VVV):- fbs_for_hooks_default(VV),arg(_,VV,Name=Bit),!,tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number((Name),VVV):- fbs_for_hooks_default(VV),arg(_,VV,override(Name)=Bit),!,tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number(override(Name),VVV):- fbs_for_hooks_default(VV),arg(_,VV,(Name)=Bit),!,tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number([A],VVV):- !,fbs_to_number(A,VVV).
fbs_to_number([A|B],VVV):- !,merge_fbs(B,A,VVV).
fbs_to_number(V,VVV) :- VVV is V.


check(Key):- flag(Key,Check,Check+1),b_getval(Key,G),dmsg(check(Key,Check,G)),fail. % , (nonvar(G)->(G,b_setval(Key));true).



%%    wi_atts(Hooks,Goal)
%
% With inherited Hooks call Goal

wi_atts(M,Goal):- must_notrace((get_metaflags(W),merge_fbs(M,W,N))),!,setup_call_cleanup_each(set_metaflags(N),Goal,set_metaflags(W)).



wno_dmvars(Goal):- wo_metaterm(wno_debug(Goal)).
w_dmvars(Goal):- with_metaterm(w_debug(Goal)).

wno_debug(Goal):- '$debuglevel'(W,0),W==0,!,Goal.
wno_debug(Goal):- setup_call_cleanup(exit_debug,Goal,enter_debug(4)).
w_debug(Goal):- setup_call_cleanup(enter_debug(4), Goal,exit_debug).

testfv:- forall(test1(T),dmsg(passed(T))).


a1:verify_attributes(_,_,[]).
a2:verify_attributes(_,_,[]).
a3:verify_attributes(_,_,[]).

test1(cmp_fbs_variants0):- put_atts(X,'$atts',4),put_attr(Y,'$atts',4),wi_atts(+variant,X=@=Y).
test1(cmp_fbs_variants0a):- put_attr(X,a1,1),put_attr(X,'$atts',4),put_attr(Y,'$atts',4),wi_atts(+variant,X=@=Y).

test1(cmp_fbs_variants1):- 
  put_attr(X,a1,1),put_attr(X,a2,2),put_attr(X,'$atts',1),
  put_attr(Y,'$atts',1),put_attr(Y,a1,1),put_attr(Y,'$atts',1),
   wi_atts(+variant,X=@=Y).

test1(cmp_fbs_variants2):- 
 put_attr(X,a1,1),put_attr(X,a2,2),
 metaterm_override_(X,+variant),
 metaterm_override_(Y,+variant),X=@=Y.

test1(cmp_fbs_variants3):- 
 put_attr(X,'$atts',1),
 put_attr(Y,'$atts',1),
   wi_atts(+variant,X=@=Y).

:- set_prolog_flag(atts_declared,auto).

:- module_transparent(system:term_expansion/2).
:- module_transparent(system:goal_expansion/2).
system:term_expansion(Dict,X):- current_prolog_flag(set_dict_attvar_reader,true),dict_to_attvar(Dict,X).
system:goal_expansion(Dict,X):- current_prolog_flag(set_dict_attvar_reader,true),dict_to_attvar(Dict,X).

% :- set_dict_attvar_reader(true).


set_module_metaterm_overriden(M,TF):- 
         module_property(M,file(F)),
         forall((current_predicate(_,_:PP), predicate_property(PP,file(F))),add_overriden(PP,TF)),
         forall((current_predicate(_,M:X),\+ predicate_property(X,imported_from(_))),add_overriden(X,TF)).

:- matts(+use_unify_var).

:- matts.


/*
:- use_module(library(logicmoo_utils)).

% :- system:reconsult('boot/attvar').


?- put_atts(X,'$meta':'$undo_unify'()=true(_)),metaterm_overriding(X,'$undo_unify',Z).

% Set =save_history= to =false= if you never want to save/restore the
% command history.   Normally, the history is enabled if the system
% provides a history and the input comes from a terminal.
rtrace(put_atts(X,'$undo_unify'()=true(_)))

% END - THESE ARE ONLY FOR TESTING - WILL BE REMOVED
metaterm_overriding(X,'$undo_unify',Z).
*/


% ?- metaterm_overide(X,print(X),(writeln('You wanted to print X'))), print(X).
% ?- metaterm_overide(X,==(_,_),same_thing(.......))

system:pointers(X,Y):- dmsg(pointers(X,Y)).

% ?- av(X),put_attr(X,'$meta',att(==(_,_),pointers(_,_),[])),'$find_override'(X,=(_,_),BAR),X==1.
% ?- av(X),put_attr(X,'$meta',att(copy_term,pointers(_,_),[])),copy_term(X,Y).

:-  set_prolog_flag(access_level,system).

:- nb_setval('$meta',true).
'$meta':verify_attributes(_,_,[]).
'$atts':verify_attributes(_,_,[]).
'$meta':attr_unify_hook(_,_).
'$atts':attr_unify_hook(_,_).

% ?-put_atts(X,'$undo_unify'(_)=true(_)),metaterm_overriding(X,'$undo_unify',_).

           /*******************************
           *	  ATTR UNDO HOOK	*


?- metaterm_override_(X,'$undo_unify'()),writeq(X),metaterm_overriding(X,'$undo_unify'(_,_),O).


           *******************************/

%%	post_unify(+Att3s, +Next, +Var, +Value)
%
%	Calls Module:attr_undo_hook(Var,Attrib,Binding) for each `Module` for which Var
%	*had* an attribute.
%
%       TODO: Currently disabled for performance reasons
/*

system:'$undo_unify'(att(Module, AttVal, Rest), Next, Var, Value):- !,
        Module:attr_undo_hook(Var, AttVal, Value),
        '$undo_unify'(Rest, Next, Var, Value).

system:'$undo_unify'(_, Next,Var, Value):- dmsg(undo(Var,Value)), call(Next).

system:attr_undo_hook(_Var, _AttVal, _Value).

*/

% END - THESE ARE ONLY FOR TESTING - WILL BE REMOVED

% av(X),put_attr(X,'$meta',att(==(_,_),pointers(_,_),[])),'$metaterm_flags'(Y,1),X==X.
% :- set_prolog_flag(save_history, false).
:- prolog_debug('MSG_METATERM'),prolog_debug('MSG_WAKEUPS'). % ,prolog_debug('MSG_ATTVAR_GENERAL').
wd:- ((prolog_nodebug('MSG_VMI'),prolog_nodebug('MSG_WAKEUPS'))).
:- wd.
wd(X):-  prolog_debug('MSG_WAKEUPS'),prolog_debug('MSG_VMI'), call_cleanup(X,wd).

% put_att_value(&gp[1],ATOM_true,makeRefL( valTermRef(id)));

:- module_transparent(export_all/0).
export_all:- 
 source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),
   \+ predicate_property(M:H,imported_from(_)),
   add_overriden(H,false),
   \+ arg(_,v(attr_unify_hook/_,metaterm_unify_hook/_,verify_attributes/_,metaterm_unify_hook/_,'$pldoc'/4,'$mode'/2,attr_portray_hook/_,attribute_goals/_),F/A),
   \+ atom_concat('_',_,F),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A))),
   \+ atom_concat('$',_,F),
   module_property(M,exports(L)),
   \+ memberchk(F/A,L),
   M:export(F/A),
   user:import(M:F/A),
   A\==0,   
   nop((writeq(F/A),writeln(',')))))).

 



system:dmsg(M):- current_predicate(MOD:dmsg/1),MOD=logicmoo_util_dmsg, !, logicmoo_util_dmsg:dmsg(M),!.
system:dmsg(M):- format(user_error,'~N~q.~n',[M]),flush_output(user_error).


tAA:verify_attributes(Var, Value, [get_attrs(CVar,AttrsNow),dmsg(tAA:goal_for(Name,Attrs=AttrsNow))]):- sformat(Name,'~w',Var), ignore(get_attrs(Var,Attrs)),put_attrs(CVar,Attrs),dmsg(tAA:va(Var,Value,[])=Attrs).
tBB:verify_attributes(Var, Value, [get_attrs(CVar,AttrsNow),dmsg(tBB:goal_for(Name,Attrs=AttrsNow))]):- sformat(Name,'~w',Var), ignore(get_attrs(Var,Attrs)),put_attrs(CVar,Attrs),dmsg(tBB:va(Var,Value,[])=Attrs).
tCC:attr_unify_hook(Attr, Value) :- dmsg(tCC:attr_unify_hook(Attr, Value)),!,Value\==bad.



tCC:attr_undo_hook(Var, Attr, Value) :- dmsg(tCC:attr_undo_hook(Var, Attr, Value)).

system:va(X):- put_attr(X,tAA,'AAA').
system:vb(X):- put_attr(X,tBB,'BBB').
system:vc(X):- put_attr(X,tCC,'CCC').

:- retract(was_access_level_atts(Was)),set_prolog_flag(access_level,Was).

:-  metaterm_flags(current,use_dra_interp,_).


/* This snoozes the pending wakeups durring Goal 
  Initialy this impl is incomplete for source 
   terms as it only deals with one Term per goal.
*/
:- meta_predicate(system:'$metaterm_call'(+,:,+,+,-,-)).
system:'$metaterm_call'(_PredName,Goal,_ArgNum,_Count,Var,Value):- 
   setup_call_cleanup( true,(must_or_die(metaterm_getval(Var,Value)),must_or_die(Var \== Value)),'$exit_metaterm_call'),
   Goal.


:- export_all.
:- set_module_metaterm_overriden('$attvar',false).
:- set_module_metaterm_overriden('atts',false).
:- add_overriden(set_varname(_,_,_),false).
:- add_overriden('$metaterm_call'(_,_,_,_,_),false).

end_of_file.


% swi prolog ignores peer wakeups ..
The following putput is incorrect...

Welcome to SWI-Prolog (Multi-threaded, 64 bits, Version 7.3.15-29-g6a6915a)
Copyright (c) 1990-2015 University of Amsterdam, VU Amsterdam
SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software,
and you are welcome to redistribute it under certain conditions.
Please visit http://www.swi-prolog.org for details.

For help, use ?- help(Topic). or ?- apropos(Word).

1 ?- va(A),vb(B),A=B.
tBB:va(_G294746,_G294739,[])=att(tBB,'BBB',[]).
tBB:goal_for("_G294746",att(tBB,'BBB',[])=att(tBB,'BBB',[])).
A = B,
put_attr(B, tAA, 'AAA').

2 ?- vb(B),va(A),A=B.
tAA:va(_G294734,_G294727,[])=att(tAA,'AAA',[]).
tAA:goal_for("_G294734",att(tAA,'AAA',[])=att(tAA,'AAA',[])).
B = A,
put_attr(A, tBB, 'BBB').


Here is this corrected...

Welcome to SWI-Prolog (Multi-threaded, 64 bits, Version 7.3.15-33-g5524040-DIRTY)

1 ?- va(A),vb(B),A=B.
tAA:va(_G319347,_G319354,[])=att(tAA,'AAA',[]).
tBB:va(_G319354,_G319347,[])=att(tBB,'BBB',[]).
tBB:goal_for("_G319354",att(tBB,'BBB',[])=att(tBB,'BBB',[])).
tAA:goal_for("_G319347",att(tAA,'AAA',[])=att(tAA,'AAA',[])).
A = B,
put_attr(B, tAA, 'AAA').

2 ?- vb(B),va(A),A=B.

tAA:va(_G319354,_G319347,[])=att(tAA,'AAA',[]).
tBB:va(_G319347,_G319354,[])=att(tBB,'BBB',[]).
tBB:goal_for("_G319347",att(tBB,'BBB',[])=att(tBB,'BBB',[])).
tAA:goal_for("_G319354",att(tAA,'AAA',[])=att(tAA,'AAA',[])).
B = A,
put_attr(A, tBB, 'BBB').

?- vc(C),freeze(F,writeln(C)),F=C.

