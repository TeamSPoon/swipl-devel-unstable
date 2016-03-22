/*  Part of SWI-Prolog

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
:- module(metaterm,[
   with_prolog_debug/2,
   w_dt/1,
   var_info/1,
   v1/2,
   ':='/2,
   use_unify_vp/1,
   use_unify_var/1,
   use_unify_var/0,
   use_h_var/1,
   use_cons_val/1,
   use_bind_const/1,
   use_barg_var/1,
   tst_ft/1,
   termfilter/2,
   term_copier_filter/2,
   term_copier_filter/1,
   term_copier/1,
   show_var/2,
   show_var/1,
   set_unifyp/2,
   set_prolog_nodebug/1,
   set_prolog_debug/1,
   run_b_test/1,
   rtrace_each/1,
   print_var/1,
   override_none/1,
   override_all/1,
   no_bind/1,
   use_vmi/1,
   nb_var/2,
   nb_var/1,
   must_ts_det/1,
   exists/1,
   unbind/1,
   must_ts/1,
   metaterm_call/2,
   memory_var/1,
   memory_fluent/1,
   maplist_local/2,
   make_list_with_element/3,
   lv/0,
   llv/0,
   label_sources/2,
   label_sources/1,
   global_or_var/2,
   enter_debug/1,
   do_test_type/1,
   dbg_list/1,
   counter_var/1,
   do_metaterm_tests/0,
   metaterm_test/0,
   plvar/1,
  anything_once/1,termfilter/1,subsumer_var/1,plvar_ex/1]).

:- multifile(atts:metaterm_type/1).
:- discontiguous(atts:metaterm_type/1).
:- dynamic(atts:metaterm_type/1).

:- multifile(fv:'$pldoc'/4).
:- discontiguous(fv:'$pldoc'/4).
:- dynamic(fv:'$pldoc'/4).

% :- user:use_module(library(metaterm)).


 /** <module> Fv Test Module

   Some experiments ongoing

   With any of the above set the system still operates as normal
              until the user invokes  'global_or_var'/2 to

   None of these option being enabled will cost more than
              if( (LD->attrvar.global_or_var & SOME_OPTION) != 0) ...

*/

:- meta_predicate must_ts_det(0).
:- meta_predicate metaterm_call(1,0).


:- user:use_module(library(atts)).

:- debug(fluents).
:- debug(attvars).
:- meta_predicate maplist_local(+,+).
:- module_transparent((maplist_local/2)).
:- meta_predicate do_test_type(1),must_ts(0),tst_ft(?).

%% depth_ometaterm_var(+Var,-FrameCount) is det.
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
% q(X) :- depth_ometaterm_var(X, D), format('Depth = ~w~n', [D]), D < 5, q(X), notail.
% notail.
% ==
%
% Running this says:
% ==
% 1 metaterm_test:- q.
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
%  metaterm_test:- anything_once(X),member(X,[1,2,3,3,3,1,2,3]).
%  X = 1;
%  X = 2;
%  X = 3;
%  No.
%  ==
% atts:metaterm_type(anything_once).
anything_once(Var):- nonvar(Var) ->true; (get_attr(Var,tnr,_)->true;put_attr(Var,tnr,old_vals([]))).

tnr:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz), \+ memberchk_same_q(VarValue,Waz),nb_setarg(1,AttValue,[VarValue|Waz]).


%% termfilter(-X) is det.
%
% Filter that may produce a term (source_fluent/1)
%
atts:metaterm_type(termfilter).
termfilter(G,X):-put_atts(X,+no_bind),put_attr(X,termfilter,G).
termfilter(X):-termfilter(dshowf(term_filer(X)),X).
termfilter:attr_unify_hook(Goal,Value):-call(Goal,Value).

%% term_copier(Fluent) is det.
%
% Aggressively make Fluent unify with non fluents (instead of the other way arround)
%
atts:metaterm_type(term_copier).
term_copier(Fluent):- put_atts(Fluent, +no_bind +term_copier +use_unify_var).
term_copier:attr_unify_hook(Var,ValueIn):-
   must_notrace((get_attr(Var,'$saved_atts',AttVal),
   del_attr(Var,term_copier),
   copy_term(Var,Value),
   put_attr(Value,'$atts',AttVal))),
   ValueIn=Value.



term_copier_filter(Goal,Fluent):-termfilter(Goal,Fluent),term_copier(Fluent).

term_copier_filter(Fluent):-termfilter(Fluent),term_copier(Fluent).

%% :=(MetaVar,Value).
% The destructive assignment operator :=/2 allows 
% you to override Prolog''s usual single-assignment 
% "write once" policy for variables. 
% It works in a way you''d expect from an imperative language.
':='(MetaVar,Value):- unbind(MetaVar),metaterm_setval(MetaVar,Value),assertion(unbind(MetaVar)).

%% nb_termfilter(-X) is det.
%
% Filters terms but stays unbound even after filtering
%


%% plvar_ex(-X) is det.
%
% Example of the well known "Prolog" variable!
%
% Using a term sink to emulate a current prolog variable (note we cannot use +no_bind)
%
% the code:
% ==
% /* if the new value is the same as the old value accept the unification*/
% plvar_ex(X):- source_fluent(X),put_attr(X,plvar_ex,binding(X,_)).
% plvar_ex:attr_unify_hook(binding(Var,Prev),Value):-  Value=Prev,put_attr(Var,plvar_ex,binding(Var,Value)).
% ==
%
% ==
% metaterm_test:- plvar_ex(X), X = 1.
% X = 1.
%
% metaterm_test:- plvar_ex(X), X = 1, X = 2.
% false.
% ==
%
/* if the new value is the same as the old value accept the unification*/


%plvar_ex(Var):- put_atts(Var,+source_fluent),put_attr(Var,plvar_ex,binding(Var,_)).
% plvar_ex:verify_attributes(Var,Value,[]):- get_attr(Var,plvar_ex,binding(Var,Prev)), Value=Prev, put_attr(Var,plvar_ex,binding(Var,Value)).
atts:metaterm_type(plvar_ex).

plvar_ex:metaterm_unify_hook(_Atom,binding(Var,Prev),_,Value):- Value=Prev,put_attr(Var,plvar_ex,binding(Var,Value)).

plvar_ex:attr_unify_hook(binding(_Var,Prev),Value):- Value=Prev.

plvar_ex(Var):- source_fluent(Var), put_attr(Var,plvar_ex,binding(Var,_)).



%plvar_ex(Var):- put_atts(Var,+source_fluent),put_attr(Var,plvar_ex,binding(Var,_)).
% plvar_ex:verify_attributes(Var,Value,[]):- get_attr(Var,plvar_ex,binding(Var,Prev)), Value=Prev, put_attr(Var,plvar_ex,binding(Var,Value)).
atts:metaterm_type(plvar).

plvar:metaterm_unify_hook(_Atom,Var,Var,Value):- metaterm_getval(Var,Prev),Value=Prev.

plvar:attr_unify_hook(Var,Value):- metaterm_getval(Var,Prev),!,Value==Prev.


use_vmi(Var):- put_atts(Var, +use_vmi).

%% exists(Var) is det.
% declare an a rebindable var that acts like a prolog variable
plvar(Var):- source_fluent(Var),put_attr(Var,plvar,Var), metaterm_setval(Var,_).


%% exists(Var) is det.
% declare an a rebindable var that acts like a minikanren variable
exists(Var):- 
   wo_metavmi((  must_notrace((  (meta(Var)->true;metaterm_setval(Var,_)),
     put_atts(Var, +(source_fluent:metaterm_getval) +(sink_fluent:metaterm_setval) +use_unify_var +no_bind + use_vmi))))).

%% unbind(Var) is det.
% unbind a variable
unbind(Var):- must_notrace((metaterm_reset(Var,_),exists(Var))).


%% subsumer_var(-X) is det.
%
%  Each time it is bound, it potentially becomes less bound!
%
%
% subsumer_var(X):- source_fluent(X),init_accumulate(X,subsumer_var,term_subsumer).
%
% ==
%  metaterm_test:-  subsumer_var(X), X= a(1), X = a(2).
%  X = a(_)  ;
% false.
%
%  metaterm_test:-  subsumer_var(X), X= a(1), X = a(2),  X=a(Y).
% X = a(Y).
% Y = _G06689  ;
% false.
%
%  metaterm_test:-  subsumer_var(X), X= a(1), X = a(2),  X=b(1).
% false
% ==
%
atts:metaterm_type(subsumer_var).
subsumer_var(X):- source_fluent(X),init_accumulate(X,pattern,term_subsumer).

metaterm_call(FluentFactory,Goal):-
   term_variables(Goal,Vs),
   maplist(FluentFactory,Vs),
   Goal.


tst:verify_attributes(X, Value, [format('~N~q, ~n',[goal_for(Name)])]) :- sformat(Name,'~w',X), get_attr(X, tst, Attr),format('~Nverifying: ~w = ~w (attr: ~w),~n', [X,Value,Attr]).

% tst:attr_unify_hook(Attr,Value):-format('~N~q, ~n',[tst:attr_unify_hook(Attr,Value)]).

% :- discontiguous(tst/1).


%% counter_var(-X) is det.
%
% Example of:
%
% Using a term sink to add numbers together
%
% ==
% counter_var(X):- source_fluent(X),init_accumulate(X,numeric,plus).
% ==
%
% ==
%  metaterm_test:-  counter_var(X), X= 1, X = 1.
%  X = 2.
% ==
%
atts:metaterm_type(counter_var).
counter_var(X):- source_fluent(X),init_accumulate(X,counter_var,plus).


%% nb_var(+X) is det.
%
% Using prolog variable that is stored as a global (for later use)
%
% nb_var/1 code above doesnt call nb_var/2 (since source_fluent/1 needs called before call we call format/3 .. promotes a _L666 varable to _G666 )
atts:metaterm_type(nb_var).
nb_var(V):- source_fluent(V), format(atom(N),'~q',[V]),nb_linkval(N,V),put_attr(V,nb_var,N),nb_linkval(N,V).
nb_var:attr_unify_hook(N,Value):-
       nb_getval(N,Prev),
       ( % This is how we produce a binding for +source_fluent "iterator"
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
%  metaterm_test:-  nb_var('ForLater',X), member(X,[1,2,3]).
%  X = 1.
%
%  metaterm_test:- nb_var('ForLater',X).
%  X = 1.
%
%
% ==
nb_var(N, V):- source_fluent(V), nb_linkval(N,V),put_attr(V,nb_var,N),nb_linkval(N,V).


:-'$debuglevel'(_,0).

system:push_current_source_module(M):- prolog_load_context(module,SM),asserta('$source_context':'$c_source_context'(SM)),'$set_source_module'(M).
system:pop_current_source_module:- retract('$source_context':'$c_source_context'(SM)),'$set_source_module'(SM).

%:- push_current_source_module(user).


ab(a1,b1).
ab(a2,b2).
ab(a3,b3).

xy(x1,y1).
xy(x2,y2).
xy(x3,y3).


equals(X,Y):-equals0(X,Y),!.

equals0(X,X).
equals0(a1,x1).
equals0(a2,x2).
equals0(a3,x3).
equals0(b1,y1).
equals0(b2,y2).
equals0(b3,y3).


q(A,B):-ab(A,B),xy(A,B).

%:- pop_current_source_module.

%% set_unifyp(+Pred,?Fluent) is det.
%
% Create or alter a Prolog variable to have overrideed unification
%
% Done with these steps:
% 1) +sink_fluent = Allow to remain a variable after binding with a nonvar
% 2) +source_fluent = Declares the variable to be a value producing with on_unify_keep_vars
% 3) Set the unifyp attribute to the Pred.
set_unifyp(Pred,Fluent):- wno_dmvars((no_bind(Fluent),put_attr(Fluent,unifyp,binding(Pred,Fluent,_Uknown)))).

% unifyp:attr_unify_hook(binding(Pred,Fluent,Prev),Value):- unifyp:metaterm_unify_hook(_Why,binding(Pred,Fluent,Prev),_What,Value).

% Our implimentation of a unifyp variable
unifyp:metaterm_unify_hook(_Atom,binding(_Pred,_Fluent,_Prev),Var,_Value):-nonvar(Var),!. % ,ignore(call(Pred,Var,Value)).
unifyp:metaterm_unify_hook(_Atom,binding(Pred,Fluent,Prev),_Var,Value):-
        % This is how we produce a binding for +source_fluent "on_unify_keep_vars"
          (var(Value),nonvar(Prev)) ->  Value=Prev;
         % same binding (effectively)
             Value==Prev->true;
         % unification we will update the internal value
             Value=Prev->put_attr(Fluent,unifyp,binding(Pred,Fluent,Value));
         % Check if out override was ok
             call(Pred,Prev,Value) -> true;
         % Symmetrically if out override was ok
             call(Pred,Value,Prev)-> true.

label_sources(A,B):-label_sources(A),label_sources(B).
label_sources( Fluent):- get_attr(Fluent,unifyp,binding(_,Fluent,Value)),!,attv_bind(Fluent,Value).
label_sources(_Fluent):-!.

lv:- user: ((metaterm_call(set_unifyp(equals),(q(A,B),label_sources(A,B),dmsg(q(A,B)))))).
llv:- log_flag(dmiles,true),user:reconsult(library(metaterm)), metaterm_call(set_unifyp(equals),(q(A,B),label_sources(A,B),dmsg(q(A,B)))).
lv2:- put_atts(X,[+use_unify_var]),X=_.

:- module_transparent(tst:verify_attributes/3).

%tst:metaterm_unify_hook(_,_,_,_).
%no_bind:metaterm_unify_hook(_,_,_,_).
%use_unify_var:metaterm_unify_hook(_,_,_,_).

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





% :- autoload.


t1:- must_ts(rtrace((when(nonvar(X),member(X,[a(1),a(2),a(3)])),!,findall(X,X=a(_),List),List==[a(1),a(2),a(3)]))).

t2:- must_ts(rtrace( (freeze(Foo,setarg(1,Foo,cant)),  Foo=break_me(borken), Foo==break_me(cant)))).


/* This tells C, even when asked, to not do bindings (yet)
                      This is to allow the variables to interact with the standard prolog terms, clause databases and foriegn objects.. for example:
                    tst:put_attr(Fluent,+no_bind),jpl_to_string("hi",Fluent),X="HI",X=['h','i'],
                       Even if verify_attributes succeeds, still do not bind to the value.
                       verify_attributes should in this case
                       use continuation goals to update some internal state to decides
                       later how it will continue to operate
                       for exmaple:  It has been unified with 'Red'  and 'Blue' (primary colors) ..

                        Fluent='Red',Fluent='Blue'


                       verify_attribute now only unify with purple as a secondary color.

                       and have the vars attributes manipulated yet still remain a Fluent and able to continue to work with further standard prolog terms
                       (like in the 'Purple' example).      */


/* attempt to linkval and replace whatever  we unify with
             (we are passed a new variable that is linkvaled into the slot )
              if X_no_trail is set, the structure modification does not backtrack
              if X_peer_trail is set, the new variable is trailed

              that veriable is trailed so we can have that slot become a variable again and then even the orginal binding
              if we bind *that* variable with the original value durring our wakeup
               */



must_ts(G):- !, must(G).
must_ts(G):- G*-> true; throw(must_ts_fail(G)).
must_ts_det(G):- !, must(G),!.
must_ts_det(G):- G,deterministic(Y),(Y==true->true;throw(must_ts_fail_det(G))).

do_test_type(MType):- strip_module(MType,_M,Type), atts:metaterm_type(Type), writeln(maplist_local=Type+X),
   call(Type,X),
  maplist_local(=(X),[1,2,3,3,3,1,2,3]),
  writeln(value=X),
  var_info(X).


do_test_type(MType):- strip_module(MType,_M,Type),atts:metaterm_type(Type),
  once((writeln(vartype=call(Type,X)),
      call(Type,X),
      ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(Type=X),
      ignore((get_attrs(X,Ats),writeln(Ats=X))),
      fail)),
      writeln(value=X))),var_info(X).

tv123(B):-put_atts(X,B),t123(X).
t123(X):- print_var(xbefore=X),L=link_term(X,Y,Z),dmsg(before=L),
  ignore((
   X=1,X=1,ignore(show_call(X=2)),w_debug(Y=X),w_debug(X=Z),print_var(x=X),
   print_var(y=Y),print_var(z=Z),ignore(show_call(X=2)),dmsg(each=L),fail)),
   dmsg(after=L).

maplist_local(G,List):-List==[]->!;(List=[H|T],must_ts(call(G,H)),maplist_local(G,T)).


:- meta_predicate w_dt(0).
w_dt(G):-
  % undo(exit_debug),
  setup_call_cleanup_each(enter_debug(4),G,exit_debug).


% dbg_list([]):-!.
% dbg_list(['MSG_WAKEUPS','MSG_METATERM','MSG_CONTINUE','MSG_ATTVAR_GENERAL']).
dbg_list(['MSG_WAKEUPS','MSG_METATERM','MSG_CONTINUE','MSG_ATTVAR_GENERAL','MSG_CUT','MSG_CLEANUP','MSG_DRA','MSG_THROW','MSG_CALL','MSG_TRACE','MSG_VMI']).
enter_debug(N):-must_notrace(('$debuglevel'(_,0),dbg_list(Lst),!,maplist(set_prolog_debug,Lst),'$debuglevel'(_,N))).
exit_debug:-must_notrace(('$debuglevel'(_,0),set_prolog_nodebug('MSG_VMI'),dbg_list(Lst),!,maplist(set_prolog_nodebug,Lst))).


% setting these flags in debugging so we can remember to turn them off/on with list_debug_topics/0.
set_prolog_debug(M):-  ignore(retract(prolog_debug:debugging(M, false,[user_error]))),prolog_debug(M),retractall(prolog_debug:debugging(M,_,_)),assert(prolog_debug:debugging(M, true,[user_error])).
set_prolog_nodebug(M):- ignore(retract(prolog_debug:debugging(M, true,[user_error]))),prolog_nodebug(M),retractall(prolog_debug:debugging(M, _,_)),assert(prolog_debug:debugging(M, false,[user_error])).

:- meta_predicate with_prolog_debug(+,0).
with_prolog_debug(M,G):- setup_call_cleanup_each(set_prolog_debug(M),G,set_prolog_nodebug(M)).

:- debug(fluents).

var_info(V):- wno_dmvars(show_var(V)).
print_var(V):-wno_dmvars(show_var(V)).
show_var(E):- wno_dmvars((nonvar(E),(N=V)=E, show_var(N,V))),!.
show_var(V):- wno_dmvars((show_var(var_was,V))).

show_var(N,V):- wno_dmvars(((((\+ attvar(V)) -> dmsg(N=V); (must_ts((get_attrs(V,Attrs),any_to_fbs(V,Bits))),dmsg(N=(V={Attrs,Bits}))))))).


% https://github.com/Muffo/aiswi/blob/master/sciff/restrictions.pl

% https://github.com/Muffo/aiswi/blob/master/sciff/quant.pl

%% source_fluent(Fluent) is det.
%
% Give Fluent a chance to supply an effective value when compared with prolog terms
%
atts:metaterm_type(source_fluent).
% source_fluent(Fluent):- global_or_var(Fluent,+source_fluent),source_fluent.

%% use_unify_var(Fluent) is det.
%
% Aggressively make Fluent unify with non fluents (instead of the other way arround)
%
atts:metaterm_type(use_unify_var).
use_unify_var(Fluent):- global_or_var(Fluent,+use_unify_var).

%% no_bind(Fluent) is det.
%
% Preserve the identity of this fluent
%
atts:metaterm_type(no_bind).
no_bind(Fluent):- global_or_var(Fluent,+no_bind).

global_or_var(Var,Set):- Var==global,!,matts(_Get,Set).
global_or_var(Var,Set):- put_atts(Var,Set).

use_bind_const(Var):- global_or_var(Var, +use_bind_const).
use_unify_vp(Var):- global_or_var(Var, +use_unify_vp).
use_h_var(Var):- global_or_var(Var, +use_h_var).
use_cons_val(Var):- global_or_var(Var, +use_cons_val).
use_barg_var(Var):- global_or_var(Var, +use_barg_var).

use_unify_var:- global_or_var(global,+use_unify_var).
noeagerly:- override_none.
source_fluent:- global_or_var(global,+source_fluent).
pass_ref:- global_or_var(global,+source_fluent).
override_none(Var):-  global_or_var(Var,-metaterm_override_usages_mask).
override_all(Var):-  global_or_var(Var,+metaterm_override_usages_mask).
override_none:-override_none(global).
override_all:-override_all(global).

test123:verify_attributes(Fluent,_Value,[]):- member(Fluent,[default1,default2,default3]).
% test123:attr_unify_hook(_,Value):- member(Value,[default1,default2,default3]).


'$ident':verify_attributes(Var,Value,Goals):- debug(attvars,'~N~q.~n',['$ident':verify_attributes(Var,Value,Goals)]),fail.
'$ident':verify_attributes(Fluent,Value,[]):- var(Fluent),contains_fbs(Fluent,on_unify_keep_vars),var(Value),!,member(Value,[default1,default2,default3]).



'$ident':attr_unify_hook(Var,Value):-
  wno_dmvars((((ignore((var(Var),get_attrs(Var,Attribs),
   debug(termsinks,'~N~q.~n',['$ident':attr_unify_hook({var=Var,attribs=Attribs},{value=Value})]))))))).
'$ident':attr_unify_hook(Var,Value):- var(Var),contains_fbs(Var,iteratorVar),var(Value),!,member(Value,[default1,default2,default3]).

:-  debug(fluents).



%% memberchk_same_q( ?X, :TermY0) is semidet.
%
% Uses =@=/2,  except with variables, it uses ==/2.
%
memberchk_same_q(X, List) :- is_list(List),!, \+ atomic(List), C=..[v|List],!,(var(X)-> (arg(_,C,YY),X==YY) ; (arg(_,C,YY),X =@= YY)),!.
memberchk_same_q(X, Ys) :-  nonvar(Ys), var(X)->memberchk_same0(X, Ys);memberchk_same1(X,Ys).
memberchk_same0(X, [Y|Ys]) :-  X == Y  ; (nonvar(Ys),memberchk_same0(X, Ys)).
memberchk_same1(X, [Y|Ys]) :-  X =@= Y ; (nonvar(Ys),memberchk_same1(X, Ys)).

memberchk_same2(X, List) :- Hold=hold(List), !,
        repeat, (arg(1,Hold,[Y0|Y0s]) ->
          ( X==Y0-> true; (nb_setarg(1,Hold,Y0s),fail)) ; (! , fail)).

memberchk_same3(X, List) :- Hold=hold(List), !,
        repeat, (arg(1,Hold,[Y0|Y0s]) ->
          ( X=@=Y0-> true; (nb_setarg(1,Hold,Y0s),fail)) ; (! , fail)).

/*
memb_r(X, List) :- Hold=hold(List), !, throw(broken_memb_r(X, List)),
         repeat,
          ((arg(1,Hold,[Y|Ys]),nb_setarg(1,Hold,Ys)) -> X=Y ; (! , fail)).
*/


%% memory_var(+Fluent) is det.
%
% An attributed variable that records it''s past experience
%
% metaterm_test:- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).
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
mv:attr_unify_hook(AttValue,FluentValue):- AttValue=old_vals(Waz),nb_setarg(1,AttValue,[FluentValue|Waz]).

atts:metaterm_type(memory_var).
memory_var(Fluent):- ensure_meta(Fluent), (nonvar(Fluent) ->true; (get_attr(Fluent,mv,_)->true;put_attr(Fluent,mv,old_vals([])))).


tst_ft(memory_var):- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).


%% memory_fluent(+Fluent) is det.
%
%  Makes a variable that remembers all of the previous bindings (even the on ..)
%
%  This is strill to be wtritten
%
%  ==
%  metaterm_test:- memory_fluent(X),member(X,[1,2,3,3,3,1,2,3]).
%  X = 1;
%  X = 2;
%  X = 3;
%  No.
%  ==
% memory_fluent(Fluent):-put_atts(Sink,[]), put_attr(Sink,zar,Sink),memory_var(Fluent),Fluent=Sink.
atts:metaterm_type(memory_fluent).
memory_fluent(Fluent):-put_atts(Fluent,[]),put_attr(Fluent,'_',Fluent),put_attr(Sink,zar,Sink),memory_var(Fluent),Fluent=Sink.




% :- [src/test_va].



/*
:- if((
  exists_source( library(logicmoo_utils)),
  current_predicate(gethostname/1),
  % fail,
  gethostname(ubuntu))).



:- use_module(library(http/http_path)).
:- use_module(library(http/http_host)).
*/


:- use_module(library(logicmoo_utils)).


% :- wo_metaterm(use_listing_vars).

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
    %  % :- debug(_).
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

make_list_with_element(0,_,[]):-!.
make_list_with_element(N,Init,[Init|List]):- Nm1 is N-1, make_list_with_element(Nm1,Init,List).



do_metaterm_tests:- forall(clause(metaterm_test,B),(nl,nl,run_b_test(B),nl,nl)).


run_b_test(B):- amsg(run_test(B)),fail.
run_b_test(B):- catch((call((B,deterministic(Det),true)),!,(Det==true->amsg(test_passed(B));amsg(test_warn_nondet(B)))),_,fail),!.
run_b_test(B):- catch((rtrace_each(B),fail),E,amsg(test_error(E,B))),!.
run_b_test(B):- amsg(test_failed(B)),!.

rtrace_each((A,B)):-!,rtrace_each(A),!,rtrace_each(B),!.
rtrace_each(B):-rtrace(B).

cls0 :- shell(clear),shell(cls).
:- export_all.
:- set_module_metaterm_overriden('metaterm',false).

:- discontiguous(metaterm_test/0).

metaterm_test:-
  source_fluent(X),metaterm_setval(X,foo),
  dmsg([x=X,y=Y,z=Z]),
  Y=X,
  dmsg([x=X,y=Y,z=Z]),
  X:=bar,
  X=Z,
  dmsg([x=X,y=Y,z=Z]),
  wo_metaterm(dmsg([x=X,y=Y,z=Z])),
  meta(X),
  writeln(X).

metaterm_test:-
  source_fluent(X),
  metaterm_setval(X,foo),
  dmsg([x=X,y=Y,z=Z]),
  Y=X,
  dmsg([x=X,y=Y,z=Z]),
  X:=bar,
  X=Z,
  dmsg([x=X,y=Y,z=Z]),
  meta(X),
  writeln(X).


metaterm_test:- source_fluent(X),not(X=one).
metaterm_test:- X:=foo,Y=X,Y==foo,meta(X).
metaterm_test:- source_fluent(X),(X:=one),X=one.
metaterm_test:- source_fluent(X),metaterm_push(X,one),metaterm_push(X,too),metaterm_push(X,3),!,findall(X,X=_,List),List==[one,too,3].
metaterm_test:- source_fluent(X),copy_var(X),(X:=foo),dmsg( ( x : X , y : Y ) ),Y=X,Y=foo,meta(X).
metaterm_test:- source_fluent(X),\+ X=one.
metaterm_test:- sink_fluent(X),X=one,X=too.
metaterm_test:- sink_fluent(X),X=one,metaterm_push(X,too),metaterm_push(X,3),X=3.
metaterm_test:- sink_fluent(X),X=one,metaterm_push(X,too),metaterm_push(X,3),source_fluent(X),!,findall(X,X=_,List),List==[one,too,3].
metaterm_test:- sink_fluent(X),source_fluent(X),X=one,Y=X,_Z=Y,Y==one,X\==one,meta(X).
metaterm_test:- sink_fluent(X),metaterm_push(X,one),metaterm_push(X,too),metaterm_push(X,3),source_fluent(X),!,findall(X,X=_,List),List==[one,too,3].
metaterm_test:- sink_fluent(X),metaterm_push(X,one),metaterm_push(X,too),metaterm_push(X,3),metaterm_push(X,4),get_attr(X,value,Vs),!,Vs==[one,too,3,4].
metaterm_test:- sink_fluent(X),metaterm_push(X,one),metaterm_push(X,too),metaterm_push(X,3),findall(X,X=_,List),List==[].
metaterm_test:- sink_fluent(X),metaterm_push(X,one), dif(X,one),copy_term(X,Y,G),member(E,G),dif(Y, one)==E.
metaterm_test:- sink_fluent(X),dif(X,one),X=too,copy_term(X,Y,G),member(E,G),dif(Y, one)==E.
metaterm_test:- no_bind(X),X=one,X=too.
metaterm_test:- exists(X),var(X),X=one,meta(X),writeln(X),unbind(X),var(X),X=too,writeln(X).
metaterm_test:- copy_var(X),Y=X,Y=one,X==Y.
metaterm_test:- copy_var(X),Y=X,Y=one,unbind(X).
metaterm_test:- copy_var(X),Y=X,X=one,writeln(Y),Y==one,unbind(Y),var(Y),X=one.

metaterm_test:- X:=one,number(X),\+ var(X).
metaterm_test:- X:=2, X:=one, X==one.
metaterm_test:- X:=2, X:=one, X=one.
metaterm_test:- X:=2, X:=one, \+ (X=2).
metaterm_test:- X:=2, X:=one, \+ (X=3).
metaterm_test:- X:=2, \+ \+ (X:=one), X==2.
metaterm_test:- X:=2, X:=one, X:=3.
metaterm_test:- X:=one,X=Y,X==one,Y==one.

system:print_metaterm(X):-writeq(X).
:-export(print_metaterm/1).
:- add_overriden(print_metaterm/1,very_deep).

/*
foo(X,X,X).. converts to  
  metaterm_getval(foo,foo(A,X,X),one,X,A), 
  metaterm_getval(foo,foo(A,B,X),2,X,B),
  metaterm_getval(foo,foo(A,B,C),3,X,C),
  metaterm_overloading(X,foo(A,B,C),G),
  call(G).
*/

metaterm_test:- source_fluent(X),metaterm_setval(X,3),metaterm_setval(X,2),3 is X + 1.
metaterm_test:- source_fluent(X),metaterm_setval(X,2),3 is X + 1.


