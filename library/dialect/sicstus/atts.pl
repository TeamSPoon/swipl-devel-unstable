/*  Part of SWI-Prolog

    Author:        Douglas R. Miles
    E-mail:        logicmoo@gmail.com
    WWW:           http://www.swi-prolog.org
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

:- module(attributes, ['attribute'/1,get_atts/2,put_atts/2, op(1150, fx, 'attribute')]).

:- meta_predicate('attribute'(:)).
:- meta_predicate(get_atts(+,:)).
:- meta_predicate(put_atts(+,:)).

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

put_atts(Var,M:Atts):- at_put(Var,M,Atts).


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

get_atts(Var,M:Atts):- at_get(Var,M,Atts).


at_exist(_A,_At):- current_prolog_flag(atts_declared,auto),!.
at_exist(M,At):- \+ \+ assertion(protobute(M,At,_)).

at_module(Var,M):- get_attr(Var,M,Was)->assertion(is_list(Was));put_attr(Var,M,[]).

at_tmpl(At,Tmpl):-functor(At,F,A),functor(Tmpl,F,A).

at_modulize([], _) --> [].
at_modulize([G|Gs], M) --> !,
    at_modulize(G, M),
    at_modulize(Gs, M).
at_modulize(G,M)-->
 {strip_module(G,_,GS),
     (G == GS -> MG = M:G ; MG = G)},
 [MG]. 


attrs_to_atts([])--> [].
attrs_to_atts(att(M,Att,Rest))-->
   at_modulize(Att,M),
   attrs_to_atts(Rest).


% Should 'user' use the import_module/2 Dag? (curretly will just return all)
at_get(Var,user,Atts):-var(Atts),!,get_attrs(Var,Attr),attrs_to_atts(Attr,Atts,[]).
% at_get(Var,M,At):-var(At),!,get_attr(Var,M,At).
at_get(Var,M,List):-is_list(List),!,maplist(at_get(Var,M),List).
at_get(Var,M,+At):- !,at_get(M,Var,At).
at_get(Var,_,-(M:At)):- !,at_get(Var,M,-At).
at_get(Var,_, (M:At)):- !,at_get(Var,M,At).
at_get(Var,M,-At):-!,
   at_exist(M,At),
   (get_attr(Var,M,Cur)->
      \+ memberchk(At,Cur) ;
    true).
at_get(Var,M,At):-
   at_exist(M,At),
   (get_attr(Var,M,Cur)->
      memberchk(At,Cur) ;
    fail).


at_put(_,M,At):-var(At),!,throw(error(instantiation_error,put_atts(M:At))).
at_put(Var,M,List):-is_list(List),!,at_module(Var,M),maplist(at_put(Var,M),List).
at_put(Var,M,+At):- !,at_put(M,Var,At).
at_put(Var,_,-(M:At)):- !,at_put(Var,M,-At).
at_put(Var,_, (M:At)):- !,at_put(Var,M,At).
at_put(Var,M,-Tmpl):-!,
   at_exist(M,Tmpl),
   (get_attr(Var,M,Cur)->
     (delete(Cur,Tmpl,Upd),put_attr(Var,M,Upd)) ;
    true).
at_put(Var,M,At):-
   at_exist(M,At),
   (get_attr(Var,M,Cur) ->
    (at_tmpl(At,Tmpl),
     delete(Cur,Tmpl,Mid), % ord_del_element wont work here because -a(_) stops short of finding a(1).
     ord_add_element(Mid,At,Upd),
     put_attr(Var,M,Upd));
    put_attr(Var,M,[At])).

