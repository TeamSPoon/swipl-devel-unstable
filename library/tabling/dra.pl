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

:- module('$dra',[]).
:- '$set_source_module'(_,'$dra').
:- 'set_prolog_flag'(access_level,system).

   % NOTICE: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %                                                                      %
   %  COPYRIGHT (2009) University of Dallas at Texas.                     %
   %                                                                      %
   %  Developed at the Applied Logic, Programming Languages and Systems   %
   %  (ALPS) Laboratory at UTD by Feliks Kluzniak.                        %
   %                                                                      %
   %  Permission is granted to modify this file, and to distribute its    %
   %  original or modified contents for non-commercial purposes, on the   %
   %  condition that this notice is included in all copies in its         %
   %  original form.                                                      %
   %                                                                      %
   %  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,     %
   %  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES     %
   %  OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, TITLE AND     %
   %  NON-INFRINGEMENT. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR        %
   %  ANYONE DISTRIBUTING THE SOFTWARE BE LIABLE FOR ANY DAMAGES OR       %
   %  OTHER LIABILITY, WHETHER IN CONTRACT, TORT OR OTHERWISE, ARISING    %
   %  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR       %
   %  OTHER DEALINGS IN THE SOFTWARE.                                     %
   %                                                                      %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- shell(cls).

:- dynamic   user:file_search_path/2.
:- multifile user:file_search_path/2.

:- meta_predicate asserta_new(:).
:- meta_predicate dra_must(:).
:- meta_predicate dra_check(:).
% asserta_new(G):-catch(G,_,fail),!.
asserta_new(G):-retract_all0(G),asserta(G).

dra_must(G):-G*->true;throw(failed_must(G)).

property_pred((table),is_tabled).
property_pred(is_cuts_ok,cuts_ok).
property_pred(never_table,is_never_tabled).
property_pred(old_first,is_old_first).
property_pred(coinductive0,is_coinductive0).
property_pred(coinductive1,is_coinductive1).

property_pred(topl,is_topl).
property_pred(support,is_support).
property_pred(local,is_local).
property_pred((traces),is_tracing).
property_pred(set_default_extension,default_extension).
property_pred(hilog,is_hilog).

:- forall(property_pred(D,F) ,((DG=..[D,_],user:asserta(( user:DG :- trace,execute_directive(DG)))), 
   ( \+ current_op(_,fy,user:D) -> op(900,fy,user:D) ; true), module_transparent(user:D/1), multifile(F/1),dynamic(F/1))).


% :- multifile sandbox:safe_primitive/1.
% :-asserta((sandbox:safe_primitive(Z):-wdmsg(Z))).

% ON :- initialization( profiler(_,walltime) ).
% ON :- initialization(user:use_module(library(swi/pce_profile))).

% :- user:ensure_loaded(library(ape/get_ape_results)).

:- user:ensure_loaded(library(logicmoo/util/logicmoo_util_all)).

:- use_module(library(coinduction),
  	  [ (coinductive)/1,
  	    op(1150, fx, (coinductive))
  	  ]).

retract_all0(R):- ignore((retract(R),fail)).

pf(F):- dra_must(retract_all0(topl(_))),
  dra_to_filename(F,FC),
   dra_must([(FC)]),!.  % ,once(ignore((run_curent_test,sleep(2)))))).

run_curent_test:- (if_is_defined(go,if_is_defined(test,if_is_defined(top)))),!.
run_curent_test:- topl(_),!,forall(topl(I),time((ignore(call((nonvar(I),dra_call(I))))))),!.

:- set_prolog_flag(debugger_show_context,true).
:- dynamic(is_clause_module/2).

clause_module(_:Goal,M):- clause_module0(Goal,M),!.
clause_module(Goal,M):-  clause_module0(Goal,M),!.
clause_module(M:_ ,M):-atom(M).

clause_module0(:- (Goal) ,M):- !, clause_module0(Goal,M).
clause_module0((Goal:- _ ),M):- !, clause_module0(Goal,M).
clause_module0((Goal , _ ),M):- !, clause_module0(Goal,M).
clause_module0(Goal,M):- is_clause_module(Goal,M),!.
clause_module0(Goal,M):- clause_module1(Goal,M),asserta(is_clause_module(Goal,M)),!.

clause_module1(Goal,M):-predicate_property(Goal,imported_from(M)),!.
clause_module1(Goal,M):-current_predicate(_,M:Goal),!.
clause_module1(Goal,M):-source_file(Goal,F), module_property(M,file(F)),!.
clause_module1(Goal,M):-predicate_property(_:Goal,imported_from(M)),!.
clause_module1(Goal,M):-current_module(M),current_predicate(_,M:Goal),!.
clause_module1(Goal,M):-clause(Goal,_,Ref),clause_property(Ref,module(M)).
clause_module1(Goal,M):-clause(_:Goal,_,Ref),clause_property(Ref,module(M)).


% dra_load( +file name ):
% Initialise, then load a program from this file, processing directives and
% queries.  After this is done, enter interactive mode.


:-export(dra_load/1).
dra_load( FileName ) :-
     dra_must((
        setup,
        initialise)),                              % provided by a metainterpreter
        dra_must((process_file( FileName ))),!,
        dra_must((check_general_consistency)),
        dra_must((program_loaded)),!.                          % provided by a metainterpreter


/*
cputime(TimeMS):- 
	statistics(runtime,[TimeMS,_]).
*/

% process_file( +file name ):
% Load a program from this file, processing directives and queries.

% :- mode process_file( +).

do_process_file( FileName ) :-    
        open_the_file( FileName, ProgStream ),
        process_input( ProgStream ),!,
        
        assertion(at_end_of_stream(ProgStream)),        
   % atom_to_memory_file('',Null_stream),
   % file_directory_name(FileName,D),
   stream_property(ProgStream,file_name(FN)),
   load_files(FN,[derived_from(FileName),register(true),stream(ProgStream)]),
        close( ProgStream ),!.

memberchk_same(X, [Y0|Ys]) :- is_list(Ys),!,C=..[v,Y0|Ys],!, arg(_,C,Y), ( X =@= Y ->  (var(X) -> X==Y ; true)),!.
memberchk_same(X, [Y|Ys]) :- (   X =@= Y ->  (var(X) -> X==Y ; true) ;   (nonvar(Ys),memberchk_same(X, Ys) )).
no_repeats_var(Var):- nonvar(Var) ->true;(get_attr(Var,nr,_)->true;put_attr(Var,nr,old_vals([]))).
nr:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz), !, \+ memberchk_same(VarValue,Waz),nb_setarg(1,AttValue,[VarValue|Waz]).

current_dirs(DO):- no_repeats_var(DO),current_dirs0(D),(atom_concat(DO,'/',D)->true;DO=D).
current_dirs0(D):- prolog_load_context(directory,D).
current_dirs0(D):- working_directory(D,D).
current_dirs0(D):- current_stream(_,read,Y), stream_property(Y,file_name(FN)), file_directory_name(FN,D).
current_dirs0(D):- stream_property(_,file_name(FN)), file_directory_name(FN,D).
current_dirs0(D):- expand_file_name('*/',X),member(E,X),absolute_file_name(E,D),exists_directory(D).
current_dirs0(D):- expand_file_name('*/*/',X),member(E,X),absolute_file_name(E,D),exists_directory(D).
current_dirs0(D):- expand_file_name('*/*/*/',X),member(E,X),absolute_file_name(E,D),exists_directory(D).
current_dirs0(D):- source_file_property(FN, modified(_)), file_directory_name(FN,D).
current_dirs0('.').

dra_to_filename( FileName, FileName ) :- atomic(FileName),exists_file(FileName),!.
dra_to_filename( FileName, AFN ) :-
 dra_must(default_extension( Ext );Ext='.tlp'), 
 dra_must((current_dirs(D),
     member(TF,[false,true]),
        absolute_file_name(FileName,AFN,[solutions(all),expand(TF),access(read),relative_to(D),file_errors(fail),
          extensions(['',Ext,'.pl','.tlp','.clp','.P'])]),
        exists_file(AFN))),!.

:-dynamic(is_pred_metainterp_0/2).
is_pred_metainterp(Pred,M):- is_pred_metainterp_0(Pred,M),!.
is_pred_metainterp(Pred,M):-
    is_tabled(Pred)-> M = is_tabled ;
    is_coinductive1(Pred)-> M = is_coinductive1 ;
    is_support(Pred)-> M = is_support ;
    cuts_ok(Pred)-> M = cuts_ok ;
    is_never_tabled(Pred)-> M = is_never_tabled.
is_pred_metainterp(Pred,M):- source_file(Pred,File),is_file_meta(File,M),!.
is_pred_metainterp(Pred,M):- might_be_clause_meta(Pred)-> M = is_never_tabled. 
is_pred_metainterp(_   ,unknown).


:- dynamic(is_file_meta/2).
add_file_meta(FileName,Type):-dra_to_filename(FileName,File),asserta_new(is_file_meta(File,Type)).

%:-add_file_meta('compatibility_utilities_swi',cuts_ok).
%:-add_file_meta('swi_toplevel',cuts_ok).
%:-add_file_meta('dra_common',cuts_ok).


user:listing_mpred_hook(What):- dra_listing(What).

dra_listing(What):-get_pi(What,PI),PI\=@=What,!,dra_listing(PI).
dra_listing(Matches):- ignore(dra_listing_0(Matches)),!.

dra_listing_0(MatchesIn):- 
 forall(property_pred(DECLF,DBF),
  (ignore(( DB=..[DBF,Matches],
  clause(DB,true),
  get_functor(Matches,PI0),
  get_functor(MatchesIn,PI1),!,
  PI0==PI1,
  functor(Matches,F,A),
  Decl=..[DECLF,F/A],
  format('~N:- ~q.~n',[Decl]))))).

set_meta(Goal, Prop):- is_pred_metainterp_0(Goal,Prop),!.
set_meta(Goal, Prop):- functor(Goal,F,A),functor(TGoal,F,A),
  dra_must(set_meta0(TGoal, Prop)),!,
  retract_all0(is_pred_metainterp_0(TGoal,_)),
  asserta_new(is_pred_metainterp_0(TGoal,Prop)).

set_meta0(TGoal,cuts_ok):-
    retract_all0(is_tabled(TGoal)),
    dra_non_meta(TGoal),
    retract_all0(is_never_tabled(TGoal)),
    asserta_new(cuts_ok(TGoal)).

set_meta0(TGoal,is_never_tabled):-
    retract_all0(is_tabled(TGoal)),
    retract_all0(cuts_ok(TGoal)),
    asserta_new(is_never_tabled(TGoal)).

set_meta0(TGoal,is_tabled):-    
    retract_all0(is_never_tabled(TGoal)),
    retract_all0(cuts_ok(TGoal)),
    asserta_new(is_tabled(TGoal)),
    dra_meta(TGoal).


:-dynamic(clause_meta/1).
might_be_clause_meta( Goal ):- compound(Goal), \+ \+ (arg(_,Goal,[_|_])),!.


%legal_directive(M:P):-atom(M),M:legal_directive(P).

%legal_directive(P):-compound(P),functor(P,F,1),property_pred(F).


%:-use_module(boot('$toplevel'),[]).
% '$dra_call_loop'/0 
(tprolog) :-   \+ lp_system( eclipse ),!,
    w_tl(op(0,fy,(traced)),   
	(((   current_prolog_flag(break_level, BreakLev)
	->  true
	;   BreakLev = -1
	),
	repeat,
	    (   '$module'(TypeIn, TypeIn),
	       '$toplevel':(((   (stream_property(user_input, tty(true)),write('tprolog '))
		->  user:prompt(TypeIn, BreakLev, Prompt),
		    prompt(Old, '|    ')
		;   Prompt = '', prompt(Old, '') ),
		trim_stacks,
	        '$toplevel':read_dra_call(Prompt, Query, Bindings),
		prompt(_, Old),
		call_expand_dra_call(Query, ExpandedQuery,
				  Bindings, ExpandedBindings)
	    ->  expand_goal(ExpandedQuery, Goal))),
	        (dra_execute(Goal, ExpandedBindings),fail) )))), !.



initialize_table:-dra_must(initialise).
print_table_statistics:-print_statistics.
%load(P):-dra_must(prog0(P)),!.


% :- ensure_loaded(library(dra_table_record)).
:- ensure_loaded((dra_table_assert)).
%:- user:ensure_loaded(library(dra/tabling3/compatibility_utilities_swi)).
%

%  Predicates specific to SWI Prolog.                                      %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (February, August 2009)               %
%                                                                          %

% :- ensure_loaded( higher_order ).
   %

   %  Some "higher order" predicates for Prolog.                              %
   %  This particular version was                                             %
   %  written by Feliks Kluzniak at UTD (February 2009).                      %
   %                                                                          %
   %  Last update: 11 June 2009.                                              %
   %                                                                          %

   % NOTE: Throughout the file "predicate name" will be used either for
   %        the name of a predicate, or for a predicate with an incomplete
   %        list of arguments (a partially applied predicate): see apply/2.


   %------------------------------------------------------------------------------
   % apply( +predicate name (possibly with arguments), +list of arguments ):
   % Extend the list of arguments of the first argument with the second argument
   % and invoke the result.
   % For example, if we have
   %     sum( A, B, C ) :-  C is A +B.
   % then
   %     dra_maplist2( sum(5 ), [ 1, 2, 3 ], Result )
   % will bind Result to [ 6, 7, 8 ].
  /*
   apply( PredNameArgs, Arguments ) :-
           PredNameArgs =.. [ PredName | Args ],
           append( Args, Arguments, AllArgs ),
           Literal =.. [ PredName | AllArgs ],
           call( Literal ).
 */

   %------------------------------------------------------------------------------
   % dra_maplist2( +PredicateName, +List, -MappedList )
   % The predicate should implement a unary function, i.e.,
   %   - it should take two arguments, the first of which is an input argument,
   %     and the second of which is an output argument;
   %   - it should always succeed, and the first result should be "what we want".
   % The predicate is applied to input arguments from the list, and the
   % corresponding outputs are returned in the second list.
   %
   % Example:
   %          square( M, N ) :-  N is M * M.
   %
   %          ?- dra_maplist2( square, [ 1, 2, 3 ], Ans ).
   %
   %          Ans = [ 1, 4, 9 ].

   dra_maplist2( _, [], [] ).

   dra_maplist2( PredName, [ H | T ], [ NH | NT ] ) :-
           apply( PredName, [ H, NH ] ),
           dra_maplist2( PredName, T, NT ).


   %------------------------------------------------------------------------------
   % filter( +predicate name, +list, - filtered list ):
   % The predicate should take one argument.
   % The output list will contain only those elements of the input list for which
   % the predicate succeeds.

   filter( _, [], [] ).

   filter( PredName, [ H | T ], NL ) :-
           (
               apply( PredName, [ H ] )
           ->
               NL = [ H | NT ]
           ;
               NL = NT
           ),
           filter( PredName, T, NT ).


   %------------------------------------------------------------------------------
   % filter2( +predicate name, +list, - yes list, - no list ):
   % The predicate should take one argument.
   % The first output list will contain only those elements of the input list for
   % which the predicate succeeds; the second output list will contain only those
   % elements of the input list for which the predicate fails.

   filter2( _, [], [], [] ) :-  !.

   filter2( PredName, [ H | T ], [ H | Yes ], No ) :-
           apply( PredName, [ H ] ),
           !,
           filter2( PredName, T, Yes, No ).

   filter2( PredName, [ H | T ], Yes, [ H | No ] ) :-
           % \+ apply( PredName, [ H ] ),
           filter2( PredName, T, Yes, No ).


   %------------------------------------------------------------------------------
   % dra_fold( +predicate name,+initial value, +list, - final value ):
   % The predicate should implement a binary function, i.e.,
   %   - it should take three arguments, the first two of which are input
   %     arguments, and the third of which is an output argument;
   %   - it should always succeed, and the first result should be "what we want".
   % If the list is empty, the initial value is returned; otherwise the predicate
   % is applied to the initial value and the first member of the list, and then
   % to the result and the third member, and so on.
   % For example, if "sum( A, B, C )" unifies "C" with the sum of "A" and "B",
   % then "dra_fold( sum, 0, [1,2,3], S )" unifies "S" with "6".

   dra_fold( _, Initial, [], Initial ).

   dra_fold( PredName, Initial, [ H | T ], Result ) :-
           apply( PredName, [ Initial, H, R ] ),
           dra_fold( PredName, R, T, Result ).

   %------------------------------------------------------------------------------

:- ensure_loaded( library( lists ) ). % An SWI library, for reverse/2.
%:- ensure_loaded( utilities ).
%

%  Some generally-useful utilities.                                        %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (January 2009).                       %
%                                                                          %
%  Last update: 28 August 2009.                                            %
%                                                                          %


%:- ensure_loaded( set_in_list ).
   %

   %  Simple, but useful operations on sets.                                  %
   %                                                                          %
   %  Written by Feliks Kluzniak at UTD (February 2009).                      %
   %                                                                          %
   %  Last update: 30 March 2009.                                             %
   %                                                                          %
   %  NOTE: Different Prolog variables are treated as different items: this   %
   %        is so by design!                                                  %
   %                                                                          %
   %        This implementation should only be used for smallish sets.        %
   %        The cost of insertion or membership check is proportional to      %
   %        the size of the set, the cost of set operations (union, equality  %
   %        etc.) is quadratic in the size of the sets.                       %
   %                                                                          %

   % Sets are represented as unordered lists.


   %------------------------------------------------------------------------------
   % empty_set( +- set ) :
   % Create an empty set, or check that the given set is empty.

   empty_set( set( [] ) ).


   %------------------------------------------------------------------------------
   % same_set_element( +item, +item ):
   % Succeeds iff the two items are identical
   % when treated as elements of a set.

   same_set_element( A, B ) :-
           (
               ( var( A ) ; A \= set( _ )
               ; var( B ) ; B \= set( _ )
               )
           ->
               A == B
           ;
               equal_sets( A, B )
           ).


   %------------------------------------------------------------------------------
   % is_in_set( +item, +set ):
   % Is the item a member of the set?

   is_in_set( Item, set( List ) ) :-
           once( is_in_set_( Item, List ) ).

   %
   is_in_set_( Item, [ H | _ ] ) :-
           same_set_element( Item, H ).

   is_in_set_( Item, [ _H | T ] ) :-
           % \+ same_element( Item, _H ),
           is_in_set_( Item, T ).


   %------------------------------------------------------------------------------
   % from_set( +set, - member, - new set ):
   % Remove an arbitrary member from the set;
   % fail if the set is empty.

   from_set( set( [ H | T ] ),  H, set( T ) ).


   %------------------------------------------------------------------------------
   % remove_from_set( +item, +set, - new set ):
   % Remove the given item from the set;
   % fail if the item is not a member.

   remove_from_set( M, set( L ), set( NL ) ) :-
           once( remove_from_set_( M, L, NL ) ).

   %
   remove_from_set_( M, [ H | T ], T ) :-
           same_set_element( M, H ).

   remove_from_set_( M, [ H | T ], [ H | NT ] ) :-
           % \+ same_set_element( M, H ).
           remove_from_set_( M, T, NT ).


   %------------------------------------------------------------------------------
   % add_to_set( +item, +set, - new set ):
   % Add the item to the set.
   %
   % WARNING: DO NOT INSTANTIATE THE ITEM WHILE IT IS IN SOME SET!

   add_to_set( Item, Set, NewSet ) :-
           once( add_to_set_( Item, Set, NewSet ) ).

   %
   add_to_set_( Item, Set, Set ) :-
           is_in_set( Item, Set ).

   add_to_set_( Item, set( L ), set( [ Item | L ] ) ).
           % \+ is_in_set( Item, set( L ) ).


   %------------------------------------------------------------------------------
   % sub_set( +set, +set ):
   % Succeed iff the first set is a subset of the second set.
   %
   % NOTE: In Eclipse the name "subset" is reserved for a built-in.

   sub_set( set( L1 ), Set2 ) :-
           once( subset_( L1, Set2 ) ).

   %
   subset_( [], _ ).

   subset_( [ H | T ], Set ) :-
           is_in_set( H, Set ),
           subset_( T, Set ).


   %------------------------------------------------------------------------------
   % equal_sets( +set, +set ):
   % Are the two sets equal?

   equal_sets( A, B ) :-
           sub_set( A, B ),
           sub_set( B, A ).


   %------------------------------------------------------------------------------
   % set_union( +set, +set, - the union ):
   % Compute the union of two sets.

   set_union( set( L1 ), S2, set( Union ) ) :-
           once( set_union_( L1, S2, Union ) ).

   %
   set_union_( [], set( L ), L ).

   set_union_( [ H | T ], S, NS ) :-
           is_in_set( H, S ),
           set_union_( T, S, NS ).

   set_union_( [ H | T ], S, [ H | NS ] ) :-
           % \+ is_in_set( H, S ),
           set_union_( T, S, NS ).


   %------------------------------------------------------------------------------
   % set_intersection( +set, +set, - the intersection ):
   % Compute the intersection of two sets.

   set_intersection( set( L1 ), S2, set( Intersection ) ) :-
           once( set_intersection_( L1, S2, Intersection ) ).

   %
   set_intersection_( [], _, [] ).

   set_intersection_( [ H | T ], S, NS ) :-
           \+ is_in_set( H, S ),
           set_intersection_( T, S, NS ).

   set_intersection_( [ H | T ], S, [ H | NS ] ) :-
           % is_in_set( H, S ),
           set_intersection_( T, S, NS ).


   %------------------------------------------------------------------------------
   % set_difference( +set, +set, - the difference ):
   % Subtract the second set from the first.

   set_difference( set( L1 ), S2, set( Difference ) ) :-
           once( set_difference_( L1, S2, Difference ) ).

   %
   set_difference_( [], _, [] ).

   set_difference_( [ H | T ], S, NS ) :-
           is_in_set( H, S ),
           set_difference_( T, S, NS ).

   set_difference_( [ H | T ], S, [ H | NS ] ) :-
           % \+ is_in_set( H, S ),
           set_difference_( T, S, NS ).


   %------------------------------------------------------------------------------
   % symmetric_set_difference( +set, +set,
   %                           - the symmetric difference
   %                         ):
   % Compute the symmetric difference of two sets.

   symmetric_set_difference( A, B, SymmetricDiff ) :-
           set_difference( A, B, DiffAB ),
           set_difference( B, A, DiffBA ),
           set_union( DiffAB, DiffBA, SymmetricDiff ).


   %------------------------------------------------------------------------------
   % set_from_list( +list, - set ):
   % Form a set with all the elements of the list.
   %
   % WARNING: DO NOT INSTANTIATE THE ITEM WHILE IT IS IN SOME SET!

   set_from_list( List, Set ) :-
           empty_set( Empty ),
           set_from_list_( List, Empty, Set ).

   %
   set_from_list_( []       , Set, Set  ).

   set_from_list_( [ H | T ], Set, NSet ) :-
           add_to_set( H, Set, Set2 ),
           set_from_list_( T, Set2, NSet ).

   %------------------------------------------------------------------------------

%:- ensure_loaded( higher_order ).
%:- ensure_loaded( vardict_utilities ).
   %

   %  Utilities that have to do with variable dictionaries.                   %
   %                                                                          %
   %  Written by Feliks Kluzniak at UTD (January 2009).                       %
   %                                                                          %
   %  Last update: 2 April 2009.                                              %
   %                                                                          %


%   :- ensure_loaded( higher_order ).



   %------------------------------------------------------------------------------
   % expand_variable_dictionary( +term,
   %                             +variable dictionary,
   %                             - variable dictionary expanded as needed
   %                           ):
   % The variable dictionary is for the term in the form it was read in, but the
   % term may have been expanded (in particular: it may have been a DCG rule).
   % Make sure that all the variables are present in the dictionary.

   expand_variable_dictionary( ExpandedTerm, VarDict, ExpandedVarDict ) :-
           ordered_term_variables( ExpandedTerm, Vars ),
           retain_new_variables( Vars, VarDict, RetainedVars ),
           mk_variable_dictionary( RetainedVars, NewVarDict ),
           append( NewVarDict, VarDict, ExpandedVarDict ).

   %
   retain_new_variables( [], _, [] ).

   retain_new_variables( [ V | Vs ], VarDict, Retained ) :-
           in_vardict( V, VarDict ),
           !,
           retain_new_variables( Vs, VarDict, Retained ).

   retain_new_variables( [ V | Vs ], VarDict, [ V | OtherRetained ] ) :-
           \+ in_vardict( V, VarDict ),
           !,
           retain_new_variables( Vs, VarDict, OtherRetained ).

   %
   in_vardict( V, [ [ _ | V2 ] | _ ] ) :-
           V == V2,
           !.

   in_vardict( V, [ _ | RestOfVarDict ] ) :-
           in_vardict( V, RestOfVarDict ).


   %------------------------------------------------------------------------------
   % extract_vars_from_dict( +variable dictionary, - list of variables ) :
   % Produce a list of the (current instantiations of) the variables that
   % occur in this dictionary.

   extract_vars_from_dict( VarDict, Vars ) :-
           dra_maplist2( drop_name, VarDict, Vars ).

   %
   drop_name( [ _Name | Var ], Var ).


   %------------------------------------------------------------------------------
   % bind_all_variables_to_names( +- term, +- variable dictionary  ):
   % Make sure that all the variables in this term are instantiated to their
   % names. This is not quite the same as bind_variables_to_names/1 (see below),
   % because variables that were originally represented by underscores do not find
   % their way into the variable dictionary.

   bind_all_variables_to_names( Term, VarDict ) :-
           bind_variables_to_names( VarDict ),
           ordered_term_variables( Term, AnonymousVars ),
           bind_anonymous( AnonymousVars ).

   %
   bind_anonymous( [] ).

   bind_anonymous( [ '_' | Vs ] ) :-
           bind_anonymous( Vs ).



   %------------------------------------------------------------------------------
   % bind_variables_to_names( +- variable dictionary  ):
   % The variable dictionary is of the format returned by readvar/3, i.e., a list
   % of pairs of the form "[ name | variable ]".  Go through the dictionary,
   % binding each variable to the associated name.
   % NOTE: 1. The assumption is that none of the variables has been instantiated!
   %       2. See also bind_all_variables_to_names/2 above!

   bind_variables_to_names( VarDict ) :-
           dra_maplist2( bind_var_to_name, VarDict, _ ).

   %
   bind_var_to_name( [ Name | Name ], _ ).



   %------------------------------------------------------------------------------
   % bind_free_variables_to_names( +- variable dictionary  ):
   % Like bind_variables_to_names/1, but done only for those items in the
   % dictionary that are still variables.

   bind_free_variables_to_names( [] ).

   bind_free_variables_to_names( [ [ Name | Var ] | RestOfVarDict ] ) :-
           ( Var = Name
           ; true
           ),
           !,
           bind_free_variables_to_names( RestOfVarDict ).



   %------------------------------------------------------------------------------
   % mk_variable_dictionary( +term, - a variable dictionary ):
   % Produce a variable dictionary for this term, as if it had been read by
   % readvar/3.
   % Since the original variable names are not available, we will use the names
   % _A, _B, _C, ... _Z, _V0, _V1 etc. (The underscore is added to avoid spurious
   % messages about singleton variables in case these names are used for output
   % that will subsequently be read by Prolog again.)
   %
   % (All this is done "by hand", since numbervars/3 are not very useful in
   % Eclipse: the writing predicates are not "aware" of '$VAR'(n).)

   mk_variable_dictionary( T, VarDict ) :-
           ordered_term_variables( T, Vars ),
           mk_variable_dictionary_( Vars, '_A', VarDict ).

   mk_variable_dictionary_( [], _, [] ).

   mk_variable_dictionary_( [ V | Vs ], Name, [ [ Name | V ] | VarDict ] ) :-
           mk_next_name( Name, NextName ),
           mk_variable_dictionary_( Vs, NextName, VarDict ).

   %
   % Once we run out of letters, we will use V0, V1 etc.
   %
   mk_next_name( '_Z', '_V0' ) :-
           !.

   mk_next_name( Name, Next ) :-
           name_chars( Name, [ U, C ] ),      % still in single letters?
           !,
           NC is C +1,         % good for ASCII, might not work for some encodings
           name_chars( Next, [ U, NC ] ).

   mk_next_name( Name, Next ) :-
           name_chars( Name, [ CodeOfUndercore, CodeOfV | DigitChars ] ),
           name_chars( Number, DigitChars ),
           NextNumber is Number +1,                               % good for ASCII
           name_chars( NextNumber, NewDigitChars ),
           name_chars( Next, [ CodeOfUndercore, CodeOfV | NewDigitChars ] ).

   %------------------------------------------------------------------------------

%:- ensure_loaded( clause_verification ).
%

%  Utilities for verifying well-formedness of clauses.                     %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (January 2009).                       %
%                                                                          %
%  Last update: 7 June 2010 (fixing errors found by Abramo Bagnara).       %
%                                                                          %

%:- ensure_loaded( boolean_operations ).
%

%  Utilities for performing operations on boolean expressions.             %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (March 2009).                         %
%                                                                          %
%  Last update: 2 March 2009.                                              %
%                                                                          %

%:- ensure_loaded( errors_and_warnings ).
%

%  Utilities for producing warning and error messages.                     %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (January 2009).                       %
%                                                                          %
%  Last update: 2 March 2009.                                              %
%                                                                          %


%------------------------------------------------------------------------------
% warning( +term ):
% warning( +list of terms ):
% Print this term or list of terms as a warning.
% There are no spaces between items on the list.
% Strings are printed without quotes.
% NOTE: If the term is "lines/1", then the argument should be a non-empty list.
%       Each of the top level items on the list is printed in a separate line.

warning( V ) :-
        var( V ),
        !,
        warning( [ 'Incorrect invocation of warning/1: \"',
                   warning( V ),
                   '\"'
                 ]
               ).

warning( [] ) :-
        !,
        begin_warning,
        end_warning.

warning( [ A | B ] ) :-
        !,
        std_warning_stream( WS ),
        begin_warning,
        write_list( WS, [ A | B ] ),
        write( WS, ' ' ),
        end_warning.

warning( lines( [ FirstLine | OtherLines ]  ) ) :-
        !,
        begin_warning,
        std_warning_stream( WS ),
        warning_line( WS, FirstLine ),
        warning_lines( OtherLines, WS ),
        end_warning.

warning( NotAList ) :-
        begin_warning,
        std_warning_stream( WS ),
        write( WS, NotAList ),
        write( WS, ' ' ),
        end_warning.

%
warning_lines( [], _ ).

warning_lines( [ Line | Lines ], WS ) :-
        write( WS, '---          ' ),
        warning_line( WS, Line ),
        warning_lines( Lines, WS ).

%
warning_line( WS, List ) :-
        ( List = [] ; List = [ _ | _ ] ),
        !,
        write_list( WS, List ),
        nl( WS ).

warning_line( WS, Term ) :-
        writeln( WS, Term ).


%------------------------------------------------------------------------------
% begin_warning:
% Begin a warning printout.

begin_warning :-
        std_warning_stream( WS ),
        write( WS, '--- WARNING: ' ).


%------------------------------------------------------------------------------
% end_warning:
% End a warning printout.

end_warning :-
        std_warning_stream( WS ),
        writeln( WS, '---' ).



%------------------------------------------------------------------------------
% error( +term ):
% error( +list of terms ):
% Print this term or list of terms as an error, then abort the computation.
% There are no spaces between items on the list.
% Strings are printed without quotes.
% NOTE: If the term is "lines/1", then the argument should be a non-empty list.
%       Each of the top level items on the list is printed in a separate line.

error( V ) :-
        var( V ),
        !,
        error( [ 'Incorrect invocation of error/1: \"', error( V ), '\"' ] ).

error( [] ) :-
        !,
        begin_error,
        end_error.

error( [ A | B ] ) :-
        !,
        begin_error,
        std_error_stream( ES ),
        write_list( ES, [ A | B ] ),
        write( ES, ' ' ),
        end_error.

error( lines( [ FirstLine | OtherLines ]  ) ) :-
        !,
        begin_error,
        std_error_stream( ES ),
        error_line( ES, FirstLine ),
        error_lines( OtherLines, ES ),
        end_error.

error( NotAList ) :-
        begin_error,
        std_error_stream( ES ),
        write( ES, NotAList ),
        write( ES, ' ' ),
        end_error.

%
error_lines( [], _ ).

error_lines( [ Line | Lines ], ES ) :-
        write( ES, '***        ' ),
        error_line( ES, Line ),
        error_lines( Lines, ES ).

%
error_line( ES, List ) :-
        ( List = [] ; List = [ _ | _ ] ),
        !,
        write_list( ES, List ),
        nl( ES ).

error_line( ES, Term ) :-
        writeln( ES, Term ).



%------------------------------------------------------------------------------
% begin_error:
% Begin an error printout.

begin_error :-
        std_error_stream( ES ),
        write( ES, '*** ERROR: ' ).


%------------------------------------------------------------------------------
% end_error:
% End an error printout.

end_error :-
        std_error_stream( ES ),
        writeln( ES, '***' ),
        abort.

%------------------------------------------------------------------------------


:- op( 500, yfx, and ).
:- op( 500, yfx, or  ).   % Following Dijkstra...
:- op( 490, fy , neg ).


%------------------------------------------------------------------------------
% bool_eval( +boolean expression, - true or false ):
% Evaluate the expression.

bool_eval( V, _ ) :-
        var( V ),
        !,
        error( 'Variable boolean' ).

bool_eval( Expression, Value ) :-
        once( beval( Expression, Value ) ).

%
beval( false, false ).

beval( true, true ).

beval( neg false, true ).

beval( neg true, false ).

beval( neg Exp, Value ) :-
        beval( Exp, V ),
        beval( neg V, Value ).

beval( false and false, false ).

beval( false and true, false ).

beval( true and false, false ).

beval( true and true, true ).

beval( A and B, Value ) :-
        beval( A, VA ),
        beval( B, VB ),
        beval( VA and VB, Value ).

beval( false or false, false ).

beval( false or true, true ).

beval( true or false, true ).

beval( true or true, true ).

beval( A or B, Value ) :-
        beval( A, VA ),
        beval( B, VB ),
        beval( VA or VB, Value ).


%------------------------------------------------------------------------------
% Predicates for the operators.

bool_and( EA, EB, V ) :-
        bool_eval( EA and EB, V ).

bool_or( EA, EB, V ) :-
        bool_eval( EA or EB, V ).

bool_neg( E, V ) :-
        bool_eval( neg E, V ).

%------------------------------------------------------------------------------

%:- ensure_loaded( vardict_utilities ).
%:- ensure_loaded( errors_and_warnings ).
%:- ensure_loaded( set_in_list ).
% NOTE: requires proper compatibility_utilities_....


%------------------------------------------------------------------------------
% verify_program_with_vars( +list of pairs ):
% Like verify_program/1 below, but instead of a list of terms we have a list
% of pairs (pair( term, variable dictionary for the term)), i.e., we can use
% information about original variable names.

% :- mode verify_program_with_vars( +).

verify_program_with_vars( Pairs ) :-
        member( Pair, Pairs ),
        Pair = pair( Term, VarDict ),
        verify_program_item( Term, VarDict ),
        fail.

verify_program_with_vars( _ ).



%------------------------------------------------------------------------------
% verify_program( +list of terms ):
% Given a list of terms that should all be clauses, directives, or queries,
% raise an error if any of the terms is obviously incorrect.
% See also verify_program_with_vars/1 above.

% :- mode verify_program( +).

verify_program( Terms ) :-
        member( Term, Terms ),
        mk_variable_dictionary( Term, VarDict ),
        verify_program_item( Term, VarDict ),
        fail.

verify_program( _ ).


%------------------------------------------------------------------------------
% verify_program_item( +list of terms, +variable dictionary ):
% Given a term that should  be a clause, a directive, or a query,
% raise an error if it is obviously incorrect.

verify_program_item( Var, VarDict ) :-
        var( Var ),
        !,
        bind_variables_to_names( VarDict ),
        error( [ 'A variable clause: \"', Var, '\"' ] ).

verify_program_item( (:- Var), VarDict ) :-
        var( Var ),
        !,
        bind_variables_to_names( VarDict ),
        error( [ 'A variable directive: \"', (:- Var), '\"' ] ).

verify_program_item( (?- Var), VarDict ) :-
        var( Var ),
        !,
        bind_variables_to_names( VarDict ),
        error( [ 'A variable dra_call: \"', (?- Var), '\"' ] ).

verify_program_item( (?- Query), VarDict ) :-       % avoid check for singletons
        !,
        empty_set( Empty ),
        check_for_variable_calls( Query, Empty, ctxt( VarDict, (?- Query) ) ).


verify_program_item( Clause, VarDict ) :-
        \+ is_a_good_clause( Clause, VarDict ),
        !,
        bind_variables_to_names( VarDict ),
        error( [ 'Incorrect clause: \"', Clause, '.\"' ] ).

verify_program_item( _, _ ).



%------------------------------------------------------------------------------
% is_a_good_clause( +term ):
% Is this term a reasonable clause?  Even if it is,  warnings may be produced.

is_a_good_clause( T ) :-
        mk_variable_dictionary( T, VarDict ),
        is_a_good_clause( T, VarDict ).


%------------------------------------------------------------------------------
% is_a_good_clause( +term, +variable dictionary ):
% Is this term a reasonable clause?  Even if it is,  warnings may be produced.

is_a_good_clause( T, VarDict ) :-
        nonvar( T ),
        get_clause_head( T, H ),
        is_a_good_clause_head( H ),
        has_a_good_clause_body( T, VarDict ).


%------------------------------------------------------------------------------
% get_clause_head( +term, - head ):
% Treat this non-variable term as a clause, get its head.

% :- mode get_clause_head( +, - ).

get_clause_head( (H :- _), H ) :-  !.
get_clause_head( H       , H ).


%------------------------------------------------------------------------------
% is_a_good_clause_head( +term ):
% Is this term a good head for a clause?

is_a_good_clause_head( Var ) :-
        var( Var ),
        !,
        fail.

is_a_good_clause_head( Hd ) :-
        atom( Hd ),
        !.

is_a_good_clause_head( Hd ) :-
        Hd \= [ _ | _ ].


%------------------------------------------------------------------------------
% has_a_good_clause_body( +term, +variable dictionary ):
% Treat this non-variable term as a clause, check it for elementary sanity.
% Assume that the head is not a variable.
%
% NOTE: The check is mainly to ensure that there are no variable literals.
%       Invocations of call/1 are allowed, but an error will be raised if
%       the argument is a variable that had no earlier occurrences.
%       As an added bonus, we produce warnings about singleton variables.
%
% Throughout most of the code we carry a context argument (Ctxt): this is
% a structure that holds the entire clause and the variable dictionary, and
% we use it to produce better diagnostics.

% :- mode has_a_good_clause_body( ?, +).

has_a_good_clause_body( Clause, VarDict ) :-
        has_a_good_clause_body_( Clause, ctxt( VarDict, Clause ) ).

has_a_good_clause_body_( Clause, Ctxt ) :-
        Clause = (Head :- Body),
        !,
        ordered_term_variables( Head, HeadVars ),
        % HeadVars has no duplicates, so we need not call set_from_list/2
        check_for_variable_calls( Body, set( HeadVars ), Ctxt ),
        check_for_singleton_variables( Clause, Ctxt ).

has_a_good_clause_body_( Fact, Ctxt ) :-
        check_for_singleton_variables( Fact, Ctxt ).



% check_for_variable_calls( +(part of a) clause body,
%                           +the set of variables seen so far,
%                           +the context (just for better diagnostics)
%                         )

check_for_variable_calls( V, _, Ctxt ) :-
        var( V ),
        !,
        clause_error( [ 'A variable literal (\"', V, '\")' ], Ctxt ).

check_for_variable_calls( (A ; B), Vars, Ctxt ) :-
        !,
        check_for_variable_calls( A, Vars, Ctxt ),
        check_for_variable_calls( B, Vars, Ctxt ).

check_for_variable_calls( (A -> B), Vars, Ctxt ) :-
        !,
        check_for_variable_calls( (A , B), Vars, Ctxt ).

check_for_variable_calls( (A , B), Vars, Ctxt ) :-
        !,
        check_for_variable_calls( A, Vars, Ctxt ),
        ordered_term_variables( A, AVars ),
        set_from_list( AVars, AVarSet ),
        set_union( AVarSet, Vars, NVars ),
        check_for_variable_calls( B, NVars, Ctxt ).

check_for_variable_calls( \+ A, Vars, Ctxt ) :-
        !,
        check_for_variable_calls( A, Vars, Ctxt ).

check_for_variable_calls( once( A ), Vars, Ctxt ) :-
        !,
        check_for_variable_calls( A, Vars, Ctxt ).

check_for_variable_calls( call( T ), Vars, Ctxt ) :-
        !,
        (
            nonvar( T )
        ->
            check_for_variable_calls( T, Vars, Ctxt )
        ;
            % var( T ),
            (
                is_in_set( T, Vars )
            ->
                true
            ;
                clause_error( [ 'The variable argument of \"', call( T ),
                                '\" does not have previous occurrences'
                              ],
                              Ctxt
                            )
            )
        ).

check_for_variable_calls( T, _, Ctxt ) :-
        \+ callable( T ),
        !,
        clause_error( [ 'Incorrect literal (\"', T, '\")' ], Ctxt ).

check_for_variable_calls( _, _, _ ).



% check_for_singleton_variables( +clause, +context ):
% Produce a warning if there is a path in the clause on which a variable occurs
% only once, that occurrence of the variable is not a unique occurrence of the
% variable on other paths, and the name of the variable does not begin with an
% underscore.
% Always succeed.
% Assume the clause has been verified by is_a_good_clause/1.

check_for_singleton_variables( Clause, Ctxt ) :-
        % expand a DCG rule
        (
            Clause = (_ --> _)
        ->
            expand_term( Clause, Expanded )
        ;
            Expanded = Clause
        ),
        % general case
        cs( Expanded, Ctxt, _, _, _, Singletons ),
        (
            empty_set( Singletons )
        ->
            true
        ;
            Singletons = set( Vars ),
            clause_warning( [ 'Singleton variables ', Vars ], Ctxt )
        ).

%
% cs( +(sub)term,
%     +context,
%     - boolean indicating whether the construct must fail,
%     - set of variables seen from front,
%     - set of variables seen from behind,
%     - set of singletons,
%   ):
% Produce the sets of variables occurring in this term (those that can be "seen"
% from the front and those that can be "seen" from behind: cf. negation), as
% well as the set of  variables that are singletons in this term.
% Produce warnings about obviously dead code
% Note that the set of singletons is a subset of the set of seen.
% Note also that a variable whose name begins with an underscore "does not
% count".

cs( V, Ctxt, false, SeenFromFront, SeenFromBehind, Single ) :-
        var( V ),
        !,
        cs_args( [ V ], Ctxt, Seen, Single ),
        empty_set( EmptyFront ),
        empty_set( EmptyBehind ),
        set_union( EmptyFront,  Seen, SeenFromFront ),
        set_union( EmptyBehind, Seen, SeenFromBehind ).

cs( fail, _, true, SeenFromFront, SeenFromBehind, Single ) :-
        !,
        empty_set( SeenFromFront  ),
        empty_set( SeenFromBehind ),
        empty_set( Single         ).

cs( A, _, false, SeenFromFront, SeenFromBehind, Single ) :-
        atomic( A ),
        !,
        empty_set( SeenFromFront  ),
        empty_set( SeenFromBehind ),
        empty_set( Single         ).

cs( (Disj , C), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ) :-
        nonvar( Disj ),
        Disj = (A ; B),
        !,
        cs_join( ((A ; B), C), Ctxt, MustFail,
                 SeenFromFront, SeenFromBehind, Single
               ).

cs( (A ; B), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ) :-
        !,
        cs( A, Ctxt, MustFailA, SeenFromFrontA, SeenFromBehindA, SingleA ),
        cs( B, Ctxt, MustFailB, SeenFromFrontB, SeenFromBehindB, SingleB ),
        set_union( SeenFromFrontA , SeenFromFrontB , SeenFromFront  ),
        set_union( SeenFromBehindA, SeenFromBehindB, SeenFromBehind ),
        set_union( SingleA        , SingleB        , Single         ),
        bool_eval( MustFailA and MustFailB, MustFail ).

cs( (A , B), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ) :-
        !,
        cs( A, Ctxt, MustFailA, SeenFromFrontA, SeenFromBehindA, SingleA ),
        cs( B, Ctxt, MustFailB, SeenFromFrontB, SeenFromBehindB, SingleB ),
        (
            MustFailA = true
        ->
            MustFail      = true,
            SeenFromFront = SeenFromFrontA,
            Single        = SingleA,
            empty_set( SeenFromBehind ),
            clause_warning( [ 'Obviously dead code: \"', B, '\"' ], Ctxt )
        ;
            set_union( SeenFromFrontA, SeenFromFrontB, SeenFromFront ),
            (
                MustFailB = true
            ->
                MustFail = true,
                empty_set( SeenFromBehind )
            ;
                set_union( SeenFromBehindA, SeenFromBehindB, SeenFromBehind ),
                bool_eval( MustFailA or MustFailB, MustFail )
            ),
            set_intersection( SeenFromBehindA, SeenFromFrontB, SeepingAB ),
            set_difference( SingleA, SeepingAB, SA ),
            set_difference( SingleB, SeepingAB, SB ),
            set_union( SA, SB, Single )
        ).

cs( (A :- B), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ) :-
        !,
        cs(  (A , B), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ).

cs( (A -> B), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ) :-
        !,
        cs( (A , B), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ).

cs( [ A | B ], Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ) :-
        !,
        cs( A, Ctxt, MustFailA, SeenFromFrontA, SeenFromBehindA, SingleA ),
        cs( B, Ctxt, MustFailB, SeenFromFrontB, SeenFromBehindB, SingleB ),
        set_union( SeenFromFrontA, SeenFromFrontB, SeenFromFront ),
        set_union( SeenFromBehindA, SeenFromBehindB, SeenFromBehind ),
        bool_eval( MustFailA or MustFailB, MustFail ),
        set_intersection( SeenFromBehindA, SeenFromFrontB, SeepingAB ),
        set_difference( SingleA, SeepingAB, SA ),
        set_difference( SingleB, SeepingAB, SB ),
        set_union( SA, SB, Single ).

cs( \+ C, Ctxt, false, SeenFromFront, Empty, Single ) :-
        empty_set( Empty ),
        cs( C, Ctxt, _, SeenFromFront, _, Single ).

cs( C, Ctxt, false, SeenFromFront, SeenFromBehind, Single ) :-
        compound( C ),
        !,
        C =.. [ _ | Args ],
        cs_args( Args, Ctxt, Seen, Single ),
        empty_set( EmptyFront ),
        empty_set( EmptyBehind ),
        set_union( EmptyFront,  Seen, SeenFromFront ),
        set_union( EmptyBehind, Seen, SeenFromBehind ).


cs( T, Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ) :-
        error( [ 'INTERNAL ERROR: (clause_verification)',
                 cs( T, Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single )
               ]
             ).


% The arguments of a single call: produce variables that are seen, and those
% that occur only once in this call.
% This has been factored out because negation, disjunction etc. in arguments
% should not have the effects that they have on the top level. (Thanks are due
% to Abramo Bagnara for detecting this error.)

cs_args( [], _Ctxt, Empty, Empty ) :-
        empty_set( Empty ).

cs_args( [ Arg | Args ], Ctxt, Seen, Single ) :-
        cs_arg( Arg, Ctxt, Seen1, Single1 ),
        cs_args( Args, Ctxt, Seen2, Single2 ),
        set_difference( Single2, Seen1, Single2OK ),
        set_difference( Single1, Seen2, Single1OK ),
        set_union( Single1OK, Single2OK, Single ),
        set_union( Seen1, Seen2, Seen ).


%
cs_arg( V, Ctxt, Seen, Single ) :-
        var( V ),
        Ctxt = ctxt( VarDict, _ ),
        member( [ Name | Var ], VarDict ),
        Var == V,
        !,
        (
            name_chars( '_',  [ Underscore ] ),
            name_chars( Name, [ Underscore | _ ] )
        ->
            % ignore a variable whose name begins with _
            empty_set( Seen ),
            empty_set( Single )
        ;
            empty_set( Empty ),
            add_to_set( V, Empty, Seen ),
            add_to_set( V, Empty, Single )
        ).

cs_arg( V, _, Seen, Single ) :-
        var( V ),                                       % '_' is not in VarDict!
        !,
        empty_set( Seen ),
        empty_set( Single ).

cs_arg( Other, Ctxt, Seen, Single ) :-
        nonvar( Other ),
        (
            atomic( Other )
        ->
            empty_set( Seen ),
            empty_set( Single )
        ;
            Other =.. [ _ | Args ],
            cs_args( Args, Ctxt, Seen, Single )
        ).



% Several paths seem to converge: special treatment is needed if any of them
% is is_known to fail.

cs_join( ((A ; B) , C), Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single
       ) :-
        cs( C, Ctxt, MustFailC, SeenFromFrontC, SeenFromBehindC, SingleC ),
        unfold_disjunction( (A ; B), Disjunctions ),
        dra_maplist2( cs2( Ctxt ), Disjunctions, Results ),
        dra_maplist2( cs_adjust( SeenFromFrontC ), Results, Adjusted ),
        dra_maplist2( result1, Adjusted, ListMustFail   ),
        dra_maplist2( result2, Adjusted, ListFromFront  ),
        dra_maplist2( result3, Adjusted, ListFromBehind ),
        dra_maplist2( result4, Adjusted, ListSingle     ),
        dra_fold( bool_and, true, ListMustFail, AllMustFailExp ),
        bool_eval( AllMustFailExp, MustFailAlt ),
        empty_set( Empty ),
        dra_fold( set_union, Empty, ListFromFront , SeenFromFrontAlt  ),
        dra_fold( set_union, Empty, ListFromBehind, SeenFromBehindAlt ),
        dra_fold( set_union, Empty, ListSingle    , SingleAlt         ),
        (
            MustFailAlt = true
        ->
            MustFail      = true,
            SeenFromFront = SeenFromFrontAlt,
            Single        = SingleAlt,
            empty_set( SeenFromBehind ),
            clause_warning( [ 'Obviously dead code: \"', C, '\"' ], Ctxt )
        ;
            set_union( SeenFromFrontAlt, SeenFromFrontC, SeenFromFront ),
            (
                MustFailC = true
            ->
                MustFail = true,
                empty_set( SeenFromBehind )
            ;
                set_union( SeenFromBehindAlt, SeenFromBehindC, SeenFromBehind ),
                bool_eval( MustFailAlt or MustFailC, MustFail )
            ),
            set_intersection( SeenFromBehindAlt, SeenFromFrontC, SeepingBC ),
            set_difference( SingleC, SeepingBC, SC ),
            set_union( SingleAlt, SC, Single )
        ).

%
unfold_disjunction( (A ; B), [ A | Disjuncts ] ) :-
        !,
        unfold_disjunction( B, Disjuncts ).

unfold_disjunction( A, [ A ] ).

%
cs2( Ctxt, Construct, result( MustFail, SeenFromFront, SeenFromBehind, Single )
   ) :-
        cs( Construct, Ctxt, MustFail, SeenFromFront, SeenFromBehind, Single ).

%
cs_adjust( SeenFromFollower, Result, NewResult ) :-
        Result = result( MustFail, SeenFromFront, SeenFromBehind, Single ),
        (
            MustFail = true
        ->
            NewResult = Result
        ;
            set_intersection( SeenFromBehind, SeenFromFollower, Seeping ),
            set_difference( Single, Seeping, NewSingle ),
            NewResult =
                      result( false, SeenFromFront, SeenFromBehind, NewSingle )
        ).

%
result1( result( A, _, _ , _ ), A ).
result2( result( _, B, _ , _ ), B ).
result3( result( _, _, C , _ ), C ).
result4( result( _, _, _ , D ), D ).



%------------------------------------------------------------------------------
% clause_error( +list to be displayed (the error message), +the context ):
% Show the error and the entire clause, with proper variable names.
% For the time being V and 'V' will both appear as V on output.

clause_error( MsgList, ctxt( VarDict, Clause ) ) :-
        bind_all_variables_to_names( Clause, VarDict ),     % may affect MSgList
        append( MsgList, [ ':' ], FullMsgList ),
        error( lines( [ FullMsgList, [ Clause, '.' ] ] ) ).


%------------------------------------------------------------------------------
% clause_warning( +list to be displayed (the warning message), +the context ):
% Show the warning and the entire clause, with proper variable names.
% For the time being V and 'V' will both appear as V on output.

clause_warning( MsgList, ctxt( VarDict, Clause ) ) :-
        bind_all_variables_to_names( Clause, VarDict ),     % may affect MSgList
        append( MsgList, [ ' in' ], FullMsgList ),
        warning( lines( [ FullMsgList, [ Clause, '.' ] ] ) ),
        fail.

clause_warning( _, _ ).


%------------------------------------------------------------------------------

%:- ensure_loaded( io_utilities ).
%


%  Utilities that have to do with input and output.                        %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (January 2009).                       %
%                                                                          %
%  Last update: 12 June 2009.                                              %
%                                                                          %


% NOTE: requires proper compatibility_utilities_....


%------------------------------------------------------------------------------
% ensure_filename_is_an_atom( +filename ):
% Verify that the filename is an atom.  If not, produce a fatal error.

ensure_filename_is_an_atom( FileName ) :-
        atom( FileName ),
        !.

ensure_filename_is_an_atom( FileName ) :-
        % \+ atom( FileName ),
        error( [ 'Illegal file name \"', FileName, '\" (not an atom).' ]
             ).



%------------------------------------------------------------------------------
% ensure_extension( +file name chars,
%                   +extension chars,
%                   - the root file name,
%                   - file name, possibly extended
%                 ):
% If the file name has no extension, add the provided extension (which dra_must
% include the period; it can also be empty) and return the file name as the
% root name; if the file name has an extension, don't change it, but extract
% the root name.

% :- mode ensure_extension( +, +, -, - ).

ensure_extension( FileNameChars, _, RootFileNameChars, FileNameChars ) :-
        name_chars( '.', [ Dot ] ),
        append( RootFileNameChars, [ Dot | _ ], FileNameChars ), % has extension
        !.

ensure_extension( FileNameChars, ExtChars,
                  FileNameChars, FullFileNameChars
                ) :-
        append( FileNameChars, ExtChars, FullFileNameChars ).



%------------------------------------------------------------------------------
% read_terms_with_vars( +input stream,
%                       - list of terms with variable dictionaries
%                     ):
% Like read_terms/2 (see below), but each item on the resulting list is of
% the form "pair( term, variable dictionary )", where the variable dictionary
% is of the format returned by readvar.

% :- mode read_terms_with_vars( +, - ).

read_terms_with_vars( InputStream, Terms ) :-
        readvar( InputStream, Term, VarDict ),
        read_terms_with_vars_( InputStream, pair( Term, VarDict ), Terms ).

%
read_terms_with_vars_( _, pair( end_of_file, _ ), [] ) :-
        !.

read_terms_with_vars_( InputStream, Pair, [ Pair | Pairs ] ) :-
        % Pair \= pair( end_of_file, _ ),
        process_if_op_directive( Pair ),
        readvar( InputStream, NextTerm, NextVarDict ),
        read_terms_with_vars_( InputStream,
                               pair( NextTerm, NextVarDict ), Pairs
                             ).

%
process_if_op_directive( pair( (:- op( P, F, Ops)), _ ) ) :-
        !,
        op( P, F, Ops ).

process_if_op_directive( _ ).


%------------------------------------------------------------------------------
% read_terms( +input stream, - list of terms ):
% Given an open input stream, produce all the terms that can be read from it.
%
% NOTE: Operator declarations are interpreted on the fly, but not deleted from
%       output.
%       See also read_terms_with_vars/2 above.

% :- mode read_terms( +, - ).

read_terms( InputStream, Terms ) :-
        read( InputStream, Term ),
        read_terms_( InputStream, Term, Terms ).

%
read_terms_( _, end_of_file, [] ) :-
        !.

read_terms_( InputStream, Term, [ Term | Terms ] ) :-
        % term \= end_of_file,
        process_if_op_directive( Term ),
        read( InputStream, NextTerm ),
        read_terms_( InputStream, NextTerm, Terms ).



%------------------------------------------------------------------------------
% write_terms( +list of terms, +output stream ):
% Given an open output stream, write onto it all the terms from the list,
% one per line but without any other pretty-printing.

% :- mode write_terms( +, +).

write_terms( Terms, OutputStream ) :-
        member( Term, Terms ),
        write( OutputStream, Term ),
        writeln( OutputStream, '.' ),
        fail.

write_terms( _, _ ).


%------------------------------------------------------------------------------
% write_clauses( +list of clauses, +output stream ):
% Given an open output stream, write onto it all the clauses from the list.

% :- mode write_clauses( +, +).

write_clauses( Clauses, OutputStream ) :-
        member( Clause, Clauses ),
        writeclause( OutputStream, Clause ),
        fail.

write_clauses( _, _ ).



%------------------------------------------------------------------------------
% write_list( +stream, +list ):
% Output the items on this list to this stream.
% There are no spaces between items on the list.
% Strings are printed without quotes.

write_list( S, V ) :-
        var( V ),
        !,
        warning( [ 'Incorrect invocation of write_list/1: \"',
                   write_list( S, V ),
                   '\"'
                 ]
               ).

write_list( _S, [] ) :-
        !.

write_list( S, [ H | T ] ) :-
        !,
        write( S, H ),
        write_list( S, T ).

write_list( S, NotAList ) :-
        !,
        warning( [ 'Incorrect invocation of write_list/1: \"',
                   write_list( S, NotAList ),
                   '\"'
                 ]
               ).



%------------------------------------------------------------------------------
% getline( +input stream, - list of character atoms ) :
%    Reads characters from this input stream upto (and including) the nearest
%    newline.  The newline is not included in the list of characters that is
%    returned.

% :- mode getline( +, - ).

getline( InputStream, Line ) :-
        getchar( InputStream, C ),
        getline_( InputStream, C, Line ).

%
% :- mode getline_( +, +, - ).

getline_( _InputStream, '\n', [] ) :-  !.

getline_( InputStream, C   , [ C | Cs ] ) :-
        getchar( InputStream, NC ),
        getline_( InputStream, NC, Cs ).


%------------------------------------------------------------------------------
% putline( +output stream, +list of character strings ) :
%    Writes the characters to this stream and follows them with a newline.

% :- mode putline( +, +).

putline( OutputStream, Cs ) :-
        putchars( OutputStream, Cs ),
        nl( OutputStream ).


%------------------------------------------------------------------------------
% putchars( +output stream, +list of character strings ) :
%    Writes the characters to the current output stream.

% :- mode putchars( +, +).

putchars( _OutputStream, [] ).

putchars( OutputStream, [ C | Cs ] ) :-
        put_char( OutputStream, C ),
        putchars( OutputStream, Cs ).

%------------------------------------------------------------------------------

% :- ensure_loaded( errors_and_warnings ).



%------------------------------------------------------------------------------
% dra_check( +goal ) :
%    Succeeds iff goal succeeds, but without instantiating any variables
%    (side-effects may appear, though).

% :- mode dra_check( +).

dra_check( Goal ) :-  \+ \+ call( Goal ) .



%------------------------------------------------------------------------------
% mk_ground( +- term ) :
%    Instantiates all the unbound variables in the term as terms of
%    the form ' V'( 0 ), ' V'( 0 ). ' V'( 0 ) etc.
%    (Note: This is mainly for "safety". If the strange names of the functors
%           are not needed, consider using:
%              mk_ground( T ) :- numbervars( T, 0, _ ).
%           on Prolog systems that support numbervars/3.
%    )
%
% NOTE: The following implementation is no good for cyclic terms.

% :- mode mk_ground( ? ).

mk_ground( T ) :-  mk_ground_aux( T, 0, _ ).

%
% :- mode mk_ground_aux( ?, +, - ).

mk_ground_aux( V, N, N1 ) :-
        var( V ),
        !,
        V = ' V'( N ),
        N1 is N +1.

mk_ground_aux( T, N, N ) :-
        atomic( T ),
        !.

mk_ground_aux( T, N, N1 ) :-
        % \+ var( T ), \+ atomic( T ),
        T =.. [ _Functor | Args ],
        mk_ground_auxs( Args, N, N1 ).

%
% :- mode mk_ground_auxs( +, +, - ).

mk_ground_auxs( []        , N, N  ).
mk_ground_auxs( [ T | Ts ], N, N2 ) :-
        mk_ground_aux( T, N, N1 ),
        mk_ground_auxs( Ts, N1, N2 ).


%------------------------------------------------------------------------------
% is_ground_var( +term ):
% Is this term a variable that was ground by mk_ground/1?

is_ground_var( Var ) :-
        var( Var ),
        !,
        fail.

is_ground_var( ' V'( N ) ) :-
        integer( N ).


%------------------------------------------------------------------------------
% ground_term_variables( +term, - set of variables ):
% Given a term grounded by mk_ground/1, produce the set of the grounded form of
% variables occurring in the term.
% (Note that the term may be a subset of a larger term grounded by mk_ground/1,
%  so the variable numbers need not be contiguous.)

% :- mode ground_term_variables( +, - ).

ground_term_variables( T, S ) :-
        empty_set( S0 ),
        gtv_( T, S0, S ),
        !.

ground_term_variables( T, _ ) :-
        error( [ 'Bad call to ground_term_variables (term not ground): ', T ] ).

%
% :- mode gtv_( +, +, - ).

gtv_( V, _, _ ) :-
        var( V ),
        !,
        fail.

gtv_( T, S, NS ) :-
        is_ground_var( T ),
        !,
        add_to_set( T, S, NS ).

gtv_( T, S, S ) :-
        atom( T ),
        !.

gtv_( [ H | T ], S, NS ) :-
        !,
        gtv_( H,  S, S2 ),
        gtv_( T, S2, NS ).

gtv_( T, S, NS ) :-
        T =.. [ _ | Args ],
        gtv_( Args, S, NS ).


%------------------------------------------------------------------------------
% is_an_instance( +term, +term ) :
%    Succeeds iff arg1 is an instance of arg2, but does not instantiate any
%    variables.
% NOTE: In Eclipse this loops on cyclic terms.

is_an_instance( T1, T2 ) :-
        dra_check( T1 = T2 ),                     % quickly weed out obvious misfits
        copy_term( T2, CT2 ), 
        subsumes_chk( CT2, T1 ).



%------------------------------------------------------------------------------
% mk_pattern( +an atom representing the name of a predicate,
%             +an integer representing the arity of the predicate,
%             - the most general pattern that matches all invocations of the
%               predicate
%           )
% Given p/k, produce p( _, _, ... _ )  (of arity k)

% :- mode mk_pattern( +, +, - ).

% mk_pattern( P, K, Pattern ) :-
%        length( Args, K ),                           % Args = K fresh variables
%        Pattern =.. [ P | Args ].

mk_pattern( P, K, Pattern ) :-
        functor( Pattern, P, K ).



%------------------------------------------------------------------------------
% most_general_instance( +a term,
%                        - a most general instance with the same main functor
%                      ):
% E.g., p( a, q( X, Y ) )  is transformed to  p( _, _ ).

% :- mode most_general_instance( +, - ).

most_general_instance( Term, Pattern ) :-
        functor( Term, Name, Arity ),
        functor( Pattern, Name, Arity ).



%------------------------------------------------------------------------------
% predspecs_to_patterns( +a conjunction of predicate specifications,
%                        - list of most general instances of these predicates
%                      ):
% Given one or several predicate specifications (in the form "p/k" or
% "p/k, q/l, ...") check whether they are well-formed: if not, raise a fatal
% error; otherwise return a list of the most general instances that correspond
% to the predicate specifications.

:- module_transparent(predspecs_to_patterns/2).

predspecs_to_patterns( Var, _ ) :-
        var( Var ),
        !, trace, 
        error( [ 'A variable instead of predicate specifications: \"',
                 Var,
                 '\"'
               ]
             ).

predspecs_to_patterns( [PredSpec | PredSpecs], [ Pattern | Patterns ] ) :-
        !,
        predspec_to_pattern( PredSpec, Pattern ),
        predspecs_to_patterns( PredSpecs, Patterns ).
predspecs_to_patterns( (PredSpec , PredSpecs), [ Pattern | Patterns ] ) :-
        !,
        predspec_to_pattern( PredSpec, Pattern ),
        predspecs_to_patterns( PredSpecs, Patterns ).

predspecs_to_patterns( PredSpec, [ Pattern ] ) :-
        predspec_to_pattern( PredSpec, Pattern ).


%------------------------------------------------------------------------------
% predspec_to_pattern( +a predicate specification,
%                      - a most general instance of this predicate
%                    ):
% Given a predicate specification (in the form "p/k") check whether it is
% well-formed: if not, raise a fatal error; otherwise return a most general
% instance that correspond to the predicate specification.

predspec_to_pattern( +PredSpec, +Pattern ) :- !,predspec_to_pattern( PredSpec, Pattern ).
predspec_to_pattern( - PredSpec, - Pattern ) :- !,predspec_to_pattern( PredSpec, Pattern ).
predspec_to_pattern( M:PredSpec, M:Pattern ):- !,predspec_to_pattern( PredSpec, Pattern ).
predspec_to_pattern( PredSpec, Pattern ) :- Pattern \= (_/_),!,PredSpec = Pattern.
predspec_to_pattern( PredSpec, Pattern ) :-
        check_predspec( PredSpec ),
        PredSpec = P / K,
        mk_pattern( P, K, Pattern ).


%------------------------------------------------------------------------------
% check_predspec:
% Raise an error if this is not a good predicate specification.
check_predspec( Var ) :-
        var( Var ),
        !,
        error( [ 'A variable instead of a predicate specification: \"',
                 Var,
                 '\"'
               ]
             ).

check_predspec( P / K ) :-
        atom( P ),
        integer( K ),
        K >= 0,
        !.

check_predspec( PredSpec ) :- trace,
        error( [ 'An incorrect predicate specification: \"', PredSpec, '\"' ] ).


%------------------------------------------------------------------------------
% is_a_variable_name( +term ):
% Is this the name of a variable?

is_a_variable_name( Term ) :-
        atom( Term ),
        name_chars( Term, [ FirstChar | _ ] ),
        name_chars( FirstCharAtom, [ FirstChar ] ),
        (
            FirstCharAtom = '_',
            !
        ;
            upper_case_letter( FirstCharAtom )
        ).

%
upper_case_letter( Atom ) :-  uc( Atom ),  !.

uc( 'A' ).  uc( 'B' ). uc( 'C' ).  uc( 'D' ).  uc( 'E' ).  uc( 'F' ).
uc( 'G' ).  uc( 'H' ). uc( 'I' ).  uc( 'J' ).  uc( 'K' ).  uc( 'L' ).
uc( 'M' ).  uc( 'N' ). uc( 'O' ).  uc( 'P' ).  uc( 'Q' ).  uc( 'R' ).
uc( 'S' ).  uc( 'T' ). uc( 'U' ).  uc( 'V' ).  uc( 'W' ).  uc( 'X' ).
uc( 'Y' ).  uc( 'Z' ).


%------------------------------------------------------------------------------
% between( +integer, +- integer, +integer ):
% Succeed if arg1 =< arg2 < arg3.
% If arg2 is a variable, generate the appropriate values

old_between( A, V, B ) :-
        integer( A ),
        integer( B ),
        (
            integer( V )
        ->
            A =< V,  V < B
        ;
            var( V )
        ->
            between_generate( A, V, B )
        ).

%
between_generate( A, A, B ) :-
        A < B.

between_generate( A, V, B ) :-
        A < B,
        NA is A +1,
        between_generate( NA, V, B ).


%------------------------------------------------------------------------------
% member_reversed( +- item, +list of items ):
% Like member/2, but the order of searching/generation is reversed.

member_reversed( M, [ _ | L ] ) :-
        member_reversed( M, L ).
member_reversed( M, [ M | _ ] ).


%------------------------------------------------------------------------------
% remove( +item, +list, - list sans item ) :
% The item is in the list: remove the first occurrence.

remove( Item, List, ListSansItem ) :-
        append( Prefix, [ Item | Postfix ], List ),
        append( Prefix, Postfix, ListSansItem ),
        !.


%------------------------------------------------------------------------------
% write_shallow_with_eq( +output stream, +term, +maximum depth ):
% Like write_shallow/3, but instead of relying on the underlying mechanism of
% Prolog write equations for terms that are cyclical at a depth that does not
% excceed the maximum depth.  This procedure is due to Ronald de Haan of TU
% Dresden.

write_shallow_with_eq( OutputStream, Term, MaxDepth ) :-
        cyclic( Term, MaxDepth ),
        !,
        get_printable_term_equation( Term, Head, List ),
        write_term( OutputStream, Head, [] ),
        print_equations( OutputStream, List ).

write_shallow_with_eq( OutputStream, Term, MaxDepth ) :-
        % \+ cyclic( Term, MaxDepth ),
        mk_variable_dictionary( Term, VarDict ),
        bind_variables_to_names( VarDict ),
        write_shallow( OutputStream, Term, MaxDepth ).


% Print the list of equations.

print_equations( _OutputStream, [] ) :-
        !.

print_equations( OutputStream, [ H | T ] ) :-
        write_term( OutputStream, H, [] ),
        print_equations( OutputStream, T ).

%------------------------------------------------------------------------------



%------------------------------------------------------------------------------
% Identify the system.

lp_system( 'SWI Prolog' ).


%------------------------------------------------------------------------------
% The standard streams.

std_input_stream(   user_input  ).
std_output_stream(  user_output ).
std_trace_stream(  user_error ).
std_error_stream(   user_error  ).
std_warning_stream( user_error  ).


%------------------------------------------------------------------------------
% getchar( +input stream, - character in the form of an atom ):
% This is introduced because the built-in get_char/2 returns strings on
% Eclipse and atoms on Sicstus.

getchar( Stream, Atom ) :-
        get_char( Stream, Atom ).


%------------------------------------------------------------------------------
% name_chars( +- atom or number,
%             -+list of characters (codes) that form its name
%           ):
% Used because Eclipse complains about name/2 being obsolete.

name_chars( Atomic, NameCharCodes ) :-
        name( Atomic, NameCharCodes ).

/*

%------------------------------------------------------------------------------
% clause_in_module( +module name, +- clause head, - clause body ):
% Like clause/2, but from the named module.
%
% NOTE: For the module 'interpreted' we provide special treatment.  Instead of
%       asserting clauses, we record them in the database, to avoid the
%       overhead of decompilation.
%       "Head :- Body" is recorded as "interpreted_clause( Head, Body )"
%       under the key "Head" (i.e., effectively under the name and arity of the
%       predicate). The effective key is also recorded, under the key
%       "interpreted_clause_key".
%   ->  This has been commented out for the time being, as the win is not all
%       that clear.  Just search for "interpreted" and uncomment to get back to
%       that version, but NOTE that it is unclear whether essence_hook/2 would
%       then work properly.


%------------------------------------------------------------------------------
% assertz_in_module( +module name, +clause ):
% Like assertz/1, but into this module.
%
% NOTE: See the note to clause_in_module/3 above.

% assertz_in_module( interpreted, Clause ) :-
%         !,
%         (
%             Clause = (Head :- Body)
%         ->
%             true
%         ;
%             Head = Clause,
%             Body = true
%         ),
%         recordz( Head, interpreted_clause( Head, Body ) ),
%         functor( Head, Name, Arity ),
%         (
%             recorded( interpreted_clause_key, Name / Arity )
%         ->
%             true
%         ;
%             recordz( interpreted_clause_key, Name / Arity )
%         ).

assertz_in_module( Module, Clause ) :-
        assertz( Module : Clause ).


%------------------------------------------------------------------------------
% retractall_in_module( +module name, +head pattern ):
% Like retractall/1, but into this module.
%
% NOTE: See the note to clause_in_module/3 above.

% retractall_in_module( interpreted, Head ) :-
%         recorded( Head, interpreted_clause( Head, _ ), RefClause ),
%         erase( RefClause ),
%         fail.

% retractall_in_module( interpreted, _ ) :-
%         !.

retractall_in_module( Module, Head ) :-
        retractall( Module : Head ).


%------------------------------------------------------------------------------
% call_in_module( +module name, +head pattern ):
% Like call/1, but into this module.

call_in_module( Module, Head ) :-
        call( Module : Head ).


%------------------------------------------------------------------------------
% export_from_module( +module name, +predicate specification ):
% For Sicstus this is a no-op.

export_from_module( _, _ ).


%------------------------------------------------------------------------------
% dynamic_in_module( +module name, +predicate specification ):
% For Sicstus this is a no-op.

dynamic_in_module( _, _ ).


%------------------------------------------------------------------------------
% compile_to_module( +module name, +file name ):
% Compile the program in this file into this module.

compile_to_module( Module, FileName ) :-
        compile( Module : FileName ).


%------------------------------------------------------------------------------
% copy_term( +term, -term ):
% Same as copy_term/2, but safe for cyclic terms.
% In the case of Sicstus there are no problems.

% copy_term( Term, Copy ) :- copy_term( Term, Copy ).

*/

%------------------------------------------------------------------------------
% are_variants( +term, +term ) :
%    Succeeds only if both arguments are variants of each other.
%    Does not instantiate any variables.
% NOTE:
%   If variant/2 turns out to be broken, replace the last call with the
%    following three:
%        dra_check( T1 = T2 ),                   % quickly weed out obvious misfits
%        copy_term( T2, CT2 ),
%        dra_check( (numbervars( T1, 0, N ), numbervars( CT2, 0, N ), T1 = CT2) ).

are_variants( T1, T2 ) :-
        variant( T1, T2 ).


%------------------------------------------------------------------------------
% write_shallow( +output stream, +term, +maximum depth ):
% Like write/2, but only to a limited print depth.

write_shallow( OutputStream, Term, MaxDepth ) :-
       write_term( OutputStream, Term, [ max_depth( MaxDepth ) ] ).


%------------------------------------------------------------------------------
% is_built_in( +- goal ):
% Does this goal call a built-in predicate?  Or generate a built-in goal.

is_swi_builtin( Pred ) :-
        ( \+ ( \+ predicate_property( Pred, built_in ))).


%------------------------------------------------------------------------------
% ordered_term_variables( +term, - list of variables ):
% Produce the set of variables in this term in the order of their occurrence.
% (term_variables/2 does it in that order in Sicstus, but in reverse order in
%  Eclipse.)

ordered_term_variables( Term, Variables ) :-
        term_variables( Term, Variables ).


%------------------------------------------------------------------------------
% readvar( +input stream, - term, - variable dictionary  ):
% Simulates Eclipse's readvar/3.  The variable dictionary will be in the format
% used by Eclipse, not by Sicstus (i.e., an entry has the form
% "[ name | Variable ]" rather than "name = variable".

readvar( InputStream, Term, EclipseVarDict ) :-
        read_term( InputStream, Term, [ variable_names( SicstusVarDict ) ] ),
        dra_maplist2( translate_vardict_entry, SicstusVarDict, EclipseVarDict ),
        !.

%
translate_vardict_entry( N = V, [ N | V ] ).



%------------------------------------------------------------------------------
% erase_module( +module name ):
% Simulates Eclipse's erase_module/1.
%
% NOTE: See the note to clause_in_module/3 above.

% erase_module( interpreted ) :-
%         recorded( interpreted_clause_key,  Name / Arity, RefKey ),
%         erase( RefKey ),
%         functor( Key, Name, Arity ),
%         recorded( Key, interpreted_clause( _, _ ), RefClause ),
%         erase( RefClause ),
%         fail.

% erase_module( interpreted ) :-
%        !.

erase_module( Module ) :-
        current_predicate( Module : PredSpec ),
        PredSpec = PredName / PredArity,
        mk_pattern( PredName, PredArity, PredPattern ),
        \+ predicate_property( Module : PredPattern, built_in ),
        abolish( Module : PredSpec ),
        fail.

erase_module( _ ).


%------------------------------------------------------------------------------
% dra_setval_flag( +name, +value ):
% Set this counter to this value.
%
% NOTE: Since DRA uses global variables to store only integers, we use the
%       flag/3 facility of SWI Prolog.  For more general values we would have
%       to use dra_nb_setval/dra_nb_getval.  See also dra_getval_flag/2 and incval/1 below.

dra_setval_flag( Name, Value ) :-
        flag( Name, _Old, Value ).


%------------------------------------------------------------------------------
% dra_getval_flag( +name, - value ):
% Get the value associated with this counter.

dra_getval_flag( Name, Value ) :-
        flag( Name, Value, Value ).


%------------------------------------------------------------------------------
% incval( +name ):
% Increment this counter by 1.
incval( Name ) :- !, flag( Name, Value, Value+1 ).
incval( Name ) :-
        dra_getval_flag( Name, Value ),
        NewValue is Value +1,
        dra_setval_flag( Name, NewValue ).


%------------------------------------------------------------------------------
% writeclause( +output stream, +clause ):
% Given an open output stream, write the clause onto it.

writeclause( OutputStream, (:- Directive) ) :-
        !,
        write( OutputStream, ':- ' ),
        write_term( OutputStream, Directive, [ quoted( true ) ] ),
        write( OutputStream, '.' ),
        nl( OutputStream ).

writeclause( OutputStream, (?- Query) ) :-
        !,
        write( OutputStream, '?- ' ),
        write_term( OutputStream, Query, [ quoted( true ) ] ),
        write( OutputStream, '.' ),
        nl( OutputStream ).

writeclause( OutputStream, Clause ) :-
        write_term( OutputStream, Clause, [ quoted( true ) ] ),
        write( OutputStream, '.' ),
        nl( OutputStream ).


%------------------------------------------------------------------------------
% writeln( +output stream, +term ):
% Write the term, followed by a newline.

/*
writeln( OutputStream, Term ) :-
        write( OutputStream, Term ),
        nl(    OutputStream ).
*/

%------------------------------------------------------------------------------
% writeln( +term ):
% Write the term to the standard output stream, followed by a newline.
/*
writeln( Term ) :-
        std_trace_stream( OutputStream ),
        writeln( OutputStream, Term ).
*/

%------------------------------------------------------------------------------
% concat_atoms( +atom, +atom, - atom ):
% Return an atom whose name is the concatenation of the names of the first two
% atoms.

concat_atoms( A, B, AB ) :-
        name( A, AChars ),
        name( B, BChars ),
        append( AChars, BChars, ABChars ),
        name( AB, ABChars ).

%------------------------------------------------------------------------------

% :- user:ensure_loaded(library(dra/tabling3/dra_common)).
%

% :- use_module(library(memo)).

%                                                                          %
%  An interpreter for tabled logic programming with coinduction:           %
%  see the description below for more information.                         %
%  Written by Feliks Kluzniak at UTD (January-February 2009).              %
%                                                                          %
%  Last update: 30 November 2009                                           %
%                                                                          %
dra_version( Version ) :-
        name_chars( 'DRA ((c) UTD 2009) version 0.97 (beta), June 2011 (',
                    VCodes
                  ),
        lp_system( Sys ),
        name_chars( Sys, SysCode ),
        name_chars( ')', RParCode ),
        append( SysCode, RParCode, SPar ),
        append( VCodes, SPar, VersionCodes ),
        name_chars( Version, VersionCodes ).

% NOTE:
%
%    1. See ../general/top_level.ecl for a description of how to load
%       and run programs.
%       Please note that in Eclipse after loading this interpreter you
%       should issue
%            :- import dra.
%       if you don't want to keep writing
%            dra:prog( filename )
%       every time.
%
%    2. The interpreter supports a number of directives:
%
%       a) Tabled and coinductive predicates should be declared as such in
%          the program file, e.g.,
%              :- table       ancestor/2.
%              :- coinductive0  comember/2.
%              :- coinductive1 comember/2.
%
%          "coinductive1" means that if there are coinductive hypotheses
%          with which a goal unifies, then the usual clauses will not be tried
%          after the hypotheses are exhausted (this is "new style"
%          coinduction).
%
%       b) To include files use the usual Prolog syntax:
%              :- [ file1, file2, ... ].
%
%       c) To declare predicates used in an interpreted program as dynamic,
%          use
%              :- dynamic p/k.
%
%       d) By default, a goal produces new (i.e., heretofore unknown) answers
%          before producing old ones.  To reverse this behaviour, use
%
%              :- old_first p/k.
%          or
%              :- old_first all.
%
%       e) To produce a wallpaper traces use the traces directive. For example,
%
%              :- traces p/3, q/0, r/1.
%
%          will traces predicates "p/3", "q/0" and "r/1".  If you want to traces
%          everything, use
%
%              :- traces all.
%
%          These directives are cumulative.
%
%       f) To print out subsets of the current answer table, use
%
%              :- answers( Goal, Pattern ).
%
%          this will print all tabled answers that are associated with a
%          variant of Goal and unifiable with Pattern.
%          To get a dump of the entire table, use just
%
%              :- answers( _, _ ).
%
%    2. The program should contain no other directives. It may, however,
%       contain queries, which will be executed immediately upon reading.
%
%    3. Just before the result of a query is reported, the interpreter
%       produces a printout with statistics accummulated since the previous
%       printout (or since the beginning, if this is the first printout during
%       this session with the interpreted program). The printout looks like
%       this:
%
%           [K steps, M new answers tabled (N in all)]
%
%       where K, M and N are some natural numbers. K is the number of
%       evaluated goals, M is the number of new additions to the answer table,
%       N is the current size of the answer table.
%
%    4. If the program invokes a built-in predicate, that predicate dra_must
%       be declared in the table "cuts_ok/1" (see file "dra_builtins.pl").
%       Every addition should be considered carefully: some built-ins might
%       require special treatment by the interpreter.
%
%    5. The program may contain clauses that modify the definition of the
%       interpreter's predicate "essence_hook/2" (the clauses will be asserted
%       at the front of the predicate, and will thus override the default
%       definition for some cases).  The default definition is
%
%          essence_hook( T, T ).
%
%       This predicate is invoked _in certain contexts_ when:
%          - two terms are about to be compared (either for equality or to
%            check whether they are variants of each other);
%          - an answer is tabled;
%          - an answer is retrieved from the table.
%
%       The primary intended use is to suppress arguments that carry only
%       administrative information and that may differ in two terms that are
%       "semantically" equal or variants of each other. (Such, for example, is
%       the argument that carries the set of coinductive hypotheses in a
%       co-logic program translated into Prolog: see "../coind/translate_clp".
%       Mind you, that translation need not be applied to programs executed by
%       this interpreter).
%
%       For example, the presence of
%
%          essence_hook( p( A, B, _ ),  p( A, B ) ).
%
%       will result in "p( a, b, c )" and "p( a, b, d )" being treated as
%       identical, as each of them will be translated to "p( a, b )" before
%       comparison.
%
%       NOTE: This facility should be used with the utmost caution, as it
%             may drastically affect the semantics of the interpreted program
%             in a fashion that would be hard to understand for someone who
%             does not understand the details of the interpreter.
%
% LIMITATIONS: - The interpreted program should not contain cuts.
%              - Error detection is quite rudimentary.




/*******************************************************************************

   General description
   -------------------

   A simple (and very inefficient) interpreter that emulates "top-down tabled
   programming", as described in

     [1] Hai-Feng Guo, Gopal Gupta:
         Tabled Logic Programming with Dynamic Ordering of Alternatives
         (17th ICLP, 2001)

   There are two significant changes with respect to the description in the
   paper:

       - A tabled goal will never produce the same answer twice.

         More specifically: two answers will never be variants of each other.
         Please note that "goal" means a goal instance.

       - By default, new answers for a tabled goal will be produced before
         old answers.  The user can reverse the order by means of an "old_first"
         directive.

         Here, "new answer for a tabled goal" means an answer that has not yet
         been seen (and tabled) for a variant of the goal.

         The default behaviour is intended to help computations converge more
         quickly.  The user is given an option to change it, because some
         predicates may produce a very large (even infinite) set of answers on
         backtracking, and the application might not require those answers.

   The terminology has been modified under the influence of

     [2] Neng-Fa Zhou, Taisuke Sato, Yi-Dong Shen:
         Linear Tabling Strategies and Optimizations
         (TPLP 2008 (?))

   More specifically, "masters" are called "pioneers" (although in a sense
   somewhat different than in [2]: we use "pioneer" for "topmost looping goal"),
   and "strongly connected components" are called "clusters".

   Note that "clusters" are detected dynamically, to achieve greater precision
   (a dependency graph among static calls can only be a rough approximation, a
   dependency graph among predicates is rougher still).


   Nomenclature
   ------------

   Some predicates are "tabled", because the user has declared them to be such
   by using an appropriate directive, e.g.,

       :- table p/2 .

   All calls to a tabled predicate that are present in the interpreted program
   are called "tabled calls".  Instances of such calls are called "tabled
   goals".  In general, we will use the term "call" to refer to a static entity
   in the program, and "goal" to refer to an instance of a call.  We will also
   avoid the conventional overloading of the term "goal" in yet another way: we
   will call a sequence (i.e., conjunction) of goals just that (unless we can
   refer to it as a "query" or a "resolvent").

   Similarly, the user can declare a predicate to be "coinductive", by using
   another kind of directive, e.g.,

       :- coinductive0  p/2 .
       :- coinductive1 q/3 .

   Calls and goals that refer to a coinductive predicate will also be called
   "coinductive".


   Limitations
   -----------

   The interpreted program must not contain cuts.  It also must not contain
   calls to built-in-predicates, except for the handful of predicates listed in
   cuts_ok/1 below.  (This list can be easily extended as the need arises.  Some
   built-in predicates, however, cannot be added without modifying the
   interpreter, sometimes extensively: "!/0" is a good example.)



   Data structures
   ---------------

   The interpreter uses a number of tables that store information accumulated
   during a computation.  A computation consists in reading a program and
   executing a number of queries.  A query is a sequence (i.e., conjunction) of
   goals.

   The tables (implemented as dynamic predicates of Prolog) are:


   -- is_coinductive0( generic head )
   -- is_coinductive1( generic head )
   -- is_tabled( generic head )
   -- is_old_first( generic head )

           Each of these tables contains an entry for each predicate that has
           been declared as having the corresponding property (i.e., as
           coinductive, table etc.).  For instance, when the interpreter reads
               :- coinductive0 p/2 .
           it stores the fact
               is_coinductive0( p( _, _ ) ).

           A "coinductive0" declaration is deemed to supersede "coinductive1",
           and information about a predicate that has been so declared is stored
           both in coinductive0/1 and coinductive1/1.

           These tables are cleared only before reading in a new program.


   -- answer( goal, fact )

           Used to store results computed for tabled goals encountered during a
           computation.  Once present, these results are also used during
           further stages of the computation.

           Note that the fact is an instantiation of the goal.  If a tabled goal
           has no solutions, it will have no entry in "answer", even though it
           may have an entry in "completed" (see below).

           (NOTE:
               1. In the actual implementation each fact in "answer" has the
                  form
                     answer( cgoal, goal, fact )
                  where "cgoal" is a copy of "goal" (no shared variables),
                  passed through essence_hook/2.
                  This is done to facilitate more effective filtering (via
                  unification) before a check is made for whether "goal" is a
                  variant of the goal for which we are seeking a tabled answer.

               2. This stuff has been removed to file dra_table_assert.pl
                  or dra_table_record.pl (only one of them is used,
                  depending on the logic programming system: see the main file
                  used to load the program.
           ))

           This table is not cleared before the evaluation of a new query.

           Detailed comments:
           ..................
           In general, for each success of a tabled goal encountered during the
           evaluation of a query, the interpreter will make certain that the
           result, i.e., the successful instantiation of that goal (which need
           not be ground!) is stored in the table "answer", accompanied by a
           variant of the original version of the goal (i.e., as it appeared
           when it was first encountered).

           Before a query finally fails (after exhausting all the answers),
           tabled goals encountered during its evaluation will have computed
           their least fixed points, i.e., all the possible results for those
           goals will be stored in "answer".  (Of course, if this set of all
           answers is not sufficiently small, the interpreter will not terminate
           successfully.)

           Results stored in "answer" can be picked up during later evaluation
           but each of them is valid only for a variant of the accompanying
           goal.

           The need for associating a fact with information about the
           corresponding goal might not be immediately obvious.  Consider the
           following example (which is simplistic in that the computation itself
           is trivial):

               program:  :- table p/2.
                         p( A, A ).
                         p( a, b ).

               queries:  ?-  p( U, V ).
                         ?-  p( Y, b ).

           During "normal" execution of this Prolog program each of the queries
           would generate a different set of results; to wit:

               p( U, V )  would generate  p( U, U ), p( a, b );
               p( Y, b )  ..............  p( b, b ), p( a, b ).

           In other words, the set of results depends not only on the predicate,
           but also on the form of the goal.

           If these results were tabled without the corresponding goals, then
           the table would be:

               answer( p( U, U ) ).
               answer( p( a, b ) ).
               answer( p( b, b ) ).

           A subsequent invocation of p( U, V ) would then return all three
           results, i.e., also "p( b, b )"!

           The proper contents of "answer" should be as follows (though not
           necessarily in this order):

               answer( p( U, V ), p( U, U ) ).
               answer( p( U, V ), p( a, b ) ).
               answer( p( Y, b ), p( b, b ) ).
               answer( p( Y, b ), p( a, b ) ).

           Please note that two different entries in "answer" will not be
           variants of each other.

   -- number_of_answers

           This is a non-logical variable that records the size of "answer".  It
           is useful for determining whether new answers have been generated
           during a phase of the computation.

           This variable is not cleared before the evaluation of a new query.


   -- pioneer( goal, index )

           If the current goal is tabled, and it is not a variant of any of its
           ancestors, then the goal is called a "pioneer" and obtains an "index"
           (i.e., an unique identifier). Both the goal and its index are
           recorded in this table.

           The role of a pioneer is to compute the fixpoint (by tabling answers)
            for itself and its cluster before failing: this is why the results
           for its variant descendants can be obtained simply by dra_calling
           "answer", without using their clauses (which prevents endless
           recursion).

           If a pioneer is later determined not to be the "topmost looping goal"
           in a "cluster" of interdependent goals (see ref. [2]), then it loses
           the status of a pioneer, and its role will be overtaken by the
           topmost goal in the cluster.  (This can happen if one of the
           descendants of a pioneer turns out to be a variant of one of its
           ancestors.)

           A pioneer also loses its status if its fixpoint has been computed: it
           then becomes a "completed" goal (and all its variants become
           completed).

           A pioneer "G" may also lose its status because another goal "G'",
           encountered after "G" succeeds without yet becoming completed, has
           become completed: if "G'" is a variant of "G", thne "G" becomes
           completed as well.

           When a pioneer loses its status, the associated entries in "pioneer",
           "loop" and "looping_alternative" (see below) are removed.  The
           associated entries in "result" are not removed. The unique index is
           not reused for other goals during the evaluation of the current
           query.

           This table is cleared before the evaluation of a new query.

           (NOTE: In the actual implementation each fact in "pioneer" has the
                  form
                     pioneer( cgoal, goal, index )
                  where "cgoal" is a copy of "goal" (no shared variables),
                  passed through essence_hook/2.
                  This is done to facilitate more effective filtering (via
                  unification) before a check is made for whether "goal" is a
                  variant of the goal for which we are checking whether it is
                  (still) a pioneer.
           )

   -- unique_index

           This is a non-logical variable that holds the index to be used for
           the next entry in "pioneer".  It is also used to generate unique
           indices for coinductive goals, which might need them to hold their
           own results in "result".

           The variable is cleared before the evaluation of a new query.


   -- result( index, fact )

           A tabled goal "G" that "started out" as a pioneer may have associated
           entries (marked with the unique index of "G") in "result".  This
           table records the instantiations of "G" that were returned as "G"
           succeeded.  By using the table, the interpreter prevents "G" from
           returning the same answer over and over again: in general, each
           tabled goal will not produce two results that are variants of each
           other.

           When a goal loses its pioneer status (because it is determined to be
           a part of a larger loop, or because it has become completed), the
           associated entries in "result" are not removed.  They are removed
           only when the goal finally fails.

           The table is also used by coinductive goals that are not pioneers.

           This table is cleared before the evaluation of a new query.


   -- loop( index, list of goals )

           A loop is discovered when the current tabled goal is a variant of one
           of its ancestors.  If the ancestor is a pioneer, the unique index of
           the pioneer ancestor and a list of the tabled goals between the
           pioneer and the variant are stored in "loop".

           A number of "loop" entries may exist for a given pioneer: together,
           they describe a "cluster" (i.e., a "strongly connected component",
           see ref. [1]).  Before finally failing upon backtracking, a pioneer
           will compute its own fixpoint as well as the fixpoints of the goals
           in its cluster.

           When a goal loses its pioneer status (because it is determined to be
           a part of a larger loop, or because it has become completed), the
           associated entries in "loop" are removed.

           This table is cleared before the evaluation of a new query.


   -- looping_alternative( index, clause )

           When a goal "G" is determined to be a variant descendant of a
           pioneer, the clause that is currently being used by the pioneer
           (i.e., the clause that led to "G") is stored in this table, together
           with the unique index of the pioneer.  "G" will then succeed only
           with answers that have been tabled so far, but the clause will be
           used again as backtracking brings the computation back to the
           pioneer.  (This is the essence of the "dynamic reordering of
           alternatives".
            )

           When a goal loses its pioneer status (because it is determined to be
           a part of a larger loop, or because it has become completed), the
           associated entries in "looping_alternative" are removed.

           This table is cleared before the evaluation of a new query.


   -- completed( goal )

           Indicates that this tabled goal is completed, i.e., its fixpoint has
           been computed, and all the possible results for variants of the goal
           can be found in table "answer".  Variants of a completed goal are
           completed as well.

           This table is not cleared before the evaluation of a new query.

           (NOTE: In the actual implementation each fact in "completed" has the
                  form
                     completed( cgoal, goal )
                  where "cgoal" is a copy of "goal" (no shared variables),
                  passed through essence_hook/2.
                  This is done to facilitate more effective filtering (via
                  unification) before a check is made for whether "goal" is a
                  variant of the goal for which we are checking whether it is
                  completed.
           )


   -- is_tracing( goal )

           A goal that matches something in this table will show up on the
           wallpaper traces.  This table is empty by default, and filled only
           by invocations of "traces" (most often in "traces" directives
           encountered when the interpreted program is being read).

   -- step_counter

           This is a non-logical variable that keeps track of the number of
           goals resolved during the evaluation of each query.  The final value
           is printed after the query terminates.

           The variable is cleared before the evaluation of a new query.

   -- old_table_size

           This is a non-logical variable that is used to store the value of
           "number_of_answers" before the evaluation of a query.  Used to
           produce automatic information about the growth of the table after the
           query terminates.

           The variable is reinitialized before the evaluation of a new query.


*******************************************************************************/


:- ensure_loaded( [ %'top_level',
                    %'utilities',
                    %dra_builtins,
                    %dra_coinductive_hypotheses,
                    %dra_stack
                  ]
                ).

%


%                                                                          %
%  A simple (!) general top level for metainterpreters.                    %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (January 2009).                       %
%                                                                          %
%  Last update: 12 June 2009.                                              %
%                                                                          %
%  NOTE: This code runs on Sicstus and Eclipse.  It may require some       %
%        tweaking for other Prolog systems.                                %
%                                                                          %

% NOTES FOR USERS:
%
%    1. To use this top level, just include it in your the file that
%       contains the code for your metainterpreter:
%
%           :- ensure_loaded( 'top_level' ).
%
%       Then load the metainterpreter into your logic programming system.
%
%
%    2. To begin execution by loading a new program, invoke
%
%           prog( filename ).
%
%       If the filename has no extension, the default extension will be
%       used if provided (see the description of "default_extension" below).
%
%       As the file is loaded, directives and queries are executed on-the-fly
%       by invoking the metainterpreter (except the ":- op ..." directive,
%       which is interpreted directly). A query is evaluated to give all
%       solutions (it is as if the user kept responding with a semicolon):
%       to avoid that use the built-in predicate once/1 .
%
%       After the file is loaded (and all the directives and queries it
%       contains are executed), interactive mode is started.  This is very
%       much like the usual top-level loop, except that the associated
%       metainterpreter -- and not the underlying Logic Programming system --
%       is used to evaluate queries and directives.
%
%
%       To just enter interactive mode invoke
%
%           top
%
%       To exit interactive mode enter end of file (^D), or just write
%
%           quit.
%
%       (the former method appears not to work with tkeclipse).
%
%       NOTE: 1. In the interactive mode one cannot input more than one term
%                per line.
%
%             2. When a query succeeds, the bindings of variables should be
%                printed upto a certain maximum depth.  The default value is
%                given in print_depth/1 below.  The maximum depth can be
%                changed from the interpreted program by invoking
%
%                   set_print_depth( N )
%
%                where N is a positive integer.
%
%                Please note that on some Prolog implementations (e.g.,
%                Eclipse) this might not prevent a loop if the printed term
%                is cyclic (as will often happen for coinductive programs).
%
%                Note also that the foregoing does not apply to invocations of
%                builtins in the interpreted program.  It is up to the user to
%                apply the is_cuts_ok appropriate for the host logic programming
%                system.  For example, in the case of Sicstus, use
%                "write_term( T, [ max_depth( 10 ) ] )" rather than just
%                "write( T )", especially if you expect T to be a cyclic term.
%
%
%    3. To include files (interactively or from other files) use
%       the usual Prolog syntax:
%
%           :- [ file1, file2, ... ].
%
%       Please note that there is a difference between "prog( file )" and
%       ":- [ file ].".  If the former is used, the metainterpreter is
%       (re)initialised before loading the file (see description of
%       initialise/0  below); if the latter is used, the file is just loaded.
%
%
%    4. The program that is read in must not contain variable literals.  It
%       may, however, contain invocations of call/1.
%
%
%    5. The interpreted program may contain declarations of "top" and
%       "support" predicates, in the form of directives:
%
%           :- topl p/1, q/2.
%           :- support check_consistency/1.
%
%       The "top" declaration indicates predicates that will be called "from
%       the outside", so if they are not called in the program, there will be
%       no warning.
%       (This declaration is also recognized when translating coinductive
%        programs into Prolog: see "../coind/translate_colp".)
%
%       The "support" declaration means that the metainterpreter should treat
%       this predicate as a built-in, i.e., just let Prolog execute it.  This
%       can be useful for increasing the efficiency of interpreted programs
%       that make use of support routines that are written in "straight"
%       Prolog.  (Please note also that support predicates can use the full
%       range of built-in predicates available in the host logic programming
%       system.)
%
%       Predicates that are declared as "support" must be defined in other
%       files.  To compile and load such files, use
%
%           :- load_is_support( filename ).



% NOTES FOR AUTHORS OF METAINTERPRETERS:
%
%    6. The clauses read in by the top level are loaded into the module
%       "interpreted".  This is done to avoid conflicts with predicates
%       used in the metainterpreter (and the top level).  The metainterpreter
%       must access them by using the predicate imported from
%       "compatibility_utilties_...":
%           clause_in_module( interpreted, ... )
%
%       The predicates defined by these clauses are stored in the table
%       defined/1, in the form of patterns, e.g.,
%           is_defined( p( _, _ ) ).
%
%
%    7. The top level notes "support" declarations in the table "support".
%       For example,
%
%           :- support p/1, q/2.
%
%       will be stored as
%
%           is_support( p( _ ) ).
%           is_support( q( _, _ ) ).
%
%       The intended meaning is that "support" predicates do not make use
%       (directly or indirectly) of the special features provided by the
%       metainterpreter, so their invocations can be handled just by handing
%       them over to Prolog (which would presumably speed up the computation).
%
%       Please note that the support predicates (which should be defined in
%       files mentioned in ":- load_is_support( filename )." directives) are
%       compiled into the module "support" (unless they are defined within
%       other modules).
%
%
%    8. The metainterpreter should provide the following predicates
%       ("hooks") that will be called by the top level:
%
%          - is_cuts_ok/1:
%                 Defines patterns for built-in predicates from the host
%                 system that can be invoked by the interpreted program.
%                 For example, to allow writeln/2, declare:
%                     is_cuts_ok( writeln( _, _ ) ).
%
%          - default_extension/1:
%                 This predicate is optional.  If present, its argument
%                 should be an atom whose name is the extension string to be
%                 added to file names that do not already have an extension.
%                 (The string should begin with a period!)
%                 For example, a metainterpreter for coinductive logic
%                 programming might contain the following fact:
%                      default_extension( '.clp' ).
%
%          - initialise/0:
%                 This will be called before loading a new program,
%                 giving the metainterpreter an opportunity to
%                 (re)initialise its data structures.
%
%          - program_loaded/0:
%                 This will be called after a program has been read in from
%                 its file and stored in memory.  The interpreter can use
%                 the opportunity to check the program's consistency, to
%                 transform the program, etc.
%
%          - legal_directive/1:
%                 Whenever the top level encounters a directive
%                 (of the form ":- D."), it will call "legal_directive( D )".
%                 If the call succeeds, the interpreter will be given
%                 a chance to process the directive (see below), otherwise
%                 the directive will be ignored (with a suitable warning).
%
%          - execute_directive/1:
%                 Whenever the top level encounters a legal directive
%                 ":- D" (see above), it invokes "execute_directive( D )"
%                 to give the interpreter a chance to act upon the
%                 directive.
%
%          - dra_call/1:
%                 This would be the main entry point of the metainterpreter.
%                 Whenever the top level encounters a query (of the form
%                 "?- Q."), it will display the query and then call
%                 "dra_call( Q )".  Depending on the result, it will then
%                 display "No", or "Yes" (preceded by a display of bindings
%                 acquired by the variables occurring in "Q"); in the latter
%                 case it will also backtrack to obtain more solutions.
%
%
%    9. The metainterpreter can also define hooks of its own.  A hook
%       predicate should be declared in a fact of "hook_predicate/1".
%       For example,
%
%           hook_predicate( essence_hook( _, _ ) ).
%
%       declares that "essence_hook/2" is a metainterpreter hook.  A hook
%       predicate (essence_hook/2 in this case) should be dynamic.  When
%       the top level encounters a clause whose head matches a hook predicate
%       declaration, the clause is asserted at the front (!) of the predicate
%       (in the module of the running program, not in "interpreted").
%
%       NOTE: If the interpreter does not use hook predicates, it must contain
%             the definition
%                 hook_predicate( '' ).


%:- ensure_loaded( utilities ).
%:- ensure_loaded( program_consistency ).
%

%                                                                          %
%  Check the consistency of the loaded program.                            %
%  An auxiliary of top_level.                                              %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (January 2009).                       %
%                                                                          %
%  Last update: 11 June 2009.                                              %
%                                                                          %


%:- ensure_loaded( utilities ).
%:- ensure_loaded( open_set_in_tree ).
%

%  Simple, but useful operations on sets.  The sets are open, i.e.,        %
%  insertion is a destructive operation.                                   %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (February 2009).                      %
%                                                                          %
%  Last update: 20 February 2009.                                          %
%                                                                          %
%  NOTE: Terms that are variants are treated as the same item: this is     %
%        so because comparison of variables is unreliable.                 %
%                                                                          %
%        The cost of insertion or membership check can be logarithmic      %
%        in the size of the set, but can be proportional to the size if    %
%        the ordering in which elements are inserted is far from random.   %
%        The cost of set operations (union, equality etc.) can also be     %
%        logarithmic, but quadratic in the worst case.                     %
%                                                                          %


% Sets are represented as open binary trees.


%------------------------------------------------------------------------------
% empty_openset( +- open set ) :
% Create an empty set, or check that the given set is empty.

empty_openset( V ) :-
        var( V ).


%------------------------------------------------------------------------------
% add_to_openset( +item, +- open set ):
% Add the item to the set.

add_to_openset( Item, Set ) :-
        (
            var( Set )
        ->
            Set = t( Item, _, _ )
        ;
            % nonvar( Set ),
            Set = t( I, L, R ),
            (
                Item = I
            ->
                true
            ;
                Item @< I
            ->
                add_to_openset( Item, L )
            ;
                add_to_openset( Item, R )
            )
        ).


%------------------------------------------------------------------------------
% is_in_openset( +item, +open set ):
% Is the given item a member of the set?

is_in_openset( Item, Set ) :-
        (
            var( Set )
        ->
            fail
        ;
            % nonvar( Set ),
            Set = t( I, L, R ),
            (
                Item = I
            ->
                true
            ;
                Item @< I
            ->
                is_in_openset( Item, L )
            ;
                is_in_openset( Item, R )
            )
        ).


%------------------------------------------------------------------------------
% generate_member_of_openset( +open set, - item ):
% Nondeterministically generate members of the set.

generate_member_of_openset( Set, Item ) :-
        nonvar( Set ),
        Set = t( I, L, R ),
        (
            generate_member_of_openset( L, Item )
        ;
            Item = I
        ;
            generate_member_of_openset( R, Item )
        ).


%------------------------------------------------------------------------------
% equal_opensets( +open set, +open set ):
% Are the two sets equal?

equal_opensets( S1, S2 ) :-
        symmetric_openset_difference( S1, S2, SD ),
        empty_openset( SD ).


%------------------------------------------------------------------------------
% openset_union( +open set, +open set, - open set ):
% Compute the union of two sets.

openset_union( S1, S2, Result ) :-
        copy_items( S1, Result ),
        copy_items( S2, Result ).

%
copy_items( V, _ ) :-
        var( V ),
        !.

copy_items( t( I, L, R ), Result ) :-
        add_to_openset( I, Result ),
        copy_items( L, Result ),
        copy_items( R, Result ).


%------------------------------------------------------------------------------
% openset_intersection( +open set, +open set, - open set ):
% Compute the intersection of two sets.

openset_intersection( S1, S2, Result ) :-
        copy_shared( S1, S2, Result ).

%
copy_shared( V, _, _ ) :-
        var( V ),
        !.

copy_shared( t( I, L, R ), S, Result ) :-
        (
            is_in_openset( I, S )
        ->
            add_to_openset( I, Result )
        ;
            true
        ),
        copy_shared( L, S, Result ),
        copy_shared( R, S, Result ).


%------------------------------------------------------------------------------
% openset_difference( +open set, +open set, - open set ):
% Subtract the second set from the first.

openset_difference( S1, S2, Result ) :-
        copy_not_shared( S1, S2, Result ).

%
copy_not_shared( V, _, _ ) :-
        var( V ),
        !.

copy_not_shared( t( I, L, R ), S, Result ) :-
        (
            is_in_openset( I, S )
        ->
            true
        ;
            add_to_openset( I, Result )
        ),
        copy_not_shared( L, S, Result ),
        copy_not_shared( R, S, Result ).


%------------------------------------------------------------------------------
% symmetric_openset_difference( +open set, +open set, - open set ):
% Compute the symmetric difference of two sets.

symmetric_openset_difference( S1, S2, Result ) :-
        openset_difference( S1, S2, Result ),
        openset_difference( S2, S1, Result ).


%------------------------------------------------------------------------------
% openset_to_list( +open set, - list ):
% Create a list that contains all the elements of the set.

openset_to_list( Set, List ) :-
        to_list( Set, [], List ).

%
to_list( V, ListSoFar, ListSoFar ) :-
        var( V ),
        !.

to_list( t( I, L, R ), ListSoFar, List ) :-
        to_list( R, ListSoFar, ListWithRight ),
        to_list( L, [ I | ListWithRight ], List ).


%------------------------------------------------------------------------------
% list_to_openset( +list, - set ):
% Create a set that contains all the elements from the list (without
% duplicates, of course).

list_to_openset( List, Set ) :-
        empty_openset( Set ),
        list_to_openset_( List, Set ).

%
list_to_openset_( [], _ ).

list_to_openset_( [ H | T ], S ) :-
        add_to_openset( H, S ),
        list_to_openset_( T, S ).

%------------------------------------------------------------------------------



% The following things are being checked:
%  - is there a call to an undefined predicate?
%  - is there a defined predicate that is not called and not declared as top?
%  - is there a predicate that was declared as top, but not defined?
%  - is there a predicate that was declared as support, but not defined?

check_general_consistency :-
%        findall( PredSpec,
%                 ( current_predicate_in_module( interpreted, PredSpec )
%                 , predspec_to_pattern( PredSpec, Pattern )
%                 , \+ is_cuts_ok( Pattern )
%                 ),
%                 ListOfDefined
%               ),
        % The above can be made simpler, now that we have "defined/1":
        findall( P / K,
                 ( is_defined( Pattern )
                 , \+ hook_predicate( Pattern )
                 , functor( Pattern, P, K )
                 ),
                 ListOfDefined
               ),
        findall( PredSpec,
                 current_predicate_in_module( support, PredSpec ),
                 ListOfDefinedSupport
               ),
        (
            is_topl( Var ),  var( Var )
        ->
            ListOfDeclaredTop = ListOfDefined
        ;
            findall( P/K
                   , ( is_topl( Pattern )
                     , functor( Pattern, P, K )
                     )
                   , ListOfDeclaredTop
                   )
        ),
        findall( P/K
               , ( is_support( Pattern )
                 , functor( Pattern, P, K )
                 )
               , ListOfDeclaredSupport
               ),

        list_to_openset( ListOfDefined        , OSetOfDefined         ),
        list_to_openset( ListOfDeclaredSupport, OSetOfDeclaredSupport ),
        list_to_openset( ListOfDefinedSupport , OSetOfDefinedSupport  ),
        list_to_openset( ListOfDeclaredTop    , OSetOfDeclaredTop     ),

        openset_difference( OSetOfDeclaredTop, OSetOfDefined, OSetOfUndefinedTop ),
        openset_difference( OSetOfDeclaredSupport, OSetOfDefinedSupport,
                         OSetOfUndefinedSupport
                       ),
        declared_undefined_warnings( OSetOfUndefinedTop    , top     ),
        declared_undefined_warnings( OSetOfUndefinedSupport, support ),

        openset_intersection( OSetOfDefinedSupport, OSetOfDeclaredSupport,
                           OSetOfCallableSupport
                         ),
        openset_union( OSetOfDefined, OSetOfCallableSupport, OSetOfAllDefined ),

        get_called_predicates( OSetOfDefined, OSetOfAllDefined, OSetOfCalled ),
        openset_difference( OSetOfDefined, OSetOfCalled, OSetOfDefinedUncalled ),
        openset_difference( OSetOfDefinedUncalled, OSetOfDeclaredTop,
                         OSetOfUncalled
                       ),
        uncalled_warnings( OSetOfUncalled ).


%
declared_undefined_warnings( OSetOfPredSpecs, KindOfDeclaration ) :-
        generate_member_of_openset( OSetOfPredSpecs, PredSpec ),
        warning( [ 'Predicate ', PredSpec,
                   ' declared as \"', KindOfDeclaration, '\" but not defined'
                 ]
               ),
        fail.

declared_undefined_warnings( _, _ ).


%
uncalled_warnings( OSetOfPredSpecs ) :-
        generate_member_of_openset( OSetOfPredSpecs, PredSpec ),
        warning( [ 'Predicate ', PredSpec, ' defined but not called' ] ),
        fail.

uncalled_warnings( _ ).



% get_called_predicates( +open set of predicates,
%                        +open set of all defined predicates,
%                        - open set of predicates called from the defined ones
%                      ):
% Produce the set of predicates called from the first set, at the same time
% producing warnings about calls to predicates that are not in the second set.

get_called_predicates( OSetOfPredicates, OSetOfDefined, OSetOfCalled ) :-
        sets_of_called( OSetOfPredicates, OSetOfDefined, ListOfSetsOfCalled ),
        empty_openset( Empty ),
        dra_fold( openset_union, Empty, ListOfSetsOfCalled, OSetOfCalled ).

%
sets_of_called( OsetOfPredicates, OSetOfDefined, ListOfSetsOfCalled ) :-
        openset_to_list( OsetOfPredicates, ListOfPredicates ),
        dra_maplist2( set_of_called( OSetOfDefined ),
             ListOfPredicates, ListOfSetsOfCalled
           ).

%
set_of_called( OSetOfDefined, PredSpec, OSetOfCalled ) :-
        predspec_to_pattern( PredSpec, Pattern ),
        findall( OSetOfCalled
               , ( clause_in_module( interpreted, Pattern, Body )
                 , extract_called( Body, OSetOfCalled )
                 )
               , OSetsOfCalled
               ),
        empty_openset( Empty ),
        dra_fold( openset_union, Empty, OSetsOfCalled, OSetOfCalled ),
        openset_difference( OSetOfCalled, OSetOfDefined, OSetOfCallsToUndefined ),
        warnings_about_called( OSetOfCallsToUndefined, PredSpec ).

%
warnings_about_called( OSetOfPredSpecsBad, ParentPredSpec ) :-
        generate_member_of_openset( OSetOfPredSpecsBad, PredSpecBad ),
        predspec_to_pattern( PredSpecBad, Pattern ),
        \+ is_cuts_ok( Pattern ),
        warning( [ 'Undefined predicate ', PredSpecBad,
                   ' called from ', ParentPredSpec
                 ]
               ),
        fail.

warnings_about_called( _, _ ).


% extract_called( +clause body, - open set of called predicates ):
% Extract the list of predicates called by this body, except for predicates
% declared as is_cuts_ok.

extract_called( Var, _ ) :-
        var( Var ),
        !.

extract_called( Binary, OSetOfCalled ) :-
        ( Binary = ( A ; B )
        ; Binary = ( A , B )
        ; Binary = ( A -> B )
        ),
        !,
        extract_called( A, OSetOfCalledA ),
        extract_called( B, OSetOfCalledB ),
        openset_union( OSetOfCalledA, OSetOfCalledB, OSetOfCalled ).

extract_called( Unary, OSetOfCalled ) :-
        ( Unary = (\+ A)
        ; Unary = once( A )
        ; Unary = call( A )
        ),
        !,
        extract_called( A, OSetOfCalled ).

extract_called( Findall, OSetOfCalled ) :-
        Findall = findall( _, Goal, _ ),
        !,
        (
            % Sicstus prefixes the second argument of findall with the module
            % name, but it does not do that for nested findall...
            lp_system( sicstus ),
            Goal = interpreted: G
        ->
            true
        ;
            G = Goal
        ),
        extract_called( G, OSetOfCalled ).


extract_called( Predicate, OSetOfCalled ) :-
        callable( Predicate ),
        !,
        functor( Predicate, P, K ),
        empty_openset( OSetOfCalled ),
        add_to_openset( P/K, OSetOfCalled ).

extract_called( _, Empty ) :-
        empty_openset( Empty ).

%------------------------------------------------------------------------------

%:- ensure_loaded( output_equation ).
%  Output cyclic terms as equations.                                       %
%                                                                          %
%  Written by Ronald de Haan at UT Dresden (January, April 2011).          %
%                                                                          %
%  Reformatted and extensively modified by FK.                             %
%                                                                          %


% :- module( output_equation,
%         [
%           cyclic/2,
%           get_term_equation/3,
%           get_printable_term_equation/3
% 	  ]).


%
% Output cyclic terms as equations                           %
%
%                                                            %
% Example of use:                                            %
%                                                            %
% ?- X = f(Y), Y = g(Y), get_term_equation(X, Eq, InitVar).  %
% X = f(g(**)),                                              %
% Y = g(**),                                                 %
% Eq = [InitVar=f(_G805), _G805=g(_G805)] .                  %
%                                                            %
%                                                            %
%



%------------------------------------------------------------------------------
% cyclic( +Term, +Max ) :
% Succeeds iff the term Term is cyclic within a depth of Max.

cyclic( Term, Max ) :-
        cyclic_term( Term ),  % if the term is not cyclic at all, don't even try
        list_subterms_up_to_depth( Term, Max, Subterms ),
        check_list_for_duplicates( Subterms ).


% list_subterms_up_to_depth( +Term, +MaxDepth, - Subterms ) :
% Produces a list of all subterms of Term upto the given depth.

list_subterms_up_to_depth( Term, MaxDepth, Subterms ) :-
        aux_subterms_up_to_depth( [ Term ], MaxDepth, Subterms, [] ).


% aux_subterms_up_to_depth( +Terms, +MaxDepth, - Subterms, - End ) :
%    - Terms is a list of subterms, all at the same level of the original term;
%    - MaxDepth is the maximum further depth to which we should descend;
%    - Subterms is an _open_ list of subterms (upto the maximum depth) obtained
%      from Terms;
%    - End is the end of the open list.
% This is an auxiliary of list_subterms_up_to_depth/3.

aux_subterms_up_to_depth( [], _MaxDepth, End, End ).

aux_subterms_up_to_depth( [ Term | Terms ], MaxDepth, Subterms, End ) :-
        (
            ( \+ compound( Term ) ; MaxDepth =< 0 )
        ->                                    % Term has no interesting subterms
            Subterms = [ Term | RestOfSubterms ]
        ;
                                              % Term has interesting subterms
            Subterms = [ Term | ArgSubterms ],
            Term =.. [ _ | Args ],
            NewMaxDepth is MaxDepth - 1,
            aux_subterms_up_to_depth( Args,        NewMaxDepth,
                                      ArgSubterms, RestOfSubterms
                                    )
        ),
        aux_subterms_up_to_depth( Terms, MaxDepth, RestOfSubterms, End ).


% check_list_for_duplicates( +List ) :
% Checks whether the list contains duplicates, i.e., at least two identical
% terms ("identical" as opposed to "unifiable").
%
% Ronald's original version was very elegant:
%
%    check_list_for_duplicates( List ) :-
%            setof( X, member( X, List ), Set ),
%            length( List, N ),
%            length( Set, M ),
%            N \= M.
%
% I have replaced it with the following in the interest of "efficiency": if
% a duplicate is found early, there is no need to go through the entire list.
% The worst-case cost should be about the same, i.e., quadratic in the length of
% the list (in the original version this is hidden within setof/3). [FK]

check_list_for_duplicates( List ) :-
        % append/3 is used to generate various splittings of List:
        append( _Prefix, [ Term | Postfix ], List ),
        identical_member( Term, Postfix ),
        !.



%------------------------------------------------------------------------------
% get_equation( +Term, - Equation ) :
%  Gets the equation corresponding to a term in
% the form of a list of equalities in which the cyclic points are marked with
% x/1 markers. The argument of x/1 is the integer that is paired with the
% replaced term.
%
% Example:
%    ?-  X = [ a | Y ],  Y = [ b | Y ],  get_equation( X, E ).
%    X = [ a, b | ** ],
%    Y = [ b | ** ],
%    E = [ (0 , [ a | x( 1 ) ]), (1 , [ b | x( 1 ) ]) ].

get_equation( Term, Equation ) :-
        obtain_all_cyclic_subterms( Term, List ),
        number_list_starting_at( List, 1, NumberedList ),
        convert( [ Term ], NumberedList,
                 [ (0 , NewTerm) ], Equation, [ NewTerm ]
               ).


% obtain_all_cyclic_subterms( +Term, - List ) :
% Create a list of all the cyclic subterms of this term.
% A "cyclic term" in this context is a term whose main functor is involved in a
% cycle, as opposed to a term that only contains cyclic subterms.  For example,
%    ?-  X = f( X ), obtain_all_cyclic_subterms( t( a( X ), b( X ) ), L ).
% will yield only  f( X ) and not, for example, a( X ).

obtain_all_cyclic_subterms( Term, List ) :-
        obtain_all_cyclic_subterms( [ Term ], [], root, [], RList ),
        reverse( RList, List ).


% obtain_all_cyclic_subterms( Terms, SeenBefore, Root, Acc, Ans ) :
%  - Terms are the terms that still have to be handled;
%  - SeenBefore is the list of terms that have already been seen;
%  - Root = root if we are at the root of the term;
%  - Acc is an accumulator (for Ans);
%  - Ans will contain the list of different subterms.
%
% Additional explanation (FK):
% When first seen, a cyclic subterm is added to SeenBefore.
% Since it is cyclic, it will be seen again, and at that point it will be added
% to the accumulator. This ensures that a term that satisfies cyclic_term/1 by
% virtue of containing cyclic subterms will not be put on the list unless its
% main functor is actually a part of the cycle.
% MODIFIED by FK:
%    1. Replaced counter with Root (i.e., just a flag).
%    2. Suppressed repetitions in the resulting list.
%    3. Replaced the call to append/3 with a recursive invocation. So the first
%       argument is now always a list of remaining siblings.  Notice that this
%       change makes SeenBefore shorter, but that is a good thing. There
%       is no need to check whether a sibling has been seen before: all we care
%       about is whether this term is identical with one of its ancestors.
%    4. Suppressed addition of siblings to SeenBefore.

obtain_all_cyclic_subterms( [], _, _, Acc, Acc ) :- !.

obtain_all_cyclic_subterms( [ T | TS ], SeenBefore, noroot, Acc, List ) :-
        identical_member( T, SeenBefore ),
        !,                   % identical with an ancestor: should be in the list
        (
            identical_member( T, Acc )
        ->                                                   % avoid repetitions
            NAcc = Acc
        ;
            NAcc = [ T | Acc ]
        ),
        obtain_all_cyclic_subterms( TS, SeenBefore, noroot, NAcc, List ).

obtain_all_cyclic_subterms( [ T | TS ], SeenBefore, _Root, Acc, List ) :-
        (
            % No need to remember terms for which cyclic_term/1 fails, no need
            % to visit their  arguments.
            \+ cyclic_term( T )
        ->
            NAcc = Acc
        ;
            % since cyclic_term( T ) succeeded, so would compound( T ):
            T =.. [ _ | SubtermList ],
            obtain_all_cyclic_subterms( SubtermList, [ T | SeenBefore ],
                                        noroot, Acc, NAcc
                                      )
        ),
        % No need to remember that we have seen a sibling:
        obtain_all_cyclic_subterms( TS, SeenBefore, noroot, NAcc, List ).


% number_list_starting_at( +List, +InitialNr, - NumberedList ) :
%  - List is the list to be numbered;
%  - InitialNr is the number to start numbering with;
%  - NumberedList is the result of numbering elements of List from InitialNr
%    on.

number_list_starting_at( [], _, [] ).

number_list_starting_at( [ H | T ], N, [ (N , H) | A ] ) :-
        M is N +1,
        number_list_starting_at( T, M, A ).


% convert( +Terms, +CyclicSubterms, +EquationAccumulator, - Equation,
%          - NewTerms
%        ) :
%    - Terms is (the remainder of) a list containing one term, or all the
%      arguments of one term (sibling terms);
%    - CyclicSubterms is a list of cyclic subterms (produced by
%      obtain_all_cyclic_subterms/2), each paired with a unique number;
%    - EquationAccumulator is the accumulator for the sub-equations of the
%      entire equation: each element is a pair consisting of a number and
%      a term;
%    - Equation is the accumulator, augmented with information produced in this
%      instance of convert/5;
%    - NewTerms is a list with the converted forms of the input terms;
%
% Conversion consists in replacing each occurrence of a (sub)term that is
% identical to one of the terms on CyclicSubterms with x( N ), where N is the
% number that is associated with the term on CyclicSubterms.  For each such
% replacement a "subequation" of the form (N , Term) must appear on Equation:
% however, care is taken not to allow repetitions on that list.  Replacement is
% carried out also for the arguments of the cyclic subterms: to prevent
% infinite looping, it is not carried out if an argument already has its number
% on the Equation list.

convert( [], _, Acc, Acc, [] ).

convert( [ T | Ts ],  CyclicSubterms, Acc, Equation, [ x( N ) | NewTs ] ) :-
        identical_member2( (N , T), CyclicSubterms ),
        !,                                              % a cyclic term: replace
        (
            member( (N , _), Acc )
        ->
            % Break the loop: don't add to Equation, don't replace in arguments
            % (if any):
            NewAcc = Acc
        ;
            % Add the term to Equation, and run through its arguments, if any:
            NAcc = [ (N , NewT) | Acc ],
            (
                compound( T )
            ->
                T =.. [ F | Args ],
                convert( Args, CyclicSubterms, NAcc, NewAcc, NewArgs ),
                NewT =.. [ F | NewArgs ]
            ;
                NewT   = T,
                NewAcc = NAcc
            )
        ),
        convert( Ts, CyclicSubterms, NewAcc, Equation, NewTs ).


convert( [ T | Ts ],  CyclicSubterms, Acc, Equation, [ NewT | NewTs ] ) :-
        % \+ identical_member2( (N , T), CyclicSubterms ),
        % Don't add to equation, but convert arguments (if any):
        (
            compound( T )
        ->
            T =.. [ F | Args ],
            convert( Args, CyclicSubterms, Acc, NewAcc, NewArgs ),
            NewT =.. [ F | NewArgs ]
        ;
            NewT   = T,
            NewAcc = Acc
        ),
        convert( Ts, CyclicSubterms, NewAcc, Equation, NewTs ).




%------------------------------------------------------------------------------
% get_printable_term_equation( +Term, - Head, - List ) :
% Returns the equation of a term as a list of strings.
% Head is a string containing the initial variable of the equation.
% List is a list of strings containing parts of the equation.

get_printable_term_equation( Term, Head, List ) :-
        get_term_equation( Term, Eq, H ),
        swritef( Head, '%w\n', [ H ] ),
        get_printable_list( Eq, List ).


% Convert a list of equations (arg1) to a list of their string forms.

get_printable_list( [], [] ).

get_printable_list( [ ( A = B ) | T ], [ String | Rest ] ) :-
        swritef( String, '%w = %w\n', [ A, B ] ),
        get_printable_list( T, Rest ).


% get_term_equation( +Term, - EquationList, - HeadVar ) :
% Obtains a list of equations corresponding to the cyclic term Term, in which
% HeadVar is the variable corresponding to Term.
% Added conversion to more sensible variable names. [FK]

get_term_equation( Term, EquationList, HeadVar ) :-
        get_equation( Term, Equation ),
        get_equation_with_variables( Equation,
                                     UnsortedEquationList, HeadVar
                                   ),
        % ADDED conversion to readable variable names [FK]:
        mk_variable_dictionary( p( HeadVar, UnsortedEquationList ),
                                VarDict
                              ),
        bind_variables_to_names( VarDict ),
        sort( UnsortedEquationList, EquationList ).



%------------------------------------------------------------------------------
% get_equation_with_variables( +Equation, - EquationList, - HeadVar ) :
% Turns an equation with x/1 markers into an equation with variables for the
% cyclic points.
%
% Example:
%    ?- X = [ a | Y ], Y = [ b | Y ],  get_equation( X, E ),
%       get_equation_with_variables( E, EL, HV ).
%    X = [ a, b | ** ],
%    Y = [ b | ** ],
%    E = [ (0 , [ a | x( 1 ) ]), (1 , [ b | x( 1 ) ]) ],
%    EL = [ HV=[ a | _G930 ], _G930=[ b | _G930 ] ] .

get_equation_with_variables( Equation, EquationList, HeadVar ) :-
        variable_list( Equation, VarList ),
        member( ( 0, HeadVar ), VarList ),
        convert_markers_to_vars( Equation, VarList, EquationList ).



% variable_list( +Equation, - VariableList ) :
% Gets a list of numbered variables for every term in the list of equations.

variable_list( [], [] ).

variable_list( [ ( N , _ ) | T ], [ ( N , _ ) | R ] ) :-
        variable_list( T, R ).


% convert_markers_to_vars( +Equation, +VarList, - NewEquation ) :
% For each pair in Equation:
%   - replace the number by the corresponding variable in VarList;
%   - convert the term by replacing each x( N ) marker with the
%     N'th variable in VarList.

convert_markers_to_vars( [], _, [] ).

convert_markers_to_vars( [ (N , T) | Rest ], VarList, [ V = NT | RestAns ] ) :-
        member( (N , V), VarList ),
        replace_markers_by_variables( T, VarList, NT ),
        convert_markers_to_vars( Rest, VarList, RestAns ).


% replace_markers_by_variable( +Term, +NumberedVarList, - NewTerm ) :
% Replaces cyclic positions, marked with x/1, with corresponding variables from
% a numbered list of variables.
%
% The original version spuriously unified a variable term with x( N ), which
% led to wrong results.  This is fixed below.  [FK]

replace_markers_by_variables( T, _VL, T ) :-
        \+ compound( T ),
        !.

replace_markers_by_variables( x( N ), VL, V ) :-
        !,
        member( (N , V), VL ).

replace_markers_by_variables( T, VL, NewT ) :-
        T =.. [ F | Args ],
        replace_markers_by_variables_in_list( Args, VL, NewArgs ),
        NewT =.. [ F | NewArgs ].


% replace_markers_by_variables_in_list( +Terms, +VarList, -Vars ) :
% Invokes replace_marker_by_variable for each item on the list.

replace_markers_by_variables_in_list( [], _, [] ).

replace_markers_by_variables_in_list( [ T | Ts ], VL, [ V | Vs ] ) :-
        replace_markers_by_variables( T, VL, V ),
        replace_markers_by_variables_in_list( Ts, VL, Vs ).



%------------------------------------------------------------------------------
% identical_member( +term, +list ) :
% Succeed if the list contains this term (as opposed to something that is
% unifiable with this term).

identical_member( X, Items ) :- member( T, Items ),X == T,!.


% identical_member2( (-+number , +term), +list of pairs ) :
% Succeed if the list contains a pair whose second element is identical to the
% second element of arg1, and whose first element unifies with the first
% element of arg1.

identical_member2( (N , Term), Items ) :-
        member( (N, T), Items ),
        Term == T,
        !.

%==============================================================================


:- op( 1010, fy, topl          ).     % allow  ":- topl p/k ."
:- op( 1010, fy, support      ).     % allow  ":- support p/k ."
:- op( 1010, fy, load_support ).     % allow  ":- load_support filename ."

:-           op( 1010, fy, coinductive0  ),    % allow  ":- coinductive0 p/k ."
             op( 1010, fy, coinductive1 ),    % allow  ":- coinductive1 p/k ."
             op( 1010, fy, table       ),    % allow  ":- table p/k ."
             op( 1010, fy, old_first    ),    % allow  ":- old_first p/k ."
             op( 1010, fy, traces        ),    % allow  ":- traces  p/k ."
             op( 1010, fy, multifile    ),    % allow  ":- multifile  p/k ."
             op( 1010, fy, topl          ),    % allow  ":- topl p/k ."
             op( 1010, fy, support      ),    % allow  ":- support p/k ."
             op( 1010, fy, load_support ).     % allow  ":- load_support filename

:- dynamic (is_support)/1.
:- dynamic (is_topl)/1.
:- dynamic (is_defined)/1.


% If "p/k" has already been seen (and declared as dynamic), the fact is recorded
% as "is_known( p( _, _, ...) )" (with "k" arguments).
% (Unlike Sicstus, Eclipse requires a dynamic declaration before the first
%  assert.)

:- dynamic is_known/1 .


% Default print depth.  (May be changed by the metainterpreter by invoking
% set_print_depth( N ).)

:- dynamic print_depth/1 .

print_depth( 10 ).

%
set_print_depth( N ) :-
        integer( N ),
        N > 0,
        !,
        retract( print_depth( _ ) ),
        assert(  print_depth( N ) ).

set_print_depth( Strange ) :-
        error( [ 'The argument of set_print_depth/1 is not a positive integer',
                 ': \"', Strange, '\"'
               ]
             ).




% prog( +file name ):
% Initialise, then load a program from this file, processing directives and
% queries.  After this is done, enter interactive mode.


prog( FileName ) :-
        setup,
        initialise,                              % provided by a metainterpreter
        process_file( FileName ),
        check_general_consistency,
        program_loaded,                          % provided by a metainterpreter
        !.

%
setup :-
        retractall( is_known( _ )   ),
        retractall( is_support( _ ) ),
        retractall( is_topl( _ )     ),
        retractall( is_defined( _ ) ),
        erase_modules.
        % create_modules.



% NOTE: In Eclipse it is possible to use the module facility in a way that
%       allows redeclaration of predicates that are built-ins, but that are
%       not wanted (see below).  It is not obvious how to do it in Sicstus, so
%       the interpreted program cannot define predicates whose names happen to
%       clash with the names of built-ins. Hence in the Sicstus version
%       the only modules that are created are "interpreted" and support.
%
% NOTE (Specific to Eclipse):
%       In order to avoid name conflicts with the numerous built-in predicates
%       of Eclipse, the only thing "interpreted" imports is the module
%       "interface".  The module "interface" is created by the top-level from
%       a declaration of built-ins allowed by the metainterpreter (and provided
%       by the latter in table "is_cuts_ok").  The difficulty is that Eclipse does
%       not allow direct exportation of built-ins: this is called by defining
%       yet another module, called "interface_aux".
%       The exact mechanics are best explained by means of an example:
%
%       1. Let the metainterpreter contain a declaration of only one built-in:
%             is_cuts_ok( writeln( _ ) ).
%
%       2. The top level will add the following clause to module
%          "interface_aux" (which imports all the built-ins by default):
%             xxx_writeln( X ) :-  writeln( X ).
%
%       3. "xxx_writeln/1" will be exported by "interface_aux".
%
%       4. Module "interface" will import only "interface_aux", and will be
%          closed to default importation of built-ins.  It will define clause:
%             writeln( X) :- xxx_writeln( X ).
%
%       5. "writeln/1" is now a user-defined predicate and can be exported from
%          "interface".
%
%       6. "interpreted" will import only "interface", and will be closed to
%          default importation of built-ins.  The interpreted program can use
%          "writeln/1" and no other built-ins.  It can also define predicates
%          whose names would normally clash with names of built-ins (e.g.,
%          "connect/2", which might be useful in, say, a graph-processing
%          application).
%
%       Please note that all this does not apply to "support".

% erase_modules:
% Erase the modules that might be there after interpreting the previous
% program.

erase_modules :-
        erase_module( interpreted ),
        erase_module( support ),
        (
            lp_system( eclipse )
        ->
            erase_module( interface ),
            erase_module( interface_aux )
        ;
            true
        ).


% create_modules:
% Create the modules.
% (In Sicstus this is a no-op: the module "interpreted" will be created
%  dynamically with the first assertion.)

/*
create_modules :-
        \+ lp_system( eclipse ),
        !.
create_modules :-
        lp_system( eclipse ),
        create_module( interface_aux ),
        create_module( interface  , [], [ interface_aux ] ),
        create_module( interpreted, [], [ interface     ] ),
        create_module( support ),
        fill_interface_modules.
%
fill_interface_modules :-
        is_cuts_ok( Pattern ),
        functor( Pattern, F, K ),
        concat_atoms( 'xxx_', F, ExtF ),
        mk_pattern( ExtF, K, ExtPattern ),
        ExtPattern =.. [ _ | Args ],
        Pattern    =.. [ _ | Args ],     % i.e., unify arguments of the patterns
        assertz_in_module( interface_aux, (ExtPattern :- Pattern) ),
        assertz_in_module( interface,     (Pattern :- ExtPattern) ),
        export_from_module( interface_aux, ExtF / K ),
        export_from_module( interface    , F    / K ),
        fail.

fill_interface_modules.
*/




% process_file( +file name ):
% Load a program from this file, processing directives and queries.

% :- mode process_file( +).

process_file( FileName ) :-
        open_the_file( FileName, ProgStream ),
        process_input( ProgStream ),
        stream_property(ProgStream,file_name(FN)),
        load_files(FN,[derived_from(FN),register(true),stream(ProgStream)]),
        close( ProgStream ).

%

open_the_file( FileName, ProgStream ) :- absolute_file_name( FileName, AFN ),!, open( AFN, read, ProgStream ).
open_the_file( FileName, ProgStream ) :-   
        ensure_filename_is_an_atom( FileName ),
        name_chars( FileName, FileNameChars ),
        (
            default_extension( Ext ),             % provided by metainterpreter?
            name_chars( Ext, ExtChars ),
            !
        ;
            ExtChars = []
        ),
        ensure_extension( FileNameChars, ExtChars, _, FullFileNameChars ),
        name_chars( FullFileName, FullFileNameChars ),
        open( FullFileName, read, ProgStream ).



% process_input( +input stream ):
% Read the stream, processing directives and queries and storing clauses.

% :- mode process_input( +).

process_input( ProgStream ) :-
        repeat,
        readvar( ProgStream, Term, VarDict ),
        preliminary_processing( Term, VarDict, NewTerm, NewVarDict ),
        process_term( NewTerm, NewVarDict ),
        NewTerm = end_of_file,              % i.e., normally fail to repeat
        !.

%
preliminary_processing( Term, VarDict, NewTerm, NewVarDict ) :-
        expand_term( Term, NewTerm ),
        expand_variable_dictionary( NewTerm, VarDict, NewVarDict ),
        verify_program_item( NewTerm, NewVarDict ).




% process_term( +term, +variable dictionary ):
% Process a term, which should be a directive, a query, a program clause or
% end_of_file.
% The variable dictionary is used for printing out the results of a query.
%
% NOTE: The superficial correctness of this term as a program item has already
%       been verified by "verify_program_item/2".

% :- mode process_term( +, +).

process_term( end_of_file, _ ) :-  !.            % just ignore this

process_term( (:- [ H | T ]), _ ) :-             % include
        !,
        include_files( [ H | T ] ).

process_term( (:- op( P, F, Ops )), _ ) :-
        !,
        op( P, F, Ops ).

process_term( (:- Directive), _ ) :-
        !,
        process_directive( Directive ).

process_term( (?- Query), VarDict ) :-
        !,
        process_dra_call( Query, VarDict ),
        !.                                            % no alternative solutions

process_term( Clause, VarDict ) :-
        get_clause_head( Clause, Head ),
        hook_predicate( Head ),               % metainterpreter's hook predicate
        !,
        check_not_builtin( Clause, VarDict ),      % fatal if redefining is_cuts_ok
        contiguity_dra_check( Clause ),
        asserta( Clause ).

process_term( Clause, VarDict ) :-
        check_not_builtin( Clause, VarDict ),      % fatal if redefining is_cuts_ok
        ensure_dynamic( Clause ),
        contiguity_dra_check( Clause ),
        assertz_in_module( interpreted, Clause ).


% include_files( +list of file names ):
% Process the files whose names are in the list.

% :- mode include_files( +).

include_files( List ) :-
        member( FileName, List ),
        process_file( FileName ),
        fail.

include_files( _ ).


% contiguity_dra_check( +clause ):
% Make sure that each predicate that is defined by a clause is stored in the
% table "defined/1".
% If the clause adds to the definition of a predicate that is present in
% the table but is not the most recent entry (i.e., is not the predicate
% defined by the previous clause), then issue a warning about non-contiguous
% definitions.

contiguity_dra_check( Clause ) :-
        get_clause_head( Clause, Head ),
        most_general_instance( Head, Pattern ),
        (
            once( is_defined( P ) ),  P = Pattern    % predicate as in last clause?
        ->
            true
        ;
            \+ is_defined( Pattern )
        ->
            asserta( is_defined( Pattern ) )
        ;
            functor( Pattern, P, K ),
            warning( [ 'Non-contiguous declaration of ', P/K ] )
        ).





% ensure_dynamic( +clause ):
% Make sure the predicate of this clause is dynamic.
% is_known/1 is used to avoid multiple declarations.
% (NOTE: This is specific to Eclipse.)

% :- mode ensure_dynamic( +).

ensure_dynamic( Clause ) :-
        lp_system( eclipse ),
        get_clause_head( Clause, Head ),
        \+ is_known( Head ),
        most_general_instance( Head, Pattern ),
        assert( is_known( Pattern ) ),
        functor( Head, PredicateName, Arity ),
        dynamic_in_module( interpreted, PredicateName / Arity ),
        fail.

ensure_dynamic( _ ).



% process_directive( +directive ):
% Process a directive.

:- module_transparent(process_directive/1).

% :- mode process_directive( +).

process_directive( (topl all) ) :-
        !,
        assert( is_topl( _ ) ).

process_directive( (topl PredSpecs) ) :-
        !,
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( is_topl( Pattern ) ),
            fail
        ;
            true
        ).

process_directive( (support PredSpecs) ) :-      % store in "support" table
        !,
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( is_support( Pattern ) ),
            fail
        ;
            true
        ).

process_directive( (load_support FileName) ) :-  % compile into module "support"
        !, compile_to_module( support, FileName ).

process_directive( Directive ) :-
        legal_directive( Directive ),            % provided by a metainterpreter
        !,
        execute_directive( Directive ).          % provided by a metainterpreter

process_directive( Directive ) :-                % unsupported directive
        % \+ legal_directive( Directive ),
        !,
        error( lines( [ 'Unknown directive:', [ (:- Directive), '.' ] ] ) ).


% process_dra_call( +query, +variable dictionary ):
% Process a query, i.e., produce and display solutions until
% no more can be found.

% :- mode process_dra_call( +, +).

process_dra_call( Query, VarDict ) :-
        std_trace_stream( Output ),
        write( Output, '-- Query: ' ),
        write( Output, Query ),
        writeln( Output, '.  --' ),
        execute_dra_call( Query, Result ),
        show_result( Result, VarDict ),
        nl( Output ),
        Result = no.                             % i.e., backtrack if 'yes'.

%
% :- mode execute_dra_call( +, +).

execute_dra_call( Query, yes ) :-
        dra_call( Query ).                          % provided by a metainterpreter

execute_dra_call( _, no ).


% show_result( +yes or no, +variable dictionary ).
% Write the bindings and "Yes", or just "No".
% NOTE: the newline is not written here, as it is not wanted in top/0.

% :- mode show_result( +, +).

show_result( yes, VarDict ) :-
        !,
        std_output_stream( Output ),
        show_bindings( VarDict ),
        write( Output, 'Yes'+VarDict ).

show_result( no, _ ) :-
        std_output_stream( Output ),
        write( Output, 'No' ).


% show_bindings( +variable dictionary ):
% Use the variable dictionary to show the results of a query.
% (Recall that the variable dictionary is in Eclipse format.)
% This version uses Ronald de Haan's equation generator
% (see output_equations.pl) to display cyclic terms.

% :- mode show_bindings( +).

% OLD VERSION:
% show_bindings( Dict ) :-
%         std_trace_stream( Output ),
%         print_depth( MaxDepth ),
%         member( [ Name | Var ], Dict ),
%         write( Output, Name ),
%         write( Output, ' = ' ),
%         write_shallow( Output, Var, MaxDepth ),
%         nl( Output ),
%         fail.
%
% show_bindings( _ ).

show_bindings( VarDict ) :-
        extract_vars_from_dict( VarDict, TopTerms ),  % instantiations, actually
        Parcel =.. [ '_parcel' | TopTerms ],          % a term with top "vars"
        get_equation( Parcel, Equations ),
        get_equation_with_variables( Equations, EquationList, HeadVar ),
        most_general_instance( Parcel, ParcelPattern ),
        remove( _ = ParcelPattern, EquationList, EquationListSansParcel ),
        % The above has instantiated ParcelPattern so that its arguments are now
        % the new versions of the instantiations of top variables: we must now
        % replace the old versions with the new ones:
        ParcelPattern =.. [ _ | NewTopTerms ],
        swap_terms( VarDict, NewTopTerms, NewVarDict ),
        % A variable dictionary for the new variables:
        mk_variable_dictionary( p( HeadVar, EquationListSansParcel ), AuxVarDict
                              ),
        % Create equations for the top variables:
        dra_maplist2( mk_eq, NewVarDict, TopEqs ),
        % Bind all uninstantiated variables to their names:
        bind_free_variables_to_names( NewVarDict ),         % names in dra_call
        bind_free_variables_to_names( AuxVarDict ),         % names for new vars
        % A unified list of all the equations:
        append( TopEqs, EquationListSansParcel, AllEquations ),
        % We don't want equation of the form  "V = V":
        filter( non_trivial_eq, AllEquations, NontrivialEquations ),
        % Sort by variable name:
        sort( NontrivialEquations, SortedEquations ),
        std_trace_stream( Output ),
        show_equations( SortedEquations, Output ),
        fail.              % We must undo all the bindings that we created here!

show_bindings( _ ).


%
swap_terms( [], [], [] ).

swap_terms( [ [ Name | _OldTerm ] | Pairs    ], [ NewTerm | NewTerms ],
            [ [ Name | NewTerm ]  | NewPairs ]
          ) :-
        swap_terms( Pairs, NewTerms, NewPairs ).


%
mk_eq( [ Name | Term ], Name = Term ).


%
non_trivial_eq( A = B ) :-  A \= B .


%
show_equations( Equations, Output ) :-
        member( Name = Term, Equations ),
        write( Output, Name ),
        write( Output, ' = ' ),
        write( Output, Term ),
        nl( Output ),
        fail.

show_equations( _, _ ).


% check_not_builtin( +clause, +variable dictionary ):
% Raise a fatal error if this clause attempts to redefine a built-in predicate.

check_not_builtin( Clause, VarDict ) :-
        get_clause_head( Clause, Head ),
        (
            lp_system( eclipse )
        ->
            is_cuts_ok( Head )     % recall that in Eclipse we hid other built-ins
        ;
            cuts_ok( Head )
        ),
        !,
        bind_variables_to_names( VarDict ),
        error( lines( [ 'An attempt to redefine a built-in predicate:',
                        [ Clause, '.' ]
                      ]
                    )
             ).

check_not_builtin( _, _ ).



% top:
% Interactive mode.  Each term that is not a directive or a query is treated
% as an abbreviated query.  After displaying the results of each query read
% characters upto the nearest newline: if the first character is ";",
% backtrack to find alternative solutions.
% Exit upon encountering end of file.
% NOTE: When running on Sicstus, each term must come on a separate line: after
%       reading the term the rest of the line is ignored, to facilitate
%       interaction with the user when asking whether more answers are needed.

old_top :-
        std_input_stream( Input ),
        std_trace_stream( Output ),
        repeat,
        (
            lp_system( eclipse )
        ->
            write( Output, ': ' )                    % a prompt
        ;
            true
        ),
        readvar( Input, Term, VarDict ),
        (
            lp_system( sicstus )
        ->
            getline( Input, _ )                      % skip the rest of the line
        ;
            true
        ),
        bare_to_dra_call( Term, NTerm ),
        verify_program_item( NTerm, VarDict ),
        interactive_term( NTerm, VarDict ),
        ( NTerm = end_of_file ; NTerm = quit ),      % i.e., normally fails
        !.


% bare_to_dra_call( +term, - term ):
% A term that is not end_of_file, quit, a directive, or a query is
% translated to a query.  (So, for example, there will be no check for
% singleton variables.)

bare_to_dra_call( Term, Term ) :-
        (
            Term = end_of_file
        ;
            Term = quit
        ;
            Term = (:- _)
        ;
            Term = (?- _)
        ),
        !.

bare_to_dra_call( Bare, (?- Bare) ).


% interactive_term( +term, +variable dictionary ):
% Process a term in interactive mode.
% The variable dictionary is used for printing out the results of a query.

% :- mode interactive_term( +, +).

interactive_term( end_of_file, _ ) :-  !.              % just ignore this

interactive_term( quit       , _ ) :-  !.              % just ignore this

interactive_term( (:- [ H | T ]), _ ) :-               % include
        !,
        include_files( [ H | T ] ).

interactive_term( (:- Directive), _ ) :-               % directive
        !,
        process_directive( Directive ).

interactive_term( (?- Query), VarDict ) :-             % dra_call
        iq( Query, VarDict ).


iq( Query ) :- term_variables(Query , VarDict), iq( Query, VarDict ).
iq( Query, VarDict ) :-
        !,
        execute_dra_call( Query, Result ),
        show_result( Result, VarDict ),
        satisfied_with_dra_call( Result ),                % or backtrack to retry
        !.


% satisfied_with_dra_call( +answer ):
% Give the user a chance to type ";" if the answer is "yes".

% :- mode satisfied_with_dra_call( +).

satisfied_with_dra_call( yes ) :-
        std_output_stream( Output ),
        flush_output( Output ),
        user_accepts,
        !.

satisfied_with_dra_call( no ) :-
        std_output_stream( Output ),
        nl( Output ),
        flush_output( Output ).


% user_accepts:
% Read input upto the nearest newline.
% If the first character is a semicolon, fail.

user_accepts :-
        std_input_stream( Input ),
        std_trace_stream( Output ),
        write( Output, '  (more?) ' ),
        flush_output( Output ),
        getline( Input, Line ),
        Line \= [ ';' | _ ].             % i.e., fail if 1st char is a semicolon

%------------------------------------------------------------------------------

%  Built-in predicates for the "dra" interpreter  %

% If the interpreted program invokes a built-in predicate, that predicate dra_must
% be declared in the table "cuts_ok/1" below.
% Every addition should be considered carefully: some built-ins might require
% special treatment by the interpreter.

%  NOTE: findall/3 is not opaque to coinductive and tabled ancestors.

%  NOTE: Just adding "!" won't do the trick, the main interpreter would
%        have to be modified substantially (but first: what are the semantics?)

:-dynamic(cuts_ok/1).
:-dynamic(is_not_builtin/1).


%cuts_ok( (_ -> _)           ).  % special treatment in dra_interp/4
%cuts_ok( (_ -> _ ; _)       ).  % special treatment in dra_interp/4
%cuts_ok( \+ ( _ )            ).  % special treatment in dra_interp/4

cuts_ok(Pred):- is_not_builtin(Pred),!,fail.
cuts_ok(Pred):- is_builtin0(Pred),asserta(cuts_ok(Pred)),!.
cuts_ok(Pred):- functor(Pred,F,A),functor(TPred,F,A),asserta(is_not_builtin(TPred)),!,fail.

is_builtin0(Pred) :- is_swi_builtin( Pred ).
is_builtin0(Pred) :- functor(Pred,F,_),atom_concat('$',_,F).
is_builtin0(Pred) :- source_file(Pred,File),is_file_meta(File,cuts_ok), \+ clause(is_tabled(Pred),true).


%


%  The "set of coinductive hypotheses" for the "dra" interpreter.          %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (March 2009)           .              %
%                                                                          %
%  Last update: 12 June 2009.                                              %
%                                                                          %

% The "set of coinductive hypotheses" contains those ancestors of the current
% goal that invoke coinductive predicates. It is used by dra_interp/4, and factored
% out as an abstract data type to facilitate changing to a more efficient
% representation.
%
% The requirements are as follows:
%
%       (a) We must be able to check whether a coinductive goal G can be
%           unified with one of its ancestors.
%
%       (b) Ancestors that might be unifiable with G must be available in
%           reverse chronological order (i.e., the nearest ancestor first).
%
%       NOTE: Before checking for unifiability the goals must be passed
%             through essence_hook/2.
%
%
% The operations are:
%
%    empty_hypotheses( - stack of hypotheses ):
%         Create an empty stack for coinductive hypotheses.
%
%    push_is_coinductive0( +goal, +stack of hypotheses , - new stack ):
%         Push the coinductive goal onto the stack.
%
%    unify_with_coinductive_ancestor( +goal, +stack of hypotheses ):
%         Fail if there is no unifiable coinductive ancestor on the stack. If
%         there is one, succeed after performing the unification with the
%         most recent such ancestor.  Upon failure undo the unification and
%         unify with the next such ancestor, and so on (in reverse
%         chronological order), failing after all unifiable ancestors are
%         exhausted.


% %--------------  The minimal implementation:  --------------%
% %
% % The set of coinductive hypotheses is just a list.
%
% % :- mode empty_hypotheses( - ).
%
% empty_hypotheses( [] ).
%
%
% % :- mode push_is_coinductive0( +, +, - ).
%
% push_is_coinductive0( Goal, Hyp, [ Goal | Hyp ] ).
%
%
% % :- mode unify_with_coinductive_ancestor( +, +).
%
% unify_with_coinductive_ancestor( Goal, Hyp ) :-
%         once( essence_hook( Goal, Essence ) ),
%         member( G, Hyp ),
%         once( essence_hook( G, Essence ) ).


%--------------  An implementation that uses goal_table:  --------------%

%:- ensure_loaded( 'goal_table_in_tree' ).
%

%  A goal table implemented by a binary tree with lists.                   %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (February 2009).                      %
%                                                                          %
%  Last update: 16 May 2009.                                               %
%                                                                          %


% :- ensure_loaded( goal_table_in_open_tree ).
% end_of_file.

%:- ensure_loaded( utilities ).
%:- ensure_loaded( higher_order ).
%:- ensure_loaded( tree ).
%

%  Operations on binary trees.                                             %
%                                                                          %
%  This particular version                                                 %
%   written by Feliks Kluzniak at UTD (May 2009).                          %
%                                                                          %
%  Last update: 16 May 2009.                                               %
%                                                                          %

%:- ensure_loaded( higher_order ).


%
%  The format of a node is:
%       t( key, information, left subtree, right subtree )
%  or
%       empty.


%------------------------------------------------------------------------------
% empty_otree( +- tree ):
% Create an empty tree, or check that the provided tree is empty.

empty_tree( empty ).


%------------------------------------------------------------------------------
% is_in_tree( +tree, +key, +comparison predicate, - information ):
% If the entry for this key is present in the tree, succeed and return the
% associated information; if it is not, fail.
% "comparison predicate" is a binary predicate that succeeds if the first
% argument is smaller than the second argument.  Any predicate that implements
% a total ordering will do.

is_in_tree( Node, Key, LessPred, Info ) :-
        Node = t( K, I, L, R ),
        (
            Key = K
        ->
            Info = I
        ;
            apply( LessPred, [ Key, K ] )
        ->
            is_in_tree( L, Key, LessPred, Info )
        ;
            is_in_tree( R, Key, LessPred, Info )
        ).


%------------------------------------------------------------------------------
% tree_add( +tree,
%           +key,
%           +information,
%           +comparison predicate,
%           +modification predicate,
%           - new tree
%         ):
% Make sure that the key is associated with this information in the tree.
% If the entry for this key is already present, modify the existing
% information.
% "less predicate" is the name of a binary predicate that succeeds if the first
% argument is smaller than the second argument.
% "modification predicate" is a predicate of three arguments that will add
% information from its second argument to its first argument, thus obtaining
% the third argument.

tree_add( Node, Key, Info, LessPred, ModifyPred, NewNode ) :-
        (
            empty_tree( Node )
        ->
            NewNode = t( Key, Info, L, R ),
            empty_tree( L ),
            empty_tree( R )
        ;
            Node = t( K, I, L, R ),
            (
                Key = K
            ->
                apply( ModifyPred, [ I, Info, NewI ] ),
                NewNode = t( K, NewI, L, R )
            ;
                apply( LessPred, [ Key, K ] )
            ->
                NewNode = t( Key, I, NewL, R ),
                tree_add( L, Key, Info, LessPred, ModifyPred, NewL )
            ;
                NewNode = t( Key, I, L, NewR ),
                tree_add( R, Key, Info, LessPred, ModifyPred, NewR )
            )
        ).

%------------------------------------------------------------------------------


% In this implementation the goal table is a binary tree.
% Each key is a predicate specification.
% The information associated with a key is a list of goals
% that invoke the predicate specified by the key.


%------------------------------------------------------------------------------
% empty_goal_table( +- goal table ):
% Create an empty goal table, or check that the provided table is empty.

empty_goal_table( Table ) :-
        empty_tree( Table ).


%------------------------------------------------------------------------------
% goal_table_member( +goal, +goal table ):
% Check whether any instantiations of the goal are in the table: if there are,
% unify the goal with the first one (backtracking will unify it with each of
% them in turn).
%
% NOTE: Using essence hook before comparison!

goal_table_member( Goal, Table ) :-
        functor( Goal, P, K ),
        is_in_tree( Table, P / K, '@<', List ),
        once( essence_hook( Goal, Essence ) ),
        member_reversed( G, List ),
        once( essence_hook( G, Essence ) ).


%------------------------------------------------------------------------------
% is_a_variant_in_goal_table( +goal, +goal table ):
% Succeed iff a variant of this goal is present in the table.
% Do not modify the goal.
%
% NOTE: Using essence hook before comparison!

is_a_variant_in_goal_table( Goal, Table ) :-
        once( essence_hook( Goal, GoalEssence ) ),
        functor( Goal, P, K ),
        is_in_tree( Table, P / K, '@<', List ),
        member_reversed( Member, List ),
        once( essence_hook( Member, MemberEssence ) ),
        are_variants( MemberEssence, GoalEssence ),
        !.


%------------------------------------------------------------------------------
% goal_table_add( +goal table, +goal, - new goal table ):
% Add this goal to the table.

goal_table_add( Table, Goal, NewTable ) :-
        functor( Goal, P, K ),
        tree_add( Table, P / K, [ Goal ], '@<', add_to_list, NewTable ).

%
add_to_list( List, [ Item ], [ Item | List ] ).

%------------------------------------------------------------------------------



% :- mode empty_hypotheses( - ).

empty_hypotheses( Hyp ) :-
        empty_goal_table( Hyp ).


% :- mode push_is_coinductive0( +, +, - ).

push_is_coinductive0( Goal, Hyp, NewHyp ) :-
        goal_table_add( Hyp, Goal, NewHyp ).


% :- mode unify_with_coinductive_ancestor( +, +).

unify_with_coinductive_ancestor( Goal, Hyp ) :-
        goal_table_member( Goal, Hyp ).

%------------------------------------------------------------------------------


%

%  The "stack" data type for the "dra" interpreter.                        %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (March 2009)           .              %
%                                                                          %
%  Last update: 12 June 2009.                                              %
%                                                                          %

% The "stack" is the chain of tabled ancestors used by dra_interp/4.  It is
% factored out as an abstract data type to facilitate changing to a more
% efficient representation.
%
% The requirements are as follows:
%
%       (a) It must be possible to check whether a tabled goal G and one of
%           its ancestors are variants. There can be at most one such
%           ancestor, call it A.
%
%       (b) We must be able to identify the "current clause" that was used by
%           A and that led to the creation of G.
%
%       (c) We must be able to identify all the tabled goals that are
%           descendants of A and ancestors of G (i.e., all tabled goals
%           "between" G and A).
%
%       NOTE: Before checking for variance the goals must be passed
%             through essence_hook/2.
%
%
% Information about an ancestor goal is kept in the form of a triple:
%    triple( goal, index, clause )
% where
%    goal    is the (current instantiation of the) goal;
%    index   is the unique index of the goal;
%    clause  is the clause that is currently used by the goal (it has been
%               instantiated by matching with the goal in its original form,
%               but does not share variables with the goal).
%
%
% The operations are:
%
%    empty_stack( - stack ):
%            Create an empty stack.
%
%    push_is_tabled( +goal, +index, +clause, +stack, - new stack ):
%            where the first three arguments are the constitutive elements of
%            a triple.
%            Push the triple goal onto the stack.
%
%    is_variant_of_ancestor( +goal,
%                            +stack,
%                            - the triple with the variant ancestor,
%                            - goals between goal and the variant ancestor
%                          )
%         Succeed if the tabled goal is a variant of some goal in the stack.
%         If successful, return the first such member and the list of
%         intervening triples.


% %--------------  The minimal implementation:  --------------%
% %
% % The stack is just a list of triples.
%
% % :- mode empty_stack( - ).
%
% empty_stack( [] ).
%
%
% % :- mode push_is_tabled( +, +, +, +, - ).
%
% push_is_tabled( Goal, PGIndex, Clause, Stack,
%              [ triple( Goal, PGIndex, Clause ) | Stack ]
%            ).
%
%
% % :- mode is_variant_of_ancestor( +, +, -, - ).
%
% is_variant_of_ancestor( Goal, Stack, AncestorTriple, Prefix ) :-
%         append( Prefix, [ AncestorTriple | _ ], Stack ),      % split the list
%         AncestorTriple = triple( G, _, _ ),
%         are_essences_variants( Goal, G ),
%         !.


%--------------  An implementation that uses goal_table:  --------------%
%
% The goal table is used to speed up the check whether there is a variant
% ancestor.  We still need a standard stack for getting the intermediate tabled
% goals.  So the "stack" is represented by
%    tstack( stack, goal table )


%:- ensure_loaded( 'goal_table_in_tree' ).


% :- mode empty_stack( - ).

empty_stack( tstack( [], Table ) ) :-
        empty_goal_table( Table ).


% :- mode push_is_tabled( +, +, +, +, - ).

push_is_tabled( Goal, PGIndex, Clause, tstack( Stack, Table ),
             tstack( [ triple( Goal, PGIndex, Clause ) | Stack ], NewTable )
           ) :-
        goal_table_add( Table, Goal, NewTable ).


% :- mode is_variant_of_ancestor( +, +, -, - ).

is_variant_of_ancestor( Goal,
                        tstack( Stack, Table ),
                        AncestorTriple,
                        Prefix
                      ) :-
        is_a_variant_in_goal_table( Goal, Table ),           % preliminary check
        append( Prefix, [ AncestorTriple | _ ], Stack ),     % split the list
        AncestorTriple = triple( G, _, _ ),
        are_essences_variants( Goal, G ),
        !.

%------------------------------------------------------------------------------

% If a file name has no extension, add ".tlp"

default_extension( '.tlp' ).                              % invoked by top_level


% Initialization of tables:

:- dynamic (is_coinductive0)/1 .
:- dynamic (is_coinductive1)/1 .
:- dynamic (is_tabled)/1 .
:- dynamic (is_old_first)/1 .
:- dynamic pioneer/3 .
:- dynamic result/2 .
:- dynamic loop/2 .
:- dynamic looping_alternative/2 .
:- dynamic completed/2 .
:- dynamic is_tracing/1.

:- dra_setval_flag( number_of_answers, 0 ).
:- dra_setval_flag( unique_index,      0 ).

initialise :-                                             % invoked by top_level
   dra_must((
        reinitialise_answer,
        reinitialise_result,
        reinitialise_pioneer,
        reinitialise_loop,
        reinitialise_looping_alternative,
        reinitialise_completed,
        retractall( is_coinductive0( _ )  ),
        retractall( is_coinductive1( _ ) ),
        retractall( is_tabled( _ )       ),
        retractall( is_old_first( _ )    ),
        retractall( is_tracing( _ )      ),
        dra_setval_flag( number_of_answers, 0 ),
        dra_setval_flag( unique_index,      0 ),
        dra_setval_flag( step_counter,      0 ),
        dra_setval_flag( old_table_size,    0 ))),
        dra_must((dra_version( Version ),
        writeln( Version ))),!.


% Checking consistency:

program_loaded :-                                         % invoked by top_level
        check_consistency.


% check_consistency:
% Produce a warning if predicates were declared but not defined (this may well
% be due to a "tabled" directive giving the wrong arity), or if tabled/
% coinductive predicates have been declared as "suppport".

check_consistency :-
        is_tabled( Head ),
        nonvar( Head ),
        functor( Head, P, K ),
        \+ current_predicate_in_module( interpreted, P / K ),
        warning( [ P/K, ' declared as tabled, but not defined' ] ),
        fail.

check_consistency :-
        is_coinductive1( Head ),
        nonvar( Head ),
        functor( Head, P, K ),
        \+ current_predicate_in_module( interpreted, P / K ),
        warning( [ P/K, ' declared as coinductive, but not defined' ] ),
        fail.

check_consistency :-
        is_support( Head ),
        is_tabled( Head ),
        functor( Head, P, K ),
        warning( [ P/K, ' declared as both tabled and \"support\"' ] ),
        fail.

check_consistency :-
        is_support( Head ),
        is_coinductive1( Head ),
        functor( Head, P, K ),
        warning( [ P/K, ' declared as both coinductive and \"support\"' ] ),
        fail.

check_consistency.



%  Hooks

% Declarations of hook predicates (for the top level):

hook_predicate( essence_hook( _, _ ) ).


% The default essence_hook:

:- dynamic essence_hook/2.

essence_hook( T, T ).    % default, may be overridden by the interpreted program




%  Administration  %

:- op( 1010, fy, coinductive0  ).    % allow  ":- coinductive0 p/k ."
:- op( 1010, fy, coinductive1 ).    % allow  ":- coinductive1 p/k ."
:- op( 1010, fy, user:table       ).    % allow  ":- table p/k ."
:- op( 1010, fy, old_first    ).    % allow  ":- old_first p/k ."
:- op( 1010, fy, traces        ).    % allow  ":- traces  p/k ."
:- op( 1010, fy, multifile    ).    % allow  ":- multifile  p/k ." (for Eclipse)
:- op( 1010, fy, hilog    ).    % allow  ":- hilog  p/k ."
:- op( 910,  fy, tnot    ).    % allow  ":- hilog  p/k ."



% The legal directives (check external form only).  (Used by the top level.)


legal_directive((coinductive( _))  ).
legal_directive( (coinductive0 _)  ).
legal_directive( (coinductive1 _) ).
legal_directive( (table _)       ).
legal_directive( (traces _)        ).
legal_directive( (dynamic _)      ).
legal_directive( (old_first _)    ).
legal_directive( (multifile _)    ).
legal_directive( answers( _, _ )  ).
legal_directive( answers          ).
legal_directive((call( _))  ).
legal_directive((hilog( _))  ).

% SWI=Prolog
legal_directive( trace ).
legal_directive( notrace ).

legal_directive(M:P):-atom(M),M:legal_directive(P).

legal_directive(P):-compound(P),functor(P,F,1),property_pred(F,_).


fresh_multifile(X):- current_module(M), dra_must(M \= user), asserta_new( ((user:X) :- (M:X))).

% Check and process the legal directives (invoked by top_level)

source_context(F):- prolog_load_context(source,F).

:- module_transparent(execute_directive/1).
execute_directive( answers( Goal, Pattern ) ) :-
        print_required_answers( Goal, Pattern ).

execute_directive( Dir ) :- property_pred(F,DBF), Dir=..[F,all],DB=..[DBF,_],
        !, once((source_context(F),add_file_meta(F,DBF));asserta_new( DB:-! )).
execute_directive( Dir ) :- property_pred(F,DBF), (Dir=..[F,none];Dir=..[F,-all]),DB=..[DBF,_],
        !, once((source_context(F),retract_all0(is_file_meta(F,DBF)));(retract_all0( DB ),retract_all0( DB :- ! ))).
execute_directive( (traces all) ) :-
        !,
        will_trace( [ _ ] ).
execute_directive( (traces PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        will_trace( Patterns ).
execute_directive( Dir ) :-
        property_pred(F,DBF), 
        Dir=..[F,PredSpecs],
        trace,
        predspecs_to_patterns( PredSpecs, Patterns ),!,
        add_patterns(Patterns,DBF).


execute_directive( (table PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        (   member( Pattern, Patterns ),
            dra_meta(Pattern),
            set_meta(Pattern,is_tabled),
            asserta_new( is_tabled( Pattern ) ),
            functor(Pattern,F,A),
            %discontiguous(F/A),
            dynamic(F/A),            
            fail
        ;
            true
        ).

execute_directive( (coinductive0 all) ) :-
        !,
        asserta_new( is_coinductive1( _ ) ),
        asserta_new( is_coinductive0( _ ) ).

execute_directive( (coinductive0 PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            asserta_new( is_coinductive1( Pattern ) ),
            asserta_new( is_coinductive0( Pattern ) ),
            fail
        ;
            true
        ).





add_patterns([],_):-!.
add_patterns([P|Patterns],DBF):- add_pattern(P,DBF),!,add_patterns(Patterns,DBF).

add_pattern(Pattern, - DBF):- DB=..[DBF,Pattern],retract_all0( DB ).
add_pattern(Pattern, + DBF):- !, add_pattern(Pattern, DBF).
add_pattern(Pattern,DBF):- DB=..[DBF,Pattern],
        set_meta0(Pattern,DBF),
        asserta_new( DB ),!.


% will_trace( +list of patterns ):
% Store the patterns in tracing/1:

will_trace( Patterns ) :-
        member( Pattern, Patterns ),
        asserta_new( is_tracing( Pattern ) ),
        fail.

will_trace( _ ).


% print_required_answers( +goal, +pattern ):
% Print the tabled answers that are associated with this goal and are unifiable
% with this pattern.  If the goal is a variable, go through all the entries in
% the table.

print_required_answers( Var, Pattern ) :-
        var( Var ),
        !,
        get_all_tabled_goals( Goals ),
        remove_variants( Goals, DifferentGoals ),
        sort( DifferentGoals, SortedDifferentGoals ),
        (
            member( Goal, SortedDifferentGoals ),      % iterate through members
            print_required_answers( Goal, Pattern ),
            nl,
            fail
        ;
            true
        ).

print_required_answers( Goal, Pattern ) :-
        copy_term( Goal, OriginalGoal ),
        get_answer( Goal ),                            % iterate through answers
        Goal = Pattern,
        mk_variable_dictionary( OriginalGoal +Goal, VarDict ),
        bind_variables_to_names( VarDict ),
        write( OriginalGoal ),  write( ' :  ' ),  writeln( Goal ),
        fail.

print_required_answers( _, _ ).


% remove_variants( +list, - reduced list ):
% Remove each member of the list that is a variant of
% a member that precedes it.  No need to preserve the order.

remove_variants( List, ReducedList ) :-
        remove_variants_( List, [], ReducedList ).

%
remove_variants_( [], Accumulator, Accumulator ).

remove_variants_( [ H | T ], Accumulator, RL ) :-
        member( M, Accumulator ),
        are_variants( H, M ),
        !,
        remove_variants_( T, Accumulator, RL ).

remove_variants_( [ H | T ], Accumulator, RL ) :-
        % H not a variant of a member of Accumulator
        remove_variants_( T, [ H | Accumulator ], RL ).








%
%  The interpreter  %


% Execute a query.

% :- mode dra_call( +).

init_dra_call:-
        reinitialise_pioneer,
        reinitialise_result,
        reinitialise_loop,
        reinitialise_looping_alternative,
        dra_setval_flag( unique_index,      0    ),
        dra_getval_flag( number_of_answers, NAns ),
        dra_setval_flag( old_table_size,    NAns ),
        dra_setval_flag( step_counter,      0    ).

% invoked by VMI/WAM
:-meta_predicate(system:dra_call( : )).
system:dra_call(M: Goals ) :-
      '$dra':dra_must(b_getval('$tabling_exec',dra_state(Stack, Hyp, ValOld, CuttedOut))),
      setup_call_cleanup(
        ((ValOld < 0) -> (( '$dra':init_query,EXIT = exit_dra_call )); (EXIT = cont_dra_call)),
        ((
           % empty_hypotheses( Hyp ),
           % empty_stack( Stack ),            
            Level is ValOld +1,
            '$dra':dra_interp(Cutted, M:Goals, Stack, Hyp, Level ),
            ((var(Cutted);((trace),'$dra':non_cutted(M:Goals,Cutted,(CuttedOut))))->true;(!,fail)),
             '$dra':EXIT)),
       (('$dra':EXIT))).


exit_dra_call:- 
            print_statistics,
            dra_setval_flag( step_counter, 0 ),
            dra_getval_flag( number_of_answers, NAns2 ),
            dra_setval_flag( old_table_size, NAns2 ),
            '$exit_dra'.

cont_dra_call :- 
            print_statistics,
            '$exit_dra'.


% Print information about the number of steps and the answer table.

print_statistics :-
        std_trace_stream( Output ),
        dra_getval_flag( step_counter, NSteps ),
        dra_getval_flag( number_of_answers, NAns ),
        dra_getval_flag( old_table_size, OldNAns ),
        TableGrowth is NAns - OldNAns,
        write(  Output, '[' ),
        write(  Output, NSteps ),
        write(  Output, ' step' ),
        plural( Output, NSteps ),
        write(  Output, ', ' ),
        write(  Output, TableGrowth ),
        write(  Output, ' new answer' ),
        plural( Output, TableGrowth ),
        write(  Output, ' tabled (' ),
        write(  Output, NAns ),
        write(  Output, ' in all)' ),
        write(  Output, ']' ),
        nl(     Output ).

%
plural( _     , 1 ) :-  !.
plural( Output, N ) :-  N \= 1,  write( Output, 's' ).


% dra_interp(Cutted, +sequence of goals,
%        +stack,
%        +coinductive hypotheses,
%        +level
%      ):
% Solve the sequence of goals, maintaining information about the current chain
% of tabled ancestors(stack) and the chain of coinductive0 ancestors
%(coinductive hypotheses).  The level is the level of recursion, and is used
% only for tracing.
%
% Each link in the chain of tabled ancestors is of the form
%    triple( goal, index, clause )
% where
%    goal    is the (current instantiation of the) goal;
%    index   is the unique index of the goal (every goal that is stacked starts
%               out as a pioneer!)
%    clause  is the clause that is currently used by the goal (it has been
%               instantiated by matching with the goal in its original form,
%               but does not share variables with the goal).
%
% NOTE: The set of coinductive hypotheses and the stack of tabled ancestors
%       have been factored out (see files "dra_coinductive_hypotheses.pl" and
%       "dra_stack.pl" 
%       )
%   The representations may have changed (to enable
%       faster access, so the comments in this file ("chain of ancestors" etc.)
%       might no longer be quite accurate. )

:- meta_predicate  dra_interp(+, :, +, +, +).
:- meta_predicate dra_int4meta(+, +, :, +, +, +).
:- meta_predicate dra_int1p(+, +, +, +, +).
:- meta_predicate dra_int2t(+, +, +, +, +).


:- 
  empty_hypotheses( Hyp ),
  empty_stack( Stack ),
  nb_setval('$tabling_exec',dra_state(Stack, Hyp, -1, _CuttedOut)).

% tnot/1 must be ran in meta-interp
tnot(G):-dra_call(tnot(G)).


% simply true.
dra_interp(_ ,     _:true, _, _, _ ) :- !.

% A negation.
dra_interp(Cutted, (_ : (\+ Goal)), Stack, Hyp, Level ) :- assertion(nonvar(Goal)),
        !,
        NLevel is Level +1,
        trace_entry( normal, \+ Goal, '?', Level ),
        (
            \+ dra_interp(Cutted, Goal, Stack, Hyp, NLevel ),
            trace_success( normal, \+ Goal, '?', Level )
        ;
            trace_failure( normal, \+ Goal, '?', Level ),
            fail
        ).


dra_interp(Cutted, (_ : (tnot Goal)) , Stack, Hyp, Level ) :- !, findall(Cutted-Goal,dra_interp(Cutted, Goal , Stack, Hyp, Level ),L),L=[].


% One solution.

dra_interp(Cutted, _M: once( Goal ), Stack, Hyp, Level ) :-
        !,
        NLevel is Level +1,
        trace_entry( normal, once( Goal ), '?', Level ),
        (
            once( dra_interp(Cutted, Goal, Stack, Hyp, NLevel ) ),
            trace_success( normal, once( Goal ), '?', Level )
        ;
            trace_failure( normal, once( Goal ), '?', Level ),
            fail
        ).


% A conditional with an else.

dra_interp(Cutted, _M:(Cond -> Then ; Else), Stack, Hyp, Level ) :- !,
      (  dra_interp(Cutted, Cond, Stack, Hyp, Level ) ->        
        dra_interp(Cutted, Then, Stack, Hyp, Level ) ;
        dra_interp(Cutted, Else, Stack, Hyp, Level )).


% A conditional without an else.

dra_interp(Cutted, _M:(Cond -> Then), Stack, Hyp, Level ) :- !,
        (dra_interp(Cutted, Cond, Stack, Hyp, Level ) -> dra_interp(Cutted, Then, Stack, Hyp, Level )).

dra_interp(Cutted, _M:(GoalsL ; GoalsR), Stack, Hyp, Level ) :- !,
        (dra_interp(Cutted, GoalsL, Stack, Hyp, Level ) ;
         dra_interp(Cutted, GoalsR, Stack, Hyp, Level )).


% A conjunction.

dra_interp(Cutted, _M:(Goals1 , Goals2), Stack, Hyp, Level ) :-
        !,
        dra_interp(Cutted, Goals1, Stack, Hyp, Level ),
        dra_interp(Cutted, Goals2, Stack, Hyp, Level ).


% call/1

dra_interp(Cutted, _M:call( Goal ), Stack, Hyp, Level ) :-
        (
            ( var( Goal )                          % e.g., Eclipse
            ; Goal = interpreted : V,  var( V )    % e.g., Sicstus
            )
        ->
            error( [ 'A variable meta-call: ', call( Goal ) ] )
        ;
            dra_interp(Cutted, Goal, Stack, Hyp, Level )
        ).



% findall/3: note that this is not opaque to coinductive and tabled ancestors!

dra_interp(Cutted, _M:findall( Template, Goal, Bag ), Stack, Hyp, Level ) :-
        !,
        NLevel is Level +1,
        (
            % Sicstus prefixes the second argument of findall with the module
            % name, but it does not do that for nested findall...
            lp_system( sicstus ),
            Goal = interpreted: G
        ->
            true
        ;
            G = Goal
        ),
        findall( Template, dra_interp(Cutted, G, Stack, Hyp, NLevel ), Bag ).

dra_interp(Cutted, _:!, _, _, _ ) :- !, (var(Cutted);Cutted=cut).
dra_interp(Cutted, _:!(Where), _, _, _ ) :- !, (var(Cutted);Cutted=cut_to(Where)).

% Some other supported built-in.


dra_interp(CuttedOut, M:Goal, Stack, Hyp,  Level ):-     
    is_pred_metainterp(Goal,Meta), !, dra_int4meta(Meta, CuttedOut, M:Goal, Stack, Hyp,  Level ).


dra_int4meta(Meta, CuttedOut, M:BuiltIn, Stack, Hyp,  Level ):-
        arg(_,cuts_ok;is_support,Meta),
        !,
        nb_setval('$tabling_exec',dra_state(Stack, Hyp, Level, Cutted)),
        incval( step_counter ),
        clause_module(M:BuiltIn,CM),!,
        call(CM: BuiltIn ),        
        ((var(Cutted);(trace,non_cutted(BuiltIn,Cutted, CuttedOut)))->true;(!,fail)). 

dra_int4meta(Meta,CuttedOut, M:Goal, Stack, Hyp,  Level ):- 
   arg(_,is_tabled;is_coinductive1,Meta),!,
  dra_int2t(Cutted, M:Goal, Stack, Hyp, Level ),
  ((var(Cutted);non_cutted(Goal,Cutted, CuttedOut))->true;(!,fail)).

dra_int4meta(_,CuttedOut, M:Goal, Stack, Hyp,  Level ):- !,  
  dra_int1p(Cutted, M:Goal, Stack, Hyp, Level ),
  ((var(Cutted);non_cutted(Goal,Cutted, CuttedOut))->true;(!,fail)).

dra_int4meta(_ANYMETA,CuttedOut, M:Goal, Stack, Hyp,  Level ):- 
  % Should read the new default
  set_meta(Goal,is_tabled),!,
  dra_int2t(Cutted, M:Goal, Stack, Hyp,  Level ),
  ((var(Cutted);non_cutted(Goal,Cutted, CuttedOut))->true;(!,fail)). 


non_cutted(_,cut,_):-!,fail.
non_cutted(Goal,cut_to(ToGoal),_):- dra_must(nonvar(ToGoal)), Goal=ToGoal, !,fail.
non_cutted(_,Cutted,Cutted).

% A "normal" goal (i.e., not tabled, not coinductive).
dra_int1p(Cutted, M:Goal, Stack, Hyp, Level ):- 
        incval( step_counter ), !,
        trace_entry( normal, Goal, '?', Level ),
        (
            NLevel is Level +1,
            use_clause( M , Goal, Body ),
            dra_interp(Cutted, Body, Stack, Hyp, NLevel ),
            trace_success( normal, Goal, '?', Level )
        ;
            trace_failure( normal, Goal, '?', Level ),
            fail
        ).

% A goal that is coinductive, but not tabled.
% Apply the coinductive hypotheses first, then the clauses.
%
% NOTE: Now that we have both "coinductive0" and "coinductive1" the logic gets a
%       little tricky.  If a goal is not "coinductive2", then it should activate
%       its clauses only if there are no unifiable ancestors (hypotheses). What
%       follows is an attempt to avoid too much duplication of code and
%       redundant invocations of the costly check for unifiable ancestors.

dra_int2t(Cutted, M:Goal, Stack, Hyp, Level ) :-
        \+ is_tabled( Goal ),
        is_coinductive1( Goal ),
        !,
        incval( step_counter ),
        trace_entry( coinductive0, Goal, '?', Level ),
        (
            \+ is_coinductive0( Goal ),
            unify_with_coinductive_ancestor( Goal, Hyp )
        ->
            (
                trace_success( 'coinductive (hypothesis)', Goal, '?', Level )
            ;
                trace_failure( coinductive, Goal, '?', Level ),
                fail
            )
        ;
            % coinductive0, or no unifiable ancestors
            (
                is_coinductive0( Goal ),
                unify_with_coinductive_ancestor( Goal, Hyp ),
                trace_success( 'coinductive0(hypothesis)', Goal, '?', Level )
            ;
                NLevel is Level +1,
                use_clause(M, Goal, Body ),
                push_is_coinductive0( Goal, Hyp, NHyp ),
                dra_interp(Cutted, Body, Stack, NHyp, NLevel ),
                trace_success( 'coinductive (clause)', Goal, '?', Level )
            ;
                trace_failure( coinductive, Goal, '?', Level ),
                fail
            )
        ).



% A tabled goal that has been completed: all the results are in "answer".

dra_int2t(_Cutted, _M:Goal, _, _, Level ) :-
        is_completed( Goal ),
        !,
        incval( step_counter ),
        trace_entry( completed, Goal, '?', Level ),
        (
            get_all_tabled_answers( Goal, '?', completed, Level )
        ;
            trace_failure( completed, Goal, '?', Level ),
            fail
        ).


% A tabled goal that has a variant among its ancestors (and has not been
% completed).
% If the goal is not coinductive, only the existing (most likely incomplete)
% results from "answer" are  returned before failure.
% If the goal is also coinductive, return the results that arise from
% coinductive hypotheses, then the remaining results from "answer".
%
% NOTE: 1. There can be only one variant ancestor, so the question of which one
%          to use does not arise.
%
%       2. Ancestor pioneer goals between this goal and its variant ancestor
%          will lose their status as pioneers (and the associated entries in
%          "loop" and "looping_alternative" will be removed).
%
%       3. If the variant ancestor is a pioneer, then:
%             - the entire prefix of the list of goals upto (but not including)
%               the variant ancestor will be added to the cluster of that
%               ancestor (by storing it in "loop");
%             - a copy of the current clause invoked by the ancestor (which can
%               be found together with the ancestor on the stack) is added to
%               "looping_alternative" entries for that ancestor.
%
%       4. If this goal is coinductive, then we use "result" to avoid
%          duplicating results.

dra_int2t(_Cutted, _M:Goal, Stack, Hyp, Level ) :-
        is_variant_of_ancestor( Goal, Stack,
                                triple( G, I, C ), InterveningTriples
                              ),
        !,
        incval( step_counter ),
        get_unique_index( PGIndex ),
        trace_entry( variant, Goal, PGIndex, Level ),
        % Rescind the status of intervening pioneers:
        suppress_pioneers_on_list( InterveningTriples, Level ),

        % Create a looping alternative if the variant ancestor is a pioneer:
        (
            is_a_variant_of_a_pioneer( G, I )
        ->
            extract_goals( InterveningTriples, InterveningGoals ),
            add_loop( I, InterveningGoals ),
            add_looping_alternative( I, C )
        ;
            true
        ),

        % The main action:
        (
            is_coinductive1( Goal )
        ->
            copy_term( Goal, OriginalGoal ),
            (
                get_tabled_if_old_first( Goal, PGIndex,
                                         'variant (coinductive0)', Level
                                       )
            ;
                % results from coinductive hypotheses:
                unify_with_coinductive_ancestor( Goal, Hyp ),
                \+ is_answer_known( OriginalGoal, Goal ),    % postpone "old"
                memo( OriginalGoal, Goal, Level ),
                new_result_or_fail( PGIndex, Goal ),           % i.e., note answer
                trace_success( 'variant (coinductive0)', Goal, PGIndex, Level )
            ;
                % other tabled results
                get_remaining_tabled_answers( Goal, PGIndex, variant, Level )
            ;
                % wrap it up
                trace_failure( 'variant (coinductive0)', Goal, PGIndex, Level ),
                retractall( result( PGIndex, _ ) ),
                fail
            )
        ;

            % Not coinductive, just sequence through tabled answers:
            (
                get_all_tabled_answers( Goal, PGIndex, variant, Level )
            ;
                trace_failure( variant, Goal, PGIndex, Level ),
                retractall( result( PGIndex, _ ) ),
                fail
            )
        ).


% A pioneer goal is called by program clauses, producing results that are stored
% in "answer".
% The goal succeeds as each new answer (i.e., an answer heretofore unknown for
% this goal) is produced, and tries to come up with more after backtracking.
% When the usual clauses are exhausted, clauses stored in the associated entries
% of "looping_alternative" will be used to produce more answers (but only those
% that have not yet been produced by the goal), until a fixed point is reached.
% The pioneer (and all the goals in its cluster) will then be marked as
% complete, and will cease to be a pioneer.
%
% Note that a pioneer may also lose its status when some descendant goal finds
% a variant ancestor that is also an ancestor of the pioneer.  See the case
% of "variant of ancestor" above.
%
% Note also that a goal might become completed after it succeeded (because
% another variant goal "on the right" has completed), so after backtracking it
% might not be necessary to continue the computation with the remaining clauses:
% the rest of the results should be picked up from the table, instead.

dra_int2t(Cutted, M:Goal, Stack, Hyp, Level ) :-
        (
            is_coinductive1( Goal )
        ->
            push_is_coinductive0( Goal, Hyp, NHyp )
        ;
            NHyp = Hyp
        ),
        incval( step_counter ),
        copy_term( Goal, OriginalGoal ),
        add_pioneer( Goal, PGIndex ),
        trace_entry( pioneer, Goal, PGIndex, Level ),

        (
            get_tabled_if_old_first( Goal, PGIndex, pioneer, Level )
        ;

            NLevel is Level +1,
            use_clause(M, Goal, Body ),
            \+ is_completed( OriginalGoal ), % might well be, after backtracking
            copy_term( (Goal :- Body), ClauseCopy ),
            push_is_tabled( OriginalGoal, PGIndex, ClauseCopy, Stack, NStack ),
            dra_interp(Cutted, Body, NStack, NHyp, NLevel ),
            \+ is_answer_known( OriginalGoal, Goal ),   % postpone "old" answers
            memo( OriginalGoal, Goal, Level ),
            new_result_or_fail( PGIndex, Goal ),          % i.e., note the answer
            trace_success( pioneer, Goal, PGIndex, Level )
        ;

            % All the clauses have been exhausted, except for looping
            % alternatives (if any).  However, the goal may have become
            % completed (by a later variant), or it might have lost its pioneer
            % status (because it belongs to a larger loop).

            is_completed( Goal )                      % a variant has completed?
        ->
            trace_other( 'Removing completed pioneer', Goal, PGIndex, Level ),
            rescind_pioneer_status( PGIndex ),
            get_remaining_tabled_answers( Goal, PGIndex, 'completed now', Level )
        ;

            is_a_variant_of_a_pioneer( Goal, PGIndex )  % not lost pioneer status?
        ->
            (
                trace_other( 'Computing fixed point for', Goal, PGIndex, Level ),
                compute_fixed_point( Goal, PGIndex, Stack, Hyp, Level ),
                \+ new_result_or_fail( PGIndex, Goal ),
                trace_success( pioneer, Goal, PGIndex, Level )
            ;
                trace_other( 'Fixed point computed', Goal, PGIndex, Level ),
                complete_goal( Goal, Level ),
                complete_cluster( PGIndex, Level ),
                trace_other( 'Removing pioneer', Goal, PGIndex, Level ),
                rescind_pioneer_status( PGIndex ),
                get_remaining_tabled_answers( Goal, PGIndex,
                                              'completed now', Level
                                            )
            ;
                retractall( result( PGIndex, _ ) ),
                fail
            )
        ;

            (
                % No longer a pioneer and not completed, so just sequence
                % through the remaining available tabled answers.
                get_remaining_tabled_answers( Goal, PGIndex,
                                              '(no longer a pioneer)', Level
                                            )
            ;
                trace_failure( '(no longer a pioneer)', Goal, PGIndex, Level ),
                retractall( result( PGIndex, _ ) ),
                fail
            )
        ).



% get_tabled_if_old_first( +goal, +GoalIndex,
%                          +traces label, +traces level
%                        ):
% If the goal has been declared as "old_first", produce all the tabled answers,
% remembering them in "result", then succeed; otherwise just fail.

% :- mode get_tabled_if_old_first( +, +, +, +).

get_tabled_if_old_first( Goal, PGIndex, Label, Level ) :-
        is_old_first( Goal ),
        get_all_tabled_answers( Goal, PGIndex, Label, Level ),
        new_result_or_fail( PGIndex, Goal ).     % i.e., make a note of the answer


% get_all_tabled_answers( +goal, +GoalIndex, +traces label, +traces level ):
% Return (one by one) all the answers that are currently tabled for this goal.
% (Each answer is returned by appropriately instantiating the goal.)

% :- mode get_all_tabled_answers( +, +, +, +).

get_all_tabled_answers( Goal, PGIndex, Label, Level ) :-
        get_answer( Goal ),
        trace_success( Label, Goal, PGIndex, Level ).


% get_remaining_tabled_answers( +goal,        +GoalIndex,
%                               +traces label, +traces level
%                             ):
% Return (one by one) all the answers that are currently tabled for this goal
% but are not present in its "result" entries.
% (Each answer is returned by appropriately instantiating the goal.)

% :- mode get_remaining_tabled_answers( +, +, +, +).

get_remaining_tabled_answers( Goal, PGIndex, Label, Level ) :-
        get_answer( Goal ),
        \+ is_result_known( PGIndex, Goal ),
        trace_success( Label, Goal, PGIndex, Level ).



% use_clause(+module, +goal, - body ):
% Warn and fail if the goal invokes a non-existing predicate.  Otherwise
% nondeterministically return the appropriately instantiated body of each
% clause whose head matches the goal.

use_clause(M, Goal, Body ) :- 
   predicate_property(M:Goal,number_of_clauses(_)),!, clause(M:Goal, Body ).
use_clause(M, Goal, M:Body ) :- 
   predicate_property(Goal,number_of_clauses(_)),!, clause(Goal, Body ).
use_clause(M, Goal, Body ) :-  set_meta(Goal, cuts_ok),Body = M:Goal.






% compute_fixed_point( +pioneer goal, +its index, +stack, +level ):
% Solve the goal by associated rules from "looping_alternative", succeeding
% with each new answer (and tabling it).  Fail when all the possible results
% are exhausted.

% :- mode compute_fixed_point( +, +, +, +, +).

compute_fixed_point( Goal, PGIndex, Stack, Hyp, Level ) :-
        NLevel is Level +1,
        (
            is_coinductive1( Goal )
        ->
            push_is_coinductive0( Goal, Hyp, NHyp )
        ;
            NHyp = Hyp
        ),
        dra_getval_flag( number_of_answers, NAns ),
        compute_fixed_point_( Goal, PGIndex, Stack, NHyp, NLevel, NAns ).

%
% :- mode compute_fixed_point_( +, +, +, +, +, +).

compute_fixed_point_( Goal, PGIndex, Stack, Hyp, Level, _ ) :-
        copy_term( Goal, OriginalGoal ),
        get_looping_alternative( PGIndex, (G :- Body) ),        % i.e., iterate
        \+ \+ G = Goal,
        copy_term( (G :- Body), ClauseCopy ),
        G = Goal,
        push_is_tabled( OriginalGoal, PGIndex, ClauseCopy, Stack, NStack ),
        dra_interp(Cutted, Body, NStack, Hyp, Level ),
        (nonvar(Cutted)-> warning(['cutted at ',Cutted]); true),
        new_result_or_fail( PGIndex, Goal ),
        memo( OriginalGoal, Goal, Level ).

compute_fixed_point_( Goal, PGIndex, Stack, Hyp, Level, NAns ) :-
        dra_getval_flag( number_of_answers, NAnsNow ),
        NAnsNow \= NAns,                % i.e., fail if there are no new answers
        compute_fixed_point_( Goal, PGIndex, Stack, Hyp, Level, NAnsNow ).



% suppress_pioneers_on_list( +list of triples, +TraceLevel ):
% If any of the triples describe goals that are pioneers, make sure those goals
% cease to be pioneers.

suppress_pioneers_on_list( Triples, Level ) :-
        member( triple( M, MI, _ ), Triples ),
        is_a_variant_of_a_pioneer( M, MI ),
        trace_other( 'Removing pioneer', M, MI, Level ),
        rescind_pioneer_status( MI ),
        fail.

suppress_pioneers_on_list( _, _ ).



% rescind_pioneer_status( +index ):
% Remove auxiliary table entries for the pioneer with this index.
% Specifically, clean up "pioneer", "loop" and "looping_alternative".

% :- mode rescind_pioneer_status( +).

rescind_pioneer_status( PGIndex ) :-
        delete_pioneer( PGIndex ),
        delete_loops( PGIndex ),
        delete_looping_alternatives( PGIndex ).


% complete_cluster( +PioneerIndex of a pioneer goal, +TraceLevel ):
% If the goal has an associated cluster, make sure all the goals in the cluster
% are marked as completed.
% Recall that a cluster may consist of a number of "loops".

% :- mode complete_cluster( +, +).

complete_cluster( PGIndex, Level ) :-
        get_loop( PGIndex, Gs ),                  % iterate over loops
        member( G, Gs ),                        % iterate over members of a loop
        complete_goal( G, Level ),
        fail.

complete_cluster( _, _ ).



% extract_goals( +list of triples of goals, indices and clauses,
%                - list of goals
%              ):
% Filter away the other info in each triple, return list of goals only.

% :- mode extract_goals( +, - ).

extract_goals( [], [] ).

extract_goals( [ triple( G, _, _ ) | Ts ], [ G | Gs ] ) :-
        extract_goals( Ts, Gs ).





%-----  The tables: access and modification  -----

% NOTE: See file dra_table_assert.pl or dra_table_record.pl for manipulation of
%       the tables "answer", "result", "pioneer", "loop",
%       "looping_alternative" and "completed".


% get_unique_index( - ):
% Produce a new unique index.

% :- mode get_unique_index( - ).

get_unique_index( PGIndex ) :-
        dra_getval_flag( unique_index, PGIndex ),
        incval( unique_index ).





%-----  Custom-tailored utilities  -----


% are_essences_variants( +term, +term ):
% Are both the terms variants of each other after filtering through
% essence_hook?

% :- mode are_essences_variants( +, +).

are_essences_variants( T1, T2 ) :-
        once( essence_hook( T1, ET1 ) ),
        once( essence_hook( T2, ET2 ) ),
        are_variants( ET1, ET2 ).



% trace_entry( +label, +goal, +GoalIndex, +level ):
% If the goal matches one of the traced patterns, print out a traces line about
% entering the goal (at this level, with this label).
% (The GoalIndex is not always relevant: "?" is used for those cases.)

trace_entry( Label, Goal, PGIndex, Level ) :-
        is_tracing( Goal ),
        !,
        write_level( Level ),
        std_trace_stream( Output ),
        write( Output, 'Entering ' ),
        write_label_and_goal( Label, Goal, PGIndex ),
        nl( Output ).

trace_entry( _, _, _, _ ).


% trace_success( +label, +goal, +GoalIndex, +level ):
% If the goal matches one of the traced patterns, print out a traces line about
% success of the goal (at this level, with this label).  Moreover, just before
% backtracking gets back to the goal, print out a traces line about retrying the
% goal.
% (The GoalIndex is not always relevant: "?" is used for those cases.)

trace_success( Label, Goal, PGIndex, Level ) :-
        is_tracing( Goal ),
        !,
        std_trace_stream( Output ),
        (
            write_level( Level ),
            write( Output, 'Success ' ),
            write_label_and_goal( Label, Goal, PGIndex ),
            nl( Output )
        ;
            write_level( Level ),
            write( Output, 'Retrying ' ),
            write_label_and_goal( Label, Goal, PGIndex ),
            nl( Output ),
            fail
        ).

trace_success( _, _, _, _ ).


% trace_failure( +label, +goal, +GoalIndex, +level ):
% If the goal matches one of the traced patterns, print out a traces line about
% failure of the goal (at this level, with this label).
% (The GoalIndex is not always relevant: "?" is used for those cases.)

trace_failure( Label, Goal, PGIndex, Level ) :-
        is_tracing( Goal ),
        !,
        write_level( Level ),
        std_trace_stream( Output ),
        write( Output, 'Failing ' ),
        write_label_and_goal( Label, Goal, PGIndex ),
        nl( Output ).

trace_failure( _, _, _, _ ).


% trace_other( +label, +goal, +GoalIndex, +level ):
% If the goal matches one of the traced patterns, print out a traces line about
% this goal (at this level, with this label).
% (The GoalIndex is not always relevant: "?" is used for those cases.)

trace_other( Label, Goal, PGIndex, Level ) :-
        is_tracing( Goal ),
        !,
        write_level( Level ),
        write_label_and_goal( Label, Goal, PGIndex ),
        std_trace_stream( Output ),
        nl( Output ).

trace_other( _, _, _, _ ).


% Auxiliaries for tracing:

write_level( Level ) :-
        std_trace_stream( Output ),
        write( Output, '[' ),
        write( Output, Level ),
        write( Output, '] ' ).

write_label_and_goal( Label, Goal, PGIndex ) :-
        print_depth( Depth ),
        std_trace_stream( Output ),
        write( Output, Label ),
        write( Output, ': ' ),
        write_goal_number( PGIndex ),
        write_shallow( Output, Goal, Depth ).


write_goal_number( '?' ) :-
        !.

write_goal_number( PGIndex ) :-
        std_trace_stream( Output ),
        write( Output, '<' ),
        write( Output, PGIndex ),
        write( Output, '> ' ).



% optional_trace( +label, +goal, +term, +level ):
% If the goal matches one of the traced patterns, print out a traces line with
% this label, the goal and the term.

optional_trace( Label, Goal, Term, Level ) :-
        is_tracing( Goal ),
        !,
        print_depth( Depth ),
        write_level( Level ),
        std_trace_stream( Output ),
        write(         Output, Label ),
        write_shallow( Output, Goal, Depth ),
        write(         Output, ' : ' ),
        write_shallow( Output, Term, Depth ),
        nl(            Output ).

optional_trace( _, _, _, _ ).



% fatal_error( +message, +stack ):
% Display the message and stack, then abort.

% :- mode fatal_error( +, +).

fatal_error( Message, Stack ) :-
        begin_error,
        writeln(    error, Message ),
        writeln(    error, '' ),
        writeln(    error, '*** The current stack:' ),
        show_stack( error, Stack ),
        end_error.

%
show_stack( Stream, Stack ) :-
        member( Call, Stack ),
        writeln( Stream, Call ),
        fail.

show_stack( _ ).

%------------------------------------------------------------------------------

% c +r = 7.949 seconds

/*
% :- pf(('dra/tabling3/examples/XSB/fib.tlp') ).

:- pf(('dra/tabling3/examples/co_t.tlp') ).


:- pf(('dra/tabling3/examples/coind2.tlp') ).
% :- pf(('dra/tabling3/examples/LTL/v.pl') ).
%:- pf(('dra/tabling3/examples/mini_graph.tlp') ).
%:- pf(('dra/tabling3/examples/mini_language.tlp') ).
:- pf(('dra/tabling3/examples/paper_example.tlp') ).



:- pf(('dra/tabling3/Bench/tabling3/run')).
:- pf(('dra/tabling3/Bench/prolog/run')).
:- pf(('dra/tabling3/Bench/clpfd/run')).
:- pf(('dra/tabling3/Bench/aspclp/run')).
*/

t0:- time([('dra/tabling3/examples/XSB/farmer.tlp')]).
tn:- time([('dra/tabling3/examples/tnot1.tlp')]).
t1:- time(process_file(('dra/tabling3/examples/XSB/farmer.tlp') )),!.
t2:- time([('dra/tabling3/examples/XSB/ham.tlp')]).
t2a:- time([('dra/tabling3/examples/XSB/ham_auto.tlp')]).

t2b:- time(pf(('dra/tabling3/examples/XSB/ham.tlp') )).
t3:- [(('dra/tabling3/examples/graph.tlp') )].
t4:- pf(('dra/tabling3/examples/module.tlp') ).
t4:- [(('dra/tabling3/examples/paper_example.tlp') )].
t4:- pf(('dra/tabling3/examples/conditional.clp') ).
t4:- pf(('dra/tabling3/examples/simple1.tlp') ).
t4:- pf(('dra/tabling3/examples/simple1_old_first.tlp') ).
t4:- pf(('dra/tabling3/examples/conditional.clp') ).
t4:- pf(('dra/tabling3/examples/small_comment_example.tlp') ).
t4:- pf(('dra/tabling3/examples/coind_new.tlp') ).
t5:- consult('/devel/LogicmooDeveloperFramework/PrologMUD/packs/MUD_PDDL/prolog/dra/tabling3/Bench/tabling/tcl.pl').

% :- repeat,logOnErrorIgnore(prolog),fail.
% user:term_expansion((?- G),_):- nonvar(G), format(atom(H),'~q .',[G]),user:rl_add_history(H),fail.
% user:goal_expansion(G,_):- G\=(_,_),G\=(_;_),\+ predicate_property(G,_),format(atom(H),'~q .',[G]),user:rl_add_history(H),fail.


:- source_location(S,_),prolog_load_context(module,FM),
 forall(source_file(M:H,S),
  ignore((functor(H,F,A),
   \+ atom_concat('$',_,F),
      M:export(M:F/A),
   \+ predicate_property(M:H,transparent),
%    writeln(M:H),
   \+ atom_concat('__aux',_,F), FM:module_transparent(M:F/A)))).


