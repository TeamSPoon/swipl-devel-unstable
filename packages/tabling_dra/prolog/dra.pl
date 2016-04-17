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
:-module('$dra',[
          dra_call_interp/1,
          dra_call_tabled/1,
          dra_call_coind0/1,
          dra_call_coind1/1,
          get_all_tabled_goals/1,
          cont_dra_call/0,
          exit_dra_call/0,
          init_dra_call/0,
          process_dra_ective/1,
          (tnot)/1,
          initialise/0,
          print_tables/0,


          op( 1010, fy, 'table'  ),    % allow  " table p/k ,"
          op( 1010, fy, 'old_first'  ),    % allow  " old_first p/k ,"
          op( 1010, fy, 'never_table'  ),    % allow  " traces  p/k ,"
          op( 1010, fy, 'coinductive0'  ),    % allow  " coinductive0 p/k ,"
          op( 1010, fy, 'coinductive1' ),    % allow  " coinductive1 p/k ,"
          op( 1010, fy, 'hilog'   ),    % allow  " hilog  p/k ,"
          op( 910,  fy, 'tnot'  )    % allow  "?- tnot  p(_) ,"
]).
/** Module 

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

       :-table p/2 .

   All calls to a tabled predicate that are present in the interpreted program
   are called "tabled calls".  Instances of such calls are called "tabled
   goals".  In general, we will use the term "call" to refer to a static entity
   in the program, and "goal" to refer to an instance of a call.  We will also
   avoid the conventional overloading of the term "goal" in yet another way: we
   will call a sequence (i.e., conjunction) of goals just that (unless we can
   refer to it as a "query" or a "resolvent").

   Similarly, the user can declare a predicate to be "coinductive", by using
   another kind of directive, e.g.,

       :-coinductive0  p/2 .
       :-coinductive1 q/3 .

   Calls and goals that refer to a coinductive predicate will also be called
   "coinductive".


   Limitations
   -----------

   The interpreted program must not contain cuts.  It also must not contain
   calls to built-in-predicates, except for the handful of predicates listed in
   is_never_tabled/1 below.  (This list can be easily extended as the need arises.  Some
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
               :-coinductive0 p/2 .
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
                  depending on the logic programming  see the main file
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

               program:  :-table p/2.
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


   -- is_traced( goal )

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


  NOTE:
 
    1. See ../general/top_level.ecl for a description of how to load
       and run programs.
       Please note that in Eclipse after loading this interpreter you
       should issue
            :-import dra.
       if you don't want to keep writing
            dra:prog( filename )
       every time.
 
    2. The interpreter supports a number of directives:
 
       a) Tabled and coinductive predicates should be declared as such in
          the program file, e.g.,
              :-table       ancestor/2.
              :-coinductive0  comember/2.
              :-coinductive1 comember/2.
 
          "coinductive1" means that if there are coinductive hypotheses
          with which a goal unifies, then the usual clauses will not be tried
          after the hypotheses are exhausted (this is "new style"
          coinduction).
 
       b) To include files use the usual Prolog syntax:
              :-[ file1, file2, ... ].
 
       c) To declare predicates used in an interpreted program as dynamic,
          use
              :-dynamic p/k.
 
       d) By default, a goal produces new (i.e., heretofore unknown) answers
          before producing old ones.  To reverse this behaviour, use
 
              :-old_first p/k.
          or
              :-old_first all.
 
       e) To produce a wallpaper traces use the traces directive. For example,
 
              :-traces p/3, q/0, r/1.
 
          will traces predicates "p/3", "q/0" and "r/1".  If you want to traces
          everything, use
 
              :-traces all.
 
          These directives are cumulative.
 
       f) To print out subsets of the current answer table, use
 
              :-answers( Goal, Pattern ).
 
          this will print all tabled answers that are associated with a
          variant of Goal and unifiable with Pattern.
          To get a dump of the entire table, use just
 
              :-answers( _, _ ).
 
    2. The program should contain no other directives. It may, however,
       contain queries, which will be executed immediately upon reading.
 
    3. Just before the result of a query is reported, the interpreter
       produces a printout with statistics accummulated since the previous
       printout (or since the beginning, if this is the first printout during
       this session with the interpreted program). The printout looks like
       this:
 
           [K steps, M new answers tabled (N in all)]
 
       where K, M and N are some natural numbers. K is the number of
       evaluated goals, M is the number of new additions to the answer table,
       N is the current size of the answer table.
 
    4. If the program invokes a built-in predicate, that predicate dra_must
       be declared in the table "is_never_tabled/1" (see file "dra_builtins.pl").
       Every addition should be considered carefully: some built-ins might
       require special treatment by the interpreter.
 
    5. The program may contain clauses that modify the definition of the
       interpreter's predicate "essence_hook/2" (the clauses will be asserted
       at the front of the predicate, and will thus override the default
       definition for some cases).  The default definition is
 
          essence_hook( T, T ).
 
       This predicate is invoked _in certain contexts_ when:
          - two terms are about to be compared (either for equality or to
            check whether they are variants of each other);
          - an answer is tabled;
          - an answer is retrieved from the table.
 
       The primary intended use is to suppress arguments that carry only
       administrative information and that may differ in two terms that are
       "semantically" equal or variants of each other. (Such, for example, is
       the argument that carries the set of coinductive hypotheses in a
       co-logic program translated into Prolog: see "../coind/translate_clp".
       Mind you, that translation need not be applied to programs executed by
       this interpreter).
 
       For example, the presence of
 
          essence_hook( p( A, B, _ ),  p( A, B ) ).
 
       will result in "p( a, b, c )" and "p( a, b, d )" being treated as
       identical, as each of them will be translated to "p( a, b )" before
       comparison.
 
       NOTE: This facility should be used with the utmost caution, as it
             may drastically affect the semantics of the interpreted program
             in a fashion that would be hard to understand for someone who
             does not understand the details of the interpreter.

 
     The top level notes "never_tabled" declarations in the table "is_never_tabled".
        For example,
 
            :-never_tabled p/1, q/2.
 
        will be stored as
 
            is_never_tabled( p( _ ) ).
            is_never_tabled( q( _, _ ) ).
 
        The intended meaning is that "never_tabled" predicates do not make use
        (directly or indirectly) of the special features provided by the
        metainterpreter, so their invocations can be handled just by handing
        them over to Prolog (which would presumably speed up the computation).
 
        Please note that the never_tabled predicates (which should be defined in
        files mentioned in ":-load_is_support( filename )." directives) are
        compiled into the module "never_tabled" (unless they are defined within
        other modules).
 
 
     The metainterpreter should provide the following predicates
        ("hooks") that will be called by the top level:
 
           - is_cut_ok/1:
                  Defines patterns for built-in predicates from the host
                  system that can may contain cuts without damaging semantics.
                  For example, to allow dra_w/2, declare:
                      is_cut_ok( dra_w( _, _ ) ).
 
           - initialise/0:
                  This will be called before loading a new program,
                  giving the metainterpreter an opportunity to
                  (re)initialise its data structures.
 
           - legal_directive/1:
                  Whenever the top level encounters a directive
                  (of the form ":-D."), it will call "legal_directive( D )".
                  If the call succeeds, the interpreter will be given
                  a chance to process the directive (see below), otherwise
                  the directive will be ignored (with a suitable warning).
 
           - process_dra_ective/1:
                  Whenever the top level encounters a legal directive
                  ":-D" (see above), it invokes "process_dra_ective( D )"
                  to give the interpreter a chance to act upon the
                  directive.
 
           - dra_call_interp/1:
                  This would be the main entry point of the metainterpreter.
                  Whenever the top level encounters a query (of the form
                  "?- Q."), it will display the query and then call
                  "dra_call_interp( Q )".  Depending on the result, it will then
                  display "No", or "Yes" (preceded by a display of bindings
                  acquired by the variables occurring in "Q"); in the latter
                  case it will also backtrack to obtain more solutions.
 

*/

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
% :-shell(cls).
:-'$set_source_module'(_,'$dra').
:-dynamic(was_access_level/1).
:-current_prolog_flag(access_level,Was),asserta(was_access_level(Was)).
:-set_prolog_flag(access_level,user).
:-meta_predicate dra_asserta_new(:).
:-meta_predicate dra_retract_all(:).
:-meta_predicate dra_must(0).


std_trace_stream(user_error).
dra_w(M):-std_trace_stream(S),format(S,'~q',[M]),flush_output(S).
dra_wln(M):-std_trace_stream(S),format(S,'~q.~n',[M]),flush_output(S).
dra_retract_all(R):-ignore((retract(R),fail)).
% dra_asserta_new(G):-catch(G,_,fail),!.
dra_asserta_new(G):-dra_retract_all(G),asserta(G).
dra_must((G1,G2)):- !, dra_must(G1),dra_must(G2).
dra_must(G):-G *->true;dra_error(failed_dra_must(G)).
dra_error(W):-throw(dra_error(W)).

% BREAKS THINGS :- meta_predicate(add_clauses(0)).
:- module_transparent(add_clauses/1).
add_clauses(_G):- current_prolog_flag(xref, true),!.
add_clauses(G):- predicate_property(G,dynamic),!,dra_asserta_new(G).
add_clauses(G):- predicate_property(G,static),!,compile_aux_clauses(G).
add_clauses(G):- compile_aux_clauses(G).


property_pred((table),is_tabled).
property_pred((traces),is_traced).
property_pred(cut_ok,is_cut_ok).
property_pred(old_first,is_old_first).
property_pred(coinductive0,is_coinductive0).
property_pred(coinductive1,is_coinductive1).
property_pred(never_tabled,is_never_tabled).
property_pred(hilog,is_hilog).


:-forall(property_pred(D,F) ,
   ((DG=..[D,_],
    M = system,
    module_transparent(M:D/1),
    add_clauses(( M:DG :- process_dra_ective(DG))), 
   ( \+ current_op(_,fy,user:D) -> op(1010,fy,user:D) ; true), 
    multifile(F/1)))).


% ON :-initialization( profiler(_,walltime) ).
% ON :-initialization(user:use_module(library(swi/pce_profile))).

% :-multifile sandbox:safe_primitive/1.
% :-asserta((sandbox:safe_primitive(Z):-wdmsg(Z))).
% :-user:ensure_loaded(library(ape/get_ape_results)).
% :-user:ensure_loaded(library(logicmoo/util/logicmoo_util_all)).

:-use_module(library(coinduction),
  	  [ (coinductive)/1,
  	    op(1150, fx, (coinductive))
  	  ]).

:-set_prolog_flag(debugger_show_context,true).

% BREAKS THINGS meta_predicate(set_meta(0,+)).
:- module_transparent(set_meta/2).
set_meta(TGoal,is_coninductive0):- !,
    set_meta(TGoal,is_coninductive1),
    add_clauses( (TGoal :- !, dra_call_coind0(TGoal) )),
    dra_asserta_new(is_coninductive0(TGoal)).

set_meta(TGoal,is_coninductive1):- !,
    add_clauses( (TGoal :- !, dra_call_coind1(TGoal) )),
    dra_asserta_new(is_coninductive1(TGoal)).

set_meta(TGoal,is_never_tabled):- !,
    dra_retract_all(is_tabled(TGoal)),
    dra_retract_all(is_old_first(TGoal)),
    dra_retract_all( (TGoal :- !, dra_call_tabled(TGoal) )),
    (is_never_tabled(TGoal)-> true ; dra_asserta_new(is_never_tabled(TGoal))).

set_meta(TGoal,is_tabled):-
    dra_retract_all(is_never_tabled(TGoal)),
    dra_asserta_new(is_tabled(TGoal)),
    add_clauses( (TGoal :- !, dra_call_tabled(TGoal))),
    functor(TGoal,F,A),discontiguous(F/A).
    %interp(dra_call_tabled,TGoal).

set_meta(TGoal,is_old_first):-
    set_meta(TGoal,is_tabled),
    dra_asserta_new(is_old_first(TGoal)).


%------------------------------------------------------------------------------

:-ensure_loaded( library( lists ) ). % An SWI library, for reverse/2.

%------------------------------------------------------------------------------

%  Built-in predicates for the "dra" interpreter  %

% If the interpreted program invokes a built-in predicate, that predicate dra_must
% be declared in the table "is_never_tabled/1" below.
% Every addition should be considered carefully: some built-ins might require
% special treatment by the interpreter.

%  NOTE: findall/3 is not opaque to coinductive and tabled ancestors.

%  NOTE: Just adding "!" won't do the trick, the main interpreter would
%        have to be modified substantially (but first: what are the semantics?)

:-dynamic(is_never_tabled/1).
:-dynamic(is_table_ok/1).


%is_never_tabled( (_ -> _)           ).  % special treatment in dra_interp/4
%is_never_tabled( (_ -> _ ; _)       ).  % special treatment in dra_interp/4
%is_never_tabled( \+ ( _ )            ).  % special treatment in dra_interp/4

is_never_tabled(Pred):-is_table_ok(Pred),!,fail.
is_never_tabled(Pred):-is_builtin(Pred),asserta(is_never_tabled(Pred)),!.
is_never_tabled(Pred):-functor(Pred,F,A),functor(TPred,F,A),asserta(is_table_ok(TPred)),!,fail.

is_builtin(Pred) :-is_swi_builtin( Pred ).
is_builtin(Pred) :-functor(Pred,F,_),atom_concat('$',_,F).
% is_builtin(Pred) :-source_file(Pred,File),is_file_meta(File,is_never_tabled), \+ clause(is_tabled(Pred),true).


%------------------------------------------------------------------------------
% mk_pattern( + an atom representing the name of a predicate,
%             + an integer representing the arity of the predicate,
%             - the most general pattern that matches all invocations of the
%               predicate
%           )
% Given p/k, produce p( _, _, ... _ )  (of arity k)

% :-mode mk_pattern( +, +, -).

% mk_pattern( P, K, Pattern ) :-
%        length( Args, K ),                           % Args = K fresh variables
%        Pattern =.. [ P | Args ].

mk_pattern( P, K, Pattern ) :-
        functor( Pattern, P, K ).



%------------------------------------------------------------------------------
% predspecs_to_patterns( +a conjunction of predicate specifications,
%                        - list of most general instances of these predicates
%                      ):
% Given one or several predicate specifications (in the form "p/k" or
% "p/k, q/l, ...") check whether they are well-formed: if not, raise a fatal
% dra_error; otherwise return a list of the most general instances that correspond
% to the predicate specifications.

:-module_transparent(predspecs_to_patterns/2).

predspecs_to_patterns( Var, _ ) :-
        var( Var ),
        !, trace, 
        dra_error( [ 'A variable instead of predicate specifications: \"',
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
% well-formed: if not, raise a fatal dra_error; otherwise return a most general
% instance that correspond to the predicate specification.

predspec_to_pattern( +PredSpec, +Pattern ) :- !,predspec_to_pattern( PredSpec, Pattern ).
predspec_to_pattern(-PredSpec, -Pattern ) :- !,predspec_to_pattern( PredSpec, Pattern ).
predspec_to_pattern( M:PredSpec, M:Pattern ):- !,predspec_to_pattern( PredSpec, Pattern ).
predspec_to_pattern( PredSpec, Pattern ) :-Pattern \= (_/_),!,PredSpec = Pattern.
predspec_to_pattern( PredSpec, Pattern ) :-
        check_predspec( PredSpec ),
        PredSpec = P / K,
        mk_pattern( P, K, Pattern ).


%------------------------------------------------------------------------------
% check_predspec:
% Raise an dra_error if this is not a good predicate specification.
check_predspec( Var ) :-
        var( Var ),
        !,
        dra_error( [ 'A variable instead of a predicate specification: \"',
                 Var,
                 '\"'
               ]
             ).

check_predspec( P / K ) :-
        atom( P ),
        integer( K ),
        K >= 0,
        !.

check_predspec( PredSpec ) :-trace,
        dra_error( [ 'An incorrect predicate specification: \"', PredSpec, '\"' ] ).


%------------------------------------------------------------------------------
% The default essence_hook:

:-dynamic essence_hook/2.

essence_hook( T, T ).    % default, may be overridden by the interpreted program


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
% dra_setval_flag( +name, +value ):
% Set this counter to this value.
%
% NOTE: Since DRA uses global variables to store only integers, we use the
%       flag/3 facility of SWI Prolog.  For more general values we would have
%       to use dra_nb_setval/dra_nb_getval.  See also dra_getval_flag/2 and dra_incval_flag/1 below.

dra_setval_flag( Name, Value ) :-flag( Name, _Old, Value ).


%------------------------------------------------------------------------------
% dra_getval_flag( +name, -value ):
% Get the value associated with this counter.

dra_getval_flag( Name, Value ) :-flag( Name, Value, Value ).


%------------------------------------------------------------------------------
% dra_incval_flag( +name ):
% Increment this counter by 1.
dra_incval_flag( Name ) :-flag( Name, Value, Value+1 ).




%==============================================================================



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
%    empty_hypotheses(-stack of hypotheses ):
%         Create an empty stack for coinductive hypotheses.
%
%    push_is_coinductive( +goal, +stack of hypotheses , -new stack ):
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
% :-mode empty_hypotheses(-).
%
% empty_hypotheses( [] ).
%
%
% :-mode push_is_coinductive( +, +, -).
%
% push_is_coinductive( Goal, Hyp, [ Goal | Hyp ] ).
%
%
% :-mode unify_with_coinductive_ancestor( +, +).
%
% unify_with_coinductive_ancestor( Goal, Hyp ) :-
%         once( essence_hook( Goal, Essence ) ),
%         member( G, Hyp ),
%         once( essence_hook( G, Essence ) ).


%--------------  An implementation that uses goal_table:  --------------%

%:-ensure_loaded( 'goal_table_in_tree' ).
%

%  A goal table implemented by a binary tree with lists.                   %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (February 2009).                      %
%                                                                          %
%  Last update: 16 May 2009.                                               %
%                                                                          %


% :-ensure_loaded( goal_table_in_open_tree ).

%:-ensure_loaded( utilities ).
%:-ensure_loaded( higher_order ).
%:-ensure_loaded( tree ).
%

%  Operations on binary trees.                                             %
%                                                                          %
%  This particular version                                                 %
%   written by Feliks Kluzniak at UTD (May 2009).                          %
%                                                                          %
%  Last update: 16 May 2009.                                               %
%                                                                          %

%:-ensure_loaded( higher_order ).


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
% is_in_tree( +tree, +key, +comparison predicate, -information ):
% If the entry for this key is present in the tree, succeed and return the
% associated information; if it is not, fail.
% "comparison predicate" is a binary predicate that succeeds if the first
% argument is smaller than the second argument.  Any predicate that implements
% a total ordering will do.

:-meta_predicate(is_in_tree( +, +, 2, -)).
is_in_tree( Node, Key, LessPred, Info ) :-
        Node = t( K, I, L, R ),
        (
            Key = K
        ->
            Info = I
        ;
            call( LessPred,  Key, K  )
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

:-meta_predicate(tree_add( +, +, +, 2, 3, -)).

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
                call( ModifyPred,  I, Info, NewI  ),
                NewNode = t( K, NewI, L, R )
            ;
                call( LessPred, Key, K  )
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
% goal_table_add( +goal table, +goal, -new goal table ):
% Add this goal to the table.

goal_table_add( Table, Goal, NewTable ) :-
        functor( Goal, P, K ),
        tree_add( Table, P / K, [ Goal ], '@<', add_to_list, NewTable ).

%
add_to_list( List, [ Item ], [ Item | List ] ).

%------------------------------------------------------------------------------



% :-mode empty_hypotheses(-).

empty_hypotheses( Hyp ) :-
        empty_goal_table( Hyp ).


% :-mode push_is_coinductive( +, +, -).

push_is_coinductive( Goal, Hyp, NewHyp ) :-
        goal_table_add( Hyp, Goal, NewHyp ).


% :-mode unify_with_coinductive_ancestor( +, +).

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
%    empty_stack(-stack ):
%            Create an empty stack.
%
%    push_is_tabled( +goal, +index, +clause, +stack, -new stack ):
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
% :-mode empty_stack(-).
%
% empty_stack( [] ).
%
%
% :-mode push_is_tabled( +, +, +, +, -).
%
% push_is_tabled( Goal, PGIndex, Clause, Stack,
%              [ triple( Goal, PGIndex, Clause ) | Stack ]
%            ).
%
%
% :-mode is_variant_of_ancestor( +, +, -, -).
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


%:-ensure_loaded( 'goal_table_in_tree' ).


% :-mode empty_stack(-).

empty_stack( tstack( [], Table ) ) :-
        empty_goal_table( Table ).


% :-mode push_is_tabled( +, +, +, +, -).

push_is_tabled( Goal, PGIndex, Clause, tstack( Stack, Table ),
             tstack( [ triple( Goal, PGIndex, Clause ) | Stack ], NewTable )
           ) :-
        goal_table_add( Table, Goal, NewTable ).


% :-mode is_variant_of_ancestor( +, +, -, -).

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


% Initialization of tables:

:-dynamic (is_coinductive0)/1 .
:-dynamic (is_coinductive1)/1 .
:-dynamic (is_tabled)/1 .
:-dynamic (is_old_first)/1 .
:-dynamic (is_traced)/1.

:-dra_setval_flag( number_of_answers, 0 ).
:-dra_setval_flag( unique_index,      0 ).

dra_version('DRA ((c) UTD 2009) version 0.97 (beta), June 2011 - LOGICMOO').

initialise :-                                        % invoked by top_level
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
        retractall( is_traced( _ )      ),
        dra_setval_flag( number_of_answers, 0 ),
        dra_setval_flag( unique_index,      0 ),
        dra_setval_flag( step_counter,      0 ),
        dra_setval_flag( old_table_size,    0 ))),
        dra_must((dra_version( Version ),
        dra_w( Version ))),!.


%  Administration  %
:-op( 1010, fy, table       ).    % allow  ":-table p/k ."
:-op( 1010, fy, old_first    ).    % allow  ":-old_first p/k ."
:-op( 1010, fy, never_table        ).    % allow  ":-traces  p/k ."
:-op( 1010, fy, coinductive0  ).    % allow  ":-coinductive0 p/k ."
:-op( 1010, fy, coinductive1 ).    % allow  ":-coinductive1 p/k ."
:-op( 1010, fy, hilog    ).    % allow  ":-hilog  p/k ."
:-op( 910,  fy, tnot    ).    % allow  "?- tnot  p(_) ."



% The legal directives (check external form only).  (Used by the top level.)


%legal_directive(M:P):-atom(M),M:legal_directive(P).
%legal_directive(P):-compound(P),functor(P,F,1),property_pred(F).
legal_directive((coinductive( _))  ).
legal_directive( (coinductive0 _)  ).
legal_directive( (coinductive1 _) ).
legal_directive( (table _)       ).
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

% Check and process the legal directives (invoked by top_level)


% process_dra_ective( +directive ):
% Process a directive.
:-module_transparent(process_dra_ective/1).

process_dra_ective( Directive ) :-           % unsupported directive
       \+ legal_directive( Directive ),
        !,
        dra_error( lines( [ 'Unknown directive:', [ (:-Directive), '.' ] ] ) ).

process_dra_ective( answers( Goal, Pattern ) ) :-
        dra_w(print_required_answers( Goal, Pattern )).

%process_dra_ective( Dir ) :-property_pred(F,DBF), Dir=..[F,all],DB=..[DBF,_], !, once((source_context(F),add_file_meta(F,DBF));dra_asserta_new( DB:- ! )).
%process_dra_ective( Dir ) :-property_pred(F,DBF), (Dir=..[F,none];Dir=..[F,-all]),DB=..[DBF,_], !, once((source_context(F),dra_retract_all(is_file_meta(F,DBF)));(dra_retract_all( DB ),dra_retract_all( DB :- ! ))).
process_dra_ective( Dir ) :-
        property_pred(F,DBF), 
        Dir=..[F,PredSpecs],
        predspecs_to_patterns( PredSpecs, Patterns ),!,
        add_patterns(Patterns,DBF).

:- meta_predicate add_pattern(+,+).

add_patterns([],_):- !.
add_patterns([P|Patterns],DBF):-add_pattern(P,DBF),!,add_patterns(Patterns,DBF).

add_pattern(Pattern, -DBF):- !, DB=..[DBF,Pattern], dra_retract_all( DB ).
add_pattern(Pattern, + DBF):- !, add_pattern(Pattern, DBF).
add_pattern(Pattern,DBF):-DB=..[DBF,Pattern],
        set_meta(Pattern,DBF),
        dra_asserta_new( DB ),!.



%
%  The interpreter  %

init_dra_call:-
        reinitialise_pioneer,
        reinitialise_result,
        reinitialise_loop,
        reinitialise_looping_alternative,
        dra_setval_flag( unique_index,      0    ),
        dra_getval_flag( number_of_answers, NAns ),
        dra_setval_flag( old_table_size,    NAns ),
        dra_setval_flag( step_counter,      0    ).


:-meta_predicate dra_call_tabled( 0).
:-module_transparent(dra_call_tabled/1).
% invoked by VMI/WAM  meta_predicate(dra_call_tabled( : )).
% Execute a query.
dra_call_tabled(Goals ) :-
      '$dra':dra_must(b_getval('$tabling_exec',dra_state(Stack, Hyp, ValOld, CuttedOut))),
      setup_call_cleanup(
        ((ValOld < 0) -> (( init_dra_call,EXIT = exit_dra_call )); (EXIT = cont_dra_call)),
        ((      
            Level is ValOld +1,
            dra_call_tabled(Cutted, Goals, Stack, Hyp, Level ),
            ((var(Cutted);((trace),'$dra':non_cutted(Goals,Cutted,(CuttedOut))))->true;(!,fail)),
             EXIT)),
       ((EXIT))).

:-module_transparent(dra_call_coind0/1).

dra_call_coind0(Goals ) :-
      '$dra':dra_must(b_getval('$tabling_exec',dra_state(Stack, Hyp, ValOld, CuttedOut))),
      setup_call_cleanup(
        ((ValOld < 0) -> (( '$dra':init_dra_call,EXIT = exit_dra_call )); (EXIT = cont_dra_call)),
        ((
           % empty_hypotheses( Hyp ),
           % empty_stack( Stack ),            
            Level is ValOld +1,
            dra_interp(Cutted, Goals, Stack, Hyp, Level ),
            ((var(Cutted);((trace),'$dra':non_cutted(Goals,Cutted,(CuttedOut))))->true;(!,fail)),
             '$dra':EXIT)),
       (('$dra':EXIT))).

:-module_transparent(dra_call_coind1/1).

dra_call_coind1(Goals ) :-
      '$dra':dra_must(b_getval('$tabling_exec',dra_state(Stack, Hyp, ValOld, CuttedOut))),
      setup_call_cleanup(
        ((ValOld < 0) -> (( '$dra':init_dra_call,EXIT = exit_dra_call )); (EXIT = cont_dra_call)),
        ((
           % empty_hypotheses( Hyp ),
           % empty_stack( Stack ),            
            Level is ValOld +1,
            dra_interp(Cutted, Goals, Stack, Hyp, Level ),
            ((var(Cutted);((trace),'$dra':non_cutted(Goals,Cutted,(CuttedOut))))->true;(!,fail)),
             '$dra':EXIT)),
       (('$dra':EXIT))).


:-module_transparent(dra_call_interp/1).

dra_call_interp(Goals ) :-
      '$dra':dra_must(b_getval('$tabling_exec',dra_state(Stack, Hyp, ValOld, CuttedOut))),
      setup_call_cleanup(
        ((ValOld < 0) -> (( '$dra':init_dra_call,EXIT = exit_dra_call )); (EXIT = cont_dra_call)),
        ((
           % empty_hypotheses( Hyp ),
           % empty_stack( Stack ),            
            Level is ValOld +1,
            dra_interp(Cutted, Goals, Stack, Hyp, Level ),
            ((var(Cutted);((trace),'$dra':non_cutted(Goals,Cutted,(CuttedOut))))->true;(!,fail)),
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
        
        dra_getval_flag( step_counter, NSteps ),
        dra_getval_flag( number_of_answers, NAns ),
        dra_getval_flag( old_table_size, OldNAns ),
        TableGrowth is NAns - OldNAns,
        dra_wln([step=NSteps,growth=TableGrowth,tabled=NAns]).



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

:-module_transparent(dra_interp/5).
:-module_transparent(dra_call_tabled/5).
:-module_transparent(dra_call_tabled/1).


:-
  empty_hypotheses( Hyp ),
  empty_stack( Stack ),
  nb_setval('$tabling_exec',dra_state(Stack, Hyp, -1, _CuttedOut)).

% tnot/1 must be ran in meta-interp
'tnot'(G):-dra_call_interp('tnot'(G)).


% A negation.
dra_interp(Cutted, ((\+ Goal)), Stack, Hyp, Level ) :-assertion(nonvar(Goal)),
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


% simply true.
dra_interp(_ ,     true, _, _, _ ) :- !.


dra_interp(Cutted, ( (tnot Goal)) , Stack, Hyp, Level ) :- !, findall(Cutted-Goal,dra_interp(Cutted, Goal , Stack, Hyp, Level ),L),L=[].


% One solution.

dra_interp(Cutted, once( Goal ), Stack, Hyp, Level ) :-
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

dra_interp(Cutted, (Cond -> Then ; Else), Stack, Hyp, Level ) :- !,
      (  dra_interp(Cutted, Cond, Stack, Hyp, Level ) ->        
        dra_interp(Cutted, Then, Stack, Hyp, Level ) ;
        dra_interp(Cutted, Else, Stack, Hyp, Level )).


% A conditional without an else.

dra_interp(Cutted, (Cond -> Then), Stack, Hyp, Level ) :- !,
        (dra_interp(Cutted, Cond, Stack, Hyp, Level ) -> dra_interp(Cutted, Then, Stack, Hyp, Level )).

dra_interp(Cutted, (GoalsL ; GoalsR), Stack, Hyp, Level ) :- !,
        (dra_interp(Cutted, GoalsL, Stack, Hyp, Level ) ;
         dra_interp(Cutted, GoalsR, Stack, Hyp, Level )).


% A conjunction.
dra_interp(Cutted, (Goals1 , Goals2), Stack, Hyp, Level ) :- !,
        dra_interp(Cutted, Goals1, Stack, Hyp, Level ),
        dra_interp(Cutted, Goals2, Stack, Hyp, Level ).


% call/1
dra_interp(Cutted, call( Goal ), Stack, Hyp, Level ) :- !,dra_interp(Cutted, Goal, Stack, Hyp, Level ) .


% findall/3: note that this is not opaque to coinductive and tabled ancestors!

dra_interp(Cutted, findall( Template, Goal, Bag ), Stack, Hyp, Level ) :- !,
        NLevel is Level +1,
        findall( Template, dra_interp(Cutted, Goal, Stack, Hyp, NLevel ), Bag ).

dra_interp(Cutted, !, _, _, _ ) :- !, (var(Cutted);Cutted=cut).
dra_interp(Cutted, !(Where), _, _, _ ) :- !, (var(Cutted);Cutted=cut_to(Where)).

dra_interp(CuttedOut, Goal, Stack, Hyp,  Level ):-
   is_tabled(Goal),!,
   dra_call_tabled(Cutted, Goal, Stack, Hyp, Level ),
  ((var(Cutted);non_cutted(Goal,Cutted, CuttedOut))->true;(!,fail)).


% A goal that is coinductive, but not tabled.
% Apply the coinductive hypotheses first, then the clauses.
%
% NOTE: Now that we have both "coinductive0" and "coinductive1" the logic gets a
%       little tricky.  If a goal is not "coinductive2", then it should activate
%       its clauses only if there are no unifiable ancestors (hypotheses). What
%       follows is an attempt to avoid too much duplication of code and
%       redundant invocations of the costly check for unifiable ancestors.

dra_interp(Cutted, Goal, Stack, Hyp, Level ) :-fail,
        is_coinductive1( Goal ),
        !,
        dra_incval_flag( step_counter ),
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
                use_clause(Goal, Body ),
                push_is_coinductive( Goal, Hyp, NHyp ),
                dra_interp(Cutted, Body, Stack, NHyp, NLevel ),
                trace_success( 'coinductive (clause)', Goal, '?', Level )
            ;
                trace_failure( coinductive, Goal, '?', Level ),
                fail
            )
        ).


% Some other supported built-in.
dra_interp(CuttedOut, BuiltIn, Stack, Hyp,  Level ):- !,
     b_setval('$tabling_exec',dra_state(Stack, Hyp, Level, Cutted)),
     call(BuiltIn ),        
    ((var(Cutted);(trace,non_cutted(BuiltIn,Cutted, CuttedOut)))->true;(!,fail)). 

/*

dra_interp(CuttedOut, Goal, Stack, Hyp,  Level ):-fail,
  % Should read the new default
  set_meta(Goal,is_tabled),!,
  dra_call_tabled(Cutted, Goal, Stack, Hyp,  Level ),
  ((var(Cutted);non_cutted(Goal,Cutted, CuttedOut))->true;(!,fail)). 

% A "normal" goal (i.e., not tabled, not coinductive).
dra_interp(Cutted, Goal, Stack, Hyp, Level ):-
       trace_entry( normal, Goal, '?', Level ),
        (
            NLevel is Level +1,
            use_clause( Goal, Body ),
            dra_interp(Cutted, Body, Stack, Hyp, NLevel ),
            trace_success( normal, Goal, '?', Level )
        ;
            trace_failure( normal, Goal, '?', Level ),
            fail
        ).

*/

non_cutted(_,cut,_):- !,fail.
non_cutted(Goal,cut_to(ToGoal),_):-dra_must(nonvar(ToGoal)), Goal=ToGoal, !,fail.
non_cutted(_,Cutted,Cutted).

% A tabled goal that has been completed: all the results are in "answer".

dra_call_tabled(_Cutted, Goal, _, _, Level ) :-
        is_completed( Goal ),
        !,
        dra_incval_flag( step_counter ),
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

dra_call_tabled(_Cutted, Goal, Stack, Hyp, Level ) :-
        is_variant_of_ancestor( Goal, Stack,
                                triple( G, I, C ), InterveningTriples
                              ),
        !,
        dra_incval_flag( step_counter ),
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

dra_call_tabled(Cutted, Goal, Stack, Hyp, Level ) :-
        (
            is_coinductive1( Goal )
        ->
            push_is_coinductive( Goal, Hyp, NHyp )
        ;
            NHyp = Hyp
        ),
        dra_incval_flag( step_counter ),
        copy_term( Goal, OriginalGoal ),
        add_pioneer( Goal, PGIndex ),
        trace_entry( pioneer, Goal, PGIndex, Level ),

        (
            get_tabled_if_old_first( Goal, PGIndex, pioneer, Level )
        ;

            NLevel is Level +1,
            use_clause(Goal, Body ),
            \+ is_completed( OriginalGoal ), % might well be, after backtracking
            copy_term( (Goal :-Body), ClauseCopy ),
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

% :-mode get_tabled_if_old_first( +, +, +, +).

get_tabled_if_old_first( Goal, PGIndex, Label, Level ) :-
        is_old_first( Goal ),
        get_all_tabled_answers( Goal, PGIndex, Label, Level ),
        new_result_or_fail( PGIndex, Goal ).     % i.e., make a note of the answer


% get_all_tabled_answers( +goal, +GoalIndex, +traces label, +traces level ):
% Return (one by one) all the answers that are currently tabled for this goal.
% (Each answer is returned by appropriately instantiating the goal.)

% :-mode get_all_tabled_answers( +, +, +, +).

get_all_tabled_answers( Goal, PGIndex, Label, Level ) :-
        get_answer( Goal ),
        trace_success( Label, Goal, PGIndex, Level ).


% get_remaining_tabled_answers( +goal,        +GoalIndex,
%                               +traces label, +traces level
%                             ):
% Return (one by one) all the answers that are currently tabled for this goal
% but are not present in its "result" entries.
% (Each answer is returned by appropriately instantiating the goal.)

% :-mode get_remaining_tabled_answers( +, +, +, +).

get_remaining_tabled_answers( Goal, PGIndex, Label, Level ) :-
        get_answer( Goal ),
        \+ is_result_known( PGIndex, Goal ),
        trace_success( Label, Goal, PGIndex, Level ).



% use_clause(+module, +goal, -body ).
% Warn and fail if the goal invokes a non-existing predicate.  Otherwise
% nondeterministically return the appropriately instantiated body of each
% clause whose head matches the goal.

:-meta_predicate(use_clause(:, -)).
use_clause(Goal, Body ) :-
   predicate_property(Goal,number_of_clauses(_)),!, clause(Goal, Body ),Body \= (!,_).

use_clause(Goal, Body ) :-set_meta(Goal, is_never_tabled),Body = call(Goal).





% compute_fixed_point( +pioneer goal, +its index, +stack, +level ):
% Solve the goal by associated rules from "looping_alternative", succeeding
% with each new answer (and tabling it).  Fail when all the possible results
% are exhausted.

% :-mode(compute_fixed_point( 0, +, +, +, +)).

compute_fixed_point( Goal, PGIndex, Stack, Hyp, Level ) :-
        NLevel is Level +1,
        (
            is_coinductive1( Goal )
        ->
            push_is_coinductive( Goal, Hyp, NHyp )
        ;
            NHyp = Hyp
        ),
        dra_getval_flag( number_of_answers, NAns ),
        compute_fixed_point_( Goal, PGIndex, Stack, NHyp, NLevel, NAns ).

%
% :-mode compute_fixed_point_( +, +, +, +, +, +).

compute_fixed_point_( Goal, PGIndex, Stack, Hyp, Level, _ ) :-
        copy_term( Goal, OriginalGoal ),
        get_looping_alternative( PGIndex, (G :-Body) ),        % i.e., iterate
        \+ \+ G = Goal,
        copy_term( (G :-Body), ClauseCopy ),
        G = Goal,
        push_is_tabled( OriginalGoal, PGIndex, ClauseCopy, Stack, NStack ),
        dra_interp(Cutted, Body, NStack, Hyp, Level ),
        (nonvar(Cutted)-> print_message(waring,[warning,'cutted at ',Cutted]); true),
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

% :-mode rescind_pioneer_status( +).

rescind_pioneer_status( PGIndex ) :-
        delete_pioneer( PGIndex ),
        delete_loops( PGIndex ),
        delete_looping_alternatives( PGIndex ).


% complete_cluster( +PioneerIndex of a pioneer goal, +TraceLevel ):
% If the goal has an associated cluster, make sure all the goals in the cluster
% are marked as completed.
% Recall that a cluster may consist of a number of "loops".

% :-mode complete_cluster( +, +).

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

% :-mode extract_goals( +, -).

extract_goals( [], [] ).

extract_goals( [ triple( G, _, _ ) | Ts ], [ G | Gs ] ) :-
        extract_goals( Ts, Gs ).



%-----  The tables: access and modification  -----

% NOTE: See file dra_table_assert.pl or dra_table_record.pl for manipulation of
%       the tables "answer", "result", "pioneer", "loop",
%       "looping_alternative" and "completed".


% get_unique_index(-):
% Produce a new unique index.

% :-mode get_unique_index(-).

get_unique_index( PGIndex ) :-
        dra_getval_flag( unique_index, PGIndex ),
        dra_incval_flag( unique_index ).





%-----  Custom-tailored utilities  -----


% are_essences_variants( +term, +term ):
% Are both the terms variants of each other after filtering through
% essence_hook?

% :-mode are_essences_variants( +, +).

are_essences_variants( T1, T2 ) :-
        once( essence_hook( T1, ET1 ) ),
        once( essence_hook( T2, ET2 ) ),
        are_variants( ET1, ET2 ).



% trace_entry( +label, +goal, +GoalIndex, +level ):
% If the goal matches one of the traced patterns, print out a traces line about
% entering the goal (at this level, with this label).
% (The GoalIndex is not always relevant: "?" is used for those cases.)

trace_entry( Label, Goal, PGIndex, Level ) :-
        is_traced( Goal ),
        !,
        write_level( Level ),
        std_trace_stream( Output ),
        dra_w( 'Entering ' ),
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
        is_traced( Goal ),
        !,
        std_trace_stream( Output ),
        (
            write_level( Level ),
            dra_w( 'Success ' ),
            write_label_and_goal( Label, Goal, PGIndex ),
            nl( Output )
        ;
            write_level( Level ),
            dra_w( 'Retrying ' ),
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
        is_traced( Goal ),
        !,
        write_level( Level ),
        std_trace_stream( Output ),
        dra_w( 'Failing ' ),
        write_label_and_goal( Label, Goal, PGIndex ),
        nl( Output ).

trace_failure( _, _, _, _ ).


% trace_other( +label, +goal, +GoalIndex, +level ):
% If the goal matches one of the traced patterns, print out a traces line about
% this goal (at this level, with this label).
% (The GoalIndex is not always relevant: "?" is used for those cases.)

trace_other( Label, Goal, PGIndex, Level ) :-
        is_traced( Goal ),
        !,
        write_level( Level ),
        write_label_and_goal( Label, Goal, PGIndex ),
        std_trace_stream( Output ),
        nl( Output ).

trace_other( _, _, _, _ ).


% Auxiliaries for tracing:

write_level( Level ) :-dra_w([Level]).

write_label_and_goal( Label, Goal, PGIndex ) :-
        print_depth( Depth ),
        std_trace_stream( Output ),
        dra_w( Label ),
        dra_w( ': ' ),
        write_goal_number( PGIndex ),
        write_shallow( Output, Goal, Depth ).


write_goal_number( '?' ) :-
        !.

write_goal_number( PGIndex ) :-
        dra_w( '<' ),
        dra_w( PGIndex ),
        dra_w( '> ' ).



:-dynamic print_depth/1 .

print_depth( 10 ).



% optional_trace( +label, +goal, +term, +level ):
% If the goal matches one of the traced patterns, print out a traces line with
% this label, the goal and the term.

optional_trace( Label, Goal, Term, Level ) :-
        is_traced( Goal ),
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


































































%------------------------------------------------------------------------------
% member_reversed( +- item, +list of items ):
% Like member/2, but the order of searching/generation is reversed.

member_reversed( M, [ _ | L ] ) :-
        member_reversed( M, L ).
member_reversed( M, [ M | _ ] ).



% c +r = 7.949 seconds


% :-repeat,logOnErrorIgnore(prolog),fail.
% user:term_expansion((?- G),_):-nonvar(G), format(atom(H),'~q .',[G]),user:rl_add_history(H),fail.
% user:goal_expansion(G,_):-G\=(_,_),G\=(_;_),\+ predicate_property(G,_),format(atom(H),'~q .',[G]),user:rl_add_history(H),fail.


:-dynamic pioneer/3 .
:-dynamic result/2 .
:-dynamic loop/2 .
:-dynamic looping_alternative/2 .
:-dynamic completed/2 .

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
%:-user:ensure_loaded(library(dra/tabling3/dra_table_assert)).
   % NOTICE:    % %
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
   %

%  Table-handling procedures for the "dra" interpreter.                    %
%                                                                          %
%  Written by Feliks Kluzniak at UTD (March 2009)           .              %
%                                                                          %
%  Last update: 25 August 2009.                                            %
%                                                                          %

% The tables are normally kept in asserted clauses, but for some systems this
% is  not convenient, because asserted clauses are compiled.
% For example, this is so in SWI Prolog, which in addition does not assert
% cyclic terms, so  for that system the "recorded" database is more
% appropriate.
% In order to facilitate such changes, routines for handling the table is
% factored out of the main program.

print_tables :-
       listing( answer( _, _, _ ) ),
       listing( result( _, _ ) ),
       listing( pioneer( _, _, _ ) ),
       listing( loop( _, _ ) ),
       listing( looping_alternative( _, _ ) ),
       listing( completed( _, _ ) ).


% >>>>>>>>>  This version for systems that use assert/1. <<<<<<<<<

:-dynamic answer/3 .


% Clear all is_known answers.

reinitialise_answer :-
        retractall( answer( _, _, _ ) ).


% is_answer_known( +goal, +fact ):
% Does the table "answer" contain a variant of this fact paired with a variant
% of this goal?

% :-mode is_answer_known( +, +).

is_answer_known( Goal, Fact ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        answer( CopyEssence, G, F ),
        are_essences_variants( G, Goal ),
        are_essences_variants( F, Fact ),
        !.


% memo( +goal, +fact, +TraceLevel ):
% If the table "answer" does not contain a variant of this fact paired with
% a variant of this goal, then add the pair to the table, increasing
% "number_of_answers".

% :-mode memo( +, +, +).

memo( Goal, Fact, _ ) :-
        is_answer_known( Goal, Fact ),
        !.

memo( Goal, Fact, Level ) :-
        % \+ is_answer_known( Goal, Fact ),
        optional_trace( 'Storing answer: ', Goal, Fact, Level ),
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        assert( answer( CopyEssence, Goal, Fact ) ),
        dra_incval_flag( number_of_answers ).


% get_answer( +- goal ):
% Get an instantiation (if any) tabled in "answer" for variants of this goal.
% Sequence through all such instantiations on backtracking.

% :-mode get_answer( ? ).

get_answer( Goal ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        answer( CopyEssence, G, Ans ),
        once( essence_hook( G, EssenceOfG ) ),
        are_variants( EssenceOfGoal, EssenceOfG ),
        EssenceOfGoal = EssenceOfG,     % make sure variables are the right ones
        once( essence_hook( Ans, EssenceOfAns ) ),
        EssenceOfGoal = EssenceOfAns .  % instantiate


% get_all_tabled_goals(-list of goals ):
% Get all the goals that were tabled together with their answers.

get_all_tabled_goals( Goals ) :-
        findall( Goal, answer( _, Goal, _ ), Goals ).



%-----------------------------------------------------------------------------

% reinitialise_result:
% Clear the table of results.

reinitialise_result :-
        retractall( result( _, _ ) ).


% is_result_known( +index, +fact ):
% Does the table "result" contain a variant of this fact associated with this
% index?

% :-mode is_result_known( +, +).

is_result_known( PGIndex, Fact ) :-
        result( PGIndex, F ),
        are_essences_variants( F, Fact ),
        !.


% new_result_or_fail( +index, +fact ):
% If the table "result" already contains a variant of this fact associated with
% this index, then fail.  Otherwise record the fact in the table and succeed.

% :-mode new_result_or_fail( +, +).

new_result_or_fail( PGIndex, Fact ) :-
        \+ is_result_known( PGIndex, Fact ),
        assert( result( PGIndex, Fact ) ).



%------------------------------------------------------------------------------

% reinitialise_pioneer:
% Clear the table of pioneers.

reinitialise_pioneer :-
        retractall( pioneer( _, _, _ ) ).

% is_a_variant_of_a_pioneer( +goal, -index ):
% Succeeds if the goal is a variant of a goal that is tabled in "pioneer";
% returns the index of the relevant entry in table "pioneer".

% :-mode is_a_variant_of_a_pioneer( +, -).

is_a_variant_of_a_pioneer( Goal, PGIndex ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        pioneer( CopyEssence, G, PGIndex ),
        are_essences_variants( Goal, G ),
        !.


% add_pioneer( +goal, -index ):
% Add an entry for this goal to "pioneer", return the unique index.

% :-mode add_pioneer( +, -).

add_pioneer( Goal, PGIndex ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        get_unique_index( PGIndex ),
        assert( pioneer( CopyEssence, Goal, PGIndex ) ).



% delete_pioneer(+PGIndex).
% Remove the entry in "pioneer" associated with this index.

delete_pioneer( PGIndex ) :-
        retract( pioneer( _, _, PGIndex )).



%------------------------------------------------------------------------------

% reinitialise_loop:
% Clear the table of pioneers.

reinitialise_loop :-
        retractall( loop( _, _ ) ).


% add_loop( +index, +list of goals ):
% Add an entry to "loop".

% :-mode add_loop( +, +).

add_loop( _, [] ) :-                           % empty loops are not stored
        !.

add_loop( PGIndex, Goals ) :-                    % neither are duplicates
        loop( PGIndex, Gs ),
        are_variants( Goals, Gs ),
        !.

add_loop( PGIndex, Goals ) :-
        assert( loop( PGIndex, Goals ) ).


% delete_loops( +index ):
% Remove all the entries in "loop" that are associated with this index.

delete_loops( PGIndex ) :-
        retractall( loop( PGIndex, _ ) ).


% get_loop( +index, -Goals ):
% Get an entry from table "loop" that is associated with this index;
% another such entry (if it exists) on backtracking etc.

get_loop( PGIndex, Gs ) :-
        loop( PGIndex, Gs ).



%------------------------------------------------------------------------------

% reinitialise_looping_alternative:
% Clear the table of pioneers.

reinitialise_looping_alternative :-
        retractall( looping_alternative( _, _ ) ).


% add_looping_alternative( +index, +Clause ):
% Add and entry to "looping_alternative".

% :-mode add_looping_alternative( +, +).

add_looping_alternative( PGIndex, Clause ) :-     % duplicates are not stored
        looping_alternative( PGIndex, C ),
        are_variants( Clause, C ),
        !.

add_looping_alternative( PGIndex, Clause ) :-
        assert( looping_alternative( PGIndex, Clause ) ).


% delete_looping_alternatives( +index ):
% Remove all the entries in "loop" that are associated with this index.

delete_looping_alternatives( PGIndex ) :-
        retractall( looping_alternative( PGIndex, _ ) ).


% get_looping_alternative( +index, -clause ):
% Get an entry from table "looping_alternative" that is associated with this
% index; another such entry (if it exists) on backtracking etc.

get_looping_alternative( PGIndex, Clause ) :-
        looping_alternative( PGIndex, Clause ).



%------------------------------------------------------------------------------

% reinitialise_completed:
% Clear the table of completed goals.

reinitialise_completed :-
        retractall( completed( _, _ ) ).


% is_completed( +goal ):
% Succeeds iff the goal is a variant of a goal that has been stored in
% the table "completed".

% :-mode is_completed( +).

is_completed( Goal ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        completed( CopyEssence, G ),
        are_essences_variants( Goal, G ).


% complete_goal( +goal, +index for tracing ):
% Make sure the goal is marked as completed.

% :-mode complete_goal( +, +).

complete_goal( Goal, _ ) :-
        is_completed( Goal ),
        !.

complete_goal( Goal, Level ) :-
        % \+ is_completed( Goal ),
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        trace_other( 'Completing', Goal, '?', Level ),
        assert( completed( CopyEssence, Goal ) ).


%------------------------------------------------------------------------------


:-source_location(S,_),prolog_load_context(module,FM),
 forall(source_file(M:H,S),
  ignore((functor(H,F,A),
   \+ atom_concat('$',_,F),
      M:export(M:F/A),
   \+ predicate_property(M:H,transparent),
%    dra_w(M:H),
   \+ atom_concat('__aux',_,F), FM:module_transparent(M:F/A)))).

:-retract(was_access_level(Was)),set_prolog_flag(access_level,Was).



% Comment this for source maintainance
end_of_file.




/*



% :-pf(('dra/tabling3/examples/XSB/fib.tlp') ).

:-pf(('dra/tabling3/examples/co_t.tlp') ).


:-pf(('dra/tabling3/examples/coind2.tlp') ).
% :-pf(('dra/tabling3/examples/LTL/v.pl') ).
%:-pf(('dra/tabling3/examples/mini_graph.tlp') ).
%:-pf(('dra/tabling3/examples/mini_language.tlp') ).
:-pf(('dra/tabling3/examples/paper_example.tlp') ).



:-pf(('dra/tabling3/Bench/tabling3/run')).
:-pf(('dra/tabling3/Bench/prolog/run')).
:-pf(('dra/tabling3/Bench/clpfd/run')).
:-pf(('dra/tabling3/Bench/aspclp/run')).

t0:-time([('dra/tabling3/examples/XSB/farmer.tlp')]).
tn:-time([('dra/tabling3/examples/tnot1.tlp')]).
t1:-time(process_file(('dra/tabling3/examples/XSB/farmer.tlp') )),!.
t2:-time([('dra/tabling3/examples/XSB/ham.tlp')]).
t2a:-time([('dra/tabling3/examples/XSB/ham_auto.tlp')]).

t2b:-time(pf(('dra/tabling3/examples/XSB/ham.tlp') )).
t3:-[(('dra/tabling3/examples/graph.tlp') )].
t4:-pf(('dra/tabling3/examples/module.tlp') ).
t4:-[(('dra/tabling3/examples/paper_example.tlp') )].
t4:-pf(('dra/tabling3/examples/conditional.clp') ).
t4:-pf(('dra/tabling3/examples/simple1.tlp') ).
t4:-pf(('dra/tabling3/examples/simple1_old_first.tlp') ).
t4:-pf(('dra/tabling3/examples/conditional.clp') ).
t4:-pf(('dra/tabling3/examples/small_comment_example.tlp') ).
t4:-pf(('dra/tabling3/examples/coind_new.tlp') ).
t5:-consult('/devel/LogicmooDeveloperFramework/PrologMUD/packs/MUD_PDDL/prolog/dra/tabling3/Bench/tabling/tcl.pl').

*/


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

%%  Table-handling procedures for the "dra" interpreter.                    %%%
%%                                                                          %%%
%%  Written by Feliks Kluzniak at UTD (March 2009)           .              %%%
%%                                                                          %%%
%%  Last update: 27 August 2009.                                            %%%
%%                                                                          %%%

% The tables are normally kept in asserted clauses, but for some systems this
% is not convenient, because asserted clauses are compiled.
% For example, this is so in SWI Prolog, which in addition does not assert
% cyclic terms, so  for that system the "recorded" database is more
% appropriate.
% In order to facilitate such changes, routines for handling the table is
% factored out of the main program.



% >>>>>>>>>  This version for systems that use the recorded database. <<<<<<<<<


%------------------------------------------------------------------------------

% ensure_recorded( + key, + item ):
% Make sure that the item is recorded in the database.

ensure_recorded( Key, Item ) :-
        (
            recorded( Key, Item )
        ->
            true
        ;
            recordz( Key, Item )
        ).




%------------------------------------------------------------------------------

% Each item recorded for table "answer" is of the form
% "answer( Filter, Goal, Fact )", where "Filter" is the essence of a copy of
% "Goal".
% The item is recorded under the key "Goal" , i.e., effectively the key is the
% principal functor of the goal.  A most general instance of the key is
% additionally recorded under the key "answer_key".


% Clear all known answers (and keys).

reinitialise_answer :-
        recorded( answer_key, Key, RefKey ),
        erase( RefKey ),
        recorded( Key, answer( _, _, _ ), RefAnswer ),
        erase( RefAnswer ),
        fail.

reinitialise_answer.


% is_answer_known( + goal, + fact ):
% Does the table "answer" contain a variant of this fact paired with a variant
% of this goal?

% :-mode is_answer_known( +, + ).

is_answer_known( Goal, Fact ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recorded( Goal, answer( CopyEssence, G, F ) ),
        are_essences_variants( G, Goal ),
        are_essences_variants( F, Fact ),
        !.


% memo( + goal, + fact, + level for tracing ):
% If the table "answer" does not contain a variant of this fact paired with
% a variant of this goal, then add the pair to the table, increasing
% "number_of_answers".

% :-mode memo( +, +, + ).

memo( Goal, Fact, _ ) :-
        is_answer_known( Goal, Fact ),
        !.

memo( Goal, Fact, Level ) :-
        % \+ is_answer_known( Goal, Fact ),
        optional_trace( 'Storing answer: ', Goal, Fact, Level ),
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recordz( Goal, answer( CopyEssence, Goal, Fact ) ),
        most_general_instance( Goal, Key ),
        ensure_recorded( answer_key, Key ),
        dra_incval_flag( number_of_answers ).

%------------------------------------------------------------------------------
% most_general_instance( + a term,
%                        - a most general instance with the same main functor
%                      ):
% E.g., p( a, q( X, Y ) )  is transformed to  p( _, _ ).

% :-mode most_general_instance( +, -).

most_general_instance( Term, Pattern ) :-
        functor( Term, Name, Arity ),
        functor( Pattern, Name, Arity ).



% get_answer( +- goal ):
% Get an instantiation (if any) tabled in "answer" for variants of this goal.
% Sequence through all such instantiations on backtracking.

% :-mode get_answer( ? ).

get_answer( Goal ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        once( essence_hook( Goal, EssenceOfGoal ) ),
        recorded( Goal, answer( CopyEssence, G, Ans ) ),
        once( essence_hook( G, EssenceOfG ) ),
        are_variants( EssenceOfGoal, EssenceOfG ),
        EssenceOfGoal = EssenceOfG,     % make sure variables are the right ones
        once( essence_hook( Ans, EssenceOfAns ) ),
        EssenceOfGoal = EssenceOfAns .  % instantiate


% get_all_tabled_goals(-list of goals ):
% Get all the goals that were tabled together with their answers.

get_all_tabled_goals( Goals ) :-
        findall( Goal,
                 (recorded( answer_key, Key ),
                  recorded( Key, answer( _, Goal, _ ) )
                 ),
                 Goals
               ).



%------------------------------------------------------------------------------

% Each item recorded for table "result" is of the form "result( Fact )".
% The item is recorded under the key "Index".  The index is additionally
% recorded under the key "result_key".

% reinitialise_result:
% Clear the result table.
reinitialise_result :-
        recorded( result_key, Index, RefIndex ),
        erase( RefIndex ),
        recorded( Index, result( _ ), RefResult ),
        erase( RefResult ),
        fail.

reinitialise_result.


% is_result_known( + index, + fact ):
% Does the table "result" contain a variant of this fact associated with this
% index?

% :-mode is_result_known( +, + ).

is_result_known( Index, Fact ) :-
        recorded( Index, result( F ) ),
        are_essences_variants( F, Fact ),
        !.


% new_result_or_fail( + index, + fact ):
% If the table "result" already contains a variant of this fact associated with
% this index, then fail.  Otherwise record the fact in the table and succeed.

% :-mode new_result_or_fail( +, + ).

new_result_or_fail( Index, Fact ) :-
        \+ is_result_known( Index, Fact ),
        recordz( Index, result( Fact ) ),
        ensure_recorded( result_key, Index ).



%-------------------------------------------------------------------------------

% Each item recorded for table "pioneer" is of the form
% "pioneer( Filter, Goal, Index )" (where "Index" is unique and "Filter" is the
% essence of a copy of "Goal".
% The item is recorded under the key "Goal" , i.e., effectively the key is the
% principal functor of the goal.  A most general instance of the goal is
% additionally  recorded under the key "pioneer_key".
% Moreover, to speed up delete_pioneer/1, the key is recorded also as
% "pioneer_goal( Key )" under the key "Index".


% reinitialise_pioneer:
% Clear the table of pioneers.

reinitialise_pioneer :-
        recorded( pioneer_key, Key, RefIndex ),
        erase( RefIndex ),
        recorded( Key, pioneer( _, _, _ ), RefResult ),
        erase( RefResult ),
        fail.

reinitialise_pioneer.


% is_a_variant_of_a_pioneer( + goal, -index ):
% Succeeds if the goal is a variant of a goal that is tabled in "pioneer";
% returns the index of the relevant entry in table "pioneer".

% :-mode is_a_variant_of_a_pioneer( +, -).

is_a_variant_of_a_pioneer( Goal, Index ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recorded( Goal, pioneer( CopyEssence, G, Index ) ),
        are_essences_variants( Goal, G ),
        !.


% add_pioneer( + goal, -index ):
% Add an entry for this goal to "pioneer", return the unique index.

% :-mode add_pioneer( +, -).

add_pioneer( Goal, Index ) :-
        get_unique_index( Index ),
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recordz( Goal, pioneer( CopyEssence, Goal, Index ) ),
        most_general_instance( Goal, Key ),
        ensure_recorded( pioneer_key, Key ),
        recordz( Index, pioneer_goal( Key ) ).


% delete_pioneer( + index ):
% Remove the entry in "pioneer" associated with this index.

% :-mode delete_pioneer( + ).

delete_pioneer( Index ) :-
        recorded( Index, pioneer_goal( Key ), RefIndex ),
        erase( RefIndex ),
        recorded( Key, pioneer( _, _, Index ), RefPioneer ),
        erase( RefPioneer ).



%-------------------------------------------------------------------------------

% Each item recorded for table "loop" is of the form "loop( Goals )".
% The item is recorded under the key "Index", where "Index" is the index
% associated with the loop.
% The index is additionally recorded under the key "loop_key".


% reinitialise_loop:
% Clear the table of pioneers.

reinitialise_loop :-
        recorded( loop_key, Index, RefIndex ),
        erase( RefIndex ),
        delete_loops( Index ),
        fail.

reinitialise_loop.


% delete_loops( + index ):
% Remove all the entries in "loop" that are associated with this index.

delete_loops( Index ) :-
        recorded( Index, loop( _ ), RefLoop ),
        erase( RefLoop ),
        fail.

delete_loops( _ ).


% add_loop( + index, + list of goals ):
% Add an entry to "loop".

% :-mode add_loop( +, + ).

add_loop( _, [] ) :-                           % empty loops are not stored
        !.

add_loop( Index, Goals ) :-                    % neither are duplicates
        get_loop( Index, Gs ),
        are_variants( Goals, Gs ),
        !.

add_loop( Index, Goals ) :-
        recordz( Index, loop( Goals ) ),
        ensure_recorded( loop_key, Index ).


% get_loop( + index, -Goals ):
% Get an entry from table "loop" that is associated with this index;
% another such entry (if it exists) on backtracking etc.

get_loop( Index, Gs ) :-
        recorded( Index, loop( Gs ) ).



%-------------------------------------------------------------------------------

% Each item recorded for table "looping_alternative" is of the form
% "looping_alternative( Clause )".
% The item is recorded under the key "Index", where "Index" is the index
% associated with the looping_alternative.
% The index is additionally recorded under the key "looping_alternative_key".


% reinitialise_looping_alternative:
% Clear the table of pioneers.

reinitialise_looping_alternative :-
        recorded( looping_alternative_key, Index, RefIndex ),
        erase( RefIndex ),
        delete_looping_alternatives( Index ),
        fail.

reinitialise_looping_alternative.


% delete_looping_alternatives( + index ):
% Remove all the entries in "loop" that are associated with this index.

delete_looping_alternatives( Index ) :-
        recorded( Index, looping_alternative( _ ), RefLoop ),
        erase( RefLoop ),
        fail.

delete_looping_alternatives( _ ).


% add_looping_alternative( + index, + Clause ):
% Add and entry to "looping_alternative".

% :-mode add_looping_alternative( +, + ).

add_looping_alternative( Index, Clause ) :-     % duplicates are not stored
        get_looping_alternative( Index, C ),
        are_variants( Clause, C ),
        !.

add_looping_alternative( Index, Clause ) :-
        recordz( Index, looping_alternative( Clause ) ),
        ensure_recorded( looping_alternative_key, Index ).


% get_looping_alternative( + index, -clause ):
% Get an entry from table "looping_alternative" that is associated with this
% index; another such entry (if it exists) on backtracking etc.

get_looping_alternative( Index, Clause ) :-
        recorded( Index, looping_alternative( Clause ) ).



%-------------------------------------------------------------------------------

% Each item recorded for table "completed" is of the form
% "completed( Filter, Goal )", where "Filter" is the essence of a copy of
% "Goal".
% The item is recorded under the key "Goal" , i.e., effectively the key is the
% principal functor of the goal.  A most general instance of the goal is
% additionally recorded under the key "completed_key".


% reinitialise_completed:
% Clear the table of completed goals.

reinitialise_completed :-
        recorded( completed_key, Key , RefIndex ),
        erase( RefIndex ),
        recorded( Key, completed( _, _ ), RefResult ),
        erase( RefResult ),
        fail.

reinitialise_completed.


% is_completed( + goal ):
% Succeeds iff the goal is a variant of a goal that has been stored in
% the table "completed".

% :-mode is_completed( + ).

is_completed( Goal ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recorded( Goal, completed( CopyEssence, G ) ),
        are_essences_variants( Goal, G ).


% complete_goal( + goal, + index for tracing ):
% Make sure the goal is marked as completed.

% :-mode complete_goal( +, + ).

complete_goal( Goal, _ ) :-
        is_completed( Goal ),
        !.

complete_goal( Goal, Level ) :-
        % \+ is_completed( Goal ),
        trace_other( 'Completing', Goal, '?', Level ),
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recordz( Goal, completed( CopyEssence, Goal ) ),
        most_general_instance( Goal, Key ),
        ensure_recorded( completed_key, Key ).

%-------------------------------------------------------------------------------



:- '$set_source_module'(_,user).
:- 'module'(user).

:- use_module(dra).


/*
% Simpler example than example12.pl, but the number of predicates involved in mutual recursion will also increase at runtime.

expected_variants([p(3,_),p(2,_),q(2,_),q(3,_),p(_,_)]).
% Note: p(3,_) and q(3,_) are empty tables, but they are there.
expected_answers_for_variant(p(_,_),[p(1,2),p(2,3),p(1,3)]).
expected_answers_for_variant(p(3,_),[]).
expected_answers_for_variant(p(2,_),[p(2,3)]).
expected_answers_for_variant(q(2,_),[q(2,3)]).
expected_answers_for_variant(q(3,_),[]).
*/

:-table((p/2, q/2)).
:-export((p/2, q/2)).


p(X,Y) :-p(X,Z), q(Z,Y).
p(X,Y) :-e(X,Y).
q(X,Y) :-p(X,Y).

e(1,2).
e(2,3).

:- listing(p/2).

:- once(\+ tnot(p(_X,_Y))).

:-print_tables.

:-make.
:-check.

:-gxref.

:- listing(tnot).
:- listing(table).



