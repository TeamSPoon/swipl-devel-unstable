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
%:- user:ensure_loaded(library(dra/tabling3/dra_table_assert)).
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

:- dynamic answer/3 .


% Clear all is_known answers.

reinitialise_answer :-
        retractall( answer( _, _, _ ) ).


% is_answer_known( +goal, +fact ):
% Does the table "answer" contain a variant of this fact paired with a variant
% of this goal?

% :- mode is_answer_known( +, +).

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

% :- mode memo( +, +, +).

memo( Goal, Fact, _ ) :-
        is_answer_known( Goal, Fact ),
        !.

memo( Goal, Fact, Level ) :-
        % \+ is_answer_known( Goal, Fact ),
        optional_trace( 'Storing answer: ', Goal, Fact, Level ),
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        assert( answer( CopyEssence, Goal, Fact ) ),
        incval( number_of_answers ).


% get_answer( +- goal ):
% Get an instantiation (if any) tabled in "answer" for variants of this goal.
% Sequence through all such instantiations on backtracking.

% :- mode get_answer( ? ).

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


% get_all_tabled_goals( - list of goals ):
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

% :- mode is_result_known( +, +).

is_result_known( PGIndex, Fact ) :-
        result( PGIndex, F ),
        are_essences_variants( F, Fact ),
        !.


% new_result_or_fail( +index, +fact ):
% If the table "result" already contains a variant of this fact associated with
% this index, then fail.  Otherwise record the fact in the table and succeed.

% :- mode new_result_or_fail( +, +).

new_result_or_fail( PGIndex, Fact ) :-
        \+ is_result_known( PGIndex, Fact ),
        assert( result( PGIndex, Fact ) ).



%------------------------------------------------------------------------------

% reinitialise_pioneer:
% Clear the table of pioneers.

reinitialise_pioneer :-
        retractall( pioneer( _, _, _ ) ).

% is_a_variant_of_a_pioneer( +goal, - index ):
% Succeeds if the goal is a variant of a goal that is tabled in "pioneer";
% returns the index of the relevant entry in table "pioneer".

% :- mode is_a_variant_of_a_pioneer( +, - ).

is_a_variant_of_a_pioneer( Goal, PGIndex ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        pioneer( CopyEssence, G, PGIndex ),
        are_essences_variants( Goal, G ),
        !.


% add_pioneer( +goal, - index ):
% Add an entry for this goal to "pioneer", return the unique index.

% :- mode add_pioneer( +, - ).

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

% :- mode add_loop( +, +).

add_loop( _, [] ) :-                                % empty loops are not stored
        !.

add_loop( PGIndex, Goals ) :-                         % neither are duplicates
        loop( PGIndex, Gs ),
        are_variants( Goals, Gs ),
        !.

add_loop( PGIndex, Goals ) :-
        assert( loop( PGIndex, Goals ) ).


% delete_loops( +index ):
% Remove all the entries in "loop" that are associated with this index.

delete_loops( PGIndex ) :-
        retractall( loop( PGIndex, _ ) ).


% get_loop( +index, - Goals ):
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

% :- mode add_looping_alternative( +, +).

add_looping_alternative( PGIndex, Clause ) :-          % duplicates are not stored
        looping_alternative( PGIndex, C ),
        are_variants( Clause, C ),
        !.

add_looping_alternative( PGIndex, Clause ) :-
        assert( looping_alternative( PGIndex, Clause ) ).


% delete_looping_alternatives( +index ):
% Remove all the entries in "loop" that are associated with this index.

delete_looping_alternatives( PGIndex ) :-
        retractall( looping_alternative( PGIndex, _ ) ).


% get_looping_alternative( +index, - clause ):
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

% :- mode is_completed( +).

is_completed( Goal ) :-
        copy_term( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        completed( CopyEssence, G ),
        are_essences_variants( Goal, G ).


% complete_goal( +goal, +index for tracing ):
% Make sure the goal is marked as completed.

% :- mode complete_goal( +, +).

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

