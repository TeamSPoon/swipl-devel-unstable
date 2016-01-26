/* Picture puzzles, a.k.a. Nonograms.
 *
 * Problem 12 at http://www.csplib.org/
 *
 * Author    : Mats Carlsson
 *
 */

:- module(starpic, [
        starpic/2
        ]).

:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(clpfd)).

%?- time(starpic(p200, Vs)).
%@ % 80,505,002 inferences, 14.078 CPU in 14.147 seconds (100% CPU, 5718389 Lips)
%@ Vs = [0, 1, 0, 1, 0, 0, 0, 0, 0|...] ;
%@ % 25,407,074 inferences, 4.405 CPU in 4.434 seconds (99% CPU, 5767828 Lips)
%@ false.

starpic(ID, Vs) :-
        data(ID, RowData, ColData),
        length(RowData, NRows),
        length(ColData, NCols),
        length(Rows, NRows),
        binary_rows(Rows, NCols),
        transpose(Rows, Cols),
        constraints(Rows, RowData),
        constraints(Cols, ColData),
        append(Rows, Vs),
        label(Vs).

binary_rows([], _).
binary_rows([X|Xs], N) :-
        length(X, N),
        X ins 0..1,
        binary_rows(Xs, N).

constraints([], []).
constraints([Row|Rows], [Datum|Data]) :-
        phrase(arcs(Datum, Source, Sink), Arcs),
        automaton(Row, _, Row, [source(Source),sink(Sink)], Arcs, [], [], []),
        constraints(Rows, Data).

arcs([], S, S)      --> [arc(S,0,S)].
arcs([C|Cs], S0, S) --> [arc(S0,0,S0)],
        ones(C, S0, S1),
        cont(Cs, S1, S).

cont([], S, S)      --> [arc(S,0,S)].
cont([C|Cs], S0, S) --> [arc(S0,0,S1),arc(S1,0,S1)],
        ones(C, S1, S2),
        cont(Cs, S2, S).

ones(0, S, S) --> !.
ones(I, S0, S) --> [arc(S0,1,S1)],
        {J #= I-1},
        ones(J, S1, S).


data(p200, [[1,1,2,2],[5,5,7],[5,2,2,9],[3,2,3,9],[1,1,3,2,7],[3,1,5],[7,1,1,1,3],[1,2,1,1,2,1],[4,2,4],[1,2,2,2],[4,6,2],[1,2,2,1],[3,3,2,1],[4,1,15],[1,1,1,3,1,1],[2,1,1,2,2,3],[1,4,4,1],[1,4,3,2],[1,1,2,2],[7,2,3,1,1],[2,1,1,1,5],[1,2,5],[1,1,1,3],[4,2,1],[3]],
    [[2,2,3],[4,1,1,1,4],[4,1,2,1,1],[4,1,1,1,1,1,1],[2,1,1,2,3,5],[1,1,1,1,2,1],[3,1,5,1,2],[3,2,2,1,2,2],[2,1,4,1,1,1,1],[2,2,1,2,1,2],[1,1,1,3,2,3],[1,1,2,7,3],[1,2,2,1,5],[3,2,2,1,2],[3,2,1,2],[5,1,2],[2,2,1,2],[4,2,1,2],[6,2,3,2],[7,4,3,2],[7,4,4],[7,1,4],[6,1,4],[4,2,2],[2,1]]).
