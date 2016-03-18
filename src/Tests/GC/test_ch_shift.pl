:- module(test_ch_shift,
	  [ test_ch_shift/0
	  ]).

%%	test_ch_shift
%
%	Tests expansion of the local stack due to a clause with many
%	choicepoints.

% TODO SEGVs on Cygwin
:- if( \+ current_prolog_flag(arch,'x86_64-cygwin')).


test_ch_shift :-
	trim_stacks,
	make_or(10000, OR),
	asserta((t :- OR), Ref),
	once(t),
	erase(Ref).

:- else.


test_ch_shift :-
	trim_stacks,
	make_or(100, OR),
	asserta((t :- OR), Ref),
	once(t),
	erase(Ref).


:- endif.

make_or(0, a) :- !.
make_or(N, (G;a)) :-
	N2 is N - 1,
	make_or(N2, G).

a.
