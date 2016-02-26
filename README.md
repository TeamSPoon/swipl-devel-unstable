This is a highly unstable theoretical fork of SWI-Prolog 
===========================================

(95-100% complete)
===========================================
* undo/1 Hook
* delimited continuations (working/passing tests)
* attvars may override *any* predicate 
* sicstus:attribute/1
* sicstus:put_atts/2
* sicstus:get_atts/2
* xsb:verify_attributes/2
* xsb:attv_unify/2
* DRA tabling (works .. needs C storage)  
* Hashtables blobs (for DRA)

With addons 
* listing/1 shows variables

(>40% complete)
===========================================
* eclipse:meta_attributes/1  (copy_term/2, ==/2, =@=/2, etc)
* sicstus:verify_attributes/3 (90%)
* mode/1, det/1, ndet/1


https://github.com/logicmoo/swipl-devel/blob/ATT_LOGICMOO/library/tabling/dra_interp.pl#L5692-L6101
````
[11979 steps, 1001 new answers tabled (1001 in all)]
Fib of 1000 is 70330367711422815821835254877183549770181269836358732742604905087154537118196933579742249494562611733487750449241765991088186363265450223647106012053374121273867339111198139373125598767690091902245245323403501
% 6,729,826 inferences, 4.405 CPU in 4.410 seconds (100% CPU, 1527685 Lips)
````
Tries based ssytme in C that is efficant as copy_term?

if i want to store  `p(q(r,A,B,t),A) = foo`.   i create a few levels deep of HTs .. 
`p/2 -> q/4 -> r -> V1 -> V2 -> t -> V1 = fo`o

(0% complete)
===========================================
* $schedule_wakeup/1 to not create a choicepoint block
* call/1, apply/2 will not create a choicepoint block (settable)

```
?- call(member(X,[1,2])),apply(call,[!]).
1
No
```

* catch/3 will not create a choicepoint block (settable)
* *All* predicates treated as transparent (settable)
 * callers context is not changed 
 * new search order: (settable)
  * definition source module context
  * caller context



Expected incompatbilities to main SWI-Prolog
===========================================
* meta_predicate/1 sets module_transparent/1 in all cases
* More issues: https://github.com/logicmoo/fluentvars/issues


Other ideas
==========================================

* delimited continuations tabling (60%)
````
work in progress
````
 * This library is described in the paper "Tabling as Library with Delimited Control" 
 * by Benoit Desouter, Marko van Dooren and Tom Schrijvers. (Email: Benoit dot Desouter at UGent dot be)
 * http://www-ps.informatik.uni-kiel.de/kdpd2013/talks/schrijvers.pdf
 * http://arxiv.org/pdf/1507.08087v1.pdf



Fluentvars is a more complete set of handlers for attributed variable operations, so that attributes are not only taken into account for unification, but also for other generic operations such as term copying and subsumption tests.

The attributed variable durring unification decides (using hooks) the ways in which it will be manipulated by the unification.

The programmer programmer may make desisions this way in how to deal with foreign (non prolog datatypes) such as xpce refs,  or pattern matchers,   .. 

Attributed Prolog variables that may remain (Free) attributed prolog variables even after unifying with nonvars! 

This can work out fine when the programmer is thinking the goal was to deal with foreign (non prolog datatypes) such as xpce refs,  or pattern matchers,   .. The attributed variable does a "check" durring unification and "it decides" (using hooks) the ways in which it will be manipulated by the unification.

Sound bizare?

Not so much, currently this is true:  

````
?-  freeze(Foo,setarg(1,Foo,cant)),  Foo=break_me(borken), Foo==break_me(cant).
Foo = break_me(cant).
````

And it is even OK to have variables that are (in themselves) able to turn unification with '='/2 into a choice point factory.

````
?- when(nonvar(X),member(X,[a(1),a(2),a(3)])), !, X=a(_).
X = a(1) ;
X = a(2) ;
X = a(3).
````


This library will explores examples explores useful tricks and chicanery that are available with TermSinks.


````
%% subsumer_var(-X) is det.
%
%  Each time it is bound, it potentially becomes less bound!
%
%
% subsumer_var(X):- termsource(X),init_accumulate(X,subsumer_var,term_subsumer).
%
% ==
%  ?-  subsumer_var(X), X= a(1), X = a(2).
%  X = a(_)  ;
% false.
%
%  ?-  subsumer_var(X), X= a(1), X = a(2),  X=a(Y).
% X = a(Y).
% Y = _G06689  ;
% false.
%
%  ?-  subsumer_var(X), X= a(1), X = a(2),  X=b(1).
% false
% ==
%

subsumer_var(X):- mvar_set(X,+remainVar),init_accumulate(X,pattern,term_subsumer).

init_accumulate(Var,M,P):-put_attr(Var,accume,init_accumulate(Var,M,P)).

accume:verify_attributes(Var,Value,[]):- get_attr(Var,accume,Attr),accum_hook(Attr,Value).

% we have our first value!
accum_hook(init_accumulate(Var,M,P),Value):- nonvar(Value),!,put_attr(Var,accume,accume_value(Var,M,P,Value)).
% some other attribute module is trolling us (make no internal changes)
accum_hook(init_accumulate(_,_,_),Value):- !,var(Value).
% we have our subsumer job 
accum_hook(accume_value(Var,M,P,Prev),Value):- nonvar(Value),!,call(P, Prev,Value,Combined),nonvar(Combined),put_attr(Var,accume,accume_value(Var,M,P,Combined)).
% Someone passed a variable and we are a "termsource" (this is the signal to drain the bilge)
accum_hook(accume_value(_Var,_M,P,Prev),Value):-  var(Value),!, nonvar(P), wno_hooks(Prev=Value).
````




Adding Paul Tarau's Fluents to SWI-Prolog.  

A Fluent is a prolog variable that has coroutines attached (and sometimes not).   What makes them different from attributed variables is that the Prolog's VM doesn't always need to provide these variables with backtracking or wakeups  ( or example EmptySinkFluent is a variable that is always free and never needs to be trailed yet two instances can be compared using == ).    Fluents can also be heavy: a text file can be a CharacterSourceFluent which is a variable that every time you REDO it moves to the next character in a file.  

Paul has many examples of what can be done with Fluents @  [http://www.cse.unt.edu/~tarau/research/99/fluents.html](http://www.cse.unt.edu/~tarau/research/99/fluents.html)  Some of the things listed there can already be done by SWI-Prolog.   Disclosure:  Douglas Miles i snot being seduced by "uniform interface for controlling multiple interpreters"  it seems interesting though!  And O_TERMSINK enables all of Paul's API documented.  But Douglas had developed this for a different end application,  it is so he and others he works for (but can't disclose)will stop feeling compelled to write yet another no gc crippled prolog in 2000 lines of C/C++ to enter into [CADE](http://www.cadeinc.org/) , [CASC](http://www.cs.miami.edu/~tptp/CASC/) and [IJCAR](http://www.ijcar.org/) or [ICAPS ](http://icaps16.icaps-conference.org/)  because of some idea they needed finer grained control of unification and backtracking and yet not interested in the rest of prolog.   And in doing some research discovered that coincidentally most of these those selective *cripplings* and *enhancements* of prolog ran parallel to having the identical controls required to produce BinProlog's Fluent model.  And still comes with the bonus API for those whom have a fetish for "uniform interface for controlling multiple interpreters".    Secretly, `verify_attributes/3` was implemented merely by converting all attvars to `fluent_sink/1`s  and then assigned in prolog's backdoor call to `'$attvar_assign'/2`)

Here is an example of a source_fluent presently in SWI-Prolog:

````
?- when(nonvar(_V),member(_V,[the(1),the(2),the(3)])), !, _V=the(X).
X=1;
X=2;
X=3
````

The cut in the above was just to remind us that the choicepoints are triggered in the unification.

O_TERMSINK would allow 

````
?- fluent_source(X), when(=(X,_),member(X,[1,2,3])), !, X=_.
X=1;
X=2;
X=3
````

An example of a sink_fluent presently in SWI-Prolog:

````
?- when(nonvar(V),
  (arg(1,V,C),flag(test,F,F+C),setarg(1,V,NewVar),
    when(nonvar(NewVar),
       (arg(1,V,C0),
        flag(test,F0,F0+C0),setarg(1,V,NewVarTwo))),
    when(nonvar(NewVarTwo),
       (arg(1,V,C1),
        flag(test,F1,F1+C1),setarg(1,V,_))))),
    V=the(1),V=the(2),V=the(3).
V = the(2),
C = F0, F0 = 1,
F = 0,
NewVar = C0, C0 = 2,
NewVarTwo = C1, C1 = F1, F1 = 3.

?- flag(test,W,W).

W = 6.
````

O_TERMSINK allows

````
?-fluent_sink(X),fluent_source(X),
    when(=(X,_),nonvar(X)->flag(test,F,F+X);flag(test,X,X)),X=1,X=2,X=3.
X=6
````

#### Fluent Constructors

**fluent_sink(-Sink).**

1 #define X_no_bind 1 /* This tells C, even when asked to, to not bind the variable */

**fluent_source(-Source)**

1 #define X_on_unify_keep_vars 6 /* when unifying with a variable call $wakeup/1 using the variable instead of being put inside the other variable (our verify_attributes or a better hook may, in this case, label that other var) */

All composers start out decending for one or both constructors

#### Fluent Composers

*Fluent composers* provide abstract operations on `Fluents`. They are implemented with lazy semantics.  

`append_sources/3` creates a new `Source` with a `=/2` operation such that when the first `Source` is stopped, iteration continues over the elements of the second `Source`.

`compose_sources/3` provides a cartesian product style composition, the new `=/2` operation returning pairs of elements of the first and second `Source`.

`reverse_source/2` builds a new Source such that its `=/2` method returns its elements in reverse order.

`split_source/3` creates two `Source` objects identical to the `Source` given as first argument. It allows writing programs which iterate over a given `Source` multiple times.

`Sources` and `Sinks` may be related through a `discharge(+Source,+Sink)` operation which sends all the elements of the `Source` to the given `Sink`.

#### Fluent modifiers

To dynamically changing some attributes of a give Fluent. 

**For optimizations**

BinProlog's `set_persistent(Fluent,YesNo)` or SWI-Prolog's `attvar_override(Fluent, (+/-)no_trail)` thus
````
set_persistent(Var,YesNo):- 
  YesNo=yes ->  
    attvar_override(Var,+no_trail) ; 
    attvar_override(Var,-no_trail) .

````
1 #define X_no_trail 2 /* Do not bother to trail the attvars previous value */

`attvar_override(Fluent, +no_wakeup)`

1 #define X_no_wakeup 3 /* This tells C, it can skip calling $wakup/1  */

````
dont_care(Fluent):-attvar_override(Fluent, +no_wakeup+no_trail+no_bind).
````

**For brevity**

`attvar_override(Fluent, +peer_wakeup)`

1  #define X_peer_wakeup 5 /* schedule wakeup on other attvar's peers we unify with */

`attvar_override(Fluent, +peer_trail)`

1  #define X_peer_trail 4 /* Trail any assignment we are about to make on other variables */

`attvar_override(Fluent, +peer_trail)`

1  #define X_on_unify_replace 7 /* unify does not replace the attvar.. but the other way around */

#### Development modifiers

Used like:  `attvar_override(Fluent,+no_vmi)` or `attvar_default(_,+no_vmi)`

/* per var overloaded */
````
#define X_disabled 0 /* Usually for enable the interp to run recursively not calling $wakeup (implies no_inherit) so that C may do our assignments instead of $wakeup */
#define X_no_inherit 8 /* this term sink doesn't not inherit flags */
#define X_uses_eager 9 /* this variable would like a chance to implement term comparison operators itself */ 
#define X_debug_attvars 10 /* print extra debug for ourselves */
#define X_debug_extreme  11 /* print extra debug for ourselves */
#define X_no_vmi 29 /* direct LD->slow_unify to be true for us to work */
#define X_vmi_ok 30 /* direct LD->slow_unify is optional */
```

#### Finer control term comparisons

attvar_default(`equal`,`eager`).  /* to make  ==/2 trigger a call to 
` eager_lr(equal,AttVar,Value)`  or  `eager_rl(equal,AttVar,Value) ` */

1 #define WHEN_per_var_eager 0
````
#define WHEN_eager 0
#define WHEN_normal 1
#define WHEN_override 1
````
````
#define WHAT_unify 0 /*  eager(=) */
#define WHAT_equal 1 /*  eager(==) call can_unify for isomorphic testing on specialAttibutedVars */
#define WHAT_variant 2 /*  eager(=@=) */
#define WHAT_unifiable 3 /*  eager(unifiable) */
#define WHAT_assignment 4 /* prioritize assignment  */
#define WHAT_copy_term 5 /*  eager(copy_term) */
#define WHAT_compare 6 /*  eager(compare) */
#define WHAT_bind_const 7
#define WHAT_unify_vp 8 /* unify_vp*/
#define WHAT_bind_vp 9 /* bind_vp*/
````

`SCRATCH TEXT`

````
/*
   Some experiments ongoing
   O_TERMSINK
         Attributed variables call $wakeup basically after their identities (the tagged variable) has been 
         removed from the current call So now the wakeups like attrib_unify_hook/2 decide 
        the effective binding of this.  Sometimes keep the attributed variable unbound despite
         being unified with a term?!? (This is what Tarau's EmtpySinks do!)
         requires O_ATTVAR
   O_ATTVAR_EAGER
         Notice potential wakeups eagerly, for example instead of being put into Variables.. 
        in do_unify(..)  the L or R side of the unify might decide.. or Before/After.
        So the above wakeups decide maybe if a binding will put into the variable instead of the attributed variable
         (Maybe allow to run code early enough the attributed variables binding is decided by attrib_unify_hook  )
   O_DONTCARE_TAGS
       We can test the implications of using variables that need no trail/undo/copy_term that claim to 
       unify with everything and remains free afterwards Currently I am implementing using attributed variables which should degrade performance but i want to see if it can be done correctly  
       eventually this would not be an attributed variable but 
        a single variable in the system that (effectively could be a constant) or *_TAG'ed *if we had any space for it(
   With any of the above set the system still operates as normal
              until the user invokes  '$sinkmode'/2 to 
   None of these option being enabled will cost more than 
              if( (LD->attrvar.gsinkmode & SOME_OPTION) != 0) ...
  
    
*/
Variables prolog programmers secretly want but are afraid or embarrassed to ask for.
"don't care" variables that don't bother saving an undo.
"really don't care!" variables that neither bother saving an undo or even bound after unification. copy_term/2 simply copies it like a constant (because of this, only one is needed in the entire system) 
"Sinks"    Which is an â€œattributedâ€ â€œdon't care" variable so that we can allow $wakeup/1 to control its binding state (however the supposed binding would be saved by wakeup calling  b_setarg or nb_setarg in one of the attributes  )
Or Paul Tarau's  "Term Sources" 
Which is yet another "attributed" â€œdon't care" variable  however  they  appear to have had label/1 called to create potential choice points (perhaps by  attr_unify_hook/2).        S

ometimes a pipe (non i/o) may be created using Fluent  TermSink  together  with a TermSource.     TermSink  is setting values somewhere and TermSource is reading those values.

Term Sources we can have:



A  (yet distasteful to purists) example:

````
mother(the(kid),the(mother)).
father(the(kid),the(father)).
cie(kid,joey).
cie(A,D):-atom(A),downcase_atom(A,D).
cie(A,U):-atom(A),upcase_atom(A,U).
predunify_var(Pred,Var):-
 put_attr(Memory,or_equals,u(Pred,_)), 
 when(nonvar(Var),
  (
   arg(1,Var,Value),
   get_attr(Memory,or_equals,u(Pred,Was)),
   (equals(Value,Was);equals(Was,Value)),
   put_attr(Memory,or_equals,u(Pred,Value)),
   setarg(1,Var,_))).
attr_unify_hook(u(Pred,Was),Var):- nonvar(Var) -> true; Var=the(Was).

?- predunify_var(cie,V), V=the('JOEY'), mother(V,the(mother)).
Yes.
````

