This is a highly unstable theoretical fork of SWI-Prolog 
===========================================

(>95% complete)
===========================================
* undo/1 Hook
* delimited continuations (working/passing tests)
* attvars may override *any* predicate 
* sicstus:attribute/1
* sicstus:put_atts/2
* sicstus:get_atts/2
* xsb:verify_attributes/2
* xsb:attv_unify/2
* listing/1 shows variables

(>40% complete)
===========================================
* eclipse:meta_attributes/1  (copy_term/2, ==/2, =@=/2, etc)
* sicstus:verify_attributes/3 (90%)
* dra-tabling interpretor (works .. needs C storage)  https://github.com/logicmoo/swipl-devel/blob/ATT_LOGICMOO/library/tabling/dra_interp.pl#L5692-L6101
````
[11979 steps, 1001 new answers tabled (1001 in all)]
Fib of 1000 is 70330367711422815821835254877183549770181269836358732742604905087154537118196933579742249494562611733487750449241765991088186363265450223647106012053374121273867339111198139373125598767690091902245245323403501
% 6,729,826 inferences, 4.405 CPU in 4.410 seconds (100% CPU, 1527685 Lips)
````
Tries based ssytme in C that is efficant as copy_term?

if i want to store  `p(q(r,A,B,t),A) = foo`.   i create a few levels deep of HTs .. 
`p/2 -> q/4 -> r -> V1 -> V2 -> t -> V1 = fo`o

* delimited continuations tabling (60%)
````
work in progress
````
 * This library is described in the paper "Tabling as Library with Delimited Control" 
 * by Benoit Desouter, Marko van Dooren and Tom Schrijvers. (Email: Benoit dot Desouter at UGent dot be)
 * http://www-ps.informatik.uni-kiel.de/kdpd2013/talks/schrijvers.pdf
 * http://arxiv.org/pdf/1507.08087v1.pdf

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


