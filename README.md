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
* dra-tabling interpretor (works .. needs C storage)
* delimited continuations tabling (60%)
 * This library is described in the paper "Tabling as Library with Delimited Control" 
 * by Benoit Desouter, Marko van Dooren and Tom Schrijvers. (Email: Benoit dot Desouter at UGent dot be)

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
 * search order: (settable)
   * definition source module context
   * caller context



Expected incompatbilities to main SWI-Prolog
===========================================
* meta_predicate/1 sets module_transparent/1 in all cases
* More issues: https://github.com/logicmoo/fluentvars/issues


