/*  Part of SWI-Prolog

    Author:        Henk Vandecasteele
    E-mail:        henk.vandecasteele@cs.kuleuven.ac.be
    WWW:           http://www.swi-prolog.org
    Copyright (C): Public domain
*/

/** <module> XSB compatibility layer

This file contains some predicates that   are  defined in BIM-prolog and
not in SWI-prolog (or at least not  with   the  same meaning). In case a
predicate has a different meaning in  SWI-prolog   and  in proLog by BIM
renaming is done.  Remark  that  some   predicates  are  only  partially
covered, feel free to add.

@author  Henk Vandecasteele
         Departement Computerwetenschappen
         Katholiek Universiteit Leuven
         Celestijnenlaan 200A
         3001 Heverlee
         BELGIUM
         henk.vandecasteele@cs.kuleuven.ac.be
*/


:- module(machine,[]).

/*
Example XSB Support
*/



% Switches us from verify_attributes/3 to verify_attributes/2 support
% This predicate is called whenever an attributed variable Var (which has at least one attribute) 
% is about to be bound to Value (a non-variable term or another attributed variable). 
% When Var is to be bound to Value, a special interrupt called attributed variable 
% interrupt is triggered, and then XSB's interrupt handler (written in Prolog) calls 
% verify_attributes/2. If it fails, the unification is deemed to have failed. 
% It may succeed non-deterministically, in which case the unification 
% might backtrack to give another answer.
:- module_transparent(system:verify_attributes/3).
system:verify_attributes(Var, Value, []):- 
      context_module(Mod),
      Mod:verify_attributes(Var, Value).

