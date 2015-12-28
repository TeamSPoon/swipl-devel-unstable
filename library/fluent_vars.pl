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

:- module(fluent_vars,[
      attvar_override/2,
      attvar_overriding/2,
      attvar_default/2,
      fluent_sink/1,
      fluent_source/1,
      dont_care/1,
      sinkbits_to_number/2]).


:- discontiguous(test/1).
:- nodebug(attvars).
:- nodebug(termsinks).


%% fluent_sink(-X) is det.
%
% Base class of var that consumes terms 
%
fluent_sink(X):-attvar_override(X,+fluent_sink).


%% fluent_source(-X) is det.
%
% Base class of var that X may have a value
%
fluent_source(X):-attvar_override(X,+fluent_source).


%% dont_care(-X) is det.
%
% nb_no_bind term filter that will bind with anything and call no wakeups
%
dont_care(X):-attvar_override(X,no_wakeup+no_bind-peer_wakeup+no_disable).


%% sinkmode(+Set) is det.
%
% Set system wide sink modes
%
% == 
% ?-listing(bits_for_sinkmode/1) to see them.
% ==
%
%   more to come...
%
sinkmode(X):- var(X),!,'$attvar_default'(X,X).
sinkmode(X):- '$attvar_default'(M,M),merge_sinkmodes(X,M,XM),must_tst('$attvar_default'(_,XM)),!,sinkmode,!.
bits_for_sinkmode(v(
          
         disabled =bit(0), /* allows interp to run recurvely not using the eagers */
         no_bind =bit(1), /* survive bindings to even constants */
         no_trail =bit(2), /* no_trail the attvars previous value */
         no_wakeup =bit(3), /* calling wakeup early to find out if we maybe care */
         peer_trail =bit(4), /* trail any assignment we are about to make on others */
         peer_wakeup =bit(5), /* schedule wakeup on other attvars */
         on_unify_keep_vars =bit(6), /* where unifying with a variable call $wakeup/=bit(1), with the variable  */
         on_unify_linkval =bit(7), /* attempt to linkval to  what  we unify */
         no_inherit =bit(8), /* this term sink doest not inherit the global flags */
         eager_needed =bit(9), /* var needs eager */
         debug_attvars =bit(10), /* print extra debug for ourselves  */
         debug_extreme =bit(11), /* print extra debug for ourselves  */
   
         eager(unify) = eager_bit(16), /*  eager(=) */
         eager(equal) = eager_bit(17), /*  eager(==) call can_unify for equal testing on specialAttibutedVars */
         eager(variant) =eager_bit(18), /*  eager(=@=) */
         eager(unifiable) =eager_bit(19), /*  eager(unifiable) */
         eager(assignment)  =eager_bit(20),  /*  eager(assignment) */
         eager(copy_term) =eager_bit(21), /*  eager(copy_term) */
         eager(compare) =eager_bit(22), /*  eager(compare) */
         eager(bind_const) =eager_bit(23), /* use assignAttvar in assignment even against Variables (if possible)  */
         eager(unify_vp) =eager_bit(24), /* use assignAttvar in assignment even against Variables (if possible)  */
         eager(bind_vp) =eager_bit(25), /* use assignAttvar in assignment even against Variables (if possible)  */    

         override(unify) = override_bit(16), /*  override(=) */
         override(equal) = override_bit(17), /*  override(==) call can_unify for equal testing on specialAttibutedVars */
         override(variant) =override_bit(18), /*  override(=@=) */
         override(unifiable) =override_bit(19), /*  override(unifiable) */
         override(assignment)  =override_bit(20),  /*  override(assignment) */
         override(copy_term) =override_bit(21), /*  override(copy_term) */
         override(compare) =override_bit(22), /*  override(compare) */
         override(bind_const) =override_bit(23), /* use assignAttvar in assignment even against Variables (if possible)  */
         override(unify_vp) =override_bit(24), /* use assignAttvar in assignment even against Variables (if possible)  */
         override(bind_vp) =override_bit(25), /* use assignAttvar in assignment even against Variables (if possible)  */    
            
         no_vmi =bit(29), /* direct LD->slow_unify to be true for us to work */
         vmi_ok =bit(30), /* direct LD->slow_unify is optional */
         
         eager(=)  = eager(unify),
         eager(==)  = eager(equal),
         eager(=@=)  = eager(variant),
         eager(can_unify)  = eager(unifiable),
         eager(\=)  = eager(unifiable),
         eager(\=@=)  = eager(variant),
         eager(\==)  = eager(equal),

         override(=)  = override(unify),
         override(==)  = override(equal),
         override(=@=)  = override(variant),
         override(can_unify)  = override(unifiable),
         override(\=)  = override(unifiable),
         override(\=@=)  = override(variant),
         override(\==)  = override(equal),

         eagerly = (+eager(assignment)+eager(variant)+eager(equal)+eager(unifiable)),
         eager_all = (+eagerly+eager(compare)+eager(copy_term)),
         fluent_sink=(+no_bind+peer_wakeup+no_inherit),
         fluent_source=(+no_bind+peer_wakeup+no_inherit+eager(unify)+on_unify_keep_vars),
         override(X)= (eager(X)<<16)
    )). 

%% sinkmode is det.
%
% Print the system global modes
%
sinkmode:-'$attvar_default'(M,M),any_to_sinkbits(M,B),format('~N~q.~n',[sinkmode(M=B)]).


%% debug_attvars is det.
%
% Turn on extreme debugging
%
debug_attvars(true):-!, sinkmode(+debug_attvars+debug_extreme).
debug_attvars(_):- sinkmode(-debug_attvars-debug_extreme).

%% attvar_overriding(Var,BitsOut)
%
% Get a variables sink properties
%
attvar_overriding(Var,BitsOut):- '$attvar_overriding'(Var,Modes),any_to_sinkbits(Modes,BitsOut),!.


%% attvar_override(Var,BitsOut)
%
% Set a variables sink properties
%
attvar_override(Var,Modes):- var(Var),
  ((
   get_attr(Var,fluent_sink,Was)->
       (merge_sinkmodes(Modes,Was,Change),put_attr(Var,fluent_sink,Change)); 
   (sinkbits_to_number(Modes,Number),put_attr(Var,fluent_sink,Number)))),!.


:-  [swi(boot/attvar)]. 
%% attvar_override(Var,Bits)
%
% Set a variables sink properties
%
new_fluent(Bits,Var):-attvar_override(Var,Bits).

contains_bit(Var,Bit):- var(Bit),'$attvar_overriding'(Var,M),any_to_sinkbits(M,Bits),!,member(Bit,Bits).
contains_bit(Var,Bit):-'$attvar_overriding'(Var,M),sinkbits_to_number(Bit,N),!,N is N /\ M.

any_to_sinkbits(BitsIn,BitsOut):-  
 sinkbits_to_number(BitsIn,Mode),
   Bits=[Mode],bits_for_sinkmode(MASKS),
   ignore((arg(_,MASKS,(N=V)),nonvar(V),sinkbits_to_number(V,VV), VV is VV /\ Mode , nb_extend_list(Bits,N),fail)),!,
   BitsOut = Bits.


nb_extend_list(List,E):-arg(2,List,Was),nb_setarg(2,List,[E|Was]).



merge_sinkmodes(V,VV,VVV):-number(V),catch((V < 0),_,fail),!, V0 is - V, merge_sinkmodes(-(V0),VV,VVV),!.
merge_sinkmodes(V,VV,VVV):-number(V),number(VV),VVV is (V \/ VV).
merge_sinkmodes(V,VV,VVV):-var(V),!,V=VV,V=VVV.
merge_sinkmodes(set(V),_,VVV):-sinkbits_to_number(V,VVV),!.
merge_sinkmodes(V,VV,VVV):-var(VV),!, sinkbits_to_number(V,VVV),!.
merge_sinkmodes(+(A),B,VVV):- must_tst((sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V \/ VV))).
merge_sinkmodes(*(A),B,VVV):- sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V /\ VV).
merge_sinkmodes(-(B),A,VVV):- sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V /\ \ VV).
merge_sinkmodes([A],B,VVV):-  must_tst(merge_sinkmodes(A,B,VVV)),!.
merge_sinkmodes([A|B],C,VVV):-merge_sinkmodes(A,C,VV),merge_sinkmodes(B,VV,VVV),!.
merge_sinkmodes(A,C,VVV):-sinkbits_to_number(A,VV),!,must_tst(merge_sinkmodes(VV,C,VVV)),!.
merge_sinkmodes(A,C,VVV):-sinkbits_to_number(eager(A),VV),!,must_tst(merge_sinkmodes(VV,C,VVV)),!.


sinkbits_to_number(N,O):-number(N),!,N=O.
sinkbits_to_number(V,O):-var(V),!,V=O.
sinkbits_to_number([],0).
sinkbits_to_number(B << A,VVV):-!, sinkbits_to_number(B,VV), VVV is (VV << A).
sinkbits_to_number(B+A,VVV):- merge_sinkmodes(+(A),B,VVV),!.
sinkbits_to_number(B*A,VVV):- merge_sinkmodes(*(A),B,VVV),!.
sinkbits_to_number(B-A,VVV):- sinkbits_to_number(B,BB),sinkbits_to_number(A,AA),VVV is (BB /\ \ AA),!.
sinkbits_to_number(+(Bit),VVV):-sinkbits_to_number((Bit),VVV),!.
sinkbits_to_number(-(Bit),VVV):-sinkbits_to_number((Bit),V),!,VVV is ( \ V).
sinkbits_to_number(~(Bit),VVV):-sinkbits_to_number((Bit),V),!,VVV is ( \ V).
sinkbits_to_number( \ (Bit),VVV):-sinkbits_to_number((Bit),V),!,VVV is ( \ V).
sinkbits_to_number(eager_bit(Bit),VVV):-!, sinkbits_to_number(bit(Bit),VV),!,VVV is (VV \/ 2^14).  % eager needed
sinkbits_to_number(override_bit(Bit),VVV):-!, Bit4 is Bit + 4, sinkbits_to_number(bit(Bit4),VVV),!.
sinkbits_to_number(bit(Bit),VVV):- number(Bit),!,VVV is 2 ^ (Bit).
sinkbits_to_number((Name),VVV):-bits_for_sinkmode(VV),arg(_,VV,Name=Bit),!,must_tst(sinkbits_to_number(Bit,VVV)),!.
sinkbits_to_number([A],VVV):-!,sinkbits_to_number(A,VVV).
sinkbits_to_number([A|B],VVV):-!,merge_sinkmodes(B,A,VVV).
sinkbits_to_number(V,VVV) :- VVV is V.


