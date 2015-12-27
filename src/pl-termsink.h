/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
		           Douglas R. Miles
    E-mail:        J.Wielemaker@uva.nl
	               logicmoo@gmail.com 
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

#ifndef PL_TERMSINK_H_INCLUDED
#define PL_TERMSINK_H_INCLUDED



/* Bits per var overloaded */
#define X_disabled 0 /* Usualy for enable the interp to run recurvely not calling $wakeup (implies no_inherit) so that C may do our assigments instead of $wakeup */
#define X_no_bind 1 /* This tells C, even when asked, to not do bindings (yet) */
#define X_no_trail 2 /* Do not bother to trail the attvars previous value */
#define X_no_wakeup 3 /* This tells C, even when asked, to not call $wakup/1  */
#define X_peer_trail 4 /* Trail any assignment we are about to make on variables */
#define X_peer_wakeup 5 /* schedule wakeup on other attvar peers we unify with */
#define X_on_unify_keep_vars 6 /* when unifying with a variable call $wakeup/1 instead of being put inside the other variable (our verify_attributes may, in this case, label that other var) */
#define X_on_unify_replace 7 /* unify doesnt replace the attvar.. bu thte otehr way arround */
#define X_no_inherit 8 /* this term sink doest not inherit the global flags */
#define X_uses_eager 9 /* this variable would like a chance to implement term comparison operators */ 
#define X_debug_attvars 10 /* print extra debug for ourselves */
#define X_debug_extreme  11 /* print extra debug for ourselves */

#define X_no_vmi 29 /* direct LD->slow_unify to be true for us to work */
#define X_vmi_ok 30 /* direct LD->slow_unify is optional */


#define WHEN_per_var_eager 0
#define WHEN_eager 0
#define WHEN_normal 1
#define WHEN_override 1

#define WHAT_unify 0 /*  eager(=) */
#define WHAT_equal 1 /*  eager(==) call can_unify for isomorphic testing on specialAttibutedVars */
#define WHAT_variant 2 /*  eager(=@=) */
#define WHAT_unifiable 3 /*  eager(unifiable) */
#define WHAT_assignment 4 /* priortize assignment  */
#define WHAT_copy_term 5 /*  eager(copy_term) */
#define WHAT_compare 6 /*  eager(compare) */
#define WHAT_bind_const 7
#define WHAT_unify_vp 8 /* unify_vp*/
#define WHAT_bind_vp 9 /* bind_vp*/

#define HOW_normal_lr 0
#define HOW_normal_rl 1
#define HOW_eager_lr 2
#define HOW_eager_rl 3
#define HOW_override_lr 4
#define HOW_override_rl 5


#define REALLY_DONT_CARE  (SINKBIT_VAL(no_bind) & SINKBIT_VAL(no_wakeup) & SINKBIT_VAL(no_trail))

#define UNSPECIAL_MASK  ( SINKBIT_VAL(no_vmi) & SINKBIT_VAL(vmi_ok) \
   & SINKBIT_VAL(no_disable) & SINKBIT_VAL(disabled) & SINKBIT_VAL(debug_attvars))

#define IS_UNSPECIAL(sinkmode)  ((sinkmode & ~UNSPECIAL_MASK)==0)

#define DONTCARE_OPTION(name) TERMSINK_ENABLED(IS_SINKMODE_GLOBAL(dont_care_uses_eager) && IS_SINKMODE_GLOBAL( name))

#define TERMSINK_ENABLED(name) ((LD->termsink.gsinkmode & SINKBIT_VAL(disabled)) == 0) && name
#define SINKBIT_N(name) X_ ## name
#define SINKBIT_VAL(name) (((int64_t)1) << SINKBIT_N(name))


#define IS_SINKMODE_FOR(modebits, name) ((modebits & SINKBIT_VAL(name)) != 0)
#define IS_SINKMODE_GLOBAL(name) IS_SINKMODE_FOR(LD->termsink.gsinkmode,name)
#define IS_SINKMODE(name) ((IS_SINKMODE_FOR(sinkmode ,name) || ((!IS_SINKMODE_FOR(sinkmode, no_inherit)) && IS_SINKMODE_GLOBAL(name))))
#define DECL_AND_GET_BOOL(name) bool name = IS_SINKMODE(name)
#define DECL_AND_SHOW(name) DECL_AND_GET_BOOL(name); DEBUG_TYPE0(name)
#define DEBUG_TYPE0(name) DEBUG_TYPE("%d",name)

#define IS_DEBUG_MASK(F) ((F & SINKBIT_VAL(debug_attvars)) != 0)
#define DEBUG_TYPE( type, name ) DEBUG_TERMSINK(if ( (name) > 0 ) DEBUG_TYPE_PRINT( type, name ))
#define DEBUG_TYPE_PRINT( type, name ) {Sdprintf("\t%%\t%s = ",#name); Sdprintf(type,(name)); Sdprintf("\n");}

#define DEBUG_UNIFY(s, t1, t2) DEBUG_TERMSINK(Sdprintf("; UNIFY %s %s",s,#t1);DEBUG_ADDR("(", t1, ")");Sdprintf("==%s",#t2);DEBUG_ADDR("(", t2, ");\n");); 
#define DEBUG_UNIFYw(s, t1, t2) DEBUG_TERMSINK(Sdprintf("; UNIFY %s %s",s,#t1);DEBUG_ADDR("(", t1, ")");Sdprintf("==%s",#t2);DEBUG_WORD("(", t2, ");\n"););  

#if defined(O_DEBUG) || defined(O_MAINTENANCE)
char *print_addr(Word adr, char *buf); 
char *print_val(word val, char *buf); 
char *print_val_recurse(word val, char *buf, int dereflevel); 
#define DEBUG_TERMSINK( DBG ) {if (IS_DEBUG_MASK(LD->termsink.gsinkmode)) { DBG ; }}
#define DEBUG_ADDRLN( txt, addr, ...)  DEBUG_TERMSINK({ DEBUG_ADDR(txt, addr, __VA_ARGS__ );Sdprintf("\n");})
#define DEBUG_WORDLN( txt, addr, ...)  DEBUG_TERMSINK({ DEBUG_WORD(txt, addr, __VA_ARGS__ );Sdprintf("\n");})
#define DEBUG_ADDR( txt, addr, ...) {Sdprintf("%s*(%s)=%s", txt,print_addr(addr,0),print_val(*addr, 0));Sdprintf("" __VA_ARGS__ );}
#define DEBUG_WORD( txt, addr, ...) {Sdprintf("%s%s", txt, print_val(addr, 0));Sdprintf("" __VA_ARGS__ );}
#define SHOW_IF_DBG(name,val) ((({if(val!=0) Sprintf("%s=%d",name,val);}), val))
#else
#define DEBUG_TERMSINK( DBG )
#define DEBUG_ADDRLN( txt, addr, ...)
#define DEBUG_WORDLN( txt, addr, ...)
#define DEBUG_WORD( txt, addr, ...)
#define DEBUG_ADDR( txt, addr, ...)
#define SHOW_IF_DBG(name,val) (val)
#endif


#define BIT_ON(BIT,VALUE) ( ((int)1)<<BIT & VALUE)!=0
#define WHY_BIT(when,what) ( WHEN_ ## when * 16 +  WHAT_ ## what  )
#define WHY_CALLING(when,what,l2r) CACHED_ATOM(LD->termsink.callbacknames,  WHAT_ ## what , #what ) ,  CACHED_ATOM(LD->termsink.modenames,  HOW_ ## when ## _ ## l2r  , #when "_" #l2r )
#define CACHED_ATOM(array,index,value) (isAtom(array[index])?array[index]:(array[index] = PL_new_atom(value)))

#define IS_OVERLOAD_GLOBAL_VAR(when,what,var) ((tag(*var) == TAG_ATTVAR && (( LD->termsink.eagermodes[WHY_BIT(when,what)] != 0 || \
       (LD->termsink.eager_vars > 0 && BIT_ON( X_uses_eager , getSinkMode(var)))))))

/* FALSE mean we let the code below do its thing we may decide to return GLOBAL_OVERFLOW and such as well as TRUE*/
#define MAYBE_IMPL(when, what ,l,r) \
   if(IS_OVERLOAD_GLOBAL_VAR(when,what,l)) { int subsink =  overloadAttVar(l,r,WHY_CALLING(when, what ,lr) PASS_LD); if(subsink>-1) return subsink; } else \
   if(IS_OVERLOAD_GLOBAL_VAR(when,what,r)) { int subsink =  overloadAttVar(r,l,WHY_CALLING(when, what ,rl) PASS_LD); if(subsink>-1) return subsink; } 


#endif /*PL_TERMSINK_H_INCLUDED*/

