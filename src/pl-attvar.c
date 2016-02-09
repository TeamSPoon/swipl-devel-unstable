/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2004-2015, University of Amsterdam
			      VU University Amsterdam

    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public
    License as published by the Free Software Foundation; either
    version 2.1 of the License, or (at your option) any later version.

    This library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*/

/*#define O_DEBUG 1*/
#include "pl-incl.h"
#include "pl-inline.h"
#ifdef O_ATTVAR

#undef LD
#define LD LOCAL_LD

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
This module defines basic attributed variable   support  as described in
"Dynamic  attributes,  their  hProlog  implementation,    and   a  first
evaluation" by Bart  Demoen,  Report   CW350,  October  2002, Katholieke
Universiteit Leuven.

An attributed is represented as a cell   pointing  with an TAG_ATTVAR to
the linked list of attributes:


  ----------
  | refptr | <--- newer attvars <--- LD->attvar.attvars
  ----------
  | attvar | --\
  ----------   | TAG_ATTVAR|STG_GLOBAL pointer
  | att/3  | <-/
  ----------
  | name   |
  ----------
  | value  |
  ----------
  | <tail> |
  ----------

Binding the attvar places the new  value   in  <attvar>  using a trailed
assignment. The attribute list remains   accessible  through the trailed
assignment until this is GC'ed.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

#define NEVER_WRITELN(ex)
/*#define NEVER_WRITELN(ex) pl_writeln(ex);*/

#ifdef O_DEBUG
static char *
vName(Word adr)
{ GET_LD
  static char name[32];

  deRef(adr);

  if (adr > (Word) lBase)
    Ssprintf(name, "_L%ld", (Word)adr - (Word)lBase);
  else
    Ssprintf(name, "_G%ld", (Word)adr - (Word)gBase);

  return name;
}
#endif


int
PL_get_attr__LD(term_t t, term_t a ARG_LD)
{ Word p = valTermRef(t);

  deRef(p);
  if ( isAttVar(*p) )
  { Word ap = valPAttVar(*p);

    *valTermRef(a) = makeRef(ap);	/* reference, so we can assign */
    succeed;
  }

  fail;
}

#define PL_get_attr(t, a) PL_get_attr__LD(t, a PASS_LD)

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
(*) Although this is an assignment from var   to value, we use a trailed
assignment  to  exploit  mergeTrailedAssignments()   in  GC,  discarding
multiple  assignments  in  the  same  segment,  needed  to  ensure  that
deterministic wakeup does not leak  space.   The  test  program is this,
which must run in constant space.

	loop :- freeze(X, true), X = a, loop.

SHIFT-SAFE: Caller must ensure 7 global and 4 trail-cells
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static void
appendWakeup(Word wake ARG_LD);

void
registerWakeup(functor_t wakeup_type,  Word attvar, Word attrs, Word value ARG_LD)
{ Word wake;

  if(LD_no_wakeup > 0)
  { DEBUG(MSG_WAKEUPS, Sdprintf("registering wakeups durring recursion\n"));
  }

  assert(gTop+7 <= gMax && tTop+4 <= tMax);

  wake = gTop;
  gTop += 5;
  wake[0] = wakeup_type;
  wake[1] = needsRef(*attrs) ? makeRef(attrs) : *attrs;
  wake[2] = ATOM_true;
  wake[3] = needsRef(*attvar) ? makeRef(attvar) : *attvar; 
  wake[4] = needsRef(*value) ? makeRef(value) : *value;
  appendWakeup(wake PASS_LD);
}

void
scheduleWakeup(word g, int alert_flags ARG_LD)
{ Word wake;

  wake = gTop;
  gTop += 3;
  wake[0] = FUNCTOR_comma2;
  wake[1] = g;
  wake[2] = ATOM_true;
  LD->alerted |= alert_flags;
  appendWakeup(wake PASS_LD);
}


static void
appendWakeup(Word wake ARG_LD)
{ Word tail = valTermRef(LD->attvar.tail);

  if ( *tail )
  { Word t;				/* Non-empty list */

    deRef2(tail, t);
    TrailAssignment(t);
    *t = consPtr(wake, TAG_COMPOUND|STG_GLOBAL);
    TrailAssignment(tail);		/* on local stack! */
    *tail = makeRef(wake+2);
    DEBUG(MSG_WAKEUPS, Sdprintf("appended to wakeup\n"));
  } else				/* empty list */
  { Word head = valTermRef(LD->attvar.head);

    assert(isVar(*head));
    TrailAssignment(head);		/* See (*) */
    *head = consPtr(wake, TAG_COMPOUND|STG_GLOBAL);
    TrailAssignment(tail);
    *tail = makeRef(wake+2);    
    LD->alerted |= ALERT_WAKEUP;
    DEBUG(MSG_WAKEUPS, Sdprintf("new wakeup alerted=%d\n", LD->alerted & ALERT_WAKEUP));

  }
}

static int put_attr(Word av, atom_t name, Word value, int backtrack_flags ARG_LD);
void
setMetaFlags(Word av, int value, int backtrack_flags ARG_LD)
{   if(!isAttVar(*av)) return;
    word wval = consUInt(value);
    put_attr(av, ATOM_datts, &wval, backtrack_flags PASS_LD);
}

/*
 Returns the "$atts" attvar property (supposed to be a small int)
 Ideally metaterms will have them at the begining
*/

int
getMetaFlags(Word av, int flags ARG_LD)
{ Word found;
    int value;
    if (!find_attr(av, ATOM_datts, &found PASS_LD) || !isInteger(*found))
        value = 0;
    else value = valInteger(*found);
    if (IS_META(META_NO_INHERIT))
        return value;

    if (value==0) return META_DEFAULT;

    flags = value;
    if (IS_META(META_DISABLED)) return META_DISABLED|META_DEFAULT;

    flags = METATERM_GLOBAL_FLAGS;
    if (IS_META(META_NO_INHERIT)) 
        return(value);
    return (value | flags);
}


static void make_new_attvar(Word p ARG_LD);

		 /*******************************
		 *	     ASSIGNMENT		*
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
assignAttVar(Word var, Word value)		(var := value)

Assign  value  to  the  given  attributed    variable,   adding  a  term
wake(Attributes, Tail, Var, Value) to the global variable resembling the goals
that should be awoken.

Before calling, av *must* point to   a  dereferenced attributed variable
and value to a legal value.

The predicate unifiable/3 and  raw_unify_ptrs()   relies  on the trailed
pattern left by this function. If you   change this you must also adjust
unifiable/3 and raw_unify_ptrs()

SHIFT-SAFE: returns TRUE, GLOBAL_OVERFLOW or TRAIL_OVERFLOW
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

void
assignAttVarBinding(Word av, Word value, int flags ARG_LD)
{
 assert(isAttVar(*av));
 assert(!isRef(*value));
 DEBUG(CHK_SECURE, assert(on_attvar_chain(av)));

 if(!(flags& ATTV_ASSIGNONLY) && (flags& META_WAKEBINDS) )
 { registerWakeup(FUNCTOR_unify4, av, valPAttVar(*av), value PASS_LD);
   return;
 }

 if ( isAttVar(*value) )
 { 
    if ( av == value) return;

    if(IS_META(META_KEEP_BOTH))
    { DEBUG(MSG_METATERM, Sdprintf("META_KEEP_BOTH\n"));
      return;
    }

    if (av > value)
    { 
        if (IS_META(META_NO_BIND))
        {  DEBUG(MSG_METATERM, Sdprintf("META_NO_BIND Unifying av <- value\n"));
        } else
        {  DEBUG(MSG_ATTVAR_GENERAL, Sdprintf("Unifying av <- value\n"));
           *av = makeRef(value);		            
        }

    } else
    {  if (!IS_META(META_DISABLE_SWAP))
       { DEBUG(MSG_ATTVAR_GENERAL, Sdprintf("SWAPPING value <- av\n"));
         TrailAssignment(value);
         *value = makeRef(av);
       } else
       { DEBUG(MSG_METATERM, Sdprintf("META_DISABLE_SWAP value -> av\n"));
         *av = makeRef(value);
       }
    }
    
 } else if ( isVar(*value) )  /* JW: Does this happen? */ /* Discussion:  https://github.com/SWI-Prolog/roadmap/issues/40#issuecomment-173002313 */
 {   if( (flags& ATTV_ASSIGNONLY) )
	 {  if(IS_META(META_KEEP_BOTH))
         { DEBUG(MSG_ATTVAR_GENERAL, Sdprintf("META_KEEP_BOTH Upgraging VAR to an ATTVAR ref\n"));
           TrailAssignment(value);
           make_new_attvar(value PASS_LD);			/* SHIFT: 3+0 */
           deRef(value);
           *valPAttVar(*value) = *valPAttVar(*av);
         } else
         { if (IS_META(META_NO_BIND))
           { DEBUG(MSG_METATERM, Sdprintf("META_NO_BIND attvar with a plain putting into VAR maybe ref\n"));
             return;
           }
           DEBUG(MSG_ATTVAR_GENERAL, Sdprintf("Assigning attvar with a plain VAR ref\n"));
           *av = makeRef(value);			            
         }
	 } else
     { DEBUG(MSG_WAKEUPS, Sdprintf("!ATTV_ASSIGNONLY FUNCTOR_unify4 with a plain VAR ref\n"));
       registerWakeup(FUNCTOR_unify4, av, valPAttVar(*av), value PASS_LD);       
     }
  } else 
  { if (IS_META(META_NO_BIND))
    { DEBUG(MSG_METATERM, Sdprintf("META_NO_BIND attvar with a value\n"));
      return;
    } else
    { *av = *value;
    }
  }
}

void
assignAttVarPreUnify(Word av, Word value, int flags ARG_LD)
{ 

  if ( isAttVar(*value) )
  { if ( value > av )
    {   if (!IS_META(META_DISABLE_SWAP))
        {
          Word tmp = av;
          av = value;
          value = tmp;
        } else
        { DEBUG(MSG_WAKEUPS, Sdprintf("assignAttVarPreUnify DISABLE_SWAP(%s)\n", vName(av)));
        }
    } else if ( av == value )
    { DEBUG(MSG_WAKEUPS, Sdprintf("no_self_unify(%s)\n", vName(av)));
      return;
    }
  }


  if(!(flags& META_NO_WAKEUP))
  { registerWakeup(FUNCTOR_pre_unify4, av, valPAttVar(*av), value PASS_LD);
  } 

 if((flags& ATTV_MUST_TRAIL))
 { mark m;
   Mark(m);		/* must be trailed, even if above last choice */
   LD->mark_bar = NO_MARK_BAR;
   TrailAssignment(av);
   DiscardMark(m);
  } else
  { TrailAssignment(av);
  }

  if((flags& ATTV_WILL_UNBIND) )
  {  assignAttVarBinding(av,value,flags PASS_LD);
  }
}

void
assignAttVar(Word av, Word value, int flags ARG_LD)
{ 
  assert(isAttVar(*av));
  assert(!isRef(*value));
  assert(gTop+7 <= gMax && tTop+6 <= tMax);
  DEBUG(CHK_SECURE, assert(on_attvar_chain(av)));

  DEBUG(MSG_ATTVAR_GENERAL, Sdprintf("assignAttVar(%s)\n", vName(av)));
  flags |= getMetaFlags(av, METATERM_GLOBAL_FLAGS PASS_LD);

  if(flags&META_ENABLE_PREUNIFY) 
  { assignAttVarPreUnify(av,value,flags PASS_LD);
    return;
  }

  if ( isAttVar(*value) )
  { if ( value > av )
    {   if (!IS_META(META_DISABLE_SWAP))
        {
          Word tmp = av;
          av = value;
          value = tmp;
        } else
        { DEBUG(MSG_WAKEUPS, Sdprintf("assignAttVar DISABLE_SWAP(%s)\n", vName(av)));
        }
    } else if ( av == value )
    { DEBUG(MSG_WAKEUPS, Sdprintf("assignAttVar no_self_unify(%s)\n", vName(av)));
      return;
    }
  }

 if(!(flags& META_NO_WAKEUP)) registerWakeup(FUNCTOR_post_unify4, av, valPAttVar(*av), value PASS_LD);

 if((flags& ATTV_MUST_TRAIL))
 { mark m;
   Mark(m);		/* must be trailed, even if above last choice */
   LD->mark_bar = NO_MARK_BAR;
   TrailAssignment(av);
   DiscardMark(m);
 } else
 { TrailAssignment(av);
 }

 if( (flags& META_NO_BIND) ) return;
 

  if ( isAttVar(*value) )
  { DEBUG(MSG_ATTVAR_GENERAL, Sdprintf("Unifying two attvars\n"));
    *av = makeRef(value);
  } else
    *av = *value;

  return;
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Link known attributes variables into a reference list.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static Word
link_attvar(ARG1_LD)
{ Word gp = gTop++;

  register_attvar(gp PASS_LD);

  return gp+1;
}


Word
alloc_attvar(ARG1_LD)
{ Word gp = allocGlobalNoShift(3);

  if ( gp )
  { register_attvar(&gp[0] PASS_LD);
    gp[1] = consPtr(&gp[2], TAG_ATTVAR|STG_GLOBAL);
    gp[2] = ATOM_nil;
    return &gp[1];
  }

  return NULL;
}


int
on_attvar_chain(Word avp)
{ GET_LD
  Word p, next;

  for(p = LD->attvar.attvars; p; p = next)
  { Word avp0 = p+1;
    next = isRef(*p) ? unRef(*p) : NULL;

    if ( avp0 == avp )
      return TRUE;
  }

  DEBUG(0, char buf[256];
	Sdprintf("%s: not on attvar chain\n", print_addr(avp, buf)));

  return FALSE;
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
The creation of an attributed variable is trailed if call_residue_vars/2
is active. This is needed to avoid   that an attributed variable that is
destroyed on backtracking (and thus should not be reported) survives due
to a frozen stack.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static inline void
trail_new_attvar(Word p ARG_LD)
{ if ( LD->attvar.call_residue_vars_count )
  { tTop->address = p;
    tTop++;
  }
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
SHIFT-SAFE: Requires 3 global + 2 trail
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static void
make_new_attvar(Word p ARG_LD)
{ Word gp;

  assert(gTop+3 <= gMax && tTop+1 <= tMax);

  gp = link_attvar(PASS_LD1);
  gp[1] = ATOM_nil;
  gp[0] = consPtr(&gp[1], TAG_ATTVAR|STG_GLOBAL);
  gTop += 2;

  trail_new_attvar(gp PASS_LD);
  Trail(p, makeRefG(gp));
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
SHIFT-SAFE: Requires 7 global + 2 trail
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static void
put_new_attvar(Word p, atom_t name, Word value ARG_LD)
{ Word gp, at;

  assert(gTop+7 <= gMax && tTop+1 <= tMax);

  gp = link_attvar(PASS_LD1);
  gTop += 6;
  at = &gp[1];
  setVar(*at);
  gp[0] = consPtr(&gp[1], TAG_ATTVAR|STG_GLOBAL);

  at[1] = FUNCTOR_att3;
  at[2] = name;
  at[3] = linkVal(value);
  at[4] = ATOM_nil;
  at[0] = consPtr(&at[1], TAG_COMPOUND|STG_GLOBAL);

  trail_new_attvar(gp PASS_LD);
  Trail(p, makeRefG(gp));
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
int find_attr(Word av, atom_t name, Word *vp)

Find the location of the value for   the  attribute named `name'. Return
TRUE if found or FALSE if not found, leaving vp pointing at the ATOM_nil
of the end of the list.  Returns FALSE with *vp == NULL if the attribute
list is invalid.

Caller must ensure 4 cells space on global stack.
DM: Not sure this  ^ is true for find_attr()
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
#ifndef O_UNDO_HOOK
static
#endif
int
find_attr(Word av, atom_t name, Word *vp ARG_LD)
{ Word l;

  deRef(av);
  assert(isAttVar(*av));
  l = valPAttVar(*av);

  for(;;)
  { deRef(l);

    if ( isNil(*l) )
    { *vp = l;
      fail;
    } else if ( isTerm(*l) )
    { Functor f = valueTerm(*l);

      if ( f->definition == FUNCTOR_att3 )
      { Word n;

	deRef2(&f->arguments[0], n);
	if ( *n == name )
	{ *vp = &f->arguments[1];

	  succeed;
	} else
	{ l = &f->arguments[2];
	}
      } else
      { *vp = NULL;			/* bad attribute list */
	fail;
      }
    } else
    { *vp = NULL;			/* bad attribute list */
      fail;
    }
  }
}


static int
find_sub_attr(Word l, word name, Word *vp ARG_LD)
{ for(;;)
  { if ( isNil(*l) )
    { *vp = l;
      fail;
    } else if ( isVar(*l) )
    { *vp = l; /* for sub-attributes (these are not stored in toplevel of att/3s) */
      fail;
    } else if ( isTerm(*l) )
    { Functor f = valueTerm(*l);

      if ( f->definition == FUNCTOR_att3 )
      { Word n;

	deRef2(&f->arguments[0], n);
	if ( *n == name )
	{ *vp = &f->arguments[1];

	  succeed;
	} else  
    {  if ( isTerm(*n) ) /* for sub-attributes (these are not stored in toplevel of att/3s) */
       {   Functor fn = valueTerm(*n);
           if (fn->definition == name)
           {  *vp = &f->arguments[1];

              succeed;
           }

           FunctorDef fd = valueFunctor(fn->definition);
           if (fd->name == name)
           {  *vp = &f->arguments[1];

              succeed;
           }
        }

        l = &f->arguments[2];
        deRef(l);

	}
   } else
   { *vp = NULL;			/* bad attribute list */
	fail;
   }
  } else
  { *vp = NULL;			/* bad attribute list */
   fail;
  }
 }
}

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
put_attr(Word attvar, atom_t name, Word value,  [N]B_PUTATTS)

Destructive assignment or adding in a list  of the form att(Name, Value,
Rest).
Word
SHIFT-SAFE: Requires max 5 global + 2 trail
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static inline void
put_att_value(Word vp, atom_t name, Word value, int backtrack_flags ARG_LD)
{ Word at = gTop;

  gTop += 4;
  at[0] = FUNCTOR_att3;
  at[1] = name;
  at[2] = linkVal(value);
  at[3] = ATOM_nil;

  if(!(backtrack_flags & NB_PUTATTS))
  TrailAssignment(vp);
  *vp = consPtr(at, TAG_COMPOUND|STG_GLOBAL);
}


static int
put_attr(Word av, atom_t name, Word value, int backtrack_flags ARG_LD)
{ Word vp;

  assert(gTop+5 <= gMax && tTop+2 <= tMax);

  if ( find_attr(av, name, &vp PASS_LD) )
  { if(!(backtrack_flags & NB_PUTATTS))
    TrailAssignment(vp);
    *vp = linkVal(value);
  } else if ( vp )
  { put_att_value(vp, name, value, backtrack_flags PASS_LD);
  } else
    return FALSE;			/* Bad attribute list */

  return TRUE;
}


static int
get_attr(Word l, atom_t name, term_t value ARG_LD)
{ for(;;)
  { deRef(l);

    if ( isTerm(*l) )
    { Functor f = valueTerm(*l);

      if ( f->definition == FUNCTOR_att3 )
      { Word n;

	deRef2(&f->arguments[0], n);
	if ( *n == name )
	{ return unify_ptrs(valTermRef(value), &f->arguments[1],
			    ALLOW_GC|ALLOW_SHIFT PASS_LD);
	} else
	{ l = &f->arguments[2];
	}
      } else
	fail;
    } else
      fail;
  }
}


static int
del_attr(Word av, atom_t name ARG_LD)
{ Word l, prev;

  deRef(av);
  assert(isAttVar(*av));
  l = valPAttVar(*av);
  deRef(l);
  prev = l;

  for(;;)
  { if ( isNil(*l) )
    { fail;
    } else if ( isTerm(*l) )
    { Functor f = valueTerm(*l);

      if ( f->definition == FUNCTOR_att3 )
      { Word n;

	deRef2(&f->arguments[0], n);
	if ( *n == name )
	{ TrailAssignment(prev);			/* SHIFT: 1+2 */

	  *prev = f->arguments[2];
	  succeed;
	} else
	{ l = &f->arguments[2];
	  deRef(l);
	  prev = l;
	}
      } else
      { fail;
      }
    } else
    { fail;
    }
  }
}


		 /*******************************
		 *	 CONTROLLING  WAKEUP    *
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Some callbacks should *not* do call the   wakeup list as their execution
does not contribute to the truth result   of  the computation. There are
two ways out:

	- Save/restore the wakeup list
	- Make sure the wakeup list is processed (i.e. empty).

Points requiring attention are:

	- Tracer
	- portray
	- interrupt (Control-C), signals in general	(S/W)
	- event hook.					(S/W)

The ones marked (S/W) should not affect execution and therefore must use
the save/restore approach. Effectively, forcing  execution of the wakeup
list from foreign code is very  hard   as  explained  in the determinism
handling of foreignWakeup(), so we will use save/restore in all places.

The functions below provide a way to   realise the save/restore. It must
be nicely nested in the  same  way   and  using  the same constraints as
PL_open_foreign_frame/PL_close_foreign_frame.

NOTE: Now we also save pending  exceptions,   for  which  the same rules
apply. The environment has size 1 if there  is a pending exception, 2 if
a wakeup was saved and 3 if both where saved.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

int
saveWakeup(wakeup_state *state, int forceframe ARG_LD)
{ Word h;

  state->flags = 0;
  state->outofstack = LD->outofstack;

  if ( *(h=valTermRef(LD->attvar.head)) ||
       exception_term ||
       forceframe )
  { term_t s;

    if ( !(state->fid = PL_open_foreign_frame()) )
      return FALSE;			/* no space! */

    if ( exception_term )
    { state->flags |= WAKEUP_STATE_EXCEPTION;
      s = PL_new_term_ref();
      *valTermRef(s) = *valTermRef(exception_term);
      exception_term = 0;
    }

    if ( *h )
    { state->flags |= WAKEUP_STATE_WAKEUP;
      s = PL_new_term_refs(2);

      DEBUG(MSG_WAKEUPS, NEVER_WRITELN(LD->attvar.head));

      *valTermRef(s+0) = *h;
      setVar(*h);
      h = valTermRef(LD->attvar.tail);
      *valTermRef(s+1) = *h;
      setVar(*h);
      DEBUG(MSG_WAKEUPS, Sdprintf("Saved wakeup to %p\n", valTermRef(s)));
    }

    return TRUE;
  } else
  { state->fid = 0;
    return TRUE;
  }
}


static void
restore_exception(Word p ARG_LD)
{ DEBUG(1, Sdprintf("Restore exception from %p\n", p));

  *valTermRef(exception_bin) = p[0];
  exception_term = exception_bin;

  DEBUG(1, NEVER_WRITELN(exception_term));
}


static void
restore_wakeup(Word p ARG_LD)
{ *valTermRef(LD->attvar.head) = p[0];
  *valTermRef(LD->attvar.tail) = p[1];

  DEBUG(MSG_WAKEUPS, NEVER_WRITELN(LD->attvar.head));
}


void
restoreWakeup(wakeup_state *state ARG_LD)
{ LD->outofstack = state->outofstack;

  if ( state->fid )
  { if ( state->flags )
    { FliFrame fr = (FliFrame) valTermRef(state->fid);
      Word p = (Word)(fr+1);

      if ( (state->flags & WAKEUP_STATE_EXCEPTION) )
      { if ( !(state->flags & WAKEUP_STATE_SKIP_EXCEPTION) )
	  restore_exception(p PASS_LD);
        p++;
      }
      if ( (state->flags & WAKEUP_STATE_WAKEUP) )
      { restore_wakeup(p PASS_LD);
      }
    }

    PL_discard_foreign_frame(state->fid);
    updateAlerted(LD);
  }
}


		 /*******************************
		 *	     PREDICATES		*
		 *******************************/

static
PRED_IMPL("attvar", 1, attvar, 0)
{ PRED_LD
  term_t t = A1;
  Word p = valTermRef(t);

  deRef(p);
  if ( isAttVar(*p) )
    succeed;

  fail;
}


static
PRED_IMPL("get_attrs", 2, get_attrs, 0)
{ PRED_LD
  term_t al = PL_new_term_ref();

  if ( !PL_get_attr(A1, al) )
    fail;

  return PL_unify(al, A2);
}


static
PRED_IMPL("get_attr", 3, get_attr, 0) /* +Var, +Name, -Value */
{ PRED_LD
  Word a1;

  a1 = valTermRef(A1);
  deRef(a1);
  if ( isAttVar(*a1) )
  { Word p = valPAttVar(*a1);
    atom_t name;

    if ( !PL_get_atom_ex(A2, &name) )
      fail;

    return get_attr(p, name, A3 PASS_LD);
  }

  fail;
}


static
PRED_IMPL("put_attr", 3, put_attr, 0)	/* +Var, +Name, +Value */
{ PRED_LD
  Word av, vp;
  atom_t name;

  GROW_OR_RET_OVERFLOW(1);  /* 0 means enough for attvars */

  if ( !PL_get_atom_ex(A2, &name) )
    fail;

  vp = valTermRef(A3);
  deRef(vp);

  if ( isVar(*vp) && vp >= (Word)lBase )/* attribute values on global */
  { Word p = gTop;

    gTop += 1;
    setVar(*p);
    LTrail(vp);
    *vp = makeRefG(p);
    vp = p;
  }

  av = valTermRef(A1);
  deRef(av);

  if ( isVar(*av) )
  { put_new_attvar(av, name, vp PASS_LD);
    return TRUE;
  } else if ( isAttVar(*av) )
  { if ( put_attr(av, name, vp, B_PUTATTS PASS_LD) )
      return TRUE;
    return PL_error("put_attr", 3, "invalid attribute structure",
		    ERR_TYPE, ATOM_attributes, A1);
  } else
  { return PL_error("put_attr", 3, NULL, ERR_UNINSTANTIATION, 1, A1);
  }
}


static
PRED_IMPL("put_attrs", 2, put_attrs, 0)
{ PRED_LD
  Word av, vp;

  GROW_OR_RET_OVERFLOW(0); /* 0 means enough for attvars */
  

  av = valTermRef(A1);
  deRef(av);

  if ( isVar(*av) )
  { make_new_attvar(av PASS_LD);			/* SHIFT: 3+0 */
    deRef(av);
  } else if ( !isAttVar(*av) )
  { return PL_error("put_attrs", 2, NULL, ERR_UNINSTANTIATION, 1, A1);
  }

  vp = valPAttVar(*av);
  TrailAssignment(vp);					/* SHIFT: 1+2 */
  *vp = linkVal(valTermRef(A2));

  return TRUE;
}


static
PRED_IMPL("del_attr", 2, del_attr2, 0)	/* +Var, +Name */
{ PRED_LD
  Word av;
  atom_t name;

  GROW_OR_RET_OVERFLOW(0);  /* 0 means enough for attvars */

  if ( !PL_get_atom_ex(A2, &name) )
    return FALSE;

  av = valTermRef(A1);
  deRef(av);

  if ( isAttVar(*av) )
  { if ( del_attr(av, name PASS_LD) )			/* SHIFT: 1+2 */
    { Word l = valPAttVar(*av);

      deRef(l);
      if ( isNil(*l) )
      { TrailAssignment(av);				/* SHIFT: 1+2 */
	setVar(*av);
      }
    }
  }

  return TRUE;
}


static
PRED_IMPL("del_attrs", 1, del_attrs, 0)	/* +Var */
{ PRED_LD
  Word av;

  GROW_OR_RET_OVERFLOW(0);  /* 0 means enough for attvars */

  av = valTermRef(A1);
  deRef(av);

  if ( isAttVar(*av) )
  { TrailAssignment(av);				/* SHIFT: 1+2  */
    setVar(*av);
  }

  return TRUE;
}

		 /*******************************
		 *	       FREEZE		*
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Freeze support predicate. This predicate succeeds   if  Goal needs to be
frozen, leading to the simple implementation of freeze/2:

freeze(X, Goal) :-
	$freeze(X, Goal), !.
freeze(_, Goal) :-
	Goal.

Note that Goal is qualified because freeze is a declared meta-predicate.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static
PRED_IMPL("$freeze", 2, freeze, 0)
{ PRED_LD
  Word v;

  GROW_OR_RET_OVERFLOW(0);

  v = valTermRef(A1);
  deRef(v);
  if ( isVar(*v) || isAttVar(*v) )
  { Word goal;

    goal = valTermRef(A2);
    deRef(goal);

    if ( isVar(*v) )
    { put_new_attvar(v, ATOM_freeze, goal PASS_LD);	/* SHIFT: 6+2 */
    } else
    { Word vp;

      if ( find_attr(v, ATOM_freeze, &vp PASS_LD) )
      { Word gc = gTop;

	gTop += 3;
	gc[0] = FUNCTOR_dand2;
	gc[1] = linkVal(vp);
	gc[2] = *goal;

	TrailAssignment(vp);				/* SHIFT: 1+2 */
	*vp = consPtr(gc, TAG_COMPOUND|STG_GLOBAL);
      } else if ( vp )					/* vp points to [] */
      { Word at = gTop;

	gTop += 4;
	at[0] = FUNCTOR_att3;
	at[1] = ATOM_freeze;
	at[2] = *goal;
	at[3] = ATOM_nil;

	assert(*vp == ATOM_nil);
	TrailAssignment(vp);				/* SHIFT: 1+2 */
	*vp = consPtr(at, TAG_COMPOUND|STG_GLOBAL);
      } else
	assert(0);					/* bad attributes */
    }

    succeed;
  }

  fail;
}


		 /*******************************
		 *	      WHEN		*
		 *******************************/

typedef enum
{ E_NOSPACE = -4,
  E_CYCLIC = -3,
  E_DOMAIN_ERROR = -2,
  E_INSTANTIATION_ERROR = -1,
  E_OK = 0
} when_status;

typedef struct
{ Word gSave;				/* Saved global top */
  int  depth;				/* Recursion depth */
} when_state;


static when_status
add_to_list(word c, Word *tailp ARG_LD)
{ Word t;

  if(isTerm(c) && functorTerm(c) == FUNCTOR_semicolon2)
  { Word p = argTermP(c, 0);
    int rc;

    if ( (rc=add_to_list(p[0], tailp PASS_LD)) < 0 )
      return rc;
    return add_to_list(p[1], tailp PASS_LD);
  }

  if ( (t=allocGlobalNoShift(3)) )
  { t[0] = FUNCTOR_dot2;
    t[1] = c;
    t[2] = ATOM_nil;
    **tailp = consPtr(t, TAG_COMPOUND|STG_GLOBAL);
    *tailp = &t[2];

    return E_OK;
  }

  return E_NOSPACE;
}


static when_status
or_to_list(word c1, word c2, Word list ARG_LD)
{ int rc;
  Word tailp = list;

  if ( (rc=add_to_list(c1, &tailp PASS_LD)) < 0 )
    return rc;
  return add_to_list(c2, &tailp PASS_LD);
}


static when_status
when_condition(Word cond, Word result, int top_or, when_state *state ARG_LD)
{ deRef(cond);

  if ( state->depth++ == 100 )
  { int rc = PL_is_acyclic(pushWordAsTermRef(cond));

    popTermRef();
    if ( !rc )
      return E_CYCLIC;
  }

  if ( isTerm(*cond) )
  { Functor term = valueTerm(*cond);
    functor_t f = term->definition;

    if ( f == FUNCTOR_unify_determined2 ) /* ?=/2 */
    { *result = *cond;
    } else if ( f == FUNCTOR_nonvar1 )
    { Word a1;

      deRef2(&term->arguments[0], a1);
      if ( canBind(*a1) )
	*result = *cond;
      else
	*result = ATOM_true;
    } else if ( f == FUNCTOR_ground1 )
    { Word a1;

      deRef2(&term->arguments[0], a1);
      if ( ground__LD(a1 PASS_LD) )
	*result = ATOM_true;
      else
	*result = *cond;
    } else if ( f == FUNCTOR_comma2 )
    { word c1, c2;
      int rc;

      if ( (rc=when_condition(&term->arguments[0], &c1, TRUE, state PASS_LD)) < 0 )
	return rc;
      if ( (rc=when_condition(&term->arguments[1], &c2, TRUE, state PASS_LD)) < 0 )
	return rc;

      if ( c1 == ATOM_true )
      { *result = c2;
      } else if ( c2 == ATOM_true )
      { *result = c1;
      } else if ( cond < state->gSave )
      { *result = *cond;
      } else
      { Word t;

	if ( (t = allocGlobalNoShift(3)) )
	{ t[0] = FUNCTOR_comma2;
	  t[1] = c1;
	  t[2] = c2;

	  *result = consPtr(t, TAG_COMPOUND|STG_GLOBAL);
	} else
	  return E_NOSPACE;
      }
    } else if ( f == FUNCTOR_semicolon2 )
    { word c1, c2;
      int rc;

      if ( (rc=when_condition(&term->arguments[0], &c1, FALSE, state PASS_LD)) < 0 )
	return rc;
      if ( c1 == ATOM_true )
      { *result = c1;
      } else
      { if ( (rc=when_condition(&term->arguments[1], &c2, FALSE, state PASS_LD)) < 0 )
	  return rc;
	if ( c2 == ATOM_true )
	{ *result = c2;
	} else if ( top_or )
	{ Word t;

	  if ( (t = allocGlobalNoShift(2)) )
	  { t[0] = FUNCTOR_or1;
	    if ( (rc=or_to_list(c1,c2,&t[1] PASS_LD)) < 0 )
	      return rc;
	    *result = consPtr(t, TAG_COMPOUND|STG_GLOBAL);
	  }
	} else
	{ Word t;

	  if ( (t = allocGlobalNoShift(3)) )
	  { t[0] = FUNCTOR_semicolon2;
	    t[1] = c1;
	    t[2] = c2;
	    *result = consPtr(t, TAG_COMPOUND|STG_GLOBAL);
	  }
	}
      }
    } else
      return E_DOMAIN_ERROR;

    return E_OK;
  }

  if ( isVar(*cond) )
    return E_INSTANTIATION_ERROR;

  return E_DOMAIN_ERROR;
}


static
PRED_IMPL("$eval_when_condition", 2, eval_when_condition, 0)
{ PRED_LD
  when_state state;
  term_t cond;
  int rc;

retry:
  cond = PL_new_term_ref();
  state.gSave = gTop;
  state.depth = 0;

  if ( (rc=when_condition(valTermRef(A1), valTermRef(cond), TRUE, &state PASS_LD)) < 0 )
  { gTop = state.gSave;
    PL_put_variable(cond);

    switch( rc )
    { case E_INSTANTIATION_ERROR:
	return PL_error(NULL, 0, NULL, ERR_INSTANTIATION);
      case E_DOMAIN_ERROR:
	return PL_error(NULL, 0, NULL, ERR_DOMAIN, ATOM_when_condition, A1);
      case E_CYCLIC:
	return PL_error(NULL, 0, NULL, ERR_TYPE, ATOM_acyclic_term, A1);
      case E_NOSPACE:
	if ( !makeMoreStackSpace(GLOBAL_OVERFLOW, ALLOW_SHIFT|ALLOW_GC) )
	  return FALSE;
        goto retry;
      default:
	assert(0);
    }
  }

  return PL_unify(A2, cond);
}


/** '$suspend'(+Var, +Attr, :Goal) is semidet.

Add Goal to an attribute with the value call(Goal).  This is the same
as:

    ==
    '$suspend'(Var, Attr, Goal) :-
	(   get_attr(Var, Attr, call(G0))
	->  put_attr(Var, Attr, call((G0,Goal)))
	;   put_attr(Var, Attr, call(Goal))
	).
    ==
*/

static
PRED_IMPL("$suspend", 3, suspend, PL_FA_TRANSPARENT)
{ PRED_LD
  atom_t name;
  Word v, g;

  GROW_OR_RET_OVERFLOW(6);		/* 0 means enough for attvars */

  if ( !PL_get_atom_ex(A2, &name) )
    return FALSE;

  g = valTermRef(A3);
  if ( !isTerm(*g) || functorTerm(*g) != FUNCTOR_colon2 )
  { Word t = gTop;
    term_t g2 = PL_new_term_ref();

    gTop += 3;
    t[0] = FUNCTOR_colon2;
    t[1] = contextModule(PL__ctx->engine->environment)->name;
    t[2] = linkVal(g);
    g = valTermRef(g2);
    *g = consPtr(t, STG_GLOBAL|TAG_COMPOUND);
  }

  v = valTermRef(A1); deRef(v);

  if ( isVar(*v) )
  { Word t = gTop;

    gTop += 3;
    t[0] = consPtr(&t[1], STG_GLOBAL|TAG_COMPOUND);
    t[1] = FUNCTOR_call1,
    t[2] = linkVal(g);
    put_new_attvar(v, name, t PASS_LD);
    return TRUE;
  } else if ( isAttVar(*v) )
  { Word vp;

    if ( find_attr(v, name, &vp PASS_LD) )
    { Word g0;

      deRef2(vp, g0);
      if ( isTerm(*g0) && functorTerm(*g0) == FUNCTOR_call1 )
      { Word t = gTop;
	Word ap = argTermP(*g0,0);

	gTop += 3;
	t[0] = FUNCTOR_comma2;
	t[1] = linkVal(ap);
	t[2] = linkVal(g);
	TrailAssignment(ap);
	*ap = consPtr(t, TAG_COMPOUND|STG_GLOBAL);

	return TRUE;
      }

      return FALSE;
    } else if ( vp )
    { Word t = gTop;

      gTop += 3;
      t[0] = consPtr(&t[1], STG_GLOBAL|TAG_COMPOUND);
      t[1] = FUNCTOR_call1,
      t[2] = linkVal(g);

      put_att_value(vp, name, t, B_PUTATTS PASS_LD);
      return TRUE;
    }
  } else
    return PL_error(NULL, 0, NULL, ERR_UNINSTANTIATION, 1, A1);

  assert(0);
  return FALSE;
}



#ifdef O_CALL_RESIDUE

		 /*******************************
		 *	   CALL RESIDUE		*
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
has_attributes_after(Word av, Choice  ch)  is   true  if  the attributed
variable av has attributes created or modified after the choicepoint ch.

We compute this by marking  all   trailed  assignments  and scanning the
attribute list for terms that are newer than the choicepoint or having a
value that is changed due to a trailed assignment.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static inline word
get_value(Word p)
{ return (*p) & ~MARK_MASK;
}

static Word
deRefM(Word p, Word pv ARG_LD)
{ for(;;)
  { word w = get_value(p);

    if ( isRef(w) )
    { p = unRef(w);
    } else
    { *pv = w;
      return p;
    }
  }
}


static int
has_attributes_after(Word av, Choice ch ARG_LD)
{ Word l;
  word w;

  DEBUG(MSG_CALL_RESIDUE_VARS,
	{ char buf[64];
	  Sdprintf("has_attributes_after(%s, %s)\n",
		   vName(av), print_addr(ch->mark.globaltop, buf));
	});

  av = deRefM(av, &w PASS_LD);
  assert(isAttVar(w));
  l = valPAttVar(w);

  for(;;)
  { l = deRefM(l, &w PASS_LD);

    if ( isNil(w) )
    { fail;
    } else if ( isTerm(w) )
    { Functor f = valueTerm(w);

      DEBUG(MSG_CALL_RESIDUE_VARS,
	    { char buf[64];
	      Sdprintf("  att/3 at %s\n", print_addr((Word)f, buf));
	    });

      if ( (Word)f >= ch->mark.globaltop )
	return TRUE;			/* created after choice */

      if ( f->definition == FUNCTOR_att3 )
      { Word pv = &f->arguments[1];	/* pointer to value */

	DEBUG(MSG_CALL_RESIDUE_VARS,
	{ char buf1[64]; char buf2[64];
	  Sdprintf("    value at %s: %s\n",
		   print_addr(pv, buf1), print_val(*pv, buf2));
	});

	if ( is_marked(pv) )
	  return TRUE;			/* modified after choice point */
	(void)deRefM(pv, &w PASS_LD);
	if ( isTerm(w) &&
	     (Word)valueTerm(w) >= ch->mark.globaltop )
	  return TRUE;			/* argument term after choice point */

	l = pv+1;
      } else
      { DEBUG(0, Sdprintf("Illegal attvar\n"));
	return FALSE;
      }
    } else
    { DEBUG(0, Sdprintf("Illegal attvar\n"));
      return FALSE;
    }
  }
}


static void
scan_trail(Choice ch, int set ARG_LD)
{ TrailEntry te, base;

  base = ch->mark.trailtop;

  for(te=tTop-1; te>=base; te--)
  { if ( isTrailVal(te->address) )
    { te--;
      if ( set )
      { DEBUG(MSG_CALL_RESIDUE_VARS,
	      { char buf1[64]; char buf2[64];
		word old = trailVal(te[1].address);
		Sdprintf("Mark %s (%s)\n",
			 print_addr(te->address, buf1), print_val(old, buf2));
	      });
	*te->address |= MARK_MASK;
      } else
      { *te->address &= ~MARK_MASK;
      }
    }
  }
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
'$attvars_after_choicepoint'(+Chp, -Vars) is det.

Find all attributed variables that got   new  attributes after Chp. Note
that the trailed assignment of  an   attributed  variable  creates a new
attributed variable, which is why we must scan the trail stack.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static
PRED_IMPL("$attvars_after_choicepoint", 2, attvars_after_choicepoint, 0)
{ PRED_LD
  intptr_t off;
  Choice ch;
  Word p, next, gend, list, tailp;

  if ( !PL_get_intptr_ex(A1, &off) )
    return FALSE;

retry:
  ch = (Choice)((Word)lBase+off);
  if ( !existingChoice(ch PASS_LD) )
    return PL_error(NULL, 0, NULL, ERR_EXISTENCE, ATOM_choice, A1);

  if ( !LD->attvar.attvars )
    return PL_unify_nil(A2);

  list = tailp = allocGlobalNoShift(1);
  if ( !list )
    goto grow;
  setVar(*list);

  scan_trail(ch, TRUE PASS_LD);

  gend = gTop;
  for(p=LD->attvar.attvars; p; p=next)
  { Word pav = p+1;
    next = isRef(*p) ? unRef(*p) : NULL;

    if ( isAttVar(*pav) &&
	 has_attributes_after(pav, ch PASS_LD) )
    { Word p = allocGlobalNoShift(3);

      if ( p )
      { p[0] = FUNCTOR_dot2;
	p[1] = makeRefG(pav);
	setVar(p[2]);
	*tailp = consPtr(p, TAG_COMPOUND|STG_GLOBAL);
	tailp = &p[2];
      } else
      { gTop = gend;
	scan_trail(ch, FALSE PASS_LD);
	goto grow;
      }
    }
  }

  scan_trail(ch, FALSE PASS_LD);

  if ( list == tailp )
  { gTop = gend;
    return PL_unify_nil(A2);
  } else
  { int rc;

    *tailp = ATOM_nil;
    rc = PL_unify(A2, pushWordAsTermRef(list));
    popTermRef();

    return rc;
  }

grow:
  if ( !makeMoreStackSpace(GLOBAL_OVERFLOW, ALLOW_SHIFT|ALLOW_GC) )
    return FALSE;
  goto retry;
}

static
PRED_IMPL("$call_residue_vars_start", 0, call_residue_vars_start, 0)
{ PRED_LD

  LD->attvar.call_residue_vars_count++;
  return TRUE;
}

static
PRED_IMPL("$call_residue_vars_end", 0, call_residue_vars_end, 0)
{ PRED_LD

  assert(LD->attvar.call_residue_vars_count>0);
  LD->attvar.call_residue_vars_count--;

  return TRUE;
}

#endif /*O_CALL_RESIDUE*/



static
PRED_IMPL("$trail_assignment", 1, dtrail_assignment, 0) 
{ PRED_LD
  Word value, av = valTermRef(A1);
  deRef2(av, value);
  if ( canBind(*value) )
  { TrailAssignment(value); 
  } else
  { TrailAssignment(unRef(*av)); 
  }
  return TRUE;
}

/** 
 *  attv_unify(+Var, +Value) is det.
 *    Is actually attv_unify/2 from XSB-Prolog
 * 
 *  Warn: dont forget to call $trail_assignment(Var) 
*/
static
PRED_IMPL("attv_unify", 2, attv_unify, 0)
{ PRED_LD

  Word value, av;
  GROW_OR_RET_OVERFLOW(0);
  
  av = valTermRef(A1);
  deRef(av);
  if ( isAttVar(*av) )
  { deRef2(valTermRef(A2), value);
    int flags = getMetaFlags(av, METATERM_GLOBAL_FLAGS PASS_LD);
    assignAttVarBinding(av, value, ATTV_ASSIGNONLY|flags PASS_LD);
    return TRUE;
  } else if ( isVar(*av) )
  { unify_vp(av,valTermRef(A2) PASS_LD);
    return TRUE;
  } else
  { return PL_unify(A1,A2);
  }

  
}


static
int
setFlagOptions(int *flag, term_t opval, term_t new)
{ GET_LD

  atom_t math;
  int was = *flag;

  if(PL_get_atom(opval, &math))
  { 
      int value;

        if(!PL_get_integer_ex(new, &value)) return FALSE;

        if(math==ATOM_bitor || math==ATOM_set)
        { *flag = was | value;
          return TRUE;
        }
        if(math==ATOM_and)
        { *flag = was & value;
          return TRUE;
        }
        if(math==ATOM_tilde || math==ATOM_not_provable)
        { *flag = was & ~value;
          return TRUE;
        }
        if(math==ATOM_equals)
        { *flag = value;
          return TRUE;
        }

        return PL_error(NULL, 0, "options_set_unset", ERR_DOMAIN, opval, "options_set_unset");

  } 
  if ( !PL_unify_integer(opval, *flag) ) fail;
  if ( PL_compare(opval,new) == CMP_EQUAL )
       return TRUE;
  return PL_get_integer_ex(new, flag);
}

static
PRED_IMPL("metaterm_flags", 3, metaterm_flags, 0)
{ PRED_LD

  Word av = valTermRef(A1);
  deRef(av);
  if ( isAttVar(*av) )
  { int backtrack_flags = PL_is_variable(A2) ? NB_PUTATTS : B_PUTATTS;
    int inherit_flags = PL_is_variable(A3) ? METATERM_GLOBAL_FLAGS : META_NO_INHERIT;
    int flags = getMetaFlags(av, inherit_flags PASS_LD);
    int was = flags;
    if(!setFlagOptions(&flags,A2,A3)) return FALSE;    
    DEBUG(MSG_METATERM,Sdprintf("metaterm_flags %s %sflags %d -> %d",vName(av),(backtrack_flags & NB_PUTATTS)?"NB-":"backtracking ",was,flags));
    if(was == flags) return TRUE;
    setMetaFlags(av, flags, backtrack_flags PASS_LD);
    return TRUE;
  } else if (!isAtom(*av) )
  { return TRUE;
  } else if(*av == ATOM_global)
  { int flags = METATERM_GLOBAL_FLAGS;
    int was = flags;
    if(!setFlagOptions(&flags,A2,A3)) return FALSE;    
    DEBUG(MSG_METATERM,Sdprintf("metaterm_flags global defaults NB-flags %d -> %d",was,flags));
    if(was == flags) return TRUE;
    *METATERM_GLOBAL = consUInt(flags);
    return TRUE;
  } else if(*av == ATOM_current)
  { int flags = METATERM_GLOBAL_FLAGS;
    int was = flags;
    if(!setFlagOptions(&flags,A2,A3)) return FALSE;
    DEBUG(MSG_METATERM,Sdprintf("metaterm_flags global current backtracking %d -> %d",was,flags));
    TrailAssignment(METATERM_GLOBAL);
    if(was == flags) return TRUE;
    *METATERM_GLOBAL = consUInt(flags);
    return TRUE;    
  }
  return FALSE;
}



#ifdef O_METATERM


static
PRED_IMPL("$schedule_wakeup", 1, dschedule_wakeup, PL_FA_TRANSPARENT)
{ PRED_LD
  Word g;

  GROW_OR_RET_OVERFLOW(6);

  g = valTermRef(A1);
  deRef(g);
  if ( !isTerm(*g) || functorTerm(*g) != FUNCTOR_colon2 )
  { Word t = gTop;
    term_t g2 = PL_new_term_ref();

    gTop += 3;

    t[0] = FUNCTOR_colon2;
    t[1] = contextModule(PL__ctx->engine->environment)->name;
    t[2] = linkVal(g);
    g = valTermRef(g2);
      *g = consPtr(t, STG_GLOBAL|TAG_COMPOUND);
  }
   scheduleWakeup(*g, ALERT_WAKEUP PASS_LD);
   return TRUE;
}

/* When a Metaterm is created it is most often the first attribute 
 This is used as a way to hide attributes in term comparison to get 
 some modules the opertunity to not confuse =@= this happens with 
  METATERM_SKIP_HIDDEN(..)
*/
Word attrs_after(Word origl, atom_t name ARG_LD)
{  Word n,l;
  deRef(origl);
  if(!name) return origl;
  deRef2(origl,l);
  for (;;)
  { if (!isTerm(*l)) return origl;
    Functor f = valueTerm(*l);
    if (f->definition != FUNCTOR_att3) return origl;
    deRef2(&f->arguments[0],n);
    deRef2(&f->arguments[2],l);    
    if (*n == name) 
      return l;    
  }
}

/* sometimes sneaking in an atom instead of a functor here */
functor_t 
getMetaOverride(Word av, functor_t f, int override_flags ARG_LD)
{ Word fdattrs,found;
  if(!(METATERM_ENABLED)) return f;
  deRef(av);
  if(!isAttVar(*av)) return f;
  if(!find_attr(av, ATOM_dmeta, &fdattrs PASS_LD)) 
  { word fallback;
    if(!gvar_value__LD(ATOM_dmeta, &fallback PASS_LD)) return f;
    if(!isAttVar(fallback)) return f;       
    if(!find_attr(&fallback, ATOM_dmeta, &fdattrs PASS_LD)) return f;
  }
  if(fdattrs==0) return f;
  deRef(fdattrs);
  if(!find_sub_attr(fdattrs, f, &found PASS_LD)) return f;
  if ( isTerm(*found) )
  {  FunctorDef fd = valueFunctor(functorTerm(*found));
     functor_t ft = fd->functor;
     if(f!=ft)
     { DEBUG(MSG_METATERM,Sdprintf("DIFF %s getMetaOverrideFunctor(%s,%s)\n",print_val(*found,0),vName(av),print_val(f,0)));
       return ft;
     }
     DEBUG(MSG_METATERM,Sdprintf("SAME getMetaOverrideFunctor(%s,%s)\n",vName(av),print_val(f,0)));
     return f;
  }
  if ( isAtom(*found) )
  {  functor_t ft = *found;
     if(f!=ft)
     { DEBUG(MSG_METATERM,Sdprintf("DIFF %s getMetaOverrideAtom(%s,%s)\n",print_val(*found,0),vName(av),print_val(f,0)));
       return ft;
     }
     DEBUG(MSG_METATERM,Sdprintf("SAME getMetaOverrideAtom(%s,%s)\n",vName(av),print_val(*found,0)));
     return f;
  }
  return f;
}

bool 
isMetaOverriden(Word av, atom_t f, int override_flags ARG_LD)
{
  if(SAFETY_FIRST) return FALSE;

  Word fdattrs,fdattrs2,found;
  if(!(override_flags & METATERM_ENABLED)) return FALSE;
  deRef(av);
  if(!isAttVar(*av)) return FALSE;
  if(!find_attr(av, ATOM_dmeta, &fdattrs PASS_LD)) 
  { word fallback;
    if(!gvar_value__LD(ATOM_dmeta, &fallback PASS_LD)) return FALSE;
    if(!fallback)  return FALSE;
    if(!isAttVar(fallback)) return FALSE;       
    if(!find_attr(&fallback, ATOM_dmeta, &fdattrs2 PASS_LD)) return FALSE;
    fdattrs = fdattrs2;
  }
  if(fdattrs==0) return FALSE;
  deRef(fdattrs);
  if(!find_sub_attr(fdattrs, f, &found PASS_LD)) return FALSE;
  DEBUG(MSG_METATERM,Sdprintf("isMetaOverriden(%s,%s,%s)\n",vName(av),print_val(f,0),print_val(*found,0)));
  return !isVar(*found);
}

static
PRED_IMPL("$get_delayed", 2, dget_delayed, 0)
{ PRED_LD
  int ret = PL_unify(A1,LD->attvar.head) && PL_unify(A2,LD->attvar.tail-2);
  return ret;
}

static
PRED_IMPL("$set_delayed", 2, dset_delayed, 0)
{ PRED_LD
    if(PL_is_variable(A1))
    { PL_put_term(LD->attvar.head,A1);
      PL_put_term(LD->attvar.tail,A2);
    } else
    { PL_put_term(LD->attvar.head,A1);
      if(PL_is_compound(LD->attvar.tail-2))
      { PL_put_term(LD->attvar.tail-2,A2);
      } else
          PL_put_term(LD->attvar.tail,A2);
      LD->alerted |= ALERT_WAKEUP;
    }
  return TRUE;
}


/*

 This for running ECLiPSe meta_attribute hooks that 
  have somehow had bypassed WAM 

 Only for: =@=/2 compare/3 undo/1 and copy_term()
    
 metatermOverride returns TRUE only if a hook was implemented 
   otherwise retresult is invalid

 retresult was hooks returns:

   =@=/2 returns TRUE or FALSE
   copy_term[_nat]/2, undo/1 return result is best ignored
   compare/3 returns a CMP_* constant

*/
int
metatermOverride(atom_t method, Word attvar, Word value, int* retresult ARG_LD)
{ static predicate_t pred;
   wakeup_state wstate;
   int rc;
    term_t regs = LD->attvar.metaterm_regs;
    *valTermRef(regs+0) = linkVal(attvar);
    *valTermRef(regs+1) = linkVal(value);

   /* opens foreign frame so Not shift safe */
  if (!saveWakeup(&wstate, TRUE PASS_LD))
      return FALSE;

    term_t av = PL_new_term_refs(4);    /* Someone outer context will free these  */
    *valTermRef(av) = method;
    *valTermRef(av+1) = *valTermRef(regs+0);
    *valTermRef(av+2) = *valTermRef(regs+1);

        /* Prevent calling a second time (allowing 1 in case no_wakeup is used by a one other wake hook calling metatermOverride)
        this prevents aquiring unwanted C stack */
    if (LD_no_wakeup>1)
    { term_t ex = av+3;
     
     rc = PL_unify_term(ex,PL_FUNCTOR, 
           PL_FUNCTOR_CHARS, "metaterm_loop_error", 3,
           PL_TERM, av+0,
           PL_TERM, av+1,
           PL_TERM, av+2);
     assert(rc!=0);

     DEBUG(MSG_WAKEUPS, NEVER_WRITELN(ex));
     restoreWakeup(&wstate PASS_LD);
     return PL_raise_exception(ex);
    }

    if (!pred)
         pred = PL_pred(FUNCTOR_dmeta4,MODULE_user);

    if(!pred) return FALSE;

    LD_no_wakeup++;
    DEBUG(MSG_METATERM, NEVER_WRITELN(av));
    rc = PL_call_predicate(NULL,  
                           PL_Q_PASS_EXCEPTION, pred, av);
    LD_no_wakeup--;
    if (rc == TRUE)
    { if (PL_get_integer(av+3,&rc))
      { if(retresult) *retresult = rc;
      } else
      { rc = FALSE;
      }
    }
    restoreWakeup(&wstate PASS_LD);
    return rc;
}

static
PRED_IMPL("metaterm_overriding", 3, metaterm_overriding, 0)
{ PRED_LD
  Word av;
  word f;
  if(!METATERM_ENABLED) fail;
  deRef2(valTermRef(A1),av);
  if(!(PL_get_functor(A2,&f) ||
      PL_get_atom(A2,&f))) return FALSE;
  functor_t becomes = getMetaOverride(av,f, META_ENABLE_VMI|META_ENABLE_CPREDS PASS_LD);
  if(isAtom(becomes)) return PL_unify_atom(A3,becomes);
  return PL_unify_functor(A3,becomes);
}

static
PRED_IMPL("$visible_attrs", 2, dvisible_attrs, 0)
{ PRED_LD
  Word p;

  deRef2(valTermRef(A1),p);
  if ( isAttVar(*p) )
  { *valTermRef(A2) = makeRef(METATERM_SKIP_HIDDEN(valPAttVar(*p)));
    succeed;
  }
  fail;
}

/* For a heuristic used elsewhere from mattss */
static
PRED_IMPL("$depth_of_var", 2, ddepth_of_var, 0)
{ PRED_LD

    Word v = valTermRef(A1);
    LocalFrame fr = environment_frame;
    long l0 = levelFrame(fr)-1;     /* -1: Use my parent as reference */

    int negInfo = -2;
    { while(isRef(*(v)))
    { negInfo--;
        (v) = unRef(*(v)); }}

    if (onStackArea(local, v))
     { DEBUG(1, Sdprintf("Ok, on local stack\n"));
        while (fr && fr > (LocalFrame)v)
            fr = parentFrame(fr);
        if (fr)
        {   l0 -= levelFrame(fr);
            return(PL_unify_integer(A2, l0));
        } else
        {   DEBUG(1,Sdprintf("Not on local stack\n"));
            return(PL_unify_integer(A2, -1));
        }
    }
    DEBUG(1,Sdprintf("!onStackArea\n"));
    return(PL_unify_integer(A2, negInfo));
   return TRUE;
}

#endif /*O_METATERM*/


		 /*******************************
		 *	    REGISTRATION	*
		 *******************************/

BeginPredDefs(attvar)
  PRED_DEF("attvar",    1, attvar,    0)
  PRED_DEF("put_attr",  3, put_attr,  0)
  PRED_DEF("get_attr",  3, get_attr,  0)
  PRED_DEF("del_attr",  2, del_attr2, 0)
  PRED_DEF("del_attrs", 1, del_attrs, 0)
  PRED_DEF("get_attrs", 2, get_attrs, 0)
  PRED_DEF("put_attrs", 2, put_attrs, 0)
  PRED_DEF("$freeze",   2, freeze,    0)
  PRED_DEF("$eval_when_condition", 2, eval_when_condition, 0)
  PRED_DEF("$suspend", 3, suspend, PL_FA_TRANSPARENT)
#ifdef O_CALL_RESIDUE
  PRED_DEF("$attvars_after_choicepoint", 2, attvars_after_choicepoint, 0)
  PRED_DEF("$call_residue_vars_start", 0, call_residue_vars_start, 0)
  PRED_DEF("$call_residue_vars_end", 0, call_residue_vars_end, 0)
#endif
  PRED_DEF("attv_unify", 2, attv_unify, 0)
#ifdef O_METATERM
  PRED_DEF("$schedule_wakeup", 1, dschedule_wakeup, PL_FA_TRANSPARENT)
  PRED_DEF("$set_delayed", 2, dset_delayed, 0)
  PRED_DEF("$get_delayed", 2, dget_delayed, 0)
  PRED_DEF("$depth_of_var",    2, ddepth_of_var,    0)
  PRED_DEF("$trail_assignment",    1, dtrail_assignment,    0)
  PRED_DEF("$visible_attrs",    2, dvisible_attrs,    0)
  PRED_DEF("metaterm_flags", 3, metaterm_flags, 0)
  PRED_DEF("metaterm_overriding", 3, metaterm_overriding, 0)
#endif

EndPredDefs

#endif /*O_ATTVAR*/
