/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2013, VU University Amsterdam

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

#include "pl-incl.h"
#include "pl-dbref.h"

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Implementation of `delimited continuation'.  Implements

  * reset(:Goal, -Cont, ?Templ)
  * shift(+Ball)
  * call_continuation(+Cont)

reset/3 is simply implemented as

  reset(Goal, _, _) :-
	call(Goal).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static
PRED_IMPL("$start_reset", 0, start_reset, 0)
{ PRED_LD
  LocalFrame fr = environment_frame;

  assert(fr->parent);
  set(fr->parent, FR_INRESET);

  return TRUE;
}


static term_t
findReset(LocalFrame fr, term_t ball ARG_LD)
{ Definition reset3  = PROCEDURE_reset3->definition;

  for(; fr; fr = fr->parent)
  { int rc;
    term_t tref;

    if ( fr->predicate != reset3 )
      continue;

    tref = consTermRef(fr);
    rc = PL_unify(consTermRef(argFrameP(fr, 2)), ball);
    fr = (LocalFrame)valTermRef(tref);

    if ( rc )
    { return consTermRef(fr);
    }
  }

  return 0;
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
put_environment() puts a term into env   that represents the environment
for fr when started from pc.

Note that if the environment contains a  variable on the local stack, we
must trail this. This is not needed   for  variables on the global stack
because the environment structure we create is newer.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static int
put_environment(term_t env, LocalFrame fr, Code pc)
{ GET_LD
  int i, slots    = fr->clause->value.clause->prolog_vars;
  size_t bv_bytes = sizeof_bitvector(slots);
  union
  { char       bv_store[bv_bytes];
    bit_vector bv;
  } store;
  bit_vector *active = &store.bv;
  term_t argv = PL_new_term_refs(2);

  init_bitvector(active, slots);
  mark_active_environment(active, fr, pc);

  PL_put_nil(env);
  for(i=0; i<slots; i++)
  { if ( true_bit(active, i) )
    { term_t fr_ref = consTermRef(fr);
      Word p = argFrameP(fr, i);

      deRef(p);
      if ( isVar(*p) && p > (Word)lBase )
	LTrail(p);
					/* internal one is void */
      PL_put_term(argv+1, consTermRef(argFrameP(fr, i)));

      if ( !PL_put_integer(argv+0, i) ||
	   !PL_cons_functor_v(argv+0, FUNCTOR_minus2, argv) ||
	   !PL_cons_list(env, argv+0, env) )
	return FALSE;			/* resource error */

      fr = (LocalFrame)valTermRef(fr_ref);
    }
  }

  return TRUE;
}



static qid_t 
quidFromGoal(Module module, term_t goal, int flags)
{ GET_LD
  functor_t fd;
  Procedure proc;
  term_t g;

  assert((Word)lTop == refFliP(fli_context, fli_context->size));

  if ( !(g=PL_new_term_ref()) )
  {
    return FALSE;
  }

  if ( !PL_strip_module(goal, &module, g) )
    return FALSE;
  if ( !PL_get_functor(g, &fd) )
  {
    PL_error(NULL, 0, NULL, ERR_TYPE, ATOM_callable, goal);
    PL_reset_term_refs(g);
    return FALSE;
  }
  proc = resolveProcedure(fd, module);

  { int arity = arityFunctor(fd);
    term_t args;
    int n;

    if ( (args = PL_new_term_refs(arity)) )
    {
      for ( n=0; n<arity; n++ )
        _PL_get_arg(n+1, g, args+n);

     return PL_open_query(module, flags, proc, args);
    }
  }
  return FALSE;
}

static int
get_deterministic(ARG1_LD)
{ LocalFrame FR  = environment_frame->parent;
  Choice     BFR = LD->choicepoints;
  
  for ( ; BFR; BFR = BFR->parent )
  {
    switch ( BFR->type )
    {
      case CHP_CLAUSE:
        if ( BFR->frame == FR )
          return CHP_CLAUSE;
      case CHP_JUMP:
        if ( (void *)BFR > (void *)FR )
          return 0;
        else
          return 2;
      default:
        continue;
    }
  }
  return 3;
}


#define RETRY_MAGIC	0x37ac7666

typedef struct retry_next
{ int		magic;			/* RETRY_MAGIC */
  term_t   presetup;		/* Used for undo  */
  qid_t    qid;		/* Used for redo  */
} retry_next;


static
PRED_IMPL("setup_call_cleanup_each", 3, setup_call_cleanup_each, PL_FA_NONDETERMINISTIC|PL_FA_TRANSPARENT)
{
  PRED_LD
  retry_next *redo;
  redo = 0;
  int rval, det;
  term_t qex = 0;
  
  switch ( CTX_CNTRL )
  {
    case FRG_FIRST_CALL:
      redo = malloc(sizeof(retry_next));
      DEBUG(MSG_NSOLS, Sdprintf("Suspend %p\n", redo));
      redo->magic = RETRY_MAGIC;
      redo->qid = quidFromGoal(NULL,A2,PL_Q_NORMAL);
    case FRG_REDO:
      if(!redo)
      {
        redo = CTX_PTR;
        if(redo->presetup) PL_reset_term_refs(redo->presetup);
      }
      redo->presetup =  PL_new_term_ref();

      startCritical;
      rval = callProlog(NULL, A1, PL_Q_PASS_EXCEPTION, NULL);
      if ( !endCritical )
        fail;       /* aborted */
      if ( rval!=TRUE )
      {
        return rval;
      }
      rval = PL_next_solution(redo->qid);

      DEBUG(MSG_NSOLS, Sdprintf("Resume %p\n", redo));
      if ( !rval )
      { det = 1;
        qex = PL_exception(redo->qid); 
      } else
      {
        det = get_deterministic(PASS_LD1);
      }
      if ( det )
      { PL_cut_query(redo->qid);
      }

      startCritical;
      callProlog(NULL, A3, PL_Q_PASS_EXCEPTION, NULL);
      if ( !endCritical )
        rval = 0;       /* aborted */

      if (qex)
      {
        PL_throw(qex);
        return rval;
      }

      if(!rval) 
      { if(redo->presetup)
          PL_reset_term_refs(redo->presetup);
        return FALSE;
      }

      if (!det )ForeignRedoPtr(redo);
      return rval;

    case FRG_CUTTED:
      redo = CTX_PTR;
      PL_cut_query(redo->qid);
      free(redo);
      return TRUE;
    default:
      assert(0);
      return FALSE;
  }
}

static int
unify_continuation(term_t cont, LocalFrame resetfr, LocalFrame fr, Code pc)
{ GET_LD
  term_t argv      = PL_new_term_refs(3);
  term_t reset_ref = consTermRef(resetfr);
  term_t contv;
  LocalFrame fr2;
  int depth = 0;

  for(fr2=fr; fr2 != resetfr; fr2=fr2->parent)
    depth++;
  if ( !(contv = PL_new_term_refs(depth)) )
    return FALSE;

  for( depth=0;
       fr != resetfr;
       pc = fr->programPointer, fr=fr->parent, depth++)
  { Clause     cl = fr->clause->value.clause;
    long pcoffset = pc - cl->codes;
    term_t fr_ref = consTermRef(fr);

    assert(!onStackArea(local, cl));

    if ( !PL_put_clref(argv+0, cl) ||
	 !PL_put_integer(argv+1, pcoffset) ||
	 !put_environment(argv+2, fr, pc) ||
	 !PL_cons_functor_v(contv+depth, FUNCTOR_dcont3, argv)  )
      return FALSE;

    resetfr = (LocalFrame)valTermRef(reset_ref);
    fr      = (LocalFrame)valTermRef(fr_ref);
  }

  return ( PL_cons_list_v(cont, depth, contv) &&
	   PL_cons_functor_v(cont, FUNCTOR_call_continuation1, cont)
	 );
}


/** shift(+Ball)

Performs the following steps:

  1. Search the stack, similar to throw/1 for reset/3 and
     unify Ball.
  2. Collect the continuation as a list of terms, each
     term is of the form

	cont(Clause, PC, Env)

     Here, Clause is the clause, PC is the program counter inside
     the clause, Env is a list of Offset-Value pairs, containing
     the reachable part of the environment.
  3. Unify Cont of the reset/2 goal with the continuation
  4. Modify the saved PC of current frame to return to the exit
     of reset/0
*/

static
PRED_IMPL("shift", 1, shift, 0)
{ PRED_LD
  term_t ball = A1;
  term_t reset;

  if ( (reset=findReset(environment_frame, ball PASS_LD)) )
  { term_t cont = PL_new_term_ref();
    LocalFrame resetfr;
    LocalFrame fr;

    DEBUG(MSG_CONTINUE, Sdprintf("Found reset/3 at %ld\n", reset));
    PL_put_nil(cont);
    resetfr = (LocalFrame)valTermRef(reset);
    if ( !unify_continuation(cont, resetfr,
			     environment_frame->parent,
			     environment_frame->programPointer) )
    { DEBUG(MSG_CONTINUE, Sdprintf("Failed to collect continuation\n"));
      return FALSE;			/* resource error */
    }

    resetfr = (LocalFrame)valTermRef(reset);
    if ( !PL_unify(consTermRef(argFrameP(resetfr, 1)), cont) )
    { DEBUG(MSG_CONTINUE, Sdprintf("Failed to unify continuation\n"));
      if ( PL_exception(0) )
	return FALSE;
      else
	return PL_error(NULL, 0, NULL, ERR_UNINSTANTIATION,
			0, consTermRef(argFrameP(resetfr, 1)));
    }
    resetfr = (LocalFrame)valTermRef(reset);

					/* leave (dynamic) predicates */
    for(fr = environment_frame->parent;
	(fr > (LocalFrame)LD->choicepoints &&
	 fr > resetfr
	);
	fr = fr->parent)
    { leaveDefinition(fr->predicate);
    }
					/* trim lTop.  Note that I_EXIT */
					/* does not touch this due to FR_KEEPLTOP */
    if ( fr <= (LocalFrame)LD->choicepoints )
    { lTop = (LocalFrame)(LD->choicepoints+1);
    } else
    { assert(fr == resetfr);
      lTop = (LocalFrame)argFrameP(fr, fr->clause->value.clause->variables);
    }

					/* return as from reset/3 */
    fr = environment_frame;
    fr->programPointer = resetfr->programPointer;
    fr->parent         = resetfr->parent;
    set(fr, FR_KEEPLTOP);

    return TRUE;
  }

  return PL_existence_error("reset/3", ball);
}


/** '$call_one_tail_body'(+Cont)

Reactivate a single tail body from a continuation. See shift for the
representation of the continuation.
*/


static
PRED_IMPL("$call_one_tail_body", 1, call_one_tail_body, 0)
{ PRED_LD
  term_t cont = A1;
  LocalFrame me, top, fr;
  Code pc;

retry:
  top    = lTop;
  me     = environment_frame;

  if ( PL_is_functor(cont, FUNCTOR_dcont3) )
  { term_t env  = PL_new_term_ref();
    term_t arg  = PL_new_term_ref();
    term_t head = PL_new_term_ref();
    Clause cl;
    ClauseRef cref;
    long pcoffset;
    size_t lneeded, lroom;
    Word ap;
    int i;

    _PL_get_arg(1, cont, arg);
    if ( !PL_get_clref(arg, &cl) )
      return FALSE;
    _PL_get_arg(2, cont, arg);
    if ( !PL_get_long_ex(arg, &pcoffset) )
      return FALSE;
    _PL_get_arg(3, cont, env);

    lneeded = SIZEOF_CREF_CLAUSE +
	      (size_t)argFrameP((LocalFrame)NULL, cl->variables);
    lroom   = roomStack(local);
    if ( lroom < lneeded )		/* resize the stack */
    { int rc;

      if ( (rc = ensureLocalSpace(roomStack(local)*2, ALLOW_SHIFT)) != TRUE )
	return raiseStackOverflow(rc);
      goto retry;
    }

    cref = (ClauseRef)top;
    fr   = addPointer(cref, SIZEOF_CREF_CLAUSE);
    top  = addPointer(top, lneeded);

    for(ap = argFrameP(fr, 0), i=cl->prolog_vars; i-- > 0; )
      *ap++ = ATOM_garbage_collected;
    for(i=cl->variables-cl->prolog_vars; i-- > 0; )
      *ap++ = 0;

    while( PL_get_list_ex(env, head, env) )
    { int offset;

      if ( !PL_is_functor(head, FUNCTOR_minus2) )
	return PL_type_error("pair", head);

      _PL_get_arg(1, head, arg);
      if ( !PL_get_integer_ex(arg, &offset) )
	return FALSE;
      _PL_get_arg(2, head, arg);
      argFrame(fr, offset) = linkVal(valTermRef(arg));
    }
    if ( !PL_get_nil_ex(env) )
      return FALSE;

    lTop = top;

    cref->next         = NULL;
    /*cref->key          = 0;*/
    cref->value.clause = cl;

    fr->programPointer = me->programPointer;
    fr->parent         = me->parent;
    fr->level          = me->level;
    fr->clause         = cref;
    fr->predicate      = cl->predicate;
    fr->context	       = fr->predicate->module;
    fr->flags          = 0;		/* TBD: anything needed? */
#ifdef O_PROFILE
    fr->prof_node      = NULL;
#endif
    setGenerationFrame(fr, GD->generation);
    enterDefinition(fr->predicate);

    pc     = cl->codes+pcoffset;

    me->parent = fr;
    me->programPointer = pc;
    set(me, FR_KEEPLTOP);

    return TRUE;
  } else
  { return PL_type_error("continuation", cont);
  }
}

		 /*******************************
		 *      PUBLISH PREDICATES	*
		 *******************************/

BeginPredDefs(cont)
  PRED_DEF("$start_reset",        0, start_reset,        0)
  PRED_DEF("shift",               1, shift,              0)
  PRED_DEF("$call_one_tail_body", 1, call_one_tail_body, 0)
  PRED_DEF("setup_call_cleanup_each", 3, setup_call_cleanup_each, PL_FA_NONDETERMINISTIC|PL_FA_TRANSPARENT)
EndPredDefs
