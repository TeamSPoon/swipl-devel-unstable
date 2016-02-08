/*  Part of SWI-Prolog

    Author:   Douglas Miles
    E-mail:   logicmoo@gmail.com
    WWW:      htbtp://www.swi-prolog.org
    Copyrightb (C): 2016, VU University Amsterdam

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

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Implementation of Dynamic Reordering of Alternatives a version of Tabling.  
  Implements:
     $enter_dra/0,
     $exit_dra/0 ...

  
#include "pl-incl.h" 
#include "pl-dict.h" 
#include "pl-dbref.h"

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

#ifdef O_DRA_TABLING
/*******************************
*	 HT_BLOB SYMBOL WRAPPER	*
*******************************/

static int release_htb(atom_t symbol);
static int compare_htbs(atom_t a, atom_t b);
static int write_htb(IOSTREAM *s, atom_t symbol, int flags);
static void acquire_htb(atom_t symbol);
static int save_htb(atom_t aref, IOSTREAM *fd);
static atom_t load_htb(IOSTREAM *fd);

static PL_blob_t ht_blob =
{ PL_BLOB_MAGIC,
  PL_BLOB_NOCOPY|PL_BLOB_UNIQUE,
  "hashtable_with_grefs",
  release_htb,
  compare_htbs,
  write_htb,
  acquire_htb,
  save_htb,
  load_htb,
};



static int
save_htb(atom_t aref, IOSTREAM *fd)
{ hashtable_with_grefs *ref = PL_blob_data(aref, NULL, NULL);
  (void)fd;

  return PL_warning("Cannot save reference to <hashtable_with_grefs>(%p)", ref);
}


static atom_t
load_htb(IOSTREAM *fd)
{ (void)fd;

  return PL_new_atom("<saved-hashtable_with_grefs-ref>");
}

static void
acquire_htb(atom_t symbol)
{ hashtable_with_grefs *htb = PL_blob_data(symbol, NULL, NULL);
  htb->symbol = symbol;
}



static int 
compare_htbs(atom_t a, atom_t b)
{ hashtable_with_grefs *htbA = PL_blob_data(a, NULL, NULL);
  hashtable_with_grefs *htbB = PL_blob_data(b, NULL, NULL);

  return( htbA > htbB ?  1 :
     htbA < htbB ? -1 : 0
   );
}



static int
write_htb(IOSTREAM *s, atom_t symbol, int flags)
{ hashtable_with_grefs *htb = PL_blob_data(symbol, NULL, NULL);

  Sfprintf(s, "<hashtable_with_grefs>(%p)", htb);
  return TRUE;
}



static void
clean_htb(hashtable_with_grefs *htb)
{ if ( htb->root )
  { destroyHTable(htb->root);
    htb->root = NULL;
  }
}

static int
destroy_htb(hashtable_with_grefs *htb)
{ clean_htb(htb);
  htb->magic = HT_W_REFS_MAGIC;
  PL_free(htb);
  return TRUE;
}

static int 
release_htb(atom_t symbol)
{ hashtable_with_grefs *htb = PL_blob_data(symbol, NULL, NULL);

  if ((htb->root))
  { destroyHTable(htb->root);
    htb->root = NULL;   
  }
  destroy_htb(htb);

  PL_free(htb);

  return TRUE;
}


static Procedure
findProcedure(term_t pred ARG_LD) 
{ functor_t fd;
  Module module = (Module) NULL;
  term_t head = PL_new_term_ref();
  if (PL_strip_module(pred, &module, head) ||
      PL_get_functor(head, &fd))
    return resolveProcedure(fd, module);
  return NULL;
}

static hashtable_with_grefs*
foc_trie_pointer(term_t pred ARG_LD) 
{ functor_t fd;
  Module module = (Module) NULL;
  term_t head = PL_new_term_ref();
  Table functor_to_ht_p = LD->dra_base.functor_to_ht_p;
  if(!functor_to_ht_p)
  {
    functor_to_ht_p = newHTable(10);
  }
  if (PL_strip_module(pred, &module, head) ||
      PL_get_functor(head, &fd))
  {
    hashtable_with_grefs* pred_trieP = lookupHTable(functor_to_ht_p,(void*)fd);
    if(!pred_trieP)
    { pred_trieP = malloc(sizeof(hashtable_with_grefs));
      addHTable(functor_to_ht_p,(void*)fd,pred_trieP);
    }
    (*pred_trieP).root = newHTable(10);
    return pred_trieP;
  }
  PL_error(NULL, 0, NULL, ERR_EXISTENCE,
                    "", pred);
  
  return NULL;
}


int
get_htb__LD(term_t t, hashtable_with_grefs **htb ARG_LD)
{ PL_blob_t *type;
  void *data;
  hashtable_with_grefs *p;

  if ( PL_get_blob(t, &data, NULL, &type) && type == &ht_blob)
  {  p = data;

    if ( p->symbol )
    { *htb = p;

      return TRUE;
    }

    PL_permission_error("access", "closed_bhtb", t);
    return FALSE;
  }
  
  Procedure proc = findProcedure(t PASS_LD);
  if(proc) 
  {
    Definition def = proc->definition;
    if(!def->pred_trie || !def->pred_trie->root)
    {
      def->pred_trie = foc_trie_pointer(t PASS_LD);
    }
    *htb = def->pred_trie;
    return htb!=NULL;
  }
  *htb = foc_trie_pointer(t PASS_LD);
  return htb!=NULL;
}
int
get_htb(term_t t, hashtable_with_grefs **htb)
{ GET_LD
  return get_htb__LD(t,htb PASS_LD);
}

int
unify_htb(term_t handle, hashtable_with_grefs *htb)
{ GET_LD

  if(!htb || !htb->root) return FALSE;

  if ( PL_unify_blob(handle, htb, sizeof(*htb), &ht_blob) )
    return TRUE;

  if ( !PL_is_variable(handle) )
    return PL_uninstantiation_error(handle);

  return FALSE;					/* (resource) error */
}



static
PRED_IMPL("new_htb",   1, new_htb,   0)
{ hashtable_with_grefs *htb = calloc(1, sizeof(*htb));

  if ( !htb )
    return PL_resource_error("memory");

  htb->magic    = HT_W_REFS_MAGIC;
  htb->root     = newHTable(10);
  htb->grefs   = 0;

  if ( unify_htb(A1, htb) )
    return TRUE;

  destroy_htb(htb);
  return FALSE;
}


static
PRED_IMPL("htb_clear",   1, htb_clear,   0)
{ PRED_LD

  hashtable_with_grefs* trie; 
  if(!get_htb__LD(A1, &trie  PASS_LD) || !trie) return FALSE;
  


  if (trie->root)
  { clearHTable(trie->root);
  }

  trie->grefs = 0;
  return TRUE;
}

static
PRED_IMPL("htb_free",   1, htb_free,   0)
{ PRED_LD

  hashtable_with_grefs* htb;

  if ( get_htb__LD(A1, &htb PASS_LD) )
  { release_htb(htb->symbol);
    htb->symbol = 0;
    clean_htb(htb);
    
    return TRUE;
  }

  return FALSE;
}



/*******************************/
/* TRIE DATABASE EXPERMENT USING HT_BLOB*/
/*******************************/


int
PL_is_htb(term_t t)
{ PL_blob_t *type;

  if ( PL_is_blob(t, &type) &&
       ( type == &ht_blob ) )
    return TRUE;

  return FALSE;
}

static
PRED_IMPL("is_htb",   1, is_htb,   0)
{ return PL_is_htb(A1);
}


static void
freezeHTGlobal(ARG1_LD)
{ LD->frozen_bar = LD->mark_bar = gTop;
  DEBUG(2, Sdprintf("*** frozen bar to %p at freezeHTGlobal()\n",
     LD->frozen_bar));
}

static void
free_key(word fkey)
{ if (isAtom(fkey))PL_unregister_atom(fkey);
}

static void
free_value(word value)
{ //hashtable_with_grefs trie = find_htb(loc  PASS_LD);
  if (isAtom(value))
    PL_unregister_atom(value);
  else if (storage(value) == STG_GLOBAL)
  { //trie->grefs--;
  }
}

static void
free_kv(void *fkey, void* value)
{ free_value((word)value);
  free_key((word)fkey);
}

#define HT_LINK_TERM 0x0

#define HT_COPY_SHARE	0x01			/* Share ground terms */
#define HT_COPY_ATTRS	0x02			/* do copy attributes */

#define HT_NB_ASSIGN 0x0
#define HT_BACKTRACK 0x8

#define HT_COPY_TERM 0x10
#define HT_DUPLICATE_TERM 0x20


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  For    backtrackable   variables  we  need
TrailAssignment(), but we can only call that  on addresses on the global
stack. Therefore we must make  a  reference   to  the  real value if the
variable is not already a reference.

SHIFT-SAFE: TrailAssignment() takes at most g+t=1+2.  One more Trail and
   2 more allocGlobal(1) makes g+t<3+3
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static int htb_assign(term_t loc, term_t key, term_t value, int assign_flags ARG_LD)
{ word fkey;
  Word p;
  word w, old;

  if (!getKeyEx(key, &fkey PASS_LD))
    fail;

  hashtable_with_grefs* trie; 
  if(!get_htb__LD(loc, &trie  PASS_LD) || !trie) return FALSE;
  

  if (!trie->root)
  { trie->root = newHTable(32);
    trie->root->free_symbol = free_kv;
  }

  if (!hasGlobalSpace(3))     /* also ensures trail for */
  { int rc;  /* TrailAssignment() */
    if ((rc=ensureGlobalSpace(3, ALLOW_GC)) != TRUE)
      return raiseStackOverflow(rc);
  }

  if (assign_flags & HT_DUPLICATE_TERM)
  { term_t copy = PL_new_term_ref();
    if (!duplicate_term(value, copy PASS_LD))
      return FALSE;
    value = copy;
  } else if (assign_flags & HT_COPY_TERM)
  { term_t copy = PL_new_term_ref();
    if (!copy_term_refs(value, copy, HT_COPY_ATTRS|HT_COPY_SHARE PASS_LD))
      return FALSE;
    value = copy;    
  }

  p = valTermRef(value);
  deRef(p);
  w = *p;

  if (canBind(w))
  { if (onStackArea(local, p))
    { Word p2 = allocGlobal(1);

      setVar(*p2);
      w = *p = makeRef(p2);
      LTrail(p);
    } else
    { w = makeRef(p);
    }
  }

  if (!(old = (word)lookupHTable(trie->root, (void*)fkey)))
  { addNewHTable(trie->root, (void*)fkey, (void*)ATOM_nil);
    if(isAtom(fkey))PL_register_atom(fkey);
    PL_register_atom(ATOM_nil);
    old = ATOM_nil;
  }
  assert(old);

  if (w == old)
    succeed;
  if (isAtom(old))
    PL_unregister_atom(old);

  if (assign_flags & HT_BACKTRACK)
  { Word p;

    if (isRef(old))
    { p = unRef(old);
    } else
    { p = allocGlobal(1);
      *p = old;
      freezeHTGlobal(PASS_LD1);   /* The value location must be */
      if (storage(old) != STG_GLOBAL)   /* preserved */
        trie->grefs++;
      updateHTable(trie->root, (void*)fkey, (void*)makeRefG(p));
    }

    TrailAssignment(p);
    *p = w;
  } else
  { if (storage(old) == STG_GLOBAL)
      trie->grefs--;

    updateHTable(trie->root, (void*)fkey, (void*)w);

    if (storage(w) == STG_GLOBAL)
    { freezeHTGlobal(PASS_LD1);
      trie->grefs++;
    } else if (isAtom(w))
      PL_register_atom(w);
  }

  succeed;
}

typedef enum
{ htb_fail,
  htb_retry,
  htb_error
} htb_key_action;

static htb_key_action
auto_define_key_value(term_t trie, word fkey)
{ GET_LD
  
static predicate_t ex;
  fid_t fid;
  term_t av;

  htb_key_action rc = htb_error;

  if (!ex)
    ex = PL_predicate("exception", 3, "user");

  if (!(fid = PL_open_foreign_frame()))
    return htb_error;
  av = PL_new_term_refs(3);
  PL_put_atom(av+0, ATOM_undefined_global_variable);
  PL_put_atom(av+1, fkey);
  PL_put_term(av+2, trie);

  rc = htb_fail;  /* retry, error, fail */

  int ret = PL_call_predicate(NULL, PL_Q_PASS_EXCEPTION, ex, av);
  if (ret==TRUE)
  { rc = htb_retry;
  } else if (ret==FALSE)
  { rc = htb_error;
  }

  PL_close_foreign_frame(fid);

  return rc;
}

/* 
htb_value_LD() is a quick and dirty way to get a global variable.
   It is used to get '$variable_names' for compiler warnings.

   Note that this function does *not* call auto_define_key_value().  This
   is on purpose because we cannot call Prolog from the compiler and
   there is no need for this hook for this variable.  Be careful to
   fix this if this function is to be used for other purposes.

int
htb_value_LD(word fkey, Word p ARG_LD)
{ if ( trie->root )
  { word w;
    if ( (w = (word)lookupHTable(trie->root, (void*)fkey)) )
    { *p = w;
 return TRUE;
    }
  }

  return FALSE;
}

*/

int
htb_lookup(term_t loc, term_t key, term_t value, int raise_error ARG_LD)
{
  word fkey;
  int i;

  if ( !getKeyEx(key, &fkey  PASS_LD) )
    fail;
  if ( !hasGlobalSpace(0) )
  { int rcgs;

    if ( (rcgs=ensureGlobalSpace(0, ALLOW_GC)) != TRUE )
      return raiseStackOverflow(rcgs);
  }

  hashtable_with_grefs* trie; 
  if(!get_htb__LD(loc, &trie  PASS_LD) || !trie) return FALSE;
  


  for ( i=0; i<2; i++ )
  { if ( trie->root )
    { word w;
      if ( (w = (word)lookupHTable(trie->root, (void*)fkey)) )
      {
        term_t tmp = PL_new_term_ref();
        *valTermRef(tmp) = w;
        return PL_unify(value, tmp);
      }
    }

    switch ( auto_define_key_value(loc, fkey) )
    { case htb_fail:
        fail;
      case htb_retry:
        continue;
      case htb_error:
        if ( exception_term )
          fail;    /* error from handler */
        goto error;
    }
  }

  error:
  if ( raise_error )
    return PL_error(NULL, 0, NULL, ERR_EXISTENCE,
                    ATOM_variable, key);
  else
    return FALSE;
}



/* disable tabling meta_interp */

static
PRED_IMPL("$enter_dra", 0, denter_dra, 0)
{ PRED_LD
  LD->dra_base.in_dra++;
  return TRUE;
}

/* re-enable tabling meta_interp */

static
PRED_IMPL("$exit_dra", 0, dexit_dra, 0)
{ PRED_LD
  LD->dra_base.in_dra--;
  return TRUE;
}


static
PRED_IMPL("htb_set_copy", 3, htb_set_copy, 0)
{ PRED_LD

  return htb_assign(A1, A2, A3, HT_COPY_TERM|HT_BACKTRACK PASS_LD);
}

static
PRED_IMPL("htb_set_duplicate_value", 3, htb_set_duplicate_value, 0)
{ PRED_LD

  return htb_assign(A1, A2, A3, HT_DUPLICATE_TERM|HT_BACKTRACK PASS_LD);
}

static
PRED_IMPL("htb_linkval", 3, htb_linkval, 0)
{ PRED_LD

  return htb_assign(A1, A2, A3, HT_LINK_TERM|HT_BACKTRACK PASS_LD);
}

static
PRED_IMPL("htb_nb_set_copy", 3, htb_nb_set_copy, 0)
{ PRED_LD

  return htb_assign(A1, A2, A3, HT_COPY_TERM|HT_NB_ASSIGN PASS_LD);
}

static
PRED_IMPL("htb_nb_set_duplicate_value", 3, htb_nb_set_duplicate_value, 0)
{ PRED_LD

  return htb_assign(A1, A2, A3, HT_DUPLICATE_TERM|HT_NB_ASSIGN PASS_LD);
}

static
PRED_IMPL("htb_nb_linkval", 3, htb_nb_linkval, 0)
{ PRED_LD

  return htb_assign(A1, A2, A3, HT_LINK_TERM|HT_NB_ASSIGN PASS_LD);
}

static
PRED_IMPL("htb_lookup", 3, htb_lookup, 0)
{ PRED_LD

  return htb_lookup(A1, A2, A3, FALSE PASS_LD);
}

static
PRED_IMPL("htb_delete", 2, htb_delete, 0)
{ PRED_LD
  word fkey;

  if (!getKeyEx(A2, &fkey  PASS_LD))
    fail;

  hashtable_with_grefs* trie; 
  if(!get_htb__LD(A1, &trie  PASS_LD) || !trie) return FALSE;
  


  if (trie->root)
  { word w;
    if ((w = (word)lookupHTable(trie->root, (void*)fkey)))
    { deleteHTable(trie->root, (void*)fkey);
       free_key(fkey);
       free_value(w);
    }
  }

  succeed;
}

static
PRED_IMPL("htb_current", 3, htb_current, PL_FA_NONDETERMINISTIC)
{ PRED_LD
  TableEnum e;
  word fkey;
  word val;
  fid_t fid;

  switch (CTX_CNTRL)
  { case FRG_FIRST_CALL:
   if (!PL_is_variable(A2))
     return htb_lookup(A1, A2, A3, FALSE PASS_LD);

   hashtable_with_grefs* trie; 
   if(!get_htb__LD(A1, &trie  PASS_LD) || !trie) return FALSE;
   

   if (trie->root)
   { e = newTableEnum(trie->root);
     break;
   } else
   { fail;
   }
      case FRG_REDO:
   e =  CTX_PTR;
   break;
      case FRG_CUTTED:
   e =  CTX_PTR;
   freeTableEnum(e);
   succeed;
      default:
   assert(0);
   fail;
  }

  if (!(fid = PL_open_foreign_frame()))
  { freeTableEnum(e);
    return FALSE;
  }
  while (advanceTableEnum(e, (void**)&fkey, (void**)&val))
  { if (unifyKey(A2, fkey) &&
   unify_ptrs(valTermRef(A3), &val, 0 PASS_LD))
    { PL_close_foreign_frame(fid);
      ForeignRedoPtr(e);
    } else
    { PL_rewind_foreign_frame(fid);
    }
  }
  PL_close_foreign_frame(fid);

  freeTableEnum(e);
  fail;
}


static inline int
isGlobalRef(word w)
{ return storage(w) == STG_GLOBAL;
}
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Dealing  with  nb_set_duplicate_value/2  and   nb_lookup/2  non-backtrackable  global
variables as defined  in  pl-gvar.c.  We   cannot  mark  and  sweep  the
hash-table itself as the  reversed   pointers  cannot  address arbitrary
addresses returned by allocHeapOrHalt(). Therefore we   turn all references to
the  global  stack  into  term-references  and  rely  on  the  available
mark-and-sweep for foreign references.

If none of the global  variable  refers   to  the  global stack we could
`unfreeze' the global stack, except  we   may  have used nb_setarg/3. We
could enhance on this by introducing  a   `melt-bar'  set  to the lowest
location which we assigned using nb_setarg/3.   If backtracking takes us
before  that  point  we  safely  know  there  are  no  terms  left  with
nb_setarg/3  assignments.  As  the  merged   backtrackable  global  vars
implementation also causes freezing of the  stacks it it uncertain there
is much to gain with this approach.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
/*
static fid_t
trie_to_term_refs(hashtable_with_grefs trie, Word **saved_bar_at)
{ GET_LD
  fid_t fid = PL_open_foreign_frame();

  if ( trie->root && trie->grefs > 0 )
  { TableEnum e = newTableEnum(trie->root);
    int found = 0;
    word w;

    while( advanceTableEnum(e, NULL, (void**)&w) )
    { if ( isGlobalRef(w) )
      { term_t t = PL_new_term_ref_noshift();

	assert(t);
	*valTermRef(t) = w;
	found++;
      }
    }

    freeTableEnum(e);
    assert(trie->grefs == found);

    DEBUG(MSG_GC_MARK_GVAR,
	  Sdprintf("Found %d global vars on global stack. "
		   "stored in frame %p\n", found, fli_context));
  }

  if ( LD->frozen_bar )
  { Word *sb;

    assert((Word)lTop + 1 <= (Word)lMax);
    sb = (Word*)lTop;
    lTop = (LocalFrame)(sb+1);
    *sb = LD->frozen_bar;
    *saved_bar_at = sb;
  } else
  { *saved_bar_at = NULL;
  }

  return fid;
}


static void
term_refs_to_trie(hashtable_with_grefs trie, fid_t fid, Word *saved_bar_at)
{ GET_LD

  if ( saved_bar_at )
  { assert((void *)(saved_bar_at+1) == (void*)lTop);
    LD->frozen_bar = valPtr2((word)*saved_bar_at, STG_GLOBAL);

    assert(onStack(global, LD->frozen_bar) || LD->frozen_bar == gTop);
    lTop = (LocalFrame) saved_bar_at;
  }

  if ( trie->grefs > 0 )
  { FliFrame fr = (FliFrame) valTermRef(fid);
    Word fp = (Word)(fr+1);
    TableEnum e = newTableEnum(trie->root);
    atom_t name;
    word p;
    int found = 0;

    while( advanceTableEnum(e, (void**)&name, (void**)&p) )
    { if ( isGlobalRef(p) )
      { p = *fp++;
	updateHTable(e->table, (void*)name, (void*)p);
	found++;
      }
    }
    assert(found == fr->size);

    freeTableEnum(e);
  }

  PL_close_foreign_frame(fid);
}
*/

/*******************************
*	    REGISTRATION	*
*******************************/

BeginPredDefs(dra)

  PRED_DEF("$enter_dra",   0, denter_dra,   0)
  PRED_DEF("$exit_dra",   0, dexit_dra,   0)

  PRED_DEF("is_htb",   1, is_htb,   0)
  PRED_DEF("htb_free",    1, htb_free,   0)

  PRED_DEF("new_htb",   1, new_htb,   0)
  PRED_DEF("htb_clear", 1, htb_clear,   0)

  
  PRED_DEF("htb_linkval", 3, htb_linkval, 0)
  PRED_DEF("htb_set_copy", 3, htb_set_copy, 0)
  PRED_DEF("htb_set_duplicate_value", 3, htb_set_duplicate_value, 0)
  PRED_DEF("htb_nb_linkval", 3, htb_nb_linkval, 0)
  PRED_DEF("htb_nb_set_copy", 3, htb_nb_set_copy, 0)
  PRED_DEF("htb_nb_set_duplicate_value", 3, htb_nb_set_duplicate_value, 0)

  PRED_DEF("htb_delete", 2, htb_delete, 0)

  PRED_DEF("htb_current", 3, htb_current, PL_FA_NONDETERMINISTIC)
  PRED_DEF("htb_lookup", 3, htb_lookup, 0)
  

EndPredDefs
#endif