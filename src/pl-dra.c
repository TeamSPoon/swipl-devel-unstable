/*  Part of SWI-Prolog

    Author:        Douglas Miles
    E-mail:        logicmoo@gmail.com
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2016, VU University Amsterdam

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
Implementation of Dynamic Reordering of Alternatives a version of Tabling.  
  Implements:
     $enter_dra/0,
     $exit_dra/0 ...

  
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* disable tabling meta_interp */
static
PRED_IMPL("$enter_dra", 0, denter_dra, 0)
{ PRED_LD
  LD->dra.in_dra++;
  return TRUE;
}

/* re-enable tabling meta_interp */
static
PRED_IMPL("$exit_dra", 0, dexit_dra, 0)
{ PRED_LD
  LD->dra.in_dra--;
  return TRUE;
}

		 /*******************************
		 *      PUBLISH PREDICATES	*
		 *******************************/

BeginPredDefs(dra)
  PRED_DEF("$enter_dra",        0, denter_dra,        0)
  PRED_DEF("$exit_dra",        0, dexit_dra,        0)
EndPredDefs