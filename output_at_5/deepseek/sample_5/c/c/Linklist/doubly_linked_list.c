#include "stdlib.h"

typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate node(node n; node prev, node next) =
  n->item |-> _ &*& n->next |-> next &*& n->prev |-> prev &*& malloc_block_node(n);
@*/

/*@
predicate dllist(dllist d) =
  d->head |-> ?head &*& d->tail |-> ?tail &*& malloc_block_dllist(d) &*&
  lseg(head, 0, tail) &*&
  tail == 0 ? emp : node(tail, ?prev, 0);
@*/

/*@
predicate lseg(node first, node prev, node last) =
  first == last ?
    emp
  :
    node(first, prev, ?next) &*&
    lseg(next, first, last);
@*/

void reverse(dllist arg)
//@ requires dllist(arg);
//@ ensures dllist(arg);
{
	//@ open dllist(arg);
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ node old_tail = arg->tail;
	//@ close lseg(ptr, 0, old_tail);
	//@ open lseg(ptr, 0, old_tail);
	while (ptr != 0)
	//@ invariant lseg(ptr, ?prev, old_tail);
	{
		//@ open node(ptr, prev, ?next);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node(ptr, temp1, temp2);
		ptr = temp1;
		//@ if (ptr != 0) { open lseg(ptr, ptr, old_tail); close lseg(ptr, ptr, old_tail); open lseg(ptr, ?oldprev, old_tail); }
	}
	//@ close lseg(0, temp2, old_tail);
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	//@ close dllist(arg);
}