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
predicate nodes(node n, node prev, node next) =
  n == 0 ?
    emp
  :
    n->item |-> _ &*& n->next |-> next &*& n->prev |-> prev &*& malloc_block_node(n) &*& nodes(next, n, ?nextnext);
@*/

/*@
predicate dllist(dllist d) =
  d->head |-> ?head &*& d->tail |-> ?tail &*& malloc_block_dllist(d) &*& nodes(head, 0, tail);
@*/

void reverse(dllist arg)
//@ requires dllist(arg);
//@ ensures dllist(arg);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ open dllist(arg);
	//@ open nodes(ptr, 0, arg->tail);
	while (ptr != 0)
	//@ invariant nodes(ptr, ?prev, ?next) &*& nodes(next, ptr, arg->tail);
	{
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ open nodes(temp1, ptr, ?temp1next);
		ptr = temp1;
		//@ close nodes(ptr, temp2, temp1next);
	}
	//@ close nodes(ptr, temp2, arg->tail);
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	//@ close dllist(arg);
}