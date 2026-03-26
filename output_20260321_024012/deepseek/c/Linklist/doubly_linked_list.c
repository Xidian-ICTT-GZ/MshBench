/*@
predicate node(node n; int v, node nxt, node prv) =
  n->item |-> v &*& n->next |-> nxt &*& n->prev |-> prv &*& malloc_block_node(n);
@*/

/*@
predicate dllist(dllist d; node h, node t) =
  d->head |-> h &*& d->tail |-> t &*& malloc_block_dllist(d);
@*/

typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

typedef struct dllist {
	node head;
	node tail;
} *dllist;

void reverse(dllist arg)
//@ requires dllist(arg, ?h, ?t);
//@ ensures dllist(arg, t, h);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ close node(0, _, _, _);
	//@ close node(0, _, _, _);
	while (ptr != 0)
	//@ invariant node(ptr, ?v, ?nxt, ?prv) &*& node(temp1, _, _, _) &*& node(temp2, _, _, _);
	{
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		ptr = temp1;
	}
	//@ open node(ptr, _, _, _);
	//@ open node(temp1, _, _, _);
	//@ open node(temp2, _, _, _);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
}