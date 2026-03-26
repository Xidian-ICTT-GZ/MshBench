typedef struct node
{
	int item;
	struct node *next;
	struct node *prev;
} *node;

typedef struct dllist
{
	node head;
	node tail;
} *dllist;

/*@

predicate node_cell(node n; int item, node next, node prev) =
    n->item |-> item &*& n->next |-> next &*& n->prev |-> prev;

predicate dllist_struct(dllist d; node h, node t) =
    d->head |-> h &*& d->tail |-> t;

@*/

void reverse(dllist arg)
 //@ requires dllist_struct(arg, ?h, ?t);
 //@ ensures dllist_struct(arg, t, h);
{

	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;

	while (ptr != 0)

	//@ invariant dllist_struct(arg, h, t);
	{

		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;

		ptr = temp1;
	}

	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
}