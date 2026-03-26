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

/*@ predicate node_struct(node n) = n->item |-> _ &*& n->next |-> _ &*& n->prev |-> _; @*/

/*@ predicate dllist_struct(dllist d) = d->head |-> _ &*& d->tail |-> _; @*/

/*@
void reverse(dllist arg)
	requires dllist_struct(arg);
	ensures dllist_struct(arg);
@*/
void reverse(dllist arg)
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;

	while (ptr != 0)
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