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
predicate nodes(struct node *n, struct node *p, struct node *nxt) =
    n == 0 ?
        emp
    :
        n->item |-> _ &*& n->next |-> nxt &*& n->prev |-> p &*& malloc_block_node(n);
@*/

/*@
predicate dllist_foot(struct node *h, struct node *t) =
    h == 0 ?
        t == 0
    :
        t->next |-> 0;
@*/

/*@
predicate dllist(dllist l) =
    l->head |-> ?h &*& l->tail |-> ?t &*& malloc_block_dllist(l) &*& nodes(h, 0, _) &*& dllist_foot(h, t);
@*/

void reverse(dllist arg)
//@ requires dllist(arg);
//@ ensures dllist(arg);
{

	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ open dllist(arg);
	//@ open nodes(arg->head, 0, _);
	//@ close nodes(arg->head, 0, _);
	//@ struct node *oldhead = arg->head;
	//@ struct node *oldtail = arg->tail;

	while (ptr != 0)
	//@ invariant nodes(ptr, ?prev, _) &*& nodes(oldhead, 0, ptr) &*& dllist_foot(oldhead, oldtail);
	{

		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ open nodes(ptr, temp2, temp1);
		//@ close nodes(ptr, temp1, temp2);

		ptr = temp1;
		//@ if (ptr != 0) { open nodes(ptr, _, _); close nodes(ptr, _, _); }
	}
	//@ open dllist_foot(oldhead, oldtail);
	//@ close dllist_foot(oldtail, oldhead);

	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	//@ close dllist(arg);
}