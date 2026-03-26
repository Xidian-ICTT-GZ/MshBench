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
predicate nodes(struct node *n;) =
	n == 0 ?
		true
	:
		n->item |-> _ &*& n->next |-> ?nxt &*& n->prev |-> _ &*& nodes(nxt);

predicate dllist(struct dllist *dl;) =
	dl->head |-> ?h &*& dl->tail |-> ?t &*& nodes(h);
@*/

void reverse(dllist arg)
//@ requires dllist(arg);
//@ ensures dllist(arg);
{

	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ open dllist(arg);

	while (ptr != 0)
	//@ invariant nodes(ptr);
	{
		//@ open nodes(ptr);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;

		ptr = temp1;
		//@ close nodes(temp2);
	}
	//@ open nodes(ptr);

	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	//@ close dllist(arg);
}