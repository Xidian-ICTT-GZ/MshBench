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
predicate nodes(node n;) =n == 0 ?
        emp
    :
        n->item |-> _ &*& n->next |-> ?next &*& n->prev |-> _ &*& nodes(next);
@*/

/*@
predicate dllist_pred(dllist d;) =
    d->head |-> ?h &*& d->tail |-> _ &*& nodes(h);
@*/

void reverse(dllist arg)
    //@ requires dllist_pred(arg);
    //@ ensures dllist_pred(arg);
{
    //@ open dllist_pred(arg);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;

    //@ close nodes(0);
    while (ptr != 0)
        //@ invariant nodes(ptr);
    {
        //@ open nodes(ptr);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;

        ptr = temp1;
    }
    //@ open nodes(0);

    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    //@ close nodes(0);//@ close dllist_pred(arg);
}