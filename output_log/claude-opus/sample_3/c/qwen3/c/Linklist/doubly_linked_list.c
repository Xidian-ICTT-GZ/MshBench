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

/*@ predicate dllist_segment(node start, node end) =
    start == end ?
        start != 0 ? start->item |-> _ &*& start->next |-> 0 &*& start->prev |-> 0 : true
    :
        start != 0 &*& end != 0 &*&
        start->item |-> _ &*& start->next |-> ?nxt &*& start->prev |-> ?prv &
        (nxt == end ?
            nxt->item |-> _ &*& nxt->next |-> 0 &*& nxt->prev |-> start
        :
            dllist_segment(nxt, end) &*&
            prv == 0 &*&
            start->prev |-> 0 &*&
            start->next |-> nxt
        );
@*/

/*@ predicate dllist_segment_reversed(node start, node end) =
    start == end ?
        start != 0 ? start->item |-> _ &*& start->next |-> 0 &*& start->prev |-> 0 : true
    :
        start != 0 &*& end != 0 &*&
        start->item |-> _ &*& start->next |-> ?prv &*& start->prev |-> ?nxt &
        (prv == end ?
            prv->item |-> _ &*& prv->next |-> 0 &*& prv->prev |-> start
        :
            dllist_segment_reversed(prv, end) &*&
            nxt == 0 &*&
            start->next |-> prv &*&
            start->prev |-> 0
        );
@*/

/*@ predicate dllist(struct dllist *l; node head, node tail) =
    l->head |-> head &*& l->tail |-> tail &*&
    (head == 0 ? tail == 0 : true) &*&
    (head != 0 ? dllist_segment(head, tail) : true);
@*/

void reverse(dllist arg)
//@ requires dllist(arg, ?head, ?tail);
//@ ensures dllist(arg, tail, head);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;

	/*@ invariant
	    ptr != 0 ?
	        dllist_segment(ptr, tail) &*&
	        dllist_segment_reversed(head, ptr) &*&
	        (ptr == head ? true : ptr->prev == ?p && p != 0) &*&
	        (head != 0 ? head->prev == 0 : true)
	    :
	        ptr == 0 &*&
	        dllist_segment_reversed(head, tail) &*&
	        (head == 0 ? tail == 0 : true)
	@*/
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