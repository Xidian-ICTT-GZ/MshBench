/*@
predicate node(node n; int v, node nxt, node prv) =
    n->item |-> v &*& n->next |-> nxt &*& n->prev |-> prv &*& malloc_block_node(n);
@*/

/*@
predicate dllist(dllist d; node h, node t) =
    d->head |-> h &*& d->tail |-> t &*& malloc_block_dllist(d);
@*/

/*@
predicate dllseg(node fr, node to; node prv, node nxt) =
    fr == to ?
        nxt == fr &*& prv == to
    :
        node(fr, ?v, ?n, prv) &*& dllseg(n, to, fr, nxt);
@*/

/*@
predicate dllist_full(dllist d) =
    dllist(d, ?h, ?t) &*& dllseg(h, 0, 0, ?n) &*& dllseg(t, 0, ?p, 0) &*& h == ?hh &*& t == ?tt &*&
    (h == 0 ? t == 0 : node(h, ?hv, ?hn, 0) &*& node(t, ?tv, 0, ?tp));
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
//@ requires dllist_full(arg);
//@ ensures dllist_full(arg);
{
	//@ open dllist_full(arg);
	//@ open dllist(arg, ?h, ?t);
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ close dllseg(ptr, 0, 0, ptr);
	//@ close dllseg(ptr, 0, ptr, 0);
	while (ptr != 0)
	//@ invariant dllseg(ptr, 0, ?prev, ?next) &*& dllseg(ptr, 0, ?prev2, ?next2);
	{
		//@ open dllseg(ptr, 0, prev, next);
		//@ open node(ptr, ?v, ?nxt, ?prv);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node(ptr, v, temp2, temp1);
		//@ close dllseg(ptr, 0, temp1, temp2);
		ptr = temp1;
		//@ close dllseg(ptr, 0, prev, next);
	}
	//@ open dllseg(ptr, 0, _, _);
	//@ open dllseg(ptr, 0, _, _);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dllist(arg, temp2, temp1);
	//@ close dllist_full(arg);
}