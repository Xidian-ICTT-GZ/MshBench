#include <stdlib.h>
/*@
predicate node(node n; int v, node nxt, node prv) =
  n->item |-> v &*& n->next |-> nxt &*& n->prev |-> prv &*& malloc_block_node(n);
@*/

/*@
predicate dllseg(node fr, node to; list<int> vs, list<node> nxts, list<node> prvs) =
  fr == to ?
    vs == nil &*& nxts == nil &*& prvs == nil
  :
    node(fr, ?v, ?nxt, ?prv) &*&
    dllseg(nxt, to, ?vs0, ?nxts0, ?prvs0) &*&
    vs == cons(v, vs0) &*& nxts == cons(nxt, nxts0) &*& prvs == cons(prv, prvs0);
@*/

/*@
predicate dllist(dllist d; list<int> vs, list<node> nxts, list<node> prvs) =
  d->head |-> ?h &*& d->tail |-> ?t &*& malloc_block_dllist(d) &*&
  dllseg(h, 0, vs, nxts, prvs) &*& t == (h == 0 ? 0 : nth(length(vs)-1, nxts));
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
//@ requires dllist(arg, ?vs, ?nxts, ?prvs);
//@ ensures dllist(arg, reverse(vs), reverse(nxts), reverse(prvs));
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ open dllist(arg, vs, nxts, prvs);
	//@ open dllseg(arg->head, 0, vs, nxts, prvs);
	while (ptr != 0)
	//@ invariant dllseg(ptr, 0, ?vs1, ?nxts1, ?prvs1) &*& dllseg(arg->head, ptr, ?vs0, ?nxts0, ?prvs0);
	{
		//@ open node(ptr, ?v, ?nxt, ?prv);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node(ptr, v, temp2, temp1);
		ptr = temp1;
		//@ if (ptr != 0) { open node(ptr, _, _, _); close node(ptr, _, _, _); }
	}
	//@ close dllseg(0, 0, nil, nil, nil);
	//@ close dllseg(arg->head, 0, reverse(vs), reverse(nxts), reverse(prvs));
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	//@ close dllist(arg, reverse(vs), reverse(nxts), reverse(prvs));
}