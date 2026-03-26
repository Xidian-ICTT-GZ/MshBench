typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@
predicate node_points_to(node n, int item, node next, node prev) =
  n != 0 &*& 
  n->item |-> item &*&
  n->next |-> next &*&
  n->prev |-> prev;
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate dllist_points_to(dllist d, node head, node tail) =
  d != 0 &*&
  d->head |-> head &*&
  d->tail |-> tail;
@*/

void reverse(dllist arg)
  //@ requires dllist_points_to(arg, ?head, ?tail) &*& (head == 0 || node_points_to(head, _, _, _));
  //@ ensures dllist_points_to(arg, tail, head) &*& (tail == 0 || node_points_to(tail, _, _, _));
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ open dllist_points_to(arg, _, _);
	
	while (ptr != 0)
		//@ invariant true;
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
	
	//@ close dllist_points_to(arg, arg->head, arg->tail);
}