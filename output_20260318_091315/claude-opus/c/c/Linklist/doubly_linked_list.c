typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@

predicate node_pred(node n;) =
  n != 0 &*&
  n->item |-> _ &*&
  n->next |-> ?next &*&
  n->prev |-> ?prev &*&
  (next != 0 ==> node_pred(next)) &*&
  (prev == 0); // we enforce prev==0 at list start for simplicity

predicate dllist_pred(dllist l;) =
  l != 0 &*&
  l->head |-> ?head &*&
  l->tail |-> ?tail &*&
  ((head == 0 &*& tail == 0) || (head != 0 &*& tail != 0)) &*&
  (head == 0 || node_pred(head)) &*&
  (tail == 0 || node_pred(tail));

@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@

predicate dllist_inv(dllist l, node curr, node oldhead, node oldtail;) =
  curr |-> ?curr_val &*&
  (curr == 0 || (curr->next |-> ?next &*& curr->prev |-> ?prev &*& dllist_inv(l, next, oldhead, oldtail))) &*&
  curr != 0 ==> // node fields flipped
     (next == curr_val->prev &*& prev == curr_val->next);

@*/

void reverse(dllist arg)
	//@ requires dllist_pred(arg);
	//@ ensures dllist_pred(arg);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ open dllist_pred(arg);
	//@ open node_pred(ptr);
	//@ close dllist_inv(arg, ptr, arg->head, arg->tail);

	while (ptr != 0)
		//@ invariant ptr != 0 || true;
		//@ invariant true;
		//@ invariant dllist_pred(arg);
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
	
	//@ close dllist_pred(arg);
}