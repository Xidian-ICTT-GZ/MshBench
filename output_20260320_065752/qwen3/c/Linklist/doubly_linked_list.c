/*@ predicate node(node n; int item, node next, node prev) =
    n != 0 &*&
    n->item |-> item &*&
    n->next |-> next &*&
    n->prev |-> prev;
@*/

/*@ predicate dllist(dllist l; node head, node tail) =
    l != 0 &*&
    l->head |-> head &*&
    l->tail |-> tail;
@*/

/*@ predicate nodes(node n; list<pair<int, pair<node, node>>> xs) =
    n == 0 ?
        xs == nil
    :
        xs == cons(pair(?item, pair(?next, ?prev)), ?xs0) &*&
        node(n, item, next, prev) &*&
        nodes(next, xs0);
@*/

void reverse(dllist arg)
//@ requires dllist(arg, ?head, ?tail) &*& nodes(head, ?xs);
//@ ensures dllist(arg, tail, head) &*& nodes(tail, reverse(xs));
{
//@ open dllist(arg, head, tail);
//@ open nodes(head, xs);
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
//@ if (ptr != 0) { assert xs == cons(?x, ?xs0); }
	while (ptr != 0)
//@ invariant dllist(arg, _, _) &*& nodes(ptr, ?curr_xs) &*& nodes(temp1, ?rest_xs) &*& append(curr_xs, rest_xs) == xs;
	{
//@ open nodes(ptr, curr_xs);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
//@ close nodes(ptr, cons(pair(ptr->item, pair(temp1, temp2)), nil));
//@ assert nodes(ptr, ?new_curr);
//@ assert append(new_curr, rest_xs) == ?new_xs;
		ptr = temp1;
//@ if (ptr != 0) { open nodes(ptr, ?next_xs); close nodes(ptr, next_xs); }
	}
//@ open nodes(temp1, _);
//@ assert xs == nil ? true : true;
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
//@ close dllist(arg, tail, head);
}