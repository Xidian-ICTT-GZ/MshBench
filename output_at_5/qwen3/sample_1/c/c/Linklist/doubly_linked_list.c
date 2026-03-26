//@ predicate dllist(dllist l) = l != 0 && l->head != 0 && l->tail != 0 &*& node_list(l->head, l->tail, true) &*& node_list(l->tail, l->head, false);
//@ predicate node(node n, int item, node next, bool is_prev) = n != 0 &*& n->item == item &*& n->next == next &*& (is_prev ? n->prev == 0 : n->prev == 0); // Simplified ghost state for structure
//@ predicate node_list(node start, node end, bool forward) = start == end;
//@ predicate node_list(node start, node end, bool forward) = start != 0 &*& start != end &*& node(start, start->item, start->next, !forward) &*& node_list(start->next, end, forward);

/*@
requires arg != 0 &*& dllist(arg);
ensures arg != 0 &*& dllist(arg);
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