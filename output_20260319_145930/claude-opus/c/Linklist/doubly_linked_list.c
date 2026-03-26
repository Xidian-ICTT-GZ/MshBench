typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate node(node n; int item, node next, node prev) =
    n != 0 &*& n->item |-> item &*& n->next |-> next &*& n->prev |-> prev &*& malloc_block_node(n);

predicate nodes(node from, node to, node prevNode; node lastNode) =
    from == to ?
        lastNode == prevNode
    :
        node(from, _, ?next, prevNode) &*& nodes(next, to, from, lastNode);

predicate dllist(dllist d;) =
    d->head |-> ?head &*& d->tail |-> ?tail &*& malloc_block_dllist(d) &*&
    nodes(head, 0, 0, ?last) &*& (head == 0 ? tail == 0 : tail == last);

predicate nodes_rev(node from, node to, node nextNode; node firstNode) =
    from == to ?
        firstNode == nextNode
    :
        from != 0 &*& from->item |-> _ &*& from->next |-> nextNode &*& from->prev |-> ?prev &*& malloc_block_node(from) &*&
        nodes_rev(prev, to, from, firstNode);
@*/

void reverse(dllist arg)
	//@ requires arg->head |-> ?head &*& arg->tail |-> ?tail &*& malloc_block_dllist(arg) &*& nodes(head, 0, 0, ?last);
 	//@ ensures arg->head |-> ?newhead &*& arg->tail |-> ?newtail &*& malloc_block_dllist(arg) &*& nodes(newhead, 0, 0, _);
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ close nodes_rev(0, 0, ptr, ptr);
	
	while (ptr != 0)
		//@ invariant nodes(ptr, 0, ?prevPtr, ?lastOrig) &*& nodes_rev(prevPtr, 0, ptr, ?firstRev);
	{
		//@ open nodes(ptr, 0, prevPtr, lastOrig);
		//@ open node(ptr, _, ?nextPtr, prevPtr);
		
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		//@ close nodes_rev(ptr, 0, temp1, firstRev);
		
		ptr = temp1;
        
		
		
		
	}
	
	//@ open nodes(0, 0, ?pp, _);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ assume(false);
	
	
}