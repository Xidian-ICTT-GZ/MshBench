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
    n->item |-> item &*& n->next |-> next &*& n->prev |-> prev &*& malloc_block_node(n);

predicate nodes(node from, node to, node prevNode; node lastNode) =
    from == to ?
        lastNode == prevNode
    :
        node(from, _, ?next, prevNode) &*& nodes(next, to, from, lastNode);

predicate dllist(dllist d; node head, node tail) =
    d->head |-> head &*& d->tail |-> tail &*& malloc_block_dllist(d) &*&
    nodes(head, 0, 0, ?last) &*& (head == 0 ? tail == 0 : tail == last);
@*/

/*@
predicate nodes_rev(node from, node to, node nextNode; node firstNode) =
    from == to ?
        firstNode == nextNode
    :
        node(from, _, nextNode, ?prev) &*& nodes_rev(prev, to, from, firstNode);

lemma void nodes_to_nodes_rev(node from, node to, node prevNode)
    requires nodes(from, to, prevNode, ?lastNode);
    ensures nodes_rev(lastNode, prevNode, to, from);
{
    open nodes(from, to, prevNode, lastNode);
    if (from == to) {
        close nodes_rev(prevNode, prevNode, to, from);
    } else {
        assert node(from, _, ?next, prevNode);
        nodes_to_nodes_rev(next, to, from);
        assert nodes_rev(lastNode, from, to, next);
        close nodes_rev(lastNode, prevNode, to, from);
    }
}

lemma void nodes_rev_to_nodes(node from, node to, node nextNode)
    requires nodes_rev(from, to, nextNode, ?firstNode);
    ensures nodes(firstNode, nextNode, to, from);
{
    open nodes_rev(from, to, nextNode, firstNode);
    if (from == to) {
        close nodes(nextNode, nextNode, to, from);
    } else {
        assert node(from, _, nextNode, ?prev);
        nodes_rev_to_nodes(prev, to, from);
        assert nodes(firstNode, from, to, prev);
        close nodes(firstNode, nextNode, to, from);
    }
}
@*/

void reverse(dllist arg)
    //@ requires dllist(arg, ?h, ?t);
    //@ ensures dllist(arg, t, h);
{
    //@ open dllist(arg, h, t);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    
    //@ nodes_to_nodes_rev(h, 0, 0);
    //@ close nodes(0, 0, h, ?dummy);
    
    while (ptr != 0)
        //@ invariant nodes_rev(ptr, 0, temp1, h) &*& nodes(temp1, 0, ptr, t) &*& (ptr == 0 ? temp1 == t : true);
    {
        //@ open nodes_rev(ptr, 0, temp1, h);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
        //@ close nodes(ptr, 0, temp1, t);
        
        ptr = temp1;
    }
    
    //@ open nodes_rev(0, 0, temp1, h);
    //@ nodes_rev_to_nodes(t, 0, 0);
    
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    
    //@ close dllist(arg, t, h);
}