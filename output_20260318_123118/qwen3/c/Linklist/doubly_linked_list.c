/*@ predicate nodes(node n; node prev, node next) =
    n == 0 ?
        true
    :
        malloc_block_node(n) &*&
        nodes(n->next, n, next) &*&
        n->prev == prev;
@*/

/*@ predicate dllist(dllist l; node head, node tail) =
    malloc_block_dllist(l) &*&
    l->head == head &*&
    l->tail == tail &*&
    nodes(head, 0, tail) &*&
    (head == 0 ? tail == 0 : true);
@*/

/*@ lemma void nodes_reverse(node n, node prev, node next)
    requires nodes(n, prev, next);
    ensures nodes(n, next, prev);
{
    if (n != 0) {
        assert malloc_block_node(n);
        nodes_reverse(n->next, n, next);
    }
}
@*/

void reverse(dllist arg)
//@ requires dllist(arg, ?head, ?tail);
//@ ensures dllist(arg, tail, head);
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;

    //@ invariant ptr == ?p &*& nodes(p, 0, ?r) &*& dllist(arg, head, tail) &*& arg->head == head &*& arg->tail == tail;
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