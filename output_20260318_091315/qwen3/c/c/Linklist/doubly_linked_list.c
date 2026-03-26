/*@ predicate node(node n; int v, node p, node nx) =
    n != 0 &*&
    struct_node_item(n, v) &*&
    struct_node_prev(n, p) &*&
    struct_node_next(n, nx);
@*/

/*@ predicate dllist(dllist l; node h, node t) =
    l != 0 &*&
    struct_dllist_head(l, h) &*&
    struct_dllist_tail(l, t);
@*/

/*@ predicate nodes_inv(node n, node prev, node next) =
    n == 0 ?
        emp
    :
        node(n, ?v, prev, ?nx) &*& nodes_inv(nx, n, ?nnx);
@*/

/*@ lemma void nodes_inv_symmetry(node n)
    requires nodes_inv(n, ?prev, ?next)
    ensures nodes_inv(n, prev, next);
@*/

void reverse(dllist arg)
//@ requires dllist(arg, ?h, ?t) &*& nodes_inv(h, 0, t);
//@ ensures dllist(arg, t, h) &*& nodes_inv(t, 0, h);
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    
    //@ invariant dllist(arg, ?orig_h, ?orig_t) &*&
    
    
    
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