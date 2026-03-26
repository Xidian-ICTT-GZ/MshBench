/*@ predicate nodep(node n; int item, node next, node prev) =
    n != 0 &*&
    n->item |-> item &*&
    n->next |-> next &*&
    n->prev |-> prev;
@*/

/*@ predicate nodes(node n; list<int> items, node next, node prev) =
    items == nil ?
        n == 0
    :
        n != 0 &*&
        nodep(n, head(items), ?n1, ?p1) &*&
        nodes(n1, tail(items), next, n) &*&
        p1 == prev;
@*/

/*@ predicate dllistp(dllist l; list<int> items) =
    l != 0 &*&
    l->head |-> ?h &*&
    l->tail |-> ?t &*&
    (items == nil ?
        h == 0 &*& t == 0
    :
        nodes(h, items, 0, 0) &*&
        t != 0 &*&
        nodep(t, last(items), 0, ?tprev) &*&
        (items == cons(_, nil) ? t == h : true)
    );
@*/

void reverse(dllist arg)
//@ requires dllistp(arg, ?items);
//@ ensures dllistp(arg, reverse(items));
{
//@ open dllistp(arg, items);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;

//@ if (items != nil) open nodes(ptr, items, 0, 0);
    while (ptr != 0)
    //@ invariant ptr != 0 ? nodes(ptr, ?rest, ?orig_next, ?orig_prev) &*& dllistp(arg, ?before_items) &*& append(before_items, rest) == items : dllistp(arg, items);
    {
    //@ open nodes(ptr, _, _, _);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
    //@ close nodes(ptr, cons(ptr->item, nil), temp2, temp1);
        ptr = temp1;
    }

    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
//@ close dllistp(arg, reverse(items));
}