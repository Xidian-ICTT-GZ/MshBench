/*@ predicate node(struct node *n; int item, struct node *next, struct node *prev) =
    n != 0 &*&
    n->item |-> item &*&
    n->next |-> next &*&
    n->prev |-> prev;
@*/

/*@ predicate dllist(struct dllist *l; struct node *head, struct node *tail) =
    l != 0 &*&
    l->head |-> head &*&
    l->tail |-> tail;
@*/

/*@ predicate nodes(struct node *n) =
    n == 0 ?
        true
    :
        node(n, ?item, ?next, ?prev) &*& nodes(next);
@*/

void reverse(dllist arg)
//@ requires dllist(arg, ?head, ?tail) &*& nodes(head);
//@ ensures dllist(arg, tail, head) &*& nodes(tail);
{
    //@ open dllist(arg, head, tail);
    //@ open nodes(head);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;

    while (ptr != 0)
    //@ invariant dllist(arg, ?h, ?t) &*& nodes(ptr) &*& h == old_h &*& t == old_t;
    //@ invariant ptr == 0 ? emp : node(ptr, ?item, ?next, ?prev) &*& nodes(next);
    {
        //@ open node(ptr, _, _, _);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
        //@ close node(ptr, _, temp2, temp1);
        ptr = temp1;
    }

    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    //@ close dllist(arg, temp2, temp1);
}