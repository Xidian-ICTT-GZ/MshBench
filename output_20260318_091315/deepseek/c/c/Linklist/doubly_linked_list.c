/*@
predicate node(node n; int v, node nxt, node prv) =
    n->item |-> v &*& n->next |-> nxt &*& n->prev |-> prv &*& malloc_block_node(n);
@*/

/*@
predicate dllseg(node fr, node to; node prv, list<int> items) =
    fr == to ?
        items == nil &*& emp
    :
        node(fr, ?v, ?nxt, prv) &*& dllseg(nxt, to, fr, ?items0) &*& items == cons(v, items0);
@*/

/*@
predicate dllist(dllist d; list<int> items) =
    d->head |-> ?h &*& d->tail |-> ?t &*& malloc_block_dllist(d) &*&
    dllseg(h, 0, 0, items) &*& node(t, ?lastv, 0, ?prev) &*&
    dllseg(h, t, 0, ?init) &*& lastv == nth(length(init) - 1, items);
@*/

void reverse(dllist arg)
//@ requires dllist(arg, ?items);
//@ ensures dllist(arg, reverse(items));
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    //@ close dllseg(ptr, 0, 0, items);
    //@ open dllseg(ptr, 0, 0, items);
    while (ptr != 0)
    //@ invariant dllseg(ptr, 0, ?prv, ?cur) &*& dllseg(arg->head, ptr, 0, ?rev) &*& reverse(rev) == prv;
    {
        //@ open dllseg(ptr, 0, prv, cur);
        //@ node ptrn = open node(ptr, _, _, _);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
        //@ close node(ptr, _, temp2, temp1);
        //@ close dllseg(ptr, ptr, temp1, cons(_, nil));
        //@ assert dllseg(arg->head, ?oldptr, 0, rev);
        //@ close dllseg(arg->head, oldptr, 0, rev);
        //@ open dllseg(arg->head, oldptr, 0, rev);
        //@ close dllseg(arg->head, ptr, 0, cons(_, rev));
        ptr = temp1;
        //@ prv = ptr;
        //@ rev = cons(_, rev);
    }
    //@ open dllseg(0, 0, _, _);
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    //@ close dllist(arg, reverse(items));
}