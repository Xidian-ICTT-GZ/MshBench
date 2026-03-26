/*@
predicate node(node n; int v, node nxt, node prv) =
    n->item |-> v &*& n->next |-> nxt &*& n->prev |-> prv &*& malloc_block_node(n);
@*/

/*@
predicate dllist(dllist d; node h, node t) =
    d->head |-> h &*& d->tail |-> t &*& malloc_block_dllist(d);
@*/

/*@
predicate dllseg(node h, node t, node h0, node t0; int count) =
    h == t ?
        count == 0 &*& h0 == h &*& t0 == t
    :
        node(h, ?v, ?n, ?p) &*&
        (h == h0 ? p == 0 : true) &*&
        (t == t0 ? n == 0 : true) &*&
        dllseg(n, t, h0, t0, ?cnt) &*& count == cnt + 1;
@*/

/*@
predicate dll(dllist d) =
    dllist(d, ?h, ?t) &*& dllseg(h, 0, h, t, ?c) &*& dllseg(t, 0, h, t, ?c2) &*& c == c2;
@*/

void reverse(dllist arg)
    //@ requires dll(arg);
    //@ ensures dll(arg);
{
    //@ open dll(arg);
    //@ open dllist(arg, ?h, ?t);
    //@ open dllseg(h, 0, h, t, _);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    //@ close dllseg(ptr, 0, h, t, _);
    //@ close dllseg(0, 0, h, t, 0);
    
    while (ptr != 0)
        //@ invariant dllseg(ptr, 0, h, t, ?cnt1) &*& dllseg(0, 0, h, t, ?cnt2) &*& cnt1 + cnt2 == _;
    {
        //@ open dllseg(ptr, 0, h, t, cnt1);
        //@ open node(ptr, ?v, ?nxt, ?prv);
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
        //@ close node(ptr, v, temp2, temp1);
        //@ close dllseg(temp1, 0, h, t, cnt1 - 1);
        ptr = temp1;
        //@ assert dllseg(ptr, 0, h, t, cnt1 - 1);
    }
    //@ open dllseg(0, 0, h, t, _);
    
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
    //@ close dllist(arg, temp2, temp1);
    //@ close dll(arg);
}