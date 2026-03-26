/*@
predicate node(node n; int v, node nx, node pv) =
    n->item |-> v &*& n->next |-> nx &*& n->prev |-> pv &*& malloc_block_node(n);
@*/

/*@
predicate dllist(dllist d; node h, node t) =
    d->head |-> h &*& d->tail |-> t &*& malloc_block_dllist(d);
@*/

/*@
predicate dllseg(node f, node b, node l, node r) =
    f == l ?
        b == r
    :
        node(f, ?v, ?n, b) &*& dllseg(n, f, l, r);
@*/

/*@
lemma void dllseg_add_back(node f, node b, node l, node r)
requires dllseg(f, b, l, r) &*& node(r, ?v, ?n, l);
ensures dllseg(f, b, n, r) &*& node(r, v, n, l);
{
    open dllseg(f, b, l, r);
    if (f == l) {
        close dllseg(r, l, n, r);
    } else {
        dllseg_add_back(f->next, f, l, r);
        close dllseg(f, b, n, r);
    }
}
@*/

/*@
lemma void dllseg_append(node f1, node b1, node m, node f2, node b2, node l)
requires dllseg(f1, b1, m, f2) &*& dllseg(f2, b2, l, ?n);
ensures dllseg(f1, b1, l, n) &*& dllseg(f2, b2, l, n);
{
    open dllseg(f1, b1, m, f2);
    if (f1 == m) {
    } else {
        dllseg_append(f1->next, f1, m, f2, b2, l);
        close dllseg(f1, b1, l, n);
    }
}
@*/

void reverse(dllist arg)
//@ requires dllist(arg, ?h, ?t) &*& dllseg(h, 0, t, 0);
//@ ensures dllist(arg, t, h) &*& dllseg(t, 0, h, 0);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ node prev = 0;
	//@ close dllseg(ptr, prev, ptr, 0);
	while (ptr != 0)
		//@ invariant dllseg(ptr, prev, ?l, 0) &*& dllseg(arg->head, 0, prev, ptr);
	{
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		//@ open dllseg(ptr, prev, l, 0);
		//@ open node(ptr, ?v, temp1, temp2);
		//@ close node(ptr, v, temp2, temp1);
		//@ close dllseg(ptr, temp1, l, 0);
		
		ptr = temp1;
		//@ node old_prev = prev;
		prev = temp2;
		//@ close dllseg(ptr, prev, l, 0);
		//@ dllseg_add_back(arg->head, 0, old_prev, ptr);
	}
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ open dllseg(0, prev, ?l, 0);
	//@ dllseg_append(arg->head, 0, prev, 0, prev, l);
}