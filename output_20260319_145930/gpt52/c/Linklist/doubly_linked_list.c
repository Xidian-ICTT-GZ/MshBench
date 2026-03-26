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

predicate nodeseg(node from, node to, node prev, node next) =
    from == to ?
        prev == next &*& true
    :
        from != 0 &*&
        from->item |-> ?it &*&
        from->next |-> ?n &*&
        from->prev |-> prev &*&
        nodeseg(n, to, from, next);

predicate dllist_inv(dllist l) =
    l != 0 &*&
    l->head |-> ?h &*&
    l->tail |-> ?t &*&
    (h == 0 ?
        t == 0
     :
        nodeseg(h, 0, 0, t) &*& t != 0 &*& t->next |-> 0);

@*/

void reverse(dllist arg)
    //@ requires dllist_inv(arg);
    //@ ensures dllist_inv(arg);
{
    //@ open dllist_inv(arg);
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;

    //@ close nodeseg(ptr, ptr, 0, ?t0);
    //@ assert ptr == 0 ? t0 == 0 : true;
    while (ptr != 0)
        //@ invariant nodeseg(?h0, ptr, 0, ?t1) &*& (ptr == 0 ? t1 == (h0 == 0 ? 0 : t1) : true) &*& (ptr == 0 ? true : ptr->item |-> ?it &*& ptr->next |-> ?n &*& ptr->prev |-> ?p) ;
    {
        //@ open nodeseg(h0, ptr, 0, t1);
        //@ assert ptr->item |-> it &*& ptr->next |-> n &*& ptr->prev |-> p;

        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;

        ptr = temp1;
        //@ close nodeseg(h0, ptr, 0, t1);
    }

    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;

    //@ close dllist_inv(arg);
}