/*@ 
predicate node(struct Node* n) = n != 0 &*& n->next |-> ?next &*& malloc_block_Node(n);
predicate stack(struct Stack* s, struct Node* head) = s != 0 &*& s->head |-> head &*& malloc_block_Stack(s);
@*/

//@ req stack: stack(s, ?head);
//@ ensures stack(stack, head) &*& result == (count_nodes(head));
//@ terminates;
unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack(stack, ?head);
//@ ensures stack(stack, head) &*& result == (count_nodes(head));
{
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open stack(stack, head);
    //@ open_nodes(n);
    loop {
        //@ inv (stack(stack, head) &*& list_segment(n, null, i));
        if n.is_null() {
            break;
        }
        //@ open node(n);
        n = (*n).next;
        i += 1;
    }
    //@ close stack(stack, head);
    i
}

/*@

fixpoint int count_nodes(struct Node* n) {
    switch(n) {
        case 0: return 0;
        case _ : open node(n); int c = 1 + count_nodes(n->next); close node(n); return c;
    }
}

predicate list_segment(struct Node* from, struct Node* to, int count) =
    from == to ? count == 0 : node(from) &*& list_segment(from->next, to, count - 1);

fixpoint void open_nodes(struct Node* n) {
    switch(n) {
        case 0: return;
        default: open node(n); open_nodes(n->next); close node(n);
    }
}

@*/