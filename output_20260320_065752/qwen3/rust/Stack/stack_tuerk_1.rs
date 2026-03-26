/*@ pred Stack(node: *mut Stack, head: *mut Node); @*/
/*@ pred Node(node: *mut Node, next: *mut Node); @*/

//@ req [?f]Stack(stack, ?head);
//@ ens [f]Stack(stack, head) &*& result == length(head);
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close Node(n, _); // dummy close to satisfy syntax if needed; actual invariant below
    //@ inv [f]Stack(stack, ?s_head) &*& n |-> ?n_next &*& i |-> ?i_val &*& i_val == length_up_to(s_head, n);
    loop {
        if n.is_null() {
            break;
        }
        //@ open Node(n, _);
        n = (*n).next;
        i += 1;
        //@ close Node(n, _);
    }
    i
}

/*@ fixpoint i32 length(*mut Node n); @*/
/*@ fixpoint i32 length_up_to(*mut Node start, *mut Node current); @*/