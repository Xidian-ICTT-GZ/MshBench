/*@ pred Stack(node: *Stack, head: *Node) =
    node != 0 &*&
    struct_Stack_padding(node) &*&
    (*node).head |-> head;
@*/

/*@ pred Node(node: *Node, next: *Node) =
    node != 0 &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next;
@*/

impl Stack {
//@ req stack != 0 &*& Stack(stack, ?s_head) &*& other != 0 &*& Stack(other, ?o_head);
//@ ens Stack(stack, result_head) &*& result_head == if o_head == 0 { s_head } else { o_head };
unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
    //@ open Stack(other, _);
    let head0 = (*other).head;
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ assert Node(n, _);
        loop {
            //@ inv n != 0 &*& Node(n, ?n_next) &*& (n_next == 0 ? true : Node(n_next, _));
            if (*n).next.is_null() {
                break;
            }
            n = (*n).next;
            //@ open Node(n, _);
        }
        //@ open Node(n, _);
        (*n).next = (*stack).head;
        //@ close Node(n, (*stack).head);
        //@ open Stack(stack, _);
        (*stack).head = head0;
        //@ close Stack(stack, head0);
    } else {
        //@ open Stack(stack, _);
        //@ close Stack(stack, s_head);
    }
}
}