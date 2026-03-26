/*@
pred_ctor Node(node: *mut Node; value: i32, next: *mut Node)() {
    alloc_block(node, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).value |-> value &*&
    (*node).next |-> next;
}

pred nodes(node: *mut Node) =
    node.is_null() ?
        true
    :
        Node(node, ?value, ?next) &*& nodes(next);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node);
//@ ens nodes(node);
{
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node);
    }
    //@ else { open nodes(node); close nodes(node); }
    result
}

/*@
pred Stack(stack: *mut Stack; head: *mut Node)() {
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
}
@*/

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?head) &*& nodes(head);
    //@ ens Stack(stack, head) &*& nodes(head);
    {
        //@ open Stack(stack, ?head);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, head);
        result
    }
}