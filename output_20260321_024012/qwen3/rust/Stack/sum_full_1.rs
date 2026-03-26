//@ pred Node(node: *mut Node; value: i32, next: *mut Node) = (*node).value |-> value &*& (*node).next |-> next;
//@ pred Stack(stack: *mut Stack; head: *mut Node) = (*stack).head |-> head;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req true;
//@ ens true;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open Node(node, ?v, ?n);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close Node(node, v, n);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?head);
    //@ ens Stack(stack, head);
    {
        //@ open Stack(stack, _);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, _);
        result
    }
}