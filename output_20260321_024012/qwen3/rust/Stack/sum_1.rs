//@ pred Node(node: *mut Node; next: *mut Node, value: i32) = (*node).next |-> next &*& (*node).value |-> value;
//@ pred Stack(stack: *mut Stack; head: *mut Node) = (*stack).head |-> head;

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == null ? true : Node(nodes, ?next, ?value);
//@ ens true;
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Node(nodes, _, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?head);
    //@ ens true;
    {
        //@ open Stack(stack, _);
        let result = get_nodes_sum((*stack).head);
        result
    }
}