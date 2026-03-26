struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes_list(node: *mut Node; sum: i32) =
    node == 0 ?
        sum == 0
    :
        (*node).value |-> ?v &*& (*node).next |-> ?n &*& nodes_list(n; ?s) &*& sum == v + s;

predicate stack(stack: *mut Stack; sum: i32) =
    (*stack).head |-> ?h &*& nodes_list(h; sum);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes_list(nodes; ?s);
//@ ensures nodes_list(nodes; s) &*& result == s;
{
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack; ?s);
    //@ ensures stack(stack; s) &*& result == s;
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}