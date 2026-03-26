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
        (*node).value |-> ?v &*&
        (*node).next |-> ?n &*&
        nodes_list(n; ?s) &*&
        sum == v + s;

predicate stack(stack: *mut Stack; sum: i32) =
    (*stack).head |-> ?h &*& nodes_list(h; sum);

@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires nodes_list(node; ?sum);
//@ ensures nodes_list(node; sum) &*& result == sum;
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack; ?sum);
    //@ ensures stack(stack; sum) &*& result == sum;
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}