struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes_list(node: *mut Node; int sum) =
    node == 0 ?
        sum == 0
    :
        (*node).value |-> ?v &*&
        (*node).next |-> ?n &*&
        nodes_list(n; ?s) &*&
        sum == v + s;

predicate stack(s: *mut Stack; int sum) =
    (*s).head |-> ?h &*&
    nodes_list(h; sum);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes_list(nodes; ?sum);
//@ ensures nodes_list(nodes; sum) &*& result == sum;
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
    //@ requires stack(stack; ?sum);
    //@ ensures stack(stack; sum) &*& result == sum;
    {
        //@ open stack(stack; sum);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack; sum);

        result
    }
}