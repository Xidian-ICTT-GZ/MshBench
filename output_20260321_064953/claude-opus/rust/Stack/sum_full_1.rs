/*@

pred Node(node: *mut Node; value: i32, next: *mut Node) =
    (*node).value |-> value &*& (*node).next |-> next;

pred Nodes(node: *mut Node; sum: i32) =
    if node == 0 {
        sum == 0
    } else {
        Node(node, ?value, ?next) &*& Nodes(next, ?tail_sum) &*& sum == value + tail_sum
    };

pred Stack(stack: *mut Stack; head: *mut Node) =
    (*stack).head |-> head;

@*/

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req Nodes(node, ?sum);
//@ ens Nodes(node, sum) &*& result == sum;
{
    //@ open Nodes(node, sum);
    let mut result = 0;
    if !node.is_null() {
        //@ open Node(node, ?value, ?next);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close Node(node, value, next);
    }
    //@ close Nodes(node, sum);
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?head) &*& Nodes(head, ?sum);
    //@ ens Stack(stack, head) &*& Nodes(head, sum) &*& result == sum;
    {
        //@ open Stack(stack, head);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, head);
        result
    }
}