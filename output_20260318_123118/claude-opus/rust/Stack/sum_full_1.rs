struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(node: *mut Node; sum: i32) =
    if node == 0 {
        sum == 0
    } else {
        (*node).value |-> ?v &*&
        (*node).next |-> ?next &*&
        Nodes(next, ?tail_sum) &*&
        sum == v + tail_sum
    };

pred Stack(stack: *mut Stack; sum: i32) =
    (*stack).head |-> ?head &*&
    Nodes(head, sum);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req Nodes(node, ?sum);
//@ ens Nodes(node, sum) &*& result == sum;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open Nodes(node, sum);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close Nodes(node, sum);
    } else {
        //@ open Nodes(node, sum);
        //@ close Nodes(node, sum);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?sum);
    //@ ens Stack(stack, sum) &*& result == sum;
    {
        //@ open Stack(stack, sum);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, sum);
        result
    }
}