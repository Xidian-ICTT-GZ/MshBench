use std::ptr;

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node; sum: i32) =if n == 0 {
        sum == 0
    } else {
        (*n).value |-> ?v &*& (*n).next |-> ?next &*& Nodes(next, ?rest) &*& sum == v + rest
    };

pred Stack(s: *mut Stack; sum: i32) =
    (*s).head |-> ?head &*& Nodes(head, sum);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes, ?sum);
//@ ens Nodes(nodes, sum) &*& result == sum;
{
    let mut result = 0;
    //@ open Nodes(nodes, sum);
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    //@ close Nodes(nodes, sum);
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