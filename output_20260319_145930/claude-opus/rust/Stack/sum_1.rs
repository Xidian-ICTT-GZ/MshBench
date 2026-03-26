/*@
pred Nodes(nodes: *mut Node, count: i32) =
    if nodes == 0 as *mut Node {
        count == 0
    } else {
        (*nodes).value |-> ?v &*&
        (*nodes).next |-> ?next &*&
        alloc_block_Node(nodes) &*&
        Nodes(next, ?rest_count) &*&
        count == rest_count + 1
    };

pred Stack(stack: *mut Stack, count: i32) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, count);
@*/

//@ req Nodes(nodes, ?count);
//@ ens Nodes(nodes, count);
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    //@ open Nodes(nodes, count);
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    //@ close Nodes(nodes, count);
    result
}

impl Stack {
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack, count);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, count);
        result
    }
}