/*@
pred Node(node: *mut Node; value: i32, next: *mut Node) = 
    alloc_block(node, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).value |-> value &*&
    (*node).next |-> next;
@*/

/*@
pred Nodes(node: *mut Node) =
    node.is_null() ? true : Node(node, ?value, ?next) &*& Nodes(next);
@*/

/*@
pred Stack(stack: *mut Stack; head: *mut Node) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

//@ req Nodes(node);
//@ ens result == nodes_sum(node);
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    let mut result = 0;
    //@ open Nodes(node);
    if !node.is_null() {
        //@ open Node(node, _, _);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close Node(node, _, _);
    }
    //@ close Nodes(node);
    result
}

impl Stack {
    //@ req Stack(stack, ?head) &*& Nodes(head);
    //@ ens Stack(stack, head) &*& Nodes(head) &*& result == nodes_sum(head);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack, _);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, _);
        result
    }
}