/*@ pred Node(node: *mut Node, value: i32, next: *mut Node) = 
    alloc_block_node(node) &*& 
    struct_Node_padding(node) &*& 
    (*node).value |-> value &*& 
    (*node).next |-> next;
@*/

/*@ pred Nodes(node: *mut Node, values: list<i32>) =
    match values {
        nil => node == 0 as *mut Node,
        cons(v, vs) => 
            Node(node, v, ?next) &*& Nodes(next, vs)
    };
@*/

/*@ pred Stack(stack: *mut Stack, values: list<i32>) =
    alloc_block_stack(stack) &*& 
    struct_Stack_padding(stack) &*& 
    (*stack).head |-> ?head &*& 
    Nodes(head, values);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req Nodes(node, ?values);
//@ ens Nodes(node, values) &*& result == sum(values);
{
    let mut result = 0;
    //@ open Nodes(node, values);
    if !node.is_null() {
        //@ open Node(node, ?v, ?next);
        let tail_sum = get_nodes_sum((*node).next);
        //@ close Node(node, v, next);
        result = (*node).value + tail_sum;
    } else {
        //@ assert values == nil;
    }
    //@ close Nodes(node, values);
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?values);
    //@ ens Stack(stack, values) &*& result == sum(values);
    {
        //@ open Stack(stack, values);
        let head = (*stack).head;
        let result = get_nodes_sum(head);
        //@ close Stack(stack, values);
        result
    }
}