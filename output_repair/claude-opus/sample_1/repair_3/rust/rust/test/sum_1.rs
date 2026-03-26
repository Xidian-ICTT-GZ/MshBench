struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        (*n).value |-> ?v &*& (*n).next |-> ?nxt &*& struct_Node_padding(n) &*& Nodes(nxt)
    };

pred Stack_own(s: *mut Stack;) =
    (*s).head |-> ?h &*& struct_Stack_padding(s) &*& Nodes(h);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes);
//@ ens Nodes(nodes);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Nodes(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Nodes(nodes);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack_own(stack);
    //@ ens Stack_own(stack);
    {
        //@ open Stack_own(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack_own(stack);

        result
    }
}