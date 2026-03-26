/*@ pred Node(node: *mut Node; next: *mut Node, value: i32) = 
    node != 0 &*& 
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@ pred Nodes(nodes: *mut Node; values: list<i32>) =
    match values {
        nil => nodes == 0,
        cons(h, t) => 
            exists(?next) &*& 
            Node(nodes, next, h) &*& 
            Nodes(next, t)
    };
@*/

/*@ pred Stack(stack: *mut Stack; values: list<i32>) =
    stack != 0 &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, values);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes, ?vs);
//@ ens Nodes(nodes, vs) &*& result == sum(vs);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Nodes(nodes, vs);
        //@ let h = head(vs); let t = tail(vs);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Nodes(nodes, vs);
    }
    //@ if (nodes == 0) { assert(vs == nil); } else { assert(vs == cons(?h, ?t)); }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?vs);
    //@ ens Stack(stack, vs) &*& result == sum(vs);
    {
        //@ open Stack(stack, vs);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, vs);

        result
    }
}