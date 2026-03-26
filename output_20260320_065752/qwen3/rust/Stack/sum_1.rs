/*@ pred Node(node: *mut Node; value: i32, next: *mut Node) = 
    node != 0 &*& 
    struct_Node_padding(node) &*&
    struct_Node_value(node, value) &*&
    struct_Node_next(node, next);
@*/

/*@ pred Nodes(nodes: *mut Node; values: list<i32>) =
    match values {
        nil => nodes == 0,
        cons(h, t) => Node(nodes, h, ?next) &*& Nodes(next, t)
    };
@*/

/*@ pred Stack(stack: *mut Stack; values: list<i32>) =
    stack != 0 &*&
    struct_Stack_padding(stack) &*&
    struct_Stack_head(stack, ?head) &*&
    Nodes(head, values);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes, ?vs);
//@ ens Nodes(nodes, vs) &*& result == sum(vs);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Nodes(nodes, _);
        //@ let v = _;
        //@ let next = _;
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Nodes(nodes, cons(v, _));
    }

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