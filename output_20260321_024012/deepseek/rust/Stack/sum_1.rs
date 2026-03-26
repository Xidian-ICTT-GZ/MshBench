unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes.is_null() ? true : struct_Node_padding(nodes) &*& Node_next(nodes, ?next) &*& Node_value(nodes, ?val);
//@ ens nodes.is_null() ? true : struct_Node_padding(nodes) &*& Node_next(nodes, next) &*& Node_value(nodes, val);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open_struct_Node(nodes);
        //@ open Node_next(nodes, _);
        //@ open Node_value(nodes, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Node_value(nodes, _);
        //@ close Node_next(nodes, _);
        //@ close_struct_Node(nodes);
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req struct_Stack_padding(stack) &*& Stack_head(stack, ?head);
    //@ ens struct_Stack_padding(stack) &*& Stack_head(stack, head);
    {

        //@ open_struct_Stack(stack);
        //@ open Stack_head(stack, _);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack_head(stack, _);
        //@ close_struct_Stack(stack);

        result
    }
}