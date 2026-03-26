unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == 0 ? true : struct_Node_padding(nodes) &*& (*nodes).value |-> ?v &*& (*nodes).next |-> ?next;
//@ ens nodes == 0 ? true : struct_Node_padding(nodes) &*& (*nodes).value |-> v &*& (*nodes).next |-> next;
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open_struct_Node(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close_struct_Node(nodes);
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req struct_Stack_padding(stack) &*& (*stack).head |-> ?head;
    //@ ens struct_Stack_padding(stack) &*& (*stack).head |-> head;
    {

        //@ open_struct_Stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close_struct_Stack(stack);

        result
    }
}