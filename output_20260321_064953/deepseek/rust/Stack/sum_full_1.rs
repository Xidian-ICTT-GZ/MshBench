// verifast_options{}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req node == 0 ? true : struct_Node_padding(node) &*& (*node).value |-> ?v &*& (*node).next |-> ?next;
//@ ens node == 0 ? true : struct_Node_padding(node) &*& (*node).value |-> v &*& (*node).next |-> next;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open_struct_Node(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close_struct_Node(node);
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