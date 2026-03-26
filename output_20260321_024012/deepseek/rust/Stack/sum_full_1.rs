// verifast_options{}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req node == 0 ? true : struct_Node_pat(node) &*& (*node).next |-> ?next &*& (*node).value |-> ?value;
//@ ens node == 0 ? true : struct_Node_pat(node) &*& (*node).next |-> next &*& (*node).value |-> value;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open struct_Node_pat(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close struct_Node_pat(node);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req struct_Stack_pat(stack) &*& (*stack).head |-> ?head;
    //@ ens struct_Stack_pat(stack) &*& (*stack).head |-> head;
    {
        //@ open struct_Stack_pat(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close struct_Stack_pat(stack);
        result
    }
}