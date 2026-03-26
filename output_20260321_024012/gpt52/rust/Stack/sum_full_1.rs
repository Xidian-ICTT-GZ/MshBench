unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req true;
//@ ens true;
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req true;
    //@ ens true;
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}