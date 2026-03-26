struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(node: *mut Node) =
    node == 0 ?
        true
    :
        (*node).value |-> ?v &*& (*node).next |-> ?n &*& nodes(n);

pred stackp(stack: *mut Stack) =
    (*stack).head |-> ?h &*& nodes(h);

@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node);
//@ ens nodes(node);
{
    //@ open nodes(node);
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node);
    } else {
        //@ close nodes(node);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stackp(stack);
    //@ ens stackp(stack);
    {
        //@ open stackp(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stackp(stack);

        result
    }
}