struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list: *mut Node) =
    list == 0 ?
        true
    :
        (*list).value |-> ?v &*& (*list).next |-> ?n &*& alloc_block_Node(list) &*& nodes(n);

pred stack(stack: *mut Stack) =
    (*stack).head |-> ?h &*& alloc_block_Stack(stack) &*& nodes(h);

@*/

//@ req nodes(node);
//@ ens nodes(node);
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    //@ open nodes(node);
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes((*node).next);
        //@ close nodes(node);
    } else {
        //@ close nodes(node);
    }

    result
}

impl Stack {
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);

        result
    }
}