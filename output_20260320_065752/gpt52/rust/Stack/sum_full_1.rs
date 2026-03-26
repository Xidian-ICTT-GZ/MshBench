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
        alloc_block_Node(node) &*&
        (*node).value |-> ?v &*&
        (*node).next |-> ?n &*&
        nodes(n);

pred stack(stack: *mut Stack) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?h &*&
    nodes(h);

@*/

//@ req nodes(node);
//@ ens nodes(node) &*& result == 0 ? true : true;
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