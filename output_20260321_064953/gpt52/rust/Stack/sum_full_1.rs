struct Node {
    value: i32,
    next: *mut Node,
}

/*@

pred nodes(list: *mut Node) =
    list == std::ptr::null_mut() ?
        true
    :
        (*list).value |-> ?v &*&
        (*list).next |-> ?n &*&
        nodes(n);

pred stack(s: *mut Stack) =
    (*s).head |-> ?h &*& nodes(h);

@*/

struct Stack {
    head: *mut Node,
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node);
//@ ens nodes(node);
{
    //@ open nodes(node);
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes((*node).next);
        let tail_sum = get_nodes_sum((*node).next);
        //@ close nodes((*node).next);
        result = (*node).value + tail_sum;
    }
    //@ close nodes(node);
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }
}