struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes_list(nodes: *mut Node) =
    nodes == std::ptr::null_mut() ?
        true
    :
        alloc_block(nodes as *u8, std::mem::size_of::<Node>()) &*&
        (*nodes).value |-> ?v &*&
        (*nodes).next |-> ?n &*&
        nodes_list(n);

pred stack(stack: *mut Stack) =
    alloc_block(stack as *u8, std::mem::size_of::<Stack>()) &*&
    (*stack).head |-> ?h &*&
    nodes_list(h);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes_list(nodes);
//@ ens nodes_list(nodes);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open nodes_list(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes_list(nodes);
    }

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