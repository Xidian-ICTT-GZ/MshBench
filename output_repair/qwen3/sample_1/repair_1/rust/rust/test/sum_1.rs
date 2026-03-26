predicate Nodes(*mut Node nodes, list<i32> values) =
    match values {
        [] => nodes == std::ptr::null_mut(),
        [head] + tail => 
            alloc_block(nodes, std::mem::size_of::<Node>()) &
            (*nodes).value |-> head &
            (*nodes).next |-> ?next &
            Nodes(next, tail)
    };

predicate Stack(*mut Stack stack, list<i32> values) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &
    (*stack).head |-> ?head &
    Nodes(head, values);

#[requires(Nodes(nodes, ?values))]
#[ensures(Nodes(nodes, values) &*& result == sum(values))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[requires(Stack(stack, ?values))]
    #[ensures(Stack(stack, values) &*& result == sum(values))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}