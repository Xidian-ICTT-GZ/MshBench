unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}


predicate Nodes(*mut Node nodes, list<i32> values) =
    match values {
        [] => nodes == std::ptr::null_mut(),
        cons(head, tail) =>
            std::alloc::alloc_block(nodes, std::mem::size_of::<Node>()) &*&
            struct_Node_padding(nodes) &*&
            Node_value(nodes, head) &*&
            Node_next(nodes, ?next) &*&
            Nodes(next, tail)
    };

predicate Stack(*mut Stack stack, list<i32> values) =
    std::alloc::alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    Stack_head(stack, ?head) &*&
    Nodes(head, values);

#[requires(Nodes(nodes, ?values))]
#[ensures(Nodes(nodes, values) &*& result == sum(values))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        open Nodes(nodes, values);
        assert std::alloc::alloc_block(nodes, _);
        assert struct_Node_padding(nodes);
        let next = (*nodes).next;
        let value = (*nodes).value;
        close Nodes(nodes, values);
        result = get_nodes_sum(next);
        result += value;
    }

    result
}

impl Stack {
    #[requires(Stack(stack, ?values))]
    #[ensures(Stack(stack, values) &*& result == sum(values))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        open Stack(stack, values);
        assert std::alloc::alloc_block(stack, _);
        assert struct_Stack_padding(stack);
        let head = (*stack).head;
        close Stack(stack, values);
        let result = get_nodes_sum(head);

        result
    }
}