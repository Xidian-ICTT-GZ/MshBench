use vstd::prelude::*;

verus! {

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_valid(n: *mut Node) -> bool {
    !n.is_null() && 
    alloc::allocated(n) && 
    exists |next| n->next == next && 
    exists |value| n->value == value
}

predicate nodes_list(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        node_valid(n) && 
        nodes_list((*n).next)
    }
}

predicate stack_valid(s: *mut Stack) -> bool {
    !s.is_null() && 
    alloc::allocated(s) && 
    exists |head| s->head == head && 
    nodes_list((*s).head)
}

#[requires(stack_valid(stack))]
#[ensures(stack_valid(stack))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 
    requires nodes_list(nodes)
    ensures nodes_list(nodes)
{
    let mut result = 0;

    if !nodes.is_null() {
        let next = (*nodes).next;
        result = get_nodes_sum(next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[requires(stack_valid(stack))]
    #[ensures(stack_valid(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = get_nodes_sum(head);
        result
    }
}

}