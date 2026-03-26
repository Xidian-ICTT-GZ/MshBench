#[predicate]
fn stack_node(node: *mut StackNode) -> bool;

#[predicate]
fn stack(stack: *mut Stack, head: *mut StackNode) -> bool;

unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[requires(stack(stack, ?head) && stack_nodes(head, _))]
    #[ensures(stack(stack, head) && stack_nodes(head, _) && result == stack_length(head))]
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(stack(stack, ?s_head) && stack_nodes(n, ?tail) && stack_nodes(tail, _) && i + stack_length(tail) == stack_length(s_head))]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}

#[predicate]
fn stack_nodes(node: *mut StackNode, tail: *mut StackNode) -> bool {
    match node.is_null() {
        true => {
            predicate_stack_nodes_true(tail)
        },
        false => {
            stack_node(node) && (*node).next |-> ?next &*& stack_nodes(next, tail)
        }
    }
}

#[predicate]
fn predicate_stack_nodes_true(tail: *mut StackNode) -> bool {
    tail.is_null() == true
}

#[pure]
fn stack_length(node: *mut StackNode) -> i32 {
    match node.is_null() {
        true => 0,
        false => 1 + stack_length((*node).next)
    }
}