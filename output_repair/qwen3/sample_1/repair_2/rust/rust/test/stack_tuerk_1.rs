#![feature(stmt_expr_attributes)]

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[verifast::predicate]
fn stack_node(node: *mut Node) -> bool {
    node != std::ptr::null_mut() && std::ptr::raw_ptr_deref(node).next |-> ?next && stack_node(next)
}

#[verifast::predicate]
fn stack(stack_ptr: *mut Stack, head: *mut Node) -> bool {
    stack_ptr != std::ptr::null_mut() && std::ptr::raw_ptr_deref(stack_ptr).head |-> head
}

#[verifast::predicate]
fn stack_nodes(node: *mut Node) -> bool {
    if node == std::ptr::null_mut() {
        true
    } else {
        stack_node(node)
    }
}

#[verifast::pure]
fn count_nodes(node: *mut Node) -> i32 {
    if node == std::ptr::null_mut() {
        0
    } else {
        1 + count_nodes(unsafe { (*node).next })
    }
}

#[verifast::pure]
fn count_from_to(start: *mut Node, end: *mut Node) -> i32 {
    if start == end {
        0
    } else if start == std::ptr::null_mut() {
        0
    } else {
        1 + count_from_to(unsafe { (*start).next }, end)
    }
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[verifast::requires(stack(stack, ?head) && stack_nodes(head))]
    #[verifast::ensures(stack(stack, head) && stack_nodes(head) && result == count_nodes(head))]
    {
        let mut n = (*stack).head;
        let mut i = 0;
        #[verifast::invariant(stack(stack, ?s_head) && stack_nodes(n) && i == count_from_to(s_head, n))]
        loop {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }

        i
    }
}