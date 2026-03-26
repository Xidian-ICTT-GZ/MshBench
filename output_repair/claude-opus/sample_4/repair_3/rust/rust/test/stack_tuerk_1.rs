#![feature(stmt_expr_attributes)]

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(n: *mut Node) -> bool {
    n.is_null() || (
        exists(|next: *mut Node| {
            points_to(n as *mut Node, Node { next: next }) &*& node_list(next)
        })
    )
}

#[predicate]
fn stack_valid(stack: *mut Stack) -> bool {
    exists(|head: *mut Node| {
        points_to(stack as *mut Stack, Stack { head: head }) &*& node_list(head)
    })
}

#[requires(stack_valid(stack))]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(i >= 0 &*& node_list(n))]
        {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
    }

    i
}