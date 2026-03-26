#[derive(Copy, Clone)]
struct Node {
    next: *mut Node,
}

#[derive(Copy, Clone)]
struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(n: *mut Node, len: usize) -> bool {
    if len == 0 {
        n.is_null()
    } else {
        !n.is_null() && exists(|next: *mut Node| {
            (*n).next == next && node_list(next, len - 1)
        })
    }
}

#[predicate]
fn stack_owns(s: *mut Stack, len: usize) -> bool {
    !s.is_null() && exists(|head: *mut Node| {
        (*s).head == head && node_list(head, len)
    })
}

impl Stack {
    #[requires(stack_owns(stack, stack_len) * stack_owns(other, other_len))]
    #[ensures(stack_owns(stack, stack_len + other_len))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(node_list(n, remaining) * node_list((*stack).head, stack_len))]
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
    }
}