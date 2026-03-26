struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(n: *mut Node, len: usize) -> bool {
    if n.is_null() {
        len == 0
    } else {
        len > 0 && exists(tail: *mut Node, node_list(tail, len - 1) && (*n).next == tail)
    }
}

#[predicate]
fn stack_owns(s: *mut Stack, len: usize) -> bool {
    exists(h: *mut Node, (*s).head == h && node_list(h, len))
}

impl Stack {
    #[requires(stack_owns(stack, stack_len) && stack_owns(other, other_len))]
    #[ensures(stack_owns(stack, stack_len + other_len))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            loop {
                #[invariant(node_list(n, remaining) && remaining > 0)]
                {
                    if (*n).next.is_null() {
                        break;
                    }
                    n = (*n).next;
                }
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
    }
}