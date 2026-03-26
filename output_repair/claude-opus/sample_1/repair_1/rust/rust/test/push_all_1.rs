struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(n: *mut Node) = 
    n.is_null() ? true : (
        exists<next: *mut Node> 
        (n as *mut u8) |-> Node { next } * node_list(next)
    );

#[predicate]
fn stack_owns(s: *mut Stack, head: *mut Node) =
    (s as *mut u8) |-> Stack { head } * node_list(head);

impl Stack {
    #[requires(stack_owns(stack, (*stack).head) * node_list(head0))]
    #[ensures(stack_owns(stack, head0))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(node_list(n) * stack_owns(stack, (*stack).head))]
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