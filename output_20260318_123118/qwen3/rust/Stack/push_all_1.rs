#[predicate]
fn stack_node(node: *mut Node) -> bool;

#[predicate]
fn stack(s: *mut Stack, head: *mut Node) -> bool {
    if head.is_null() {
        true
    } else {
        stack_node(head)
    }
}

#[predicate]
fn stack_node(node: *mut Node) -> bool {
    node != std::ptr::null_mut() &&
    sep!(
        node |-> ?next,
        match next {
            None => true,
            Some(n) => stack_node(n),
        }
    )
}

impl Stack {
    #[requires(
        stack(stack, ?head1) &&
        stack(other, ?head2) &&
        stack != std::ptr::null_mut() &&
        other != std::ptr::null_mut() &&
        stack != other
    )]
    #[ensures(
        stack(stack, sep_join(head2, head1)) &&
        !stack(other, _)
    )]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(
                stack_node(n) &&
                sep_exists(next: *mut Node,
                    n |-> next &&
                    (next.is_null() ==> n == ?last) &&
                    (!next.is_null() ==> stack_node(next))
                ) &&
                stack(stack, ?head1) &&
                head0 != std::ptr::null_mut()
            )]
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