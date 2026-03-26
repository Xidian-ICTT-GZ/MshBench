#[predicate]
fn node(n: *mut Node) -> bool;

#[predicate]
fn stack(s: *mut Stack, head: *mut Node) -> bool;

impl Stack {
    #[requires(stack(stack, ?head1) && stack(other, ?head2))]
    #[ensures(stack(stack, head2) && stack(other, _))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(node(n) && n != std::ptr::null_mut())]
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