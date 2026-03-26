#[predicate]
fn Node(n: *mut struct_Node) -> bool {
    (*n).next |-> ?next &*& n as *mut u8 |-> _ &*& struct_Node_padding(n)
}

#[predicate]
fn Stack(s: *mut struct_Stack) -> bool {
    (*s).head |-> ?head &*& s as *mut u8 |-> _ &*& struct_Stack_padding(s)
}

#[predicate]
fn list(nodes: *mut struct_Node) -> bool {
    if nodes == std::ptr::null_mut() {
        emp
    } else {
        Node(nodes) * list((*nodes).next)
    }
}

impl struct_Stack {
    #[requires(Stack(stack))]
    #[requires(Stack(other))]
    #[ensures(Stack(stack))]
    unsafe fn push_all(stack: *mut struct_Stack, other: *mut struct_Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<struct_Stack>());
        let mut n = head0;

        if n != std::ptr::null_mut() {
            loop
                invariant list(n) * Stack(stack) * n != std::ptr::null_mut();
            {
                if (*n).next == std::ptr::null_mut() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;
            (*stack).head = head0;
        }
    }
}