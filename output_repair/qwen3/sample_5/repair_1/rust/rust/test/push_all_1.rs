#[predicate]
pub pred Node(n: *mut Node) = (*n).next |-> ?next &*& n as *mut u8 |-> ?val &*& struct_Node_padding(n);

#[predicate]
pub pred Stack(s: *mut Stack) = (*s).head |-> ?head &*& s as *mut u8 |-> _ &*& struct_Stack_padding(s);

#[predicate]
pub pred list(nodes: *mut Node) =
    if nodes.is_null() {
        emp
    } else {
        Node(nodes) * list((*nodes).next)
    };

impl Stack {
    #[requires(Stack(stack))]
    #[requires(Stack(other))]
    #[ensures(Stack(stack))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(list(n) * Stack(stack) * n != null)]
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