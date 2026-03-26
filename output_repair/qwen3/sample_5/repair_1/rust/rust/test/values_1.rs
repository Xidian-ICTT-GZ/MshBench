use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node head;);

predicate stack_inv(*mut Stack s) = 
    s |-> ?stack && node_list(stack.head);

lemma_auto() node_list_null()
    requires true;
    ensures node_list(std::ptr::null_mut());
{
}

lemma_auto() node_list_cons(*mut Node p)
    requires p |-> ?n && node_list(n.next);
    ensures node_list(p);
{
}

impl Stack {
    #[ensures(result as *mut u8 |-> _ && stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        leak node_list_null();
        leak stack_inv_facts(stack);
        stack
    }

    #[requires(stack as *mut u8 |-> _ && stack_inv(stack))]
    #[ensures(stack as *mut u8 |-> _ && stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node_list(n);
        close stack_inv(stack);
    }

    #[requires(stack as *mut u8 |-> _ && stack_inv(stack))]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

lemma stack_inv_facts(*mut Stack s)
    requires s |-> ?stack;
    ensures s |-> stack && node_list(stack.head) == stack_inv(s);
{
    close stack_inv(s);
}