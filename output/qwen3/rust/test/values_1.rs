use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred] struct NodePred {
    next: *mut Node,
    value: i32,
    #[ghost] inv: bool,
}

#[pred] struct StackPred {
    head: *mut Node,
    #[ghost] inv: bool,
}

#[lemma]
fn node_pred_valid(n: *mut Node) -> bool
    requires
        n != std::ptr::null_mut(),
        node(n) |-> ?n_val,
        node_pred(n) == NodePred { next: ?next, value: ?val, inv: ?inv },
    ensures
        inv ==> (next == ?next && val == ?val),
{
    // This lemma is trivially true by definition of node_pred
}

#[predicate] fn node_pred(p: *mut Node) -> NodePred {
    NodePred { next: (*p).next, value: (*p).value, inv: true }
}

#[predicate] fn stack_pred(p: *mut Stack) -> StackPred {
    StackPred { head: (*p).head, inv: true }
}

#[predicate] fn stack_list(head: *mut Node) -> bool {
    head == std::ptr::null_mut() ||
    (head != std::ptr::null_mut() &&
     node(head) |-> ?n &&
     node_pred(head) == NodePred { next: ?next, value: ?val, inv: true } &&
     stack_list(next))
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires layout_of::<Stack>() == Layout::new::<Stack>() ]
        #[ensures result != std::ptr::null_mut() && stack_pred(result) == StackPred { head: std::ptr::null_mut(), inv: true } &&
                node(result) |-> ?s && stack_pred(result) == StackPred { head: std::ptr::null_mut(), inv: true }]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires stack != std::ptr::null_mut() &&
                 node(stack) |-> ?s &&
                 stack_pred(stack) == StackPred { head: ?head, inv: true } &&
                 (head == std::ptr::null_mut() || (head != std::ptr::null_mut() && stack_list(head)))]
        #[ensures node(stack) |-> ?s' &&
                 stack_pred(stack) == StackPred { head: ?new_head, inv: true } &&
                 new_head != std::ptr::null_mut() &&
                 node(new_head) |-> ?n &&
                 node_pred(new_head) == NodePred { next: ?old_head, value: value, inv: true } &&
                 (old_head == std::ptr::null_mut() || stack_list(old_head))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires stack != std::ptr::null_mut() &&
                 node(stack) |-> ?s &&
                 stack_pred(stack) == StackPred { head: ?head, inv: true } &&
                 (head == std::ptr::null_mut() || stack_list(head))]
        #[ensures true]
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}