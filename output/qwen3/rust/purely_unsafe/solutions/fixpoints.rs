use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
struct NodePred {
    next: *mut Node,
    value: i32,
}

#[pred]
struct StackPred {
    head: *mut Node,
}

#[lem]
fn node_pred_inv(n: *mut Node) -> bool
    requires
        n |-> ?node,
        node.next |-> ?next_node,
        node.value == ?v,
        NodePred { next: node.next, value: v }(n),
    ensures
        NodePred { next: node.next, value: v }(n),
{
}

#[lem]
fn stack_pred_inv(s: *mut Stack) -> bool
    requires
        s |-> ?stack,
        stack.head |-> ?head_node,
        StackPred { head: stack.head }(s),
    ensures
        StackPred { head: stack.head }(s),
{
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires Layout::new::<Stack>().size() > 0 && Layout::new::<Stack>().align() > 0 ]
        #[ensures result |-> StackPred { head: std::ptr::null_mut() } ]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires
            stack |-> StackPred { head: ?old_head },
            old_head |-> ?old_node ==> NodePred { next: ?old_next, value: ?old_val }(old_head),
            old_head == std::ptr::null_mut() ==> true,
            old_head != std::ptr::null_mut() ==> old_next |-> ?_ ==> NodePred { next: ?_, value: ?_ }(old_next)
        ]
        #[ensures
            stack |-> StackPred { head: ?new_head },
            new_head |-> NodePred { next: ?old_head, value: value },
            old_head |-> ?old_node ==> NodePred { next: ?old_next, value: ?old_val }(old_head),
            old_head == std::ptr::null_mut() ==> true,
            old_head != std::ptr::null_mut() ==> old_next |-> ?_ ==> NodePred { next: ?_, value: ?_ }(old_next)
        ]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires
            stack |-> StackPred { head: ?head },
            head != std::ptr::null_mut(),
            head |-> NodePred { next: ?next, value: ?val }
        ]
        #[ensures
            result == val &&
            stack |-> StackPred { head: next },
            next |-> ?next_node ==> NodePred { next: ?_, value: ?_ }(next),
            next == std::ptr::null_mut() ==> true
        ]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires
            stack |-> StackPred { head: ?head },
            head == std::ptr::null_mut() ==> true,
            head != std::ptr::null_mut() ==> head |-> NodePred { next: ?next, value: ?val },
            next == std::ptr::null_mut() ==> true,
            next != std::ptr::null_mut() ==> next |-> NodePred { next: ?_, value: ?_ }
        ]
        #[ensures true]
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}