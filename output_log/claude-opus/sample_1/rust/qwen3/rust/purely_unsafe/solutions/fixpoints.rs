use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
#[verbatim] //# VeriFast syntax in Rust attribute comment for predicates
fn NodePred(this: *mut Node, next: *mut Node, value: i32) =
    this |-> Node { next: next, value: value };

#[predicate]
#[verbatim]
fn StackPred(this: *mut Stack, head: *mut Node) =
    this |-> Stack { head: head };

#[lemma]
fn node_pred_inv(n: *mut Node)
    requires NodePred(n, ?next_node, ?v);
    ensures NodePred(n, next_node, v);
{
}

#[lemma]
fn stack_pred_inv(s: *mut Stack)
    requires StackPred(s, ?head_node);
    ensures StackPred(s, head_node);
{
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires Layout::new::<Stack>().size() > 0 && Layout::new::<Stack>().align() > 0]
        #[ensures StackPred(result, std::ptr::null_mut()) ]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires
            StackPred(stack, ?old_head) &*&
            (old_head == std::ptr::null_mut() ?
                true
                :
                NodePred(old_head, ?old_next, ?old_val))
        ]
        #[ensures
            StackPred(stack, ?new_head) &*&
            new_head != std::ptr::null_mut() &*&
            NodePred(new_head, old_head, value) &*&
            (old_head == std::ptr::null_mut() ?
                true
                :
                NodePred(old_head, old_next, old_val))
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
            StackPred(stack, ?head) &*&
            head != std::ptr::null_mut() &*&
            NodePred(head, ?next, ?val)
        ]
        #[ensures
            result == val &*&
            StackPred(stack, next) &*&
            (next == std::ptr::null_mut() ? true : NodePred(next, ?_, ?_))
        ]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires
            StackPred(stack, ?head) &*&
            (
                head == std::ptr::null_mut() ? true :
                NodePred(head, ?next, ?val) &*&
                (next == std::ptr::null_mut() ? true : NodePred(next, ?_, ?_))
            )
        ]
        #[ensures true]
        let mut current = head;
        while current != std::ptr::null_mut()
            invariant
                StackPred(stack, current) &*&
                (
                    current == std::ptr::null_mut() ? true :
                    NodePred(current, ?next_node, ?v) &*&
                    (next_node == std::ptr::null_mut() ? true : NodePred(next_node, ?_, ?_))
                )
        {
            let next = (*current).next;
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
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