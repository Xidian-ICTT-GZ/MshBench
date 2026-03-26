use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    pub next: *mut Node,
    pub value: i32,
}

#[repr(C)]
pub struct Stack {
    pub head: *mut Node,
}

#[predicate]
pub unsafe fn NodePred(n: *mut Node, next: *mut Node, value: i32, owned: bool) = 
    owned ? ( 
        n != std::ptr::null_mut() &*&
        // n points to Node struct with next and value
        // We model ownership as full permission to n
        // VeriFast syntax for points-to field predicates:
        n |-> _ &*&
        (n as *mut u8) |->_ &*&
        // more precisely:
        n->next |-> next &*&
        n->value |-> value
    )
    : n == std::ptr::null_mut();

#[predicate]
pub unsafe fn StackPred(s: *mut Stack, head: *mut Node, owned: bool) = 
    owned ? (
        s != std::ptr::null_mut() &*&
        s->head |-> head
    )
    : s == std::ptr::null_mut();

// Lemma to dispose a node predicate by dealloc
#[lemma]
pub unsafe fn node_pred_dispose(n: *mut Node)
    requires
        NodePred(n, ?next, ?value, true),
    ensures
        NodePred(n, next, value, false),
{
}

// Lemma to dispose a stack predicate by dealloc
#[lemma]
pub unsafe fn stack_pred_dispose(s: *mut Stack)
    requires
        StackPred(s, ?head, true),
    ensures
        StackPred(s, head, false),
{
}

impl Stack {
    #[requires(
        Layout::new::<Stack>().size() > 0 &&
        Layout::new::<Stack>().align() > 0
    )]
    #[ensures(
        result != std::ptr::null_mut() &&
        StackPred(result, std::ptr::null_mut(), true)
    )]
    pub unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(
        StackPred(stack, ?head, true)
    )]
    #[ensures(
        StackPred(stack, head, true) &&
        result == ((*stack).head == std::ptr::null_mut())
    )]
    pub unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;
        head.is_null()
    }

    #[requires(
        StackPred(stack, ?old_head, true) &&
        Layout::new::<Node>().size() > 0 &&
        Layout::new::<Node>().align() > 0
    )]
    #[ensures(
        StackPred(stack, result, true) &&
        NodePred(result, old_head, value, true)
    )]
    pub unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(
        StackPred(stack, ?head, true) &&
        head != std::ptr::null_mut() &&
        NodePred(head, ?next, ?value, true)
    )]
    #[ensures(
        StackPred(stack, next, true) &&
        result == value
    )]
    pub unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(
        StackPred(stack, ?head, true)
    )]
    #[ensures(
        StackPred(stack, std::ptr::null_mut(), false)
    )]
    pub unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(
    NodePred(n, ?next, ?value, true)
)]
#[ensures(
    NodePred(n, next, value, false)
)]
pub unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}