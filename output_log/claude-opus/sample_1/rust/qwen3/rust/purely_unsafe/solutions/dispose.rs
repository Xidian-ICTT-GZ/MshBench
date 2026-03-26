use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[pred]
fn NodePred(n: *mut Node, next: *mut Node, value: i32, owned: bool) =
    owned ?
        n != std::ptr::null_mut() &*&
        n->next |-> next &*&
        n->value |-> value
    :  
        n != std::ptr::null_mut() &*&
        n->next |-> next &*&
        n->value |-> value
;

#[pred]
fn StackPred(s: *mut Stack, head: *mut Node, owned: bool) =
    owned ?
        s != std::ptr::null_mut() &*&
        s->head |-> head
    :
        s != std::ptr::null_mut() &*&
        s->head |-> head
;

#[lemma]
fn node_pred_dispose(n: *mut Node)
    requires
        NodePred(n, ?next, ?value, true),
    ensures
        NodePred(n, next, value, false),
{
    close NodePred(n, next, value, false);
}

#[lemma]
fn stack_pred_dispose(s: *mut Stack)
    requires
        StackPred(s, ?head, true),
    ensures
        StackPred(s, head, false),
{
    close StackPred(s, head, false);
}

impl Stack {
    #[requires(
        Layout::new::<Stack>().size() > 0 &*&
        Layout::new::<Stack>().align() > 0
    )]
    #[ensures(
        result != std::ptr::null_mut() &*&
        StackPred(result, std::ptr::null_mut(), true)
    )]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() { handle_alloc_error(Layout::new::<Stack>()); }
        (*stack).head = std::ptr::null_mut();
        // allocate stack ownership:
        close StackPred(stack, std::ptr::null_mut(), true);
        return stack;
    }

    #[requires(
        StackPred(stack, ?head, true)
    )]
    #[ensures(
        StackPred(stack, head, true) &*&
        result == (head == std::ptr::null_mut())
    )]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        open StackPred(stack, ?head, true);
        let result = (*stack).head.is_null();
        close StackPred(stack, head, true);
        return result;
    }

    #[requires(
        StackPred(stack, ?old_head, true) &*&
        Layout::new::<Node>().size() > 0 &*&
        Layout::new::<Node>().align() > 0
    )]
    #[ensures(
        StackPred(stack, ?new_head, true) &*&
        NodePred(new_head, old_head, value, true)
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open StackPred(stack, ?old_head, true);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() { handle_alloc_error(Layout::new::<Node>()); }
        (*n).next = old_head;
        (*n).value = value;
        close NodePred(n, old_head, value, true);
        (*stack).head = n;
        close StackPred(stack, n, true);
    }

    #[requires(
        StackPred(stack, ?head, true) &*&
        head != std::ptr::null_mut() &*&
        NodePred(head, ?next, ?value, true)
    )]
    #[ensures(
        StackPred(stack, next, true) &*&
        result == value
    )]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open StackPred(stack, head, true);
        open NodePred(head, ?next, ?value, true);
        let result = (*head).value;
        (*stack).head = next;
        close StackPred(stack, next, true);
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    #[requires(
        StackPred(stack, ?head, true)
    )]
    #[ensures(
        StackPred(stack, head, false)
    )]
    unsafe fn dispose(stack: *mut Stack) {
        open StackPred(stack, ?head, true);
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
        close StackPred(stack, head, false);
    }
}

#[requires(
    NodePred(n, ?next, ?value, true)
)]
#[ensures(
    NodePred(n, next, value, false)
)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        open NodePred(n, ?next, ?value, true);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        close NodePred(n, next, value, false);
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