use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn NodePred(n: *mut Node, next: *mut Node, value: i32) = 
    n |-> Node { next: next, value: value };

#[predicate]
fn StackPred(s: *mut Stack, head: *mut Node) =
    s |-> Stack { head: head };

#[lemma]
fn node_pred_inv(n: *mut Node)
    requires NodePred(n, ?next, ?v);
    ensures  NodePred(n, next, v);
{
    open NodePred(n, next, v);
    close NodePred(n, next, v);
}

#[lemma]
fn stack_pred_inv(s: *mut Stack)
    requires StackPred(s, ?head);
    ensures  StackPred(s, head);
{
    open StackPred(s, head);
    close StackPred(s, head);
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires(Layout::new::<Stack>().size() > 0 && Layout::new::<Stack>().align() > 0)]
        #[ensures StackPred(result, std::ptr::null_mut()) ]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        close StackPred(stack, std::ptr::null_mut());

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        open StackPred(stack, ?old_head);

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }

        (*n).next = old_head;
        (*n).value = value;

        close NodePred(n, old_head, value);

        (*stack).head = n;

        close StackPred(stack, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        open StackPred(stack, ?head);
        head != std::ptr::null_mut() ensures true;

        open NodePred(head, ?next, ?val);

        let result = (*head).value;
        (*stack).head = next;

        close StackPred(stack, next);

        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        open StackPred(stack, ?head);
        let mut curr = head;
        while curr != std::ptr::null_mut()
            invariant curr |-> ?node &*& (exists next, val; NodePred(curr, next, val)) &*& StackPred(stack, ?_ )
        {
            open NodePred(curr, ?next, ?val);
            let next_curr = next;
            dealloc(curr as *mut u8, Layout::new::<Node>());
            curr = next_curr;
        }
        close StackPred(stack, std::ptr::null_mut());

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