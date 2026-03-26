use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
pub unsafe fn NodePred(n: *mut Node) = 
    n |-> Node { next: ?next_node, value: ?v } &*&
    (next_node == std::ptr::null_mut() || NodePred(next_node));

#[pred]
pub unsafe fn StackPred(s: *mut Stack) = 
    s |-> Stack { head: ?head } &*&
    (head == std::ptr::null_mut() || NodePred(head));

struct Node { next: *mut Node, value: i32 }
struct Stack { head: *mut Node }

#[lem]
fn node_pred_inductive(n: *mut Node)
    requires NodePred(n)
    ensures NodePred(n)
{
    if (n != std::ptr::null_mut()) {
        let node = unsafe { &*n };
        if (node.next != std::ptr::null_mut()) {
            node_pred_inductive(node.next);
        }
    }
}

#[lem]
fn stack_pred_inductive(s: *mut Stack)
    requires StackPred(s)
    ensures StackPred(s)
{
    let stack = unsafe { &*s };
    if (stack.head != std::ptr::null_mut()) {
        node_pred_inductive(stack.head);
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        #[requires(Layout::new::<Stack>().size() > 0 && Layout::new::<Stack>().align() > 0)]
        #[ensures StackPred(result)]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() { handle_alloc_error(Layout::new::<Stack>()); }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires StackPred(stack)]
        #[ensures StackPred(stack)]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() { handle_alloc_error(Layout::new::<Node>()); }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires StackPred(stack)]
        #[requires (*stack).head != std::ptr::null_mut()]
        #[ensures StackPred(stack)]
        #[ensures result == old((*stack).head).value]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires StackPred(stack)]
        #[ensures true]
    {
        let mut cur = (*stack).head;
        while cur != std::ptr::null_mut()
            #[invariant
                (cur == std::ptr::null_mut() && StackPred(stack)) ||
                (cur != std::ptr::null_mut() && NodePred(cur) &*&
                 (cur != std::ptr::null_mut() ==> true)) 
            ]
        {
            let next = (*cur).next;
            dealloc(cur as *mut u8, Layout::new::<Node>());
            cur = next;
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