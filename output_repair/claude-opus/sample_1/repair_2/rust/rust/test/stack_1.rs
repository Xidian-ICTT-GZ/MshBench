use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& Nodes(next)
    };

pred StackInv(s: *mut Stack;) =
    (*s).head |-> ?head &*& Nodes(head);
@*/

impl Stack {
    #[requires(true)]
    #[ensures(StackInv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Nodes(0 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        //@ close StackInv(stack);
        stack
    }
    #[requires(StackInv(stack))]
    #[ensures(StackInv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open StackInv(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open Nodes((*stack).head);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close StackInv(stack);
    }
    #[requires(StackInv(stack) & (*stack).head != 0)]
    #[ensures(StackInv(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open StackInv(stack);
        let head = (*stack).head;
        //@ open Nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackInv(stack);
        result
    }
    #[requires(StackInv(stack) & (*stack).head == 0)]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open StackInv(stack);
        //@ open Nodes(0 as *mut Node);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
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