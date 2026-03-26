use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node_own(n: *mut Node; next: *mut Node, value: i32) =
    (*n).next |-> next &*& (*n).value |-> value;

pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        Node_own(n, ?next, ?value) &*& Nodes(next)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head;

pred Stack_inv(s: *mut Stack;) =
    Stack_own(s, ?head) &*& Nodes(head);
@*/

#[requires(Nodes(nodes))]
#[ensures(Nodes(nodes))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Nodes(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Nodes(nodes);
    }

    result
}

impl Stack {
    #[requires(true)]
    #[ensures(Stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node);
        //@ close Stack_own(stack, 0 as *mut Node);
        //@ close Stack_inv(stack);

        stack
    }

    #[requires(Stack_inv(stack))]
    #[ensures(Stack_inv(stack))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        //@ open Stack_inv(stack);
        //@ open Stack_own(stack, ?head);
        let _head = (*stack).head;

        let result = (*stack).head.is_null();
        //@ close Stack_own(stack, head);
        //@ close Stack_inv(stack);

        result
    }

    #[requires(Stack_inv(stack))]
    #[ensures(Stack_inv(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        //@ open Stack_inv(stack);
        //@ open Stack_own(stack, ?head);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack_own(stack, head);
        //@ close Stack_inv(stack);

        result
    }

    #[requires(Stack_inv(stack))]
    #[ensures(Stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open Stack_inv(stack);
        //@ open Stack_own(stack, ?old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node_own(n, old_head, value);
        //@ close Nodes(n);
        //@ close Stack_own(stack, n);
        //@ close Stack_inv(stack);
    }

    #[requires(Stack_inv(stack))]
    #[ensures(Stack_inv(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open Stack_inv(stack);
        //@ open Stack_own(stack, ?old_head);
        let head = (*stack).head;
        //@ open Nodes(head);
        //@ open Node_own(head, ?next, ?val);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack, next);
        //@ close Stack_inv(stack);

        result
    }

    #[requires(Stack_inv(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open Stack_inv(stack);
        //@ open Stack_own(stack, ?head);
        let mut n = (*stack).head;
        loop {
            //@ invariant(Nodes(n))
            if n.is_null() {
                break;
            }
            //@ open Nodes(n);
            //@ open Node_own(n, ?next, ?val);

            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }

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