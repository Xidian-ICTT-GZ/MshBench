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
    (*n).next |-> next &*& (*n).value |-> value &*& alloc_block(n as *mut u8, Layout::new::<Node>());

pred node_list(n: *mut Node;) =
    if n == 0 as *mut Node {
        true
    } else {
        Node_own(n, ?next, ?value) &*& node_list(next)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head &*& alloc_block(s as *mut u8, Layout::new::<Stack>());

pred stack_inv(s: *mut Stack;) =
    Stack_own(s, ?head) &*& node_list(head);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req node_list(nodes)
//@ ens node_list(nodes)
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open node_list(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node_list(nodes);
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true
    //@ ens stack_inv(result)
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close node_list(0 as *mut Node);
        //@ close Stack_own(stack, 0 as *mut Node);
        //@ close stack_inv(stack);

        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack_inv(stack)
    //@ ens stack_inv(stack)
    {
        //@ open stack_inv(stack);
        //@ open Stack_own(stack, ?head);
        let _head = (*stack).head;

        let result = (*stack).head.is_null();
        //@ close Stack_own(stack, head);
        //@ close stack_inv(stack);

        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack_inv(stack)
    //@ ens stack_inv(stack)
    {
        //@ open stack_inv(stack);
        //@ open Stack_own(stack, ?head);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack_own(stack, head);
        //@ close stack_inv(stack);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack_inv(stack)
    //@ ens stack_inv(stack)
    {
        //@ open stack_inv(stack);
        //@ open Stack_own(stack, ?old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node_own(n, old_head, value);
        //@ close node_list(n);
        //@ close Stack_own(stack, n);
        //@ close stack_inv(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack_inv(stack) &*& (*stack).head != 0 as *mut Node
    //@ ens stack_inv(stack)
    {
        //@ open stack_inv(stack);
        //@ open Stack_own(stack, ?old_head);
        let head = (*stack).head;
        //@ open node_list(head);
        //@ open Node_own(head, ?next, ?val);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack, next);
        //@ close stack_inv(stack);

        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack_inv(stack)
    //@ ens true
    {
        //@ open stack_inv(stack);
        //@ open Stack_own(stack, ?head);
        let mut n = (*stack).head;
        //@ inv node_list(n)
        loop {
            if n.is_null() {
                break;
            }
            //@ open node_list(n);
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