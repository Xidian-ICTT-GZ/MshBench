use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(ptr: *mut Node) =
    ptr.is_null() ? emp : (
        ptr->Node.next |-> ?next &*&
        ptr->Node.value |-> ?val &*&
        node_list(next)
    );

predicate stack_inv(s: *mut Stack) =
    s->Stack.head |-> ?head &*&
    node_list(head);

#[requires(node_list(nodes))]
#[ensures(node_list(nodes))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[ensures(stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let _head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_inv(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        loop {
            #[invariant(node_list(n))]
            {
                if n.is_null() {
                    break;
                }

                let next = (*n).next;
                dealloc(n as *mut u8, Layout::new::<Node>());
                n = next;
            }
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