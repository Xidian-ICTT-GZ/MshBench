use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(node: *mut Node; next: *mut Node, value: i32) =
    node != std::ptr::null_mut() &*& 
    *node |-> struct_Node { next: next, value: value };

predicate stack(stack: *mut Stack; nodes: list<*mut Node>) =
    stack != std::ptr::null_mut() &*&
    *stack |-> struct_Stack { head: ?head } &*&
    stack_nodes(head, nodes);

predicate stack_nodes(head: *mut Node; nodes: list<*mut Node>) =
    match nodes {
        cons(n, rest) => node(n, ?next, _) &*& stack_nodes(next, rest),
        nil => head == std::ptr::null_mut()
    };

impl Stack {

    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, cons(?n, nodes)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }
    
    #[requires(stack(stack, cons(?n, ?rest)))]
    #[ensures(stack(stack, rest) &*& result == ?val &*& node(n, _, val))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, reverse(nodes)))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        #[invariant(stack_nodes(n, ?suffix) &*& stack_nodes(m, ?prefix) &*& append(reverse(prefix), suffix) == nodes)]
        loop {
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
        }
        (*stack).head = m;
    }

    #[requires(stack(stack, _))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
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