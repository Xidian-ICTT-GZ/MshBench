use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

predicate node_pred(n: *mut Node, next: *mut Node, v: i32) = 
    n |-> Node { next: next, value: v };

predicate stack_pred(s: *mut Stack, head: *mut Node) =
    s |-> Stack { head: head };

fixpoint bool is_node_list(*mut Node n) {
    switch(n) {
        case std::ptr::null_mut() => true,
        case _ =>
            exists<*mut Node next; int v;>(
                node_pred(n, next, v) && is_node_list(next)
            )
    }
}

fixpoint bool is_stack(*mut Stack s) {
    switch(s) {
        case std::ptr::null_mut() => false,
        case _ => true
    }
}

impl Stack {
    #[requires(Layout::new::<Stack>().size() > 0 && Layout::new::<Stack>().align() > 0)]
    #[ensures(stack_pred(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack_pred(stack, ?old_head) &*&
               (old_head == std::ptr::null_mut() ?
                true : node_pred(old_head, ?old_next, ?old_val) &*& is_node_list(old_next)))]
    #[ensures(stack_pred(stack, ?new_head) &*&
              node_pred(new_head, old_head, value) &*&
              (old_head == std::ptr::null_mut() ? true :
               node_pred(old_head, old_next, old_val) &*& is_node_list(old_next)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_pred(stack, ?head) &*&
               head != std::ptr::null_mut() &*&
               node_pred(head, ?next, ?val) &*& is_node_list(next))]
    #[ensures(result == val &*&
              stack_pred(stack, next) &*&
              (next == std::ptr::null_mut() ? true : is_node_list(next)))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack_pred(stack, ?head) &*&
               (head == std::ptr::null_mut() ? true :
                node_pred(head, ?next, ?val) &*& is_node_list(next)))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut node = (*stack).head;
        while (node != std::ptr::null_mut())
            invariant stack_pred(stack, node) &*& is_node_list(node)
        {
            let next = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            node = next;
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