use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr::null_mut;

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(node_ptr: *mut Node, next_ptr: *mut Node, val: i32) =
    node_ptr != null_mut() &*&
    node_ptr->next |-> next_ptr &*&
    node_ptr->value |-> val;

predicate stack(stack_ptr: *mut Stack, head_ptr: *mut Node) =
    stack_ptr != null_mut() &*&
    stack_ptr->head |-> head_ptr;

predicate stack_list(node_ptr: *mut Node) = 
    node_ptr == null_mut() ?
        emp
    :
        node(node_ptr, ?next_ptr, ?val) &*&
        stack_list(next_ptr);

impl Stack {
    unsafe fn create() -> *mut Stack
    #[requires true]
    #[ensures result != null_mut() &*& stack(result, null_mut())]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires stack(stack, ?head) &*& stack_list(head)]
    #[ensures stack(stack, result_head) &*& stack_list(result_head) &*&
              node(result_head, head, value)]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn dispose(stack: *mut Stack)
    #[requires stack(stack, ?head) &*& stack_list(head)]
    #[ensures true]
    {
        // Deallocate all nodes in the list
        let mut cur = head;
        while (cur != null_mut())
        #[invariant stack_list(cur)]
        {
            let next = (*cur).next;
            dealloc(cur as *mut u8, Layout::new::<Node>());
            cur = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}