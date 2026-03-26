use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

predicate node<n>(n: *mut Node, next: *mut Node, v: i32) =
    n != std::ptr::null_mut() &*&
    n->next |-> next &*&
    n->value |-> v;

predicate stack(stack_ptr: *mut Stack, head: *mut Node) =
    stack_ptr != std::ptr::null_mut() &*&
    stack_ptr->head |-> head &*&
    stack_list(head);

predicate stack_list(head: *mut Node) =
    head == std::ptr::null_mut() ?
        emp
    :
        exists<*mut Node, i32>(|next, v| node(head, next, v) &*& stack_list(next));

impl Stack {
    unsafe fn create() -> *mut Stack
    #[requires layout_of::<Stack>() == Layout::new::<Stack>()]
    #[ensures stack(result, std::ptr::null_mut())]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires stack(stack, ?head)]
    #[ensures  stack(stack, result_head) &*&
               result_head != std::ptr::null_mut() &*&
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
    #[requires stack(stack, ?head)]
    #[ensures emp]
    {
        // Need to recursively deallocate nodes
        self.dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

impl Stack {
    unsafe fn dispose_nodes(&self, n: *mut Node)
    #[requires stack_list(n)]
    #[ensures emp]
    {
        if n != std::ptr::null_mut() {
            let next = (*n).next;
            self.dispose_nodes(next);
            dealloc(n as *mut u8, Layout::new::<Node>());
        }
    }
}