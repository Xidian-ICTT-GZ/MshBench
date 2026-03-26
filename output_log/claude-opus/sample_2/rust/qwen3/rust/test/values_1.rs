use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr;

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

predicate node_pred(n: *mut Node) = 
    n != ptr::null_mut() &*& 
    n->next |-> ?next &*&
    n->value |-> ?value &*&
    (next == ptr::null_mut() || node_pred(next));

predicate stack_list(head: *mut Node) = 
    head == ptr::null_mut() ?
        emp
    :
        node_pred(head);

predicate stack_pred(s: *mut Stack, head0: *mut Node) = 
    s != ptr::null_mut() &*&
    s->head |-> head0 &*&
    stack_list(head0);

/* Lemma is omitted since it is trivial */

impl Stack {
    unsafe fn create() -> *mut Stack
    #[requires(true)]
    #[ensures stack_pred(result, ptr::null_mut()) &*& result->head |-> ptr::null_mut()]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = ptr::null_mut();
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires stack_pred(stack, ?head) &*& (head == ptr::null_mut() || stack_list(head))]
    #[ensures stack_pred(stack, ?new_head) &*& new_head != ptr::null_mut() &*&
              new_head->next |-> head &*& new_head->value |-> value &*&
              (head == ptr::null_mut() || stack_list(head))]
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
    #[requires stack_pred(stack, ?head) &*& (head == ptr::null_mut() || stack_list(head))]
    #[ensures true]
    {
        // Deallocate linked list nodes recursively
        let mut curr = (*stack).head;
        while curr != ptr::null_mut()
        #[invariant
            stack_pred(stack, curr) &*&
            (curr == ptr::null_mut() || node_pred(curr))
        ]
        {
            let next = (*curr).next;
            dealloc(curr as *mut u8, Layout::new::<Node>());
            curr = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}