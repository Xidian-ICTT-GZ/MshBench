use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
/*@ 
predicate node(struct Node* n; int value, struct Node* next) = 
    n->next |-> next &*& n->value |-> value;
@*/
struct Stack {
    head: *mut Node,
}
/*@
predicate stack(struct Stack* s; struct Node* head) = 
    s->head |-> head;
@*/

impl Stack {
    //@ req true;
    //@ ensures stack(result, null);
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, std::ptr::null_mut());
        stack
    }

    //@ req stack(stack, ?head);
    //@ ensures stack(stack, ?new_head) &*& (new_head == result_node || new_head == result_node);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, value, (*stack).head);
        (*stack).head = n;
        //@ close stack(stack, n);
    }

    //@ req stack(stack, ?head);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, head);
        //@ struct Node* curr = head;
        //@ while (curr != std::ptr::null_mut()) 
        //@     inv true;
        //@ {
        //@     open node(curr, _, _);
        //@     curr = (*curr).next;
        //@ }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}