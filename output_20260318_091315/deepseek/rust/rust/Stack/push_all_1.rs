use std::alloc::{Layout, dealloc};
use std::ptr::null_mut;

struct Node {
    data: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_own(n: *mut Node; data: i32, next: *mut Node) {
    n != null_mut() && struct_Node!{n => {data: data, next: next}}
}

predicate nodes(n: *mut Node) {
    n == null_mut() ? 
        emp 
    : 
        node_own(n; _, next) * nodes(next)
}

predicate stack_own(s: *mut Stack) {
    s != null_mut() && struct_Stack!{s => {head: head}} * nodes(head)
}

impl Stack {
    #[requires(stack_own(stack) * stack_own(other))]
    #[ensures(stack_own(stack))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        #[assert(stack_own(other))]
        #[assert(struct_Stack!{other => {head: head0}} * nodes(head0))]
        
        #[assert(stack_own(other))]
        dealloc(other as *mut u8, Layout::new::<Stack>());
        #[assert(nodes(head0))]
        
        let mut n = head0;

        if !n.is_null() {
            #[assert(nodes(n))]
            #[invariant(nodes(n))]
            loop {
                #[assert(nodes(n))]
                if (*n).next.is_null() {
                    break;
                }
                #[assert(node_own(n; _, next) * nodes(next))]
                n = (*n).next;
                #[assert(nodes(n))]
            }
            #[assert(node_own(n; _, next) * next == null_mut())]
            #[assert(nodes(head0))]
            
            #[assert(stack_own(stack))]
            #[assert(struct_Stack!{stack => {head: stack_head}} * nodes(stack_head))]
            (*n).next = (*stack).head;
            #[assert(node_own(n; _, stack_head) * nodes(stack_head))]
            #[assert(nodes(head0))]
            
            (*stack).head = head0;
            #[assert(struct_Stack!{stack => {head: head0}} * nodes(head0))]
        }
        #[assert(stack_own(stack))]
    }
}