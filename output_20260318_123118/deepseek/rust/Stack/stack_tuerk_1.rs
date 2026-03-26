use vstd::prelude::*;
use vstd::ptr::*;

verus! {

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_valid(n: *mut Node) -> bool
    reads n
    is
        !n.is_null() ==>
            alloc::alloc::points_to(n, Node {
                next: ?next_ptr
            }) && node_valid(next_ptr);

predicate stack_valid(s: *mut Stack) -> bool
    reads s
    is
        !s.is_null() ==>
            alloc::alloc::points_to(s, Stack {
                head: ?head_ptr
            }) && node_valid(head_ptr);

#[requires(stack_valid(stack))]
#[ensures(stack_valid(stack))]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    requires(stack_valid(stack));
    ensures(stack_valid(stack));
    ensures(result >= 0);
    {
        let mut n = (*stack).head;
        let mut i: i32 = 0;
        
        #[invariant(stack_valid(stack))]
        #[invariant(node_valid(n))]
        #[invariant(i >= 0)]
        loop {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
        
        i
    }
}

}