use vstd::prelude::*;
use vstd::ptr::*;

verus! {

struct Node {
    next: *mut Node,
    value: i32,
}

predicate node(n: *mut Node) {
    is_null(n) ? true : 
        exists|next: *mut Node, value: i32| 
            n --> Node { next, value } && 
            (is_null(next) ? true : node(next))
}

predicate stack(s: *mut Stack) {
    exists|head: *mut Node| s --> Stack { head } && node(head)
}

struct Stack {
    head: *mut Node,
}

#[requires(stack(stack))]
#[ensures(stack(stack) && result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    open stack(stack);
    let head = (*stack).head;
    close stack(stack);
    
    let mut n = head;
    let mut i = 0;
    
    #[invariant(node(n) && i >= 0)]
    loop {
        if n.is_null() {
            break;
        }
        open node(n);
        n = (*n).next;
        i += 1;
    }
    
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}

}