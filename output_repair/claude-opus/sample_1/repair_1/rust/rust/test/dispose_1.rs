use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node_list(n: *mut Node) =
    if n == std::ptr::null_mut() {
        emp
    } else {
        (*n).value |-> ?_ &*& (*n).next |-> ?next &*& node_list(next)
    };

pred stack_own(s: *mut Stack) =
    (*s).head |-> ?head &*& node_list(head);
@*/

#[requires(node_list(n))]
#[ensures(emp)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        //@ open node_list(n);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open node_list(n);
    }
}

impl Stack {
    #[requires(stack_own(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack_own(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}