use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node_value(n: *mut Node; v: i32) = (*n).value |-> v;
pred Node_next(n: *mut Node; next: *mut Node) = (*n).next |-> next;
pred Stack_head(s: *mut Stack; head: *mut Node) = (*s).head |-> head;

pred node_list(n: *mut Node;) =
    if n == 0 as *mut Node {
        true
    } else {
        Node_value(n, _) &*& Node_next(n, ?next) &*& struct_Node_padding(n) &*& alloc_block_Node(n) &*& node_list(next)
    };

pred stack_own(s: *mut Stack;) =
    Stack_head(s, ?head) &*& struct_Stack_padding(s) &*& alloc_block_Stack(s) &*& node_list(head);
@*/

unsafe fn dispose_nodes(n: *mut Node)
//@ req node_list(n);
//@ ens true;
{
    if !n.is_null() {
        //@ open node_list(n);
        let next = (*n).next;
        dispose_nodes(next);
        //@ close_struct(n);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open node_list(n);
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack_own(stack);
    //@ ens true;
    {
        //@ open stack_own(stack);
        dispose_nodes((*stack).head);
        //@ close_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}