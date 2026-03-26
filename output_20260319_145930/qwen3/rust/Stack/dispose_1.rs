use std::alloc::{dealloc, Layout};

/*@ pred node(n: *mut Node, v: i32, next: *mut Node) = 
    n != 0 &*& 
    [1/2]n as *mut i32 |-> v &*& 
    [1/2](n as *mut i32).offset(1) as *mut *mut Node |-> next;
@*/

/*@ pred nodes(n: *mut Node) =
    n == 0 ? true : 
    exists(?v, ?next) &*& node(n, v, next) &*& nodes(next);
@*/

/*@ pred stack(s: *mut Stack, head: *mut Node) =
    s != 0 &*& 
    s as *mut *mut Node |-> head;
@*/

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes(n);
        //@ let v = _; let next = _; open node(n, v, next);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens true;
    {
        
        //@ open stack(stack, head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}