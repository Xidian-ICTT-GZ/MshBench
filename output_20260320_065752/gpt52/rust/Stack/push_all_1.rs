use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node_chain(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        alloc_block_Node(n) &*& (*n).next |-> ?next &*& node_chain(next);

pred stack(s: *mut Stack) =
    alloc_block_Stack(s) &*& (*s).head |-> ?h &*& node_chain(h);

@*/

impl Stack {
    //@ req stack(stack) &*& stack(other);
    //@ ens stack(stack);
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    {
        //@ open stack(other);
        let head0 = (*other).head;
        //@ close node_chain(head0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        //@ open stack(stack);
        let mut n = head0;

        if !n.is_null() {

            //@ open node_chain(n);
            loop {
                //@ inv node_chain(n);

                if (*n).next.is_null() {
                    break;
                }
                let next = (*n).next;
                //@ open node_chain(next);
                //@ close node_chain(n);
                n = next;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
            //@ close node_chain(n);
        }

        //@ close stack(stack);
    }
}