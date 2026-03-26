use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes_list(n: *mut Node, next: *mut Node) =
    if n == next {
        emp
    } else {
        std::alloc::alloc_block_Node(n) &*& (*n).next |-> ?nxt &*& nodes_list(nxt, next);
    };

pred stack(s: *mut Stack) =
    std::alloc::alloc_block_Stack(s) &*& (*s).head |-> ?h &*& nodes_list(h, std::ptr::null_mut());

@*/

impl Stack {
    //@ req stack(stack) &*& stack(other);
    //@ ens stack(stack) &*& nodes_list((*other).head, std::ptr::null_mut()); // 'other' deallocated; keep nodes
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    {
        //@ open stack(other);
        let head0 = (*other).head;
        //@ open nodes_list(head0, std::ptr::null_mut());
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {

            loop {
                //@ inv nodes_list(head0, n) &*& nodes_list(n, std::ptr::null_mut()) &*& stack(stack);
                //@ open nodes_list(n, std::ptr::null_mut());
                if (*n).next.is_null() {
                    //@ close nodes_list(n, std::ptr::null_mut());
                    break;
                }
                let nnext = (*n).next;
                //@ close nodes_list(n, nnext);
                n = nnext;
            }

            //@ open stack(stack);
            //@ assert (*stack).head |-> ?oldhead;
            //@ close nodes_list(oldhead, std::ptr::null_mut());
            //@ open nodes_list(n, std::ptr::null_mut());
            //@ assert (*n).next |-> ?nn;
            (*n).next = (*stack).head;
            //@ close nodes_list(n, std::ptr::null_mut());
            (*stack).head = head0;
            //@ close nodes_list(head0, std::ptr::null_mut());
            //@ close stack(stack);
        } else {
            //@ close nodes_list(head0, std::ptr::null_mut());
        }

        //@ close stack(stack);
        //@ open stack(stack);
        //@ close stack(stack);
        //@ close nodes_list((*other).head, std::ptr::null_mut());
    }
}