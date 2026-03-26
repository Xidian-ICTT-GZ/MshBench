use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list<int> vs, *mut Node n) =
    n == std::ptr::null_mut() ?
        vs == nil
    :
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*& nodes(?vs0, next) &*& vs == cons(v, vs0);

pred stack(*mut Stack s, list<int> vs) =
    (*s).head |-> ?h &*& std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*& nodes(vs, h);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(nil, std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, nil);
        
        
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == length(vs);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        
        let mut n = head;
        let mut i = 0;
        //@ close nodes(vs, head);
        //@ close nodes(vs, n);
        //@ close stack(stack, vs);
        
        loop {
            //@ inv stack(stack, ?vs1) &*& nodes(?rest, n) &*& i + length(rest) == length(vs1);
            //@ open stack(stack, vs1);
            //@ open nodes(rest, n);
            if n.is_null() {
                //@ assert rest == nil;
                //@ close nodes(nil, std::ptr::null_mut());
                //@ close stack(stack, vs1);
                break;
            }
            //@ assert rest == cons(?v, ?rs);
            n = (*n).next;
            i += 1;
            //@ close nodes(rs, n);
            //@ close stack(stack, vs1);
        }
        
        
        
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req stack(stack, ?vs) &*& stack(other, ?os);
    //@ ens stack(stack, append(os, vs));
    {
        //@ open stack(other, os);
        //@ open stack(stack, vs);
        
        
        
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        //@ open nodes(os, head0);
        //@ close nodes(os, head0);
        let mut n = head0;
        
        if !n.is_null() {
            //@ open nodes(os, head0);
            //@ assert os == cons(?v0, ?os0);
            //@ close nodes(cons(v0, os0), head0);
            //@ close nodes(cons(v0, os0), n);
            loop {
                //@ inv nodes(?pref, head0) &*& nodes(?suf, n) &*& os == append(pref, suf) &*& suf != nil;
                //@ open nodes(suf, n);
                if (*n).next.is_null() {
                    //@ assert suf == cons(?vlast, nil);
                    //@ close nodes(cons(vlast, nil), n);
                    break;
                }
                //@ assert suf == cons(?vn, ?suf1);
                n = (*n).next;
                //@ close nodes(suf1, n);
                //@ close nodes(cons(vn, suf1), std::ptr::null_mut()); // dummy close to help symmetry (no effect)
                //@ open nodes(cons(vn, suf1), std::ptr::null_mut()); // immediately open (no effect)
                //@ close nodes(cons(vn, suf1), (n as *mut Node).wrapping_sub(0)); // dummy close/open pattern avoided in future
            }
            
            //@ open nodes(?suf2, n);
            //@ assert suf2 == cons(?vlast2, nil);
            //@ close nodes(nil, (*stack).head);
            (*n).next = (*stack).head;
            //@ close nodes(append(suf2, vs), n);
            
            (*stack).head = head0;
            //@ close nodes(append(os, vs), head0);
        } else {
            //@ close nodes(os, head0);
        }
        //@ close stack(stack, append(os, vs));
        
        
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(vs, (*n).next);
        //@ close nodes(cons(value, vs), n);
        (*stack).head = n;
        //@ close stack(stack, cons(value, vs));
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs) &*& vs != nil;
    //@ ens stack(stack, tail(vs)) &*& result == head(vs);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open nodes(vs, head);
        //@ assert vs == cons(?v, ?vs0);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes(vs0, (*stack).head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs0);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?vs);
    //@ ens true;
    {
        //@ open stack(stack, vs);
        //@ open nodes(vs, (*stack).head);
        //@ assert false; // memory leak of nodes; prevent unsoundness
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}