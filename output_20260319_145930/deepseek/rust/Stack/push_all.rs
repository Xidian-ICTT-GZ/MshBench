use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred nodes(n: *mut Node; count: i32) =
    if n.is_null() then
        count == 0
    else
        alloc_block(n, std::mem::size_of::<Node>()) &*&
        struct_Node_padding(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?val &*&
        nodes(next, ?c) &*&
        count == c + 1;
@*/

/*@
pred stack(stack: *mut Stack) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    nodes(head, _);
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut(), 0);
        //@ close stack(stack);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& nodes(?head, ?count);
    //@ ens stack(stack) &*& nodes(head, count) &*& result == count;
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, _);
        let mut n = head;
        let mut i = 0;
        //@ close nodes(head, _);
        //@ close stack(stack);
        
        //@ invariant nodes(n, ?rem) &*& i >= 0 &*& i + rem == count;
        loop {
            //@ open nodes(n, _);
            if n.is_null() {
                //@ close nodes(std::ptr::null_mut(), 0);
                break;
            }
            n = (*n).next;
            i += 1;
            //@ close nodes(n, _);
        }
        
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req stack(stack) &*& nodes(?head1, ?c1) &*& stack(other) &*& nodes(?head2, ?c2);
    //@ ens stack(stack) &*& nodes(head2, c2) &*& head1 == (*stack).head &*& c1 + c2 == ?c &*& nodes(head2, c);
    {
        //@ open stack(other);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            //@ open nodes(head0, _);
            //@ close nodes(head0, _);
            
            //@ invariant nodes(n, ?rem) &*& rem >= 1;
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
                //@ open nodes(n, _);
                //@ close nodes(n, _);
            }
            
            //@ open stack(stack);
            (*n).next = (*stack).head;
            (*stack).head = head0;
            //@ close stack(stack);
        } else {
            //@ open nodes(std::ptr::null_mut(), 0);
            //@ close nodes(std::ptr::null_mut(), 0);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack) &*& nodes(?head, ?count);
    //@ ens stack(stack) &*& nodes((*stack).head, count + 1);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, count + 1);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& nodes(?head, ?count) &*& count >= 1;
    //@ ens stack(stack) &*& nodes((*stack).head, count - 1) &*& result == (*head).value;
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack) &*& nodes(?head, _);
    //@ ens true;
    {
        //@ open stack(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
//@ req true;
//@ ens true;
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