use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

/*@
pred lseg(first: *mut Node, last: *mut Node) =
    if (first == last) {
        true
    } else {
        Node(first, ?next, ?val) &*& lseg(next, last)
    };
@*/

/*@
pred Stack(stack: *mut Stack) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    lseg(head, std::ptr::null_mut());
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close lseg(std::ptr::null_mut(), std::ptr::null_mut());
        //@ close Stack(stack);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        //@ close lseg(head, head);
        //@ open lseg(head, head);
        //@ if (head != std::ptr::null_mut()) { open Node(head, _, _); }
        loop {
            //@ inv lseg(head, n) &*& i >= 0;
            if n.is_null() {
                break;
            }
            //@ open Node(n, ?next, _);
            n = (*n).next;
            i += 1;
            //@ close lseg(n, n);
            //@ open lseg(n, n);
        }
        //@ close lseg(head, std::ptr::null_mut());
        //@ close Stack(stack);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack(stack) &*& Stack(other);
    //@ ens Stack(stack);
    {
        //@ open Stack(other);
        let head0 = (*other).head;
        //@ open lseg(head0, std::ptr::null_mut());
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            //@ close lseg(head0, head0);
            //@ open lseg(head0, head0);
            //@ open Node(head0, ?next0, _);
            loop {
                //@ inv lseg(head0, n) &*& Node(n, ?next, ?val);
                if (*n).next.is_null() {
                    break;
                }
                //@ open Node((*n).next, ?nextnext, ?nextval);
                n = (*n).next;
                //@ close lseg(n, n);
                //@ open lseg(n, n);
            }
            //@ open Stack(stack);
            (*n).next = (*stack).head;
            //@ close lseg((*stack).head, std::ptr::null_mut());
            (*stack).head = head0;
            //@ close lseg(head0, std::ptr::null_mut());
            //@ close Stack(stack);
        } else {
            //@ close Stack(stack);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node(n, (*stack).head, value);
        //@ close lseg((*stack).head, std::ptr::null_mut());
        (*stack).head = n;
        //@ close lseg(n, std::ptr::null_mut());
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open lseg(head, std::ptr::null_mut());
        //@ open Node(head, ?next, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close lseg((*stack).head, std::ptr::null_mut());
        //@ close Stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack);
    //@ ens true;
    {
        //@ open Stack(stack);
        //@ open lseg((*stack).head, std::ptr::null_mut());
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