use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens ptr::non_null(result) &*& StackOwned(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackOwned(stack);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req StackOwned(stack);
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(stack);
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        //@ close nodes(n, 0);
        loop {
            //@ open nodes(n, _);
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
            //@ close nodes(n, i);
        }
        //@ open nodes(_, _);
        //@ close StackOwned(stack);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req StackOwned(stack) &*& StackOwned(other);
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(other);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            //@ close nodes(head0, 0);
            loop {
                //@ open nodes(n, _);
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
                //@ close nodes(n, _);
            }
            //@ open nodes(n, _);
            (*n).next = (*stack).head;
            //@ open StackOwned(stack);
            (*stack).head = head0;
            //@ close StackOwned(stack);
            //@ open nodes(head0, _);
        } else {
            //@ open StackOwned(stack);
            //@ close StackOwned(stack);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackOwned(stack);
    //@ ens StackOwned(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open StackOwned(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close StackOwned(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackOwned(stack) &*& (*stack).head != 0;
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(stack);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackOwned(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackOwned(stack);
    //@ ens true;
    {
        //@ open StackOwned(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

//@ predicate nodes(*mut Node n, i32 count) = n == 0 ? count == 0 : NodeOwned(n) &*& nodes((*n).next, count - 1);
//@ predicate NodeOwned(*mut Node n) = alloc::allocated(n, std::mem::size_of::<Node>(), _) &*& struct_Node_padding(n);
//@ predicate StackOwned(*mut Stack s) = alloc::allocated(s, std::mem::size_of::<Stack>(), _) &*& (*s).head |-> ?h &*& nodes(h, _) &*& struct_Stack_padding(s);

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