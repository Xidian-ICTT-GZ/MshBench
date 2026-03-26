use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(p: *mut Node, contents: list<i32>) = 
//@     if p == std::ptr::null_mut() { emp } 
//@     else p |-> Node { next: ?next, value: ?v } &*& nodes(next, ?tail) &*& contents == cons(v, tail);

//@ pred stack(s: *mut Stack, contents: list<i32>) = s |-> Stack { head: ?head } &*& nodes(head, contents);

// verifast_options{}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        result: *mut Stack = stack;
        result
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?contents);
    //@ ensures stack(stack, contents) &*& result == length(contents);
    {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        loop
        //@ invariant nodes(n, ?rest) &*& i == length(contents) - length(rest);
        {
            if n.is_null() {
                break;
            }

            //@ open nodes(n, ?lst);
            n = (*n).next;
            i += 1;
        }

        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ requires stack(stack, ?c1) &*& stack(other, ?c2);
    //@ ensures stack(stack, append(c2, c1));
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());

        let mut n = head0;

        if !n.is_null() {

            loop
            //@ invariant n != std::ptr::null_mut() &*& nodes(n, ?rest);
            {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?contents);
    //@ ensures stack(stack, cons(value, contents));
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?contents) &*& contents != nil;
    //@ ensures stack(stack, tail(contents)) &*& result == head(contents);
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, nil);
    //@ ensures true;
    {
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