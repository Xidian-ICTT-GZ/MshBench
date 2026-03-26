use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list<i32> vs, *mut Node p) =
    p == 0 ?
        vs == nil
    :
        alloc_block(p as *mut u8, Layout::new::<Node>()) &*&
        field_ptr(p, "next", ?nxt) &*&
        field_ptr(p, "value", ?v) &*&
        nodes(?vs0, nxt) &*&
        vs == cons(v, vs0);

pred stack(*mut Stack s; list<i32> vs) =
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    field_ptr(s, "head", ?h) &*&
    nodes(vs, h);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(nil, 0);
        //@ close stack(stack, nil);
        stack
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
        (*stack).head = n;
        //@ close field_ptr(n, "next", (*n).next);
        //@ close field_ptr(n, "value", value);
        //@ close nodes(cons(value, vs), n);
        //@ close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs) &*& vs != nil;
    //@ ens stack(stack, ?vs0) &*& vs == cons(result, vs0);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open nodes(vs, head);
        //@ open field_ptr(head, "value", ?v);
        //@ open field_ptr(head, "next", ?nxt);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes(?vs0, nxt);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs0);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, nil);
    //@ ens true;
    {
        //@ open stack(stack, nil);
        //@ open nodes(nil, _);
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