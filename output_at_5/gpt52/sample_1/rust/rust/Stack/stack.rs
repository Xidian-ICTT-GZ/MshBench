use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list<Node> vs, *mut Node p) =
    p == std::ptr::null_mut() ?
        vs == nil
    :
        std::alloc::alloc_block(p as *mut u8, Layout::new::<Node>()) &*&
        std::ptr::field(p, "next", ?nxt) &*&
        std::ptr::field(p, "value", ?v) &*&
        nodes(?vs0, nxt) &*&
        vs == cons(Node { next: nxt, value: v }, vs0);

pred stack(*mut Stack s; list<Node> vs) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    std::ptr::field(s, "head", ?h) &*&
    nodes(vs, h);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result == std::ptr::null_mut() ? true : stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(nil, std::ptr::null_mut());
        //@ close stack(stack, nil);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(Node { next: _, value: value }, vs));
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ open nodes(vs, (*n).next);
        //@ close nodes(vs, (*n).next);
        //@ close nodes(cons(Node { next: (*n).next, value: value }, vs), n);
        //@ close stack(stack, cons(Node { next: (*n).next, value: value }, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs) &*& vs != nil;
    //@ ens stack(stack, ?vs0) &*& vs == cons(?n, vs0) &*& result == n.value;
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open nodes(vs, head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open nodes(?vs0, (*head).next);
        //@ close nodes(vs0, (*head).next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs0);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?vs);
    //@ ens true;
    {
        //@ open stack(stack, vs);
        //@ open nodes(vs, _);
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