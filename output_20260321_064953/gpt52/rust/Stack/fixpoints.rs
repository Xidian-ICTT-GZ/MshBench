use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes_list(node: *mut Node; elems: list<i32>) =
    node == std::ptr::null_mut() ?
        elems == nil
    :
        (*node).next |-> ?nxt &*&
        (*node).value |-> ?v &*&
        std::alloc::alloc_block(node as *mut u8, Layout::new::<Node>()) &*&
        nodes_list(nxt, ?es) &*& elems == cons(v, es);

pred stack(stack: *mut Stack; elems: list<i32>) =
    (*stack).head |-> ?h &*&
    std::alloc::alloc_block(stack as *mut u8, Layout::new::<Stack>()) &*&
    nodes_list(h, elems);

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
        //@ assume(!stack.is_null());
        //@ close stack(stack, nil);
        (*stack).head = std::ptr::null_mut();
        //@ open stack(stack, nil);
        //@ close stack(stack, nil);

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?es);
    //@ ens stack(stack, cons(value, es));
    {
        //@ open stack(stack, es);

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ assume(!n.is_null());
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes_list(n, cons(value, es));
        (*stack).head = n;

        //@ close stack(stack, cons(value, es));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?v, ?vs));
    //@ ens stack(stack, vs) &*& result == v;
    {
        //@ open stack(stack, cons(v, vs));
        //@ open nodes_list((*stack).head, cons(v, vs));

        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open nodes_list((*head).next, vs);
        //@ close nodes_list((*head).next, vs);
        dealloc(head as *mut u8, Layout::new::<Node>());

        //@ close stack(stack, vs);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, nil);
    //@ ens true;
    {
        //@ open stack(stack, nil);
        //@ open nodes_list((*stack).head, nil);

        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
        let _ = result1;
        let _ = result2;
    }
}