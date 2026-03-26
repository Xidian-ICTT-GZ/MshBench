use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
/*@

pred nodes(list<int> xs, *mut Node p) =
    p == std::ptr::null_mut() ? xs == [] : 
    p |-> Node { next: ?n, value: ?v } &*& nodes(?tl, n) &*& xs == cons(v, tl);

@*/

struct Stack {
    head: *mut Node,
}
/*@
pred stack(s: *mut Stack, list<int> xs) =
    s |-> Stack { head: ?h } &*& nodes(xs, h);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    //@ requires nodes(?xs);
    //@ ensures nodes(xs) &*& result == fold_int_add(xs, 0);
{
    let mut result = 0;
    if !nodes.is_null() {
        //@ open nodes(?xs, nodes);
        //@ assert nodes == nodes(xs);
        //@ open nodes(xs, nodes);
        //@ open nodes(?tl, (*nodes).next);
        //@ open nodes(tl, (*nodes).next);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(xs, nodes);
    }
    //@ close nodes(?_xs, nodes);
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        //@ requires true;
        //@ ensures stack(result, []);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes([], std::ptr::null_mut());
        //@ close stack(stack, []);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        //@ requires stack(stack, ?xs);
        //@ ensures stack(stack, xs);
    {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ assert stack(stack, xs);
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        //@ requires stack(stack, ?xs);
        //@ ensures stack(stack, xs) &*& result == fold_int_add(xs, 0);
    {
        //@ open stack(stack, xs);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, xs);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        //@ requires stack(stack, ?xs);
        //@ ensures stack(stack, cons(value, xs));
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ open stack(stack, xs);
        //@ close nodes(xs, (*stack).head.next);
        //@ close nodes(cons(value, xs), n);
        //@ close stack(stack, cons(value, xs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        //@ requires stack(stack, ?xs) &*& xs != [];
        //@ ensures stack(stack, tail(xs)) &*& result == head(xs);
    {
        //@ open stack(stack, xs);
        let head = (*stack).head;
        //@ open nodes(xs, head);
        //@ assert head |-> Node{next: ?next_node, value: ?v};
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes(tail(xs), (*stack).head);
        //@ close stack(stack, tail(xs));
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        //@ requires stack(stack, ?xs);
        //@ ensures true;
    {
        //@ open stack(stack, xs);
        let mut n = (*stack).head;
        loop {
            //@ if (n == std::ptr::null_mut()) {
            //@     close nodes([], n);
            //@ }
            if n.is_null() {
                break;
            }
            //@ open nodes(?ys, n);
            //@ assert n |-> Node { next: ?next, value: _ };
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}

/*@
fixpoint int fold_int_add(list<int> xs, int init) {
    switch(xs) {
        case nil: return init;
        case cons(h, t): return fold_int_add(t, init + h);
    }
}
@*/