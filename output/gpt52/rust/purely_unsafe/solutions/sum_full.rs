use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node(p: *mut Node, next: *mut Node, v: i32) =
    p->next |-> next &*& p->value |-> v;

predicate nodes(p: *mut Node; xs: list<i32>) =
    p == 0 ?
        xs == nil
    :
        node(p, ?n, ?v) &*& nodes(n; ?xs0) &*& xs == cons(v, xs0);

predicate stack(s: *mut Stack; xs: list<i32>) =
    s->head |-> ?h &*& nodes(h; xs);

@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
/*@
requires nodes(node; ?xs);
ensures nodes(node; xs) &*& result == sum(xs);
@*/
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
    /*@
    requires true;
    ensures stack(result; nil);
    @*/
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    /*@
    requires stack(stack; ?xs);
    ensures stack(stack; xs) &*& result == sum(xs);
    @*/
    {
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    /*@
    requires stack(stack; ?xs);
    ensures stack(stack; cons(value, xs));
    @*/
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
    /*@
    requires stack(stack; ?xs) &*& xs != nil;
    ensures stack(stack; tail(xs)) &*& result == head(xs);
    @*/
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack)
    /*@
    requires stack(stack; ?xs) &*& xs == nil;
    ensures true;
    @*/
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
/*@
requires true;
ensures true;
@*/
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);

        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}