use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(*n: *mut Node, list: list<int>) = 
    n |-> Node(next: nxt, value: v) &*& nodes(nxt, ?tail) &*& list == cons(v, tail)
    ;
predicate nodes(null_mut(), nil) = true;

predicate stack(*s: *mut Stack, list: list<int>) =
    s |-> Stack(head: hd) &*& nodes(hd, list);

#[requires(nodes(n, ?list))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node)
    //@ requires nodes(n, list);
    //@ ensures true;
{
    if !n.is_null() {
        let nxt = (*n).next;
        dispose_nodes(nxt);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        return stack;
    }

    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, list))]
    #[ensures(result == (list == nil))]
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ requires stack(stack, list);
    //@ ensures stack(stack, list) &*& result == (list == nil);
    {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        return result;
    }

    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, cons(value, list)))]
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, list);
    //@ ensures stack(stack, cons(value, list));
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, ?list)) &*& list != nil]
    #[ensures(stack(stack, tail))] 
    #[ensures(result == head_value)]
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, list);
    //@ requires list != nil;
    //@ ensures stack(stack, tail);
    //@ ensures result == head_value;
    {
        let head = (*stack).head;
        let head_value = switch list { case cons(h, t) => h };
        let tail = switch list { case cons(h, t) => t };
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    #[requires(stack(stack, ?list))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, list);
    //@ ensures true;
    {
        dispose_nodes((*stack).head);
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