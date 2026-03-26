use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(n: &Node, val: int, next: *mut Node) =
//@     n.value |-> val &*& n.next |-> next;

//@ fixpoint list<int> tail(list<int> xs) {
//@     switch(xs) {
//@         case Nil => Nil;
//@         case Cons(x, xs0) => xs0;
//@     }
//@ }

//@ pred list_nodes(n: *mut Node, vs: list<int>) =
//@     switch(vs) {
//@         case Nil => n == null &*& emp;
//@         case Cons(head_val, tail_vals) =>
//@             n != null &*& node(&*n, head_val, ?next) &*& list_nodes(next, tail_vals);
//@     };

//@ pred stack(s: *mut Stack, vs: list<int>) =
//@     s != null &*& s->head |-> ?h &*& list_nodes(h, vs);

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, Nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, Nil);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, Cons(value, vs));
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(&*n, value, (*stack).head);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close stack(stack, Cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vs) &*& vs != Nil;
    //@ ensures stack(stack, tail(vs)) &*& result == head(vs);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open node(&*head, ?v, ?next);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, tail(vs));
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, Nil);
    //@ ensures true;
    {
        //@ open stack(stack, Nil);
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