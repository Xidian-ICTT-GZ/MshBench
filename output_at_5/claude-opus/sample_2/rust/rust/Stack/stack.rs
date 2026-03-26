use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate node(struct n: *mut Node, int val, struct next) =
//@     n->value |-> val &*& n->next |-> next;

//@ fixpoint list<int> ltail(list<int> xs) {
//@     switch(xs) {
//@         case Nil => Nil;
//@         case Cons(x, xs0) => xs0;
//@     }
//@ }

//@ predicate list_nodes(struct n: *mut Node, list<int> vs) =
//@     switch(vs) {
//@         case Nil => n == std::ptr::null_mut() &*& emp;
//@         case Cons(head_val, tail_vals) =>
//@             node(n, head_val, ?next) &*& list_nodes(next, tail_vals);
//@     };

//@ predicate stack(struct s: *mut Stack, list<int> vs) =
//@     s->head |-> ?h &*& list_nodes(h, vs);

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
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, value, ?old_head);
        //@ close stack(stack, Cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vs) &*& vs != Nil;
    //@ ensures stack(stack, ltail(vs)) &*& result == vs.head;
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open node(head, ?v, ?next);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, ltail(vs));
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