use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node_ptr(*mut Node n; *mut Node next, i32 value) =
    n != 0 &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

predicate nodes(*mut Node h; list<i32> vs) =
    h == 0 ?
        vs == nil
    :
        exists::<*mut Node>(?nxt) &*& exists::<i32>(?v) &*&
        node_ptr(h; nxt, v) &*&
        nodes(nxt; ?vs0) &*&
        vs == cons(v, vs0);

predicate stack_ptr(*mut Stack s; list<i32> vs) =
    s != 0 &*&
    (*s).head |-> ?h &*&
    nodes(h; vs);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(stack_ptr(result, nil))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes(0, nil);
        //@ close stack_ptr(stack, nil);
        stack
    }

    #[requires(stack_ptr(stack, ?vs))]
    #[ensures(stack_ptr(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack_ptr(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open nodes(?h0, vs);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node_ptr(n; h0, value);
        //@ close nodes(n, cons(value, vs));
        //@ close stack_ptr(stack, cons(value, vs));
    }

    #[requires(stack_ptr(stack, cons(?v, ?vs0)))]
    #[ensures(stack_ptr(stack, vs0) &*& result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack_ptr(stack, cons(v, vs0));
        let head = (*stack).head;
        //@ open nodes(head, cons(v, vs0));
        //@ open node_ptr(head; ?nxt, v);

        let result = (*head).value;
        (*stack).head = (*head).next;

        //@ close nodes(nxt, vs0);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_ptr(stack, vs0);

        result
    }

    #[requires(stack_ptr(stack, nil))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack_ptr(stack, nil);
        //@ open nodes(?h, nil);
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