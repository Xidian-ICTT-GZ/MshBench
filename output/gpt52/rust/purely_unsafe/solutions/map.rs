use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

/*@

predicate node(struct Node *n; struct Node *next, i32 value) =
    n->next |-> next &*& n->value |-> value;

predicate nodes(struct Node *n; list<i32> vs) =
    n == 0 ?
        vs == nil
    :
        node(n, ?next, ?v) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate stack(struct Stack *s; list<i32> vs) =
    s->head |-> ?h &*& nodes(h, vs);

predicate i32_cell(i32 *p; i32 v) =
    *p |-> v;

/* A functional contract for callbacks used by map_nodes/map. */
predicate i32_func(I32Func f; predicate(*mut u8;_) ctx) = true;

@*/

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
/*@ requires nodes(n, ?vs) &*& i32_func(f, ?ctx) &*& ctx(data, ?a0); @*/
/*@ ensures nodes(n, ?vs2) &*& i32_func(f, ctx) &*& ctx(data, ?a1); @*/
{
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
/*@ requires nodes(n, ?vs); @*/
/*@ ensures true; @*/
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    /*@ requires true; @*/
    /*@ ensures stack(result, nil); @*/
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    /*@ requires stack(stack, ?vs); @*/
    /*@ ensures stack(stack, cons(value, vs)); @*/
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
    /*@ requires stack(stack, cons(?v, ?vs0)); @*/
    /*@ ensures stack(stack, vs0) &*& result == v; @*/
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    /*@ requires stack(stack, ?vs) &*& i32_func(f, ?ctx) &*& ctx(data, ?a0); @*/
    /*@ ensures stack(stack, ?vs2) &*& i32_func(f, ctx) &*& ctx(data, ?a1); @*/
    {
        map_nodes((*stack).head, f, data);
    }

    unsafe fn dispose(stack: *mut Stack)
    /*@ requires stack(stack, ?vs); @*/
    /*@ ensures true; @*/
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
/*@ requires i32_cell(data as *mut i32, ?a); @*/
/*@ ensures i32_cell(data as *mut i32, a) &*& result == x + a; @*/
{
    let result = x + *(data as *mut i32);

    result
}

unsafe fn read_i32() -> i32
/*@ requires true; @*/
/*@ ensures true; @*/
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
/*@ requires true; @*/
/*@ ensures true; @*/
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        //@ close i32_cell(&raw mut a, a);

        Stack::map(s, plus_a, &raw mut a as *mut u8);

        //@ open i32_cell(&raw mut a, _);
        Stack::dispose(s);
    }
}