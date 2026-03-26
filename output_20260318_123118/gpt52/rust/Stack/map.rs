use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node(struct Node* n; struct Node* next, i32 value) =
    n != 0 &*&
    n->next |-> next &*&
    n->value |-> value;

predicate nodes(struct Node* n) =
    n == 0 ?
        emp
    :
        node(n, ?next, ?value) &*& nodes(next);

predicate stack(struct Stack* s) =
    s != 0 &*&
    s->head |-> ?h &*& nodes(h);

predicate i32_cell(struct i32* p; i32 v) =
    p != 0 &*& *p |-> v;

@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
/*@
requires nodes(n) &*& i32_cell((struct i32*)data, ?a);
ensures nodes(n) &*& i32_cell((struct i32*)data, a);
@*/
{
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
/*@
requires nodes(n);
ensures emp;
@*/
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    /*@
    requires emp;
    ensures stack(result);
    @*/
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        return stack;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    /*@
    requires stack(stack);
    ensures stack(stack);
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
    requires stack(stack) &*& stack->head |-> ?h &*& h != 0;
    ensures stack(stack);
    @*/
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    /*@
    requires stack(stack) &*& i32_cell((struct i32*)data, ?a);
    ensures stack(stack) &*& i32_cell((struct i32*)data, a);
    @*/
    {
        map_nodes((*stack).head, f, data);
    }

    unsafe fn dispose(stack: *mut Stack)
    /*@
    requires stack(stack);
    ensures emp;
    @*/
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
/*@
requires i32_cell((struct i32*)data, ?a);
ensures i32_cell((struct i32*)data, a) &*& result == x + a;
@*/
{
    let result = x + *(data as *mut i32);

    result
}

unsafe fn read_i32() -> i32
/*@
requires emp;
ensures emp;
@*/
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
/*@
requires emp;
ensures emp;
@*/
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();

        /*@
        close i32_cell(&a, a);
        @*/
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        /*@
        open i32_cell(&a, ?av);
        @*/

        Stack::dispose(s);
    }
}