use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
predicate node(Node *n) =
    n != 0 &*&
    n->next |-> ?next &*&
    n->value |-> ?value &*&
    (next == 0 ? true : node(next));
@*/

struct Stack {
    head: *mut Node,
}

/*@
predicate stack(Stack *s) =
    s != 0 &*&
    s->head |-> ?head &*&
    (head == 0 ? true : node(head));
@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
    //@ requires n == std::ptr::null_mut() ? true : node(n);
    //@ ensures n == std::ptr::null_mut() ? true : node(n);
{
    if !n.is_null() {
        //@ open node(n);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close node(n);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    //@ requires n == std::ptr::null_mut() ? true : node(n);
    //@ ensures true;
{
    if !n.is_null() {
        //@ open node(n);
        dispose_nodes((*n).next);
        //@ close node(n);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        return stack;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open node(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        map_nodes((*stack).head, f, data);
        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack);
    //@ ensures true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
    //@ requires true;
    //@ ensures true;
{
    let result = x + *(data as *mut i32);
    result
}

unsafe fn read_i32() -> i32
    //@ requires true;
    //@ ensures true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();

        Stack::map(s, plus_a, &raw mut a as *mut u8);

        Stack::dispose(s);
    }
}