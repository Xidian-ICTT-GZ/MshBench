use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate node(struct Node *node; struct Node *next, i32 value) =
//@     node != 0 &*&
//@     struct_Node_padding(node) &*&
//@     (*node).next |-> next &*&
//@     (*node).value |-> value;

//@ predicate nodes(struct Node *n) =
//@     n == 0 ? true : node(n, ?next, ?value) &*& nodes(next);

//@ predicate stack(struct Stack *stack) =
//@     stack != 0 &*&
//@     struct_Stack_padding(stack) &*&
//@     (*stack).head |-> ?head &*&
//@     nodes(head);

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
//@ req nodes(n) &*& [?q]integer(data, _);
//@ ens nodes(n) &*& [q]integer(data, _);
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open node(n, _, _);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close node(n, _, _);
    }
    //@ close nodes(n);
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open node(n, _, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack);
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, old_head, value);
        //@ close nodes(n);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head != 0;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        //@ open nodes(head);
        //@ open node(head, _, _);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes(next);
        //@ close stack(stack);
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    //@ req stack(stack) &*& [?q]integer(data, _);
    //@ ens stack(stack) &*& [q]integer(data, _);
    {
        //@ open stack(stack);
        map_nodes((*stack).head, f, data);
        //@ close stack(stack);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
//@ req integer(data, ?a);
//@ ens integer(data, a) &*& result == x + a;
{
    //@ open integer(data, _);
    let result = x + *(data as *mut i32);
    //@ close integer(data, _);
    result
}

unsafe fn read_i32() -> i32
//@ req true;
//@ ens true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        //@ close integer(&raw mut a, a);
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        //@ open integer(&raw mut a, _);
        Stack::dispose(s);
    }
}