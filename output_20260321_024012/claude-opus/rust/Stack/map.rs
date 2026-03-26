use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

//@ predicate nodes(struct Node* n; ) = n == 0 ? emp : n->next |-> ?nx &*& n->value |-> _ &*& nodes(nx);
//@ predicate stack(struct Stack* s; ) = s->head |-> ?h &*& nodes(h);

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
//@ requires nodes(n);
//@ ensures nodes(n);
{
    if !n.is_null() {
        //@ open nodes(n);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close nodes(n);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ requires nodes(n);
//@ ensures emp;
{
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires emp;
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
        (*stack).head = n;
        //@ close nodes(n);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack) &*& exists<*mut Node>(|head| head != std::ptr::null_mut() &*& nodes(head));
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
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
    //@ ensures emp;
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