use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred Stack(stack: *mut Stack; head: *mut Node) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        Node(n, ?next, ?value) &*& nodes(next);
@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

//@ req nodes(n) &*& [?q]func(f, data);
//@ ens nodes(n);
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open Node(n, _, _);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close Node(n, (*n).next, y);
    }
    //@ close nodes(n);
}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open Node(n, _, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    //@ req true;
    //@ ens Stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack, std::ptr::null_mut());
        return stack;
    }
    
    //@ req Stack(stack, ?head);
    //@ ens Stack(stack, ?new_head) &*& Node(new_head, head, value);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open Stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node(n, head, value);
        //@ close Stack(stack, n);
    }

    //@ req Stack(stack, ?head) &*& head != std::ptr::null_mut() &*& Node(head, ?next, ?value);
    //@ ens Stack(stack, next) &*& result == value;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack, head);
        let head = (*stack).head;
        //@ open Node(head, next, value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, next);
        return result;
    }
    
    //@ req Stack(stack, ?head) &*& [?q]func(f, data);
    //@ ens Stack(stack, head);
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    {
        //@ open Stack(stack, head);
        map_nodes((*stack).head, f, data);
        //@ close Stack(stack, head);
    }
    
    //@ req Stack(stack, ?head);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open Stack(stack, head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

//@ req *(data as *mut i32) |-> ?a;
//@ ens *(data as *mut i32) |-> a &*& result == x + a;
unsafe fn plus_a(data: *mut u8, x: i32) -> i32
{
    let result = x + *(data as *mut i32);
    result
}

//@ assume_correct
unsafe fn read_i32() -> i32
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
        //@ close exists(a);
        //@ produce_fn_ptr_chunk i32_func(plus_a)(data) { true } { *(data as *mut i32) |-> ?a } { *(data as *mut i32) |-> a &*& result == x + a }();
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        Stack::dispose(s);
    }
}