use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred Node(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred Stack(stack: *mut Stack; head: *mut Node) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

/*@
pred lseg(start: *mut Node, end: *mut Node) =
    start == end ?
        true
    :
        Node(start, ?next, ?value) &*& lseg(next, end);
@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
//@ req lseg(n, 0) &*& [?q]alloc_block(data, 1);
//@ ens lseg(n, 0) &*& [q]alloc_block(data, 1);
{
    if !n.is_null() {
        //@ open lseg(n, 0);
        //@ open Node(n, _, _);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close Node(n, (*n).next, y);
        //@ close lseg(n, 0);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req lseg(n, 0);
//@ ens true;
{
    if !n.is_null() {
        //@ open lseg(n, 0);
        //@ open Node(n, ?next, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack, 0);
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?head);
    //@ ens Stack(stack, ?newHead) &*& Node(newHead, head, value);
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

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?head) &*& head != 0 &*& Node(head, ?next, ?value);
    //@ ens Stack(stack, next) &*& value == result;
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
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    //@ req Stack(stack, ?head) &*& [?q]alloc_block(data, 1);
    //@ ens Stack(stack, head) &*& [q]alloc_block(data, 1);
    {
        //@ open Stack(stack, head);
        map_nodes((*stack).head, f, data);
        //@ close Stack(stack, head);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, ?head);
    //@ ens true;
    {
        //@ open Stack(stack, head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
//@ req [?q]alloc_block(data, 1) &*& *(data as *mut i32) |-> ?a;
//@ ens [q]alloc_block(data, 1) &*& *(data as *mut i32) |-> a &*& result == x + a;
{
    //@ assume_correct;
    let result = x + *(data as *mut i32);
    result
}

unsafe fn read_i32() -> i32
//@ req true;
//@ ens true;
{
    //@ assume_correct;
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
        //@ close alloc_block(&raw mut a as *mut u8, 1);
        //@ close *( &raw mut a as *mut i32) |-> a;
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        //@ open *( &raw mut a as *mut i32) |-> _;
        //@ open alloc_block(&raw mut a as *mut u8, 1);
        Stack::dispose(s);
    }
}