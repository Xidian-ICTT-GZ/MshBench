use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node; count: i32) =
    if n == 0 {
        count == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, ?count0) &*&
        count == count0 + 1
    };

pred Stack(s: *mut Stack; count: i32) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, count);

pred_ctor I32Func_pre(f: I32Func, data: *mut u8)(x: i32) = true;
pred_ctor I32Func_post(f: I32Func, data: *mut u8)(x: i32, result: i32) = true;

pred I32Func_data(f: I32Func, data: *mut u8) = true;

@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
//@ req Nodes(n, ?count) &*& I32Func_data(f, data);
//@ ens Nodes(n, count) &*& I32Func_data(f, data);
{
    //@ open Nodes(n, count);
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
    //@ close Nodes(n, count);
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, ?count);
//@ ens true;
{
    //@ open Nodes(n, count);
    if !n.is_null() {
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
        //@ close Nodes(0 as *mut Node, 0);
        //@ close Stack(stack, 0);
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count + 1);
    {
        //@ open Stack(stack, count);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, count + 1);
        //@ close Stack(stack, count + 1);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count) &*& count > 0;
    //@ ens Stack(stack, count - 1);
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ open Nodes(head, count);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, count - 1);
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    //@ req Stack(stack, ?count) &*& I32Func_data(f, data);
    //@ ens Stack(stack, count) &*& I32Func_data(f, data);
    {
        //@ open Stack(stack, count);
        map_nodes((*stack).head, f, data);
        //@ close Stack(stack, count);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, ?count);
    //@ ens true;
    {
        //@ open Stack(stack, count);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
//@ req true;
//@ ens true;
{
    //@ assume_correct
    let result = x + *(data as *mut i32);
    
    result
}

unsafe fn read_i32() -> i32
//@ req true;
//@ ens true;
//@ assume_correct
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
        //@ close I32Func_data(plus_a, &raw mut a as *mut u8);
        
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        //@ open I32Func_data(plus_a, &raw mut a as *mut u8);
        Stack::dispose(s);
    }
}