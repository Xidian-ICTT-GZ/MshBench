use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred Nodes<T>(node: *mut Node<T>, count: i32) =
    if node == 0 {
        count == 0
    } else {
        count > 0 &*&
        alloc_block_Node::<T>(node) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?value &*&
        Nodes::<T>(next, count - 1)
    };

pred Stack<T>(stack: *mut Stack<T>, count: i32) =
    alloc_block_Stack::<T>(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes::<T>(head, count) &*&
    count >= 0;

pred Vector(v: *mut Vector) =
    alloc_block_Vector(v) &*&
    (*v).x |-> _ &*&
    (*v).y |-> _;

pred Vectors(node: *mut Node<*mut Vector>, count: i32) =
    if node == 0 {
        count == 0
    } else {
        count > 0 &*&
        alloc_block_Node::<*mut Vector>(node) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?v &*&
        Vector(v) &*&
        Vectors(next, count - 1)
    };

pred VectorStack(stack: *mut Stack<*mut Vector>, count: i32) =
    alloc_block_Stack::<*mut Vector>(stack) &*&
    (*stack).head |-> ?head &*&
    Vectors(head, count) &*&
    count >= 0;

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens Stack::<T>(result, 0);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes::<T>(0 as *mut Node<T>, 0);
        //@ close Stack::<T>(stack, 0);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req Stack::<T>(stack, ?count);
    //@ ens Stack::<T>(stack, count + 1);
    {
        //@ open Stack::<T>(stack, count);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Nodes::<T>(n, count + 1);
        //@ close Stack::<T>(stack, count + 1);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req Stack::<T>(stack, ?count);
    //@ ens Stack::<T>(stack, count) &*& result == (count == 0);
    {
        //@ open Stack::<T>(stack, count);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, count);
        let result = head.is_null();
        //@ close Nodes::<T>(head, count);
        //@ close Stack::<T>(stack, count);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req Stack::<T>(stack, ?count) &*& count > 0;
    //@ ens Stack::<T>(stack, count - 1);
    {
        //@ open Stack::<T>(stack, count);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, count);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack::<T>(stack, count - 1);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack::<T>(stack, 0);
    //@ ens true;
    {
        //@ open Stack::<T>(stack, 0);
        //@ open Nodes::<T>(_, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_char() -> char
//@ req true;
//@ ens true;
//@ assume_correct
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32
//@ req true;
//@ ens true;
//@ assume_correct
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens Vector(result);
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector(result);
        result
    }
    
}

unsafe fn push_vector(stack: *mut Stack<*mut Vector>, v: *mut Vector, count: i32)
//@ req VectorStack(stack, count) &*& Vector(v);
//@ ens VectorStack(stack, count + 1);
{
    //@ open VectorStack(stack, count);
    let n = alloc(Layout::new::<Node<*mut Vector>>()) as *mut Node<*mut Vector>;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node<*mut Vector>>());
    }
    (*n).next = (*stack).head;
    (&raw mut (*n).value).write(v);
    (*stack).head = n;
    //@ close Vectors(n, count + 1);
    //@ close VectorStack(stack, count + 1);
}

unsafe fn is_empty_vector(stack: *mut Stack<*mut Vector>, count: i32) -> bool
//@ req VectorStack(stack, count);
//@ ens VectorStack(stack, count) &*& result == (count == 0);
{
    //@ open VectorStack(stack, count);
    let head = (*stack).head;
    //@ open Vectors(head, count);
    let result = head.is_null();
    //@ close Vectors(head, count);
    //@ close VectorStack(stack, count);
    result
}

unsafe fn pop_vector(stack: *mut Stack<*mut Vector>, count: i32) -> *mut Vector
//@ req VectorStack(stack, count) &*& count > 0;
//@ ens VectorStack(stack, count - 1) &*& Vector(result);
{
    //@ open VectorStack(stack, count);
    let head = (*stack).head;
    //@ open Vectors(head, count);
    (*stack).head = (*head).next;
    let result = (&raw mut (*head).value).read();
    dealloc(head as *mut u8, Layout::new::<Node<*mut Vector>>());
    //@ close VectorStack(stack, count - 1);
    result
}

unsafe fn create_vector_stack() -> *mut Stack<*mut Vector>
//@ req true;
//@ ens VectorStack(result, 0);
{
    let stack = alloc(Layout::new::<Stack<*mut Vector>>()) as *mut Stack<*mut Vector>;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack<*mut Vector>>());
    }
    (*stack).head = std::ptr::null_mut();
    //@ close Vectors(0 as *mut Node<*mut Vector>, 0);
    //@ close VectorStack(stack, 0);
    stack
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = create_vector_stack();
        let mut count: i32 = 0;
        //@ assert VectorStack(s, 0);
        loop {
            //@ inv VectorStack(s, count) &*& count >= 0;
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    push_vector(s, v, count);
                    count = count + 1;
                }
                '+' => {
                    assert!(!is_empty_vector(s, count), "Stack underflow");
                    //@ assert count > 0;
                    let v1 = pop_vector(s, count);
                    count = count - 1;
                    //@ open Vector(v1);
                    assert!(!is_empty_vector(s, count), "Stack underflow");
                    //@ assert count > 0;
                    let v2 = pop_vector(s, count);
                    count = count - 1;
                    //@ open Vector(v2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    push_vector(s, sum, count);
                    count = count + 1;
                }
                '=' => {
                    assert!(!is_empty_vector(s, count), "Stack underflow");
                    //@ assert count > 0;
                    let v_ = pop_vector(s, count);
                    count = count - 1;
                    //@ open Vector(v_);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}