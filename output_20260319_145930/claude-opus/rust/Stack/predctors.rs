use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred Nodes<T>(n: *mut Node<T>, count: i32) =
    if n == 0 {
        count == 0
    } else {
        count > 0 &*&
        alloc_block_Node::<T>(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        Nodes::<T>(next, count - 1)
    };

pred Stack<T>(s: *mut Stack<T>, count: i32) =
    alloc_block_Stack::<T>(s) &*&
    (*s).head |-> ?head &*&
    Nodes::<T>(head, count) &*&
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
        //@ close Nodes::<T>(std::ptr::null_mut(), 0);
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

/*@

pred Vector(v: *mut Vector, limit: i32) =
    alloc_block_Vector(v) &*&
    (*v).x |-> ?x &*&
    (*v).y |-> ?y &*&
    x * x + y * y <= limit * limit;

pred VectorStack(s: *mut Stack<*mut Vector>, count: i32, limit: i32) =
    Stack::<*mut Vector>(s, count) &*&
    VectorNodes(s, count, limit);

pred VectorNodes(s: *mut Stack<*mut Vector>, count: i32, limit: i32) =
    count >= 0;

@*/

impl Vector {

    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ req x * x + y * y <= limit * limit;
    //@ ens Vector(result, limit);
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector(result, limit);
        result
    }
    
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        
        loop {
            //@ inv Stack::<*mut Vector>(s, ?count) &*& count >= 0;
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    //@ open Vector(v, limit);
                    Stack::push(s, v);
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    
                    
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ open Vector(sum, limit);
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    
                    
                    std::hint::assert_unchecked((*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}