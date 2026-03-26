use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

predicate nodes<T>(node: *mut Node<T>; n: i32) =
    node == std::ptr::null_mut() ?
        n == 0
    :
        n > 0 &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?v &*&
        nodes::<T>(next, n - 1);

predicate stack<T>(s: *mut Stack<T>; n: i32) =
    (*s).head |-> ?h &*& nodes::<T>(h, n);

@*/

impl<T> Stack<T> {
    unsafe fn create() -> *mut Stack<T>
    //@ requires true;
    //@ ensures result != std::ptr::null_mut() &*& stack::<T>(result, 0);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes::<T>(std::ptr::null_mut(), 0);
        //@ close stack::<T>(stack, 0);
        stack
    }

    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires stack::<T>(stack, ?n);
    //@ ensures stack::<T>(stack, n + 1);
    {
        //@ open stack::<T>(stack, n);
        let nnode = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if nnode.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ open nodes::<T>((*stack).head, n);
        (*nnode).next = (*stack).head;
        (&raw mut (*nnode).value).write(value);
        (*stack).head = nnode;
        //@ close nodes::<T>((*nnode).next, n);
        //@ close nodes::<T>(nnode, n + 1);
        //@ close stack::<T>(stack, n + 1);
    }

    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ requires stack::<T>(stack, ?n);
    //@ ensures stack::<T>(stack, n);
    {
        //@ open stack::<T>(stack, n);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close stack::<T>(stack, n);
        result
    }

    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires stack::<T>(stack, ?n) &*& n > 0;
    //@ ensures stack::<T>(stack, n - 1);
    {
        //@ open stack::<T>(stack, n);
        let head = (*stack).head;
        //@ open nodes::<T>(head, n);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ close nodes::<T>((*head).next, n - 1);
        //@ close stack::<T>(stack, n - 1);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires stack::<T>(stack, 0);
    //@ ensures true;
    {
        //@ open stack::<T>(stack, 0);
        //@ open nodes::<T>((*stack).head, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

unsafe fn input_char() -> char
//@ requires true;
//@ ensures true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32
//@ requires true;
//@ ensures true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)
//@ requires true;
//@ ensures true;
{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

/*@

predicate vector(v: *mut Vector; x: i32, y: i32) =
    (*v).x |-> x &*& (*v).y |-> y;

@*/

impl Vector {
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ requires true;
    //@ ensures result != std::ptr::null_mut() &*& vector(result, x, y);
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;

        //@ close vector(result, x, y);
        result
    }
}

fn main()
//@ requires true;
//@ ensures true;
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();

        //@ close stack::<*mut Vector>(s, 0);
        loop {
            //@ invariant stack::<*mut Vector>(s, ?n);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    //@ open stack::<*mut Vector>(s, n);
                    //@ close stack::<*mut Vector>(s, n);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, n);
                    //@ close stack::<*mut Vector>(s, n);
                    let v1 = Stack::pop(s);

                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, n - 1);
                    //@ close stack::<*mut Vector>(s, n - 1);
                    let v2 = Stack::pop(s);

                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ open vector(v1, ?x1, ?y1);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    //@ open vector(v2, ?x2, ?y2);
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ open stack::<*mut Vector>(s, n - 2);
                    //@ close stack::<*mut Vector>(s, n - 2);
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, n);
                    //@ close stack::<*mut Vector>(s, n);
                    let v_ = Stack::pop(s);

                    //@ open vector(v_, ?xv, ?yv);
                    std::hint::assert_unchecked((*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command"),
            }
        }
    }
}