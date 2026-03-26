use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(n: *mut Node<T>, v: T, next: *mut Node<T>) = n |-> Node { next: next, value: v };
//@ pred stack<T>(s: *mut Stack<T>, contents: list<T>) = s |-> Stack { head: ?h } &*& nodes<T>(h, contents);
//@ pred nodes<T>(n: *mut Node<T>, contents: list<T>) = 
//@     if contents.is_empty() {
//@         n == std::ptr::null_mut()
//@     } else {
//@         n != std::ptr::null_mut() &*& node<T>(n, head(contents), ?next) &*& nodes<T>(next, tail(contents))
//@     };

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ requires true;
    //@ ensures stack<T>(result, nil);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack<T>(stack, nil);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires stack<T>(stack, ?contents);
    //@ ensures stack<T>(stack, cons(value, contents));
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ open stack<T>(stack, contents);
        //@ close node<T>(n, value, (*n).next);
        //@ close nodes<T>((*stack).head, cons(value, contents));
        //@ close stack<T>(stack, cons(value, contents));
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ requires stack<T>(stack, ?contents);
    //@ ensures stack<T>(stack, contents) &*& result == contents.is_empty();
    {
        let head = (*stack).head;
        let result = head.is_null();
        //@ open stack<T>(stack, contents);
        //@ close stack<T>(stack, contents);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires stack<T>(stack, ?contents) &*& contents != nil;
    //@ ensures stack<T>(stack, tail(contents)) &*& result == head(contents);
    {
        let head = (*stack).head;
        //@ open stack<T>(stack, contents);
        //@ open nodes<T>(head, contents);
        //@ open node<T>(head, _, _);
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack<T>(stack, tail(contents));
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires stack<T>(stack, nil);
    //@ ensures true;
    {
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

//@ pred vector(v: *mut Vector, x: i32, y: i32) = v |-> Vector { x: x, y: y };

impl Vector {

    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ requires x * x + y * y <= limit * limit;
    //@ ensures vector(result, x, y);
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
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        //@ open stack<Vector>(s, nil);
        loop {
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    //@ open stack<Vector>(s, ?contents);
                    Stack::push(s, v);
                    //@ close stack<Vector>(s, cons(v, contents));
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack<Vector>(s, ?contents1);
                    //@ assert contents1 == cons(?v1, ?rest1);
                    let v1 = Stack::pop(s);
                    //@ open vector(v1, _, _);

                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack<Vector>(s, ?contents2);
                    //@ assert contents2 == cons(?v2, ?rest2);
                    let v2 = Stack::pop(s);
                    //@ open vector(v2, _, _);

                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ open vector(sum, _, _);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    //@ close stack<Vector>(s, cons(sum, rest2));
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack<Vector>(s, ?contents);
                    //@ assert contents == cons(?v_, ?rest);
                    let v_ = Stack::pop(s);
                    //@ open vector(v_, ?vx, ?vy);

                    std::hint::assert_unchecked(vx * vx + vy * vy <= limit * limit);
                    output_i32(vx);
                    output_i32(vy);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                    //@ close stack<Vector>(s, rest);
                }
                _ => panic!("Bad command")
            }
        }
    }
}