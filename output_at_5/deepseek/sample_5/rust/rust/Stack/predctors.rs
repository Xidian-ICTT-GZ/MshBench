use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ predicate node<T>(n: *mut Node<T>, v: T, next: *mut Node<T>) = 
//@     struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> v;

//@ predicate nodes<T>(n: *mut Node<T>) =
//@     n == 0 ? true : node::<T>(n, _, ?next) &*& nodes(next);

//@ predicate stack<T>(s: *mut Stack<T>) =
//@     struct_Stack_padding(s) &*& (*s).head |-> ?head &*& nodes(head);

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close node::<T>(n, value, (*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == 0);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close stack(stack);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack(stack) &*& (*stack).head != 0;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node::<T>(head, ?value, ?next);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close nodes((*stack).head);
        //@ close stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_char() -> char
//@ req true;
//@ ens true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32
//@ req true;
//@ ens true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

//@ predicate vector(v: *mut Vector, x: i32, y: i32) =
//@     struct_Vector_padding(v) &*& (*v).x |-> x &*& (*v).y |-> y;

impl Vector {

    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ req x * x + y * y <= limit * limit;
    //@ ens vector(result, x, y);
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
//@ req true;
//@ ens true;
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        
        loop {
            
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    Stack::push(s, v);
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open vector(v1, ?x1, ?y1);
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open vector(v2, ?x2, ?y2);
                    
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open vector(v_, ?x_, ?y_);
                    
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