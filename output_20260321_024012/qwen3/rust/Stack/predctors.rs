//@ pred stack<T>(s: *mut Stack<T>) = s == null ? true : (*s).head |-> ?head &*& struct_Stack_padding(s);
//@ pred node<T>(n: *mut Node<T>, v: T, next: *mut Node<T>) = n == null ? false : (*n).next |-> next &*& (*n).value |-> v &*& struct_Node_padding(n);

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack<T>
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close stack(stack);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    //@ req stack(stack) &*& [?q]node(?n, value, _);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    
    
    {
        
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ close node(n, value, (*stack).head);
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        
        
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == null);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    
    
    {
        
        let head = (*stack).head;
        
        let result = head.is_null();
        
        
        result
    }
    
    //@ req stack(stack) &*& (*stack).head != null &*& node((*stack).head, ?v, ?next);
    //@ ens stack(stack) &*& result == v;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        
        let head = (*stack).head;
        //@ open node(head, _, _);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_char() -> char

{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32

{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)

{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {

    //@ req true;
    //@ ens [?q](*result).x |-> x &*& [q](*result).y |-> y &*& struct_Vector_padding(result);
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    
    
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        
        result
    }
    
}

fn main()

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
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    
                    
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
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