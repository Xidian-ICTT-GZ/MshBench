use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
pred stack<T>(s: *mut Stack<T>; head: *mut Node<T>) =
    s != 0 &*& (*s).head |-> head;

pred node<T>(n: *mut Node<T>; next: *mut Node<T>) =
    n != 0 &*& (*n).next |-> next;

pred vector(v: *mut Vector; x: i32, y: i32) =
    v != 0 &*& (*v).x |-> x &*& (*v).y |-> y;
@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens result != 0 &*& stack::<T>(result, std::ptr::null_mut());
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close stack::<T>(stack, _);
        (*stack).head = std::ptr::null_mut();
        //@ open stack::<T>(stack, _);
        //@ close stack::<T>(stack, std::ptr::null_mut());
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack::<T>(stack, ?head);
    //@ ens stack::<T>(stack, ?newHead) &*& node::<T>(newHead, head);
    
    
    {
        
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ close node::<T>(n, _);
        //@ open node::<T>(n, _);
        (*n).next = (*stack).head;
        //@ close node::<T>(n, (*stack).head);
        //@ open node::<T>(n, _);
        (&raw mut (*n).value).write(value);
        //@ close node::<T>(n, (*stack).head);
        //@ open stack::<T>(stack, head);
        (*stack).head = n;
        //@ close stack::<T>(stack, n);
        
        
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack::<T>(stack, ?head);
    //@ ens stack::<T>(stack, head) &*& result == (head == std::ptr::null_mut());
    
    
    {
        
        //@ open stack::<T>(stack, head);
        let head = (*stack).head;
        //@ close stack::<T>(stack, head);
        
        let result = head.is_null();
        
        
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack::<T>(stack, ?head) &*& head != std::ptr::null_mut() &*& node::<T>(head, ?next);
    //@ ens stack::<T>(stack, next);
    
    
    {
        
        //@ open stack::<T>(stack, head);
        let head = (*stack).head;
        
        //@ open node::<T>(head, next);
        (*stack).head = (*head).next;
        //@ close stack::<T>(stack, next);
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack::<T>(stack, _);
    //@ ens true;
    
    
    {
        
        
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

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens result != 0 &*& vector(result, x, y);
    
    
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        //@ close vector(result, _, _);
        //@ open vector(result, _, _);
        (*result).x = x;
        (*result).y = y;
        //@ close vector(result, x, y);
        
        result
    }
    
}

fn main()

{
    unsafe {
        let s = Stack::create();
        
        loop {
            
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ open stack::<*mut Vector>(s, ?head);
                    //@ close stack::<*mut Vector>(s, head);
                    Stack::push(s, v);
                    //@ open stack::<*mut Vector>(s, ?nh);
                    //@ assert node::<*mut Vector>(nh, head);
                    //@ close stack::<*mut Vector>(s, nh);
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, ?head1);
                    //@ close stack::<*mut Vector>(s, head1);
                    //@ assert head1 != std::ptr::null_mut();
                    //@ assert node::<*mut Vector>(head1, ?next1);
                    let v1 = Stack::pop(s);
                    //@ open stack::<*mut Vector>(s, next1);
                    //@ close stack::<*mut Vector>(s, next1);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, ?head2);
                    //@ close stack::<*mut Vector>(s, head2);
                    //@ assert head2 != std::ptr::null_mut();
                    //@ assert node::<*mut Vector>(head2, ?next2);
                    let v2 = Stack::pop(s);
                    //@ open stack::<*mut Vector>(s, next2);
                    //@ close stack::<*mut Vector>(s, next2);
                    
                    
                    //@ open vector(v1, ?x1, ?y1);
                    //@ open vector(v2, ?x2, ?y2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ close vector(v1, x1, y1);
                    //@ close vector(v2, x2, y2);
                    //@ open vector(v1, _, _);
                    //@ open vector(v2, _, _);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ open stack::<*mut Vector>(s, ?head3);
                    //@ close stack::<*mut Vector>(s, head3);
                    Stack::push(s, sum);
                    //@ open stack::<*mut Vector>(s, ?nh2);
                    //@ assert node::<*mut Vector>(nh2, head3);
                    //@ close stack::<*mut Vector>(s, nh2);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, ?head);
                    //@ close stack::<*mut Vector>(s, head);
                    //@ assert head != std::ptr::null_mut();
                    //@ assert node::<*mut Vector>(head, ?next);
                    let v_ = Stack::pop(s);
                    //@ open stack::<*mut Vector>(s, next);
                    //@ close stack::<*mut Vector>(s, next);
                    
                    
                    //@ open vector(v_, ?vx, ?vy);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    //@ close vector(v_, vx, vy);
                    //@ open vector(v_, _, _);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}