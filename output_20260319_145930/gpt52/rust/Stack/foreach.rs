use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred nodes<T>(head: *mut Node<T>) =
    head == std::ptr::null_mut() ?
        true
    :
        alloc_block(head as *mut u8, Layout::new::<Node<T>>()) &*&
        (*head).next |-> ?next &*&
        (*head).value |-> ?v &*&
        nodes::<T>(next);

pred stack<T>(s: *mut Stack<T>) =
    alloc_block(s as *mut u8, Layout::new::<Stack<T>>()) &*&
    (*s).head |-> ?h &*&
    nodes::<T>(h);

@*/

impl<T> Stack<T> {

    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& stack::<T>(result);
    unsafe fn create() -> *mut Stack<T>
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        //@ close nodes::<T>(std::ptr::null_mut());
        //@ close stack::<T>(stack);
        stack
    }
    
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    
    
    {
        
        //@ open stack::<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        
        
        //@ close nodes::<T>(n);
        //@ close stack::<T>(stack);
    }
    
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack) &*& result == ((*stack).head == std::ptr::null_mut());
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    
    
    {
        
        //@ open stack::<T>(stack);
        let head = (*stack).head;
        
        let result = head.is_null();
        
        
        //@ close stack::<T>(stack);
        result
    }
    
    //@ req stack::<T>(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack::<T>(stack);
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        
        //@ open stack::<T>(stack);
        //@ open nodes::<T>((*stack).head);
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack::<T>(stack);
        result
    }

    //@ req stack::<T>(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        
        
        //@ open stack::<T>(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

//@ req true;
//@ ens true;
unsafe fn input_char() -> char

{
    //@ assume_correct
    let mut line = String::new();
    //@ assume_correct
    std::io::stdin().read_line(&mut line).unwrap();
    //@ assume_correct
    line.chars().next().unwrap()
}

//@ req true;
//@ ens true;
unsafe fn input_i32() -> i32

{
    //@ assume_correct
    let mut line = String::new();
    //@ assume_correct
    std::io::stdin().read_line(&mut line).unwrap();
    //@ assume_correct
    line.trim().parse().unwrap()
}

//@ req true;
//@ ens true;
unsafe fn output_i32(value: i32)

{
    //@ assume_correct
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

/*@

pred vector(v: *mut Vector; x: i32, y: i32) =
    alloc_block(v as *mut u8, Layout::new::<Vector>()) &*&
    (*v).x |-> x &*&
    (*v).y |-> y;

@*/

impl Vector {

    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& vector(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    
    
    {
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
        let s = Stack::create();
        //@ open stack::<*mut Vector>(s);
        //@ close stack::<*mut Vector>(s);
        
        loop {
            //@ inv stack::<*mut Vector>(s);
            
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    Stack::push(s, v);
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    
                    
                    //@ open vector(v1, ?x1, ?y1);
                    //@ open vector(v2, ?x2, ?y2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    
                    
                    //@ open vector(v_, ?x_, ?y_);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}