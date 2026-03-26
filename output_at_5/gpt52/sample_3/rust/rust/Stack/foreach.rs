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
    head == 0 ?
        true
    :
        std::alloc::alloc_block(head as *mut u8, Layout::new::<Node<T>>()) &*&
        (*head).next |-> ?next &*&
        nodes::<T>(next);

pred stack<T>(s: *mut Stack<T>) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack<T>>()) &*&
    (*s).head |-> ?h &*& nodes::<T>(h);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens result != 0 &*& stack::<T>(result);
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        //@ close nodes::<T>(0);
        //@ close stack::<T>(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    
    
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
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    
    
    {
        //@ open stack::<T>(stack);
        
        let head = (*stack).head;
        
        let result = head.is_null();
        
        
        //@ close stack::<T>(stack);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack::<T>(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack::<T>(stack);
    
    
    {
        //@ open stack::<T>(stack);
        //@ open nodes::<T>(h);
        
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack::<T>(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack::<T>(stack);
    //@ ens true;
    
    
    {
        //@ open stack::<T>(stack);
        //@ open nodes::<T>((*stack).head);
        
        
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
    //@ ens result != 0 &*& std::alloc::alloc_block(result as *mut u8, Layout::new::<Vector>());
    
    
    {
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
        let s = Stack::create();
        
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
                    //@ open stack::<*mut Vector>(s);
                    //@ assert (*s).head |-> ?h1 &*& h1 != 0;
                    //@ close stack::<*mut Vector>(s);
                    let v1 = Stack::pop(s);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s);
                    //@ assert (*s).head |-> ?h2 &*& h2 != 0;
                    //@ close stack::<*mut Vector>(s);
                    let v2 = Stack::pop(s);
                    
                    
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s);
                    //@ assert (*s).head |-> ?h &*& h != 0;
                    //@ close stack::<*mut Vector>(s);
                    let v_ = Stack::pop(s);
                    
                    
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}