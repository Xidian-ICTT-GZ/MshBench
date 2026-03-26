use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred nodes<T>(head: *mut Node<T>; n: i32) =
    head == std::ptr::null_mut() ?
        n == 0
    :
        n > 0 &*&
        (*head).next |-> ?next &*&
        std::ptr::writeable(&(*head).value) &*&
        nodes::<T>(next, n - 1);

pred stack<T>(s: *mut Stack<T>; n: i32) =
    (*s).head |-> ?h &*& nodes::<T>(h, n);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& (*result).head |-> std::ptr::null_mut() &*& nodes::<T>(std::ptr::null_mut(), 0);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        //@ close nodes::<T>(std::ptr::null_mut(), 0);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack::<T>(stack, ?n);
    //@ ens stack::<T>(stack, n + 1);
    {
        //@ open stack::<T>(stack, n);
        
        let n_ = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n_.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n_).next = (*stack).head;
        (&raw mut (*n_).value).write(value);
        (*stack).head = n_;
        
        
        //@ close nodes::<T>(n_, n + 1);
        //@ close stack::<T>(stack, n + 1);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack::<T>(stack, ?n);
    //@ ens stack::<T>(stack, n) &*& result == (n == 0);
    {
        //@ open stack::<T>(stack, n);
        
        let head = (*stack).head;
        
        let result = head.is_null();
        
        
        //@ close stack::<T>(stack, n);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack::<T>(stack, ?n) &*& n > 0;
    //@ ens stack::<T>(stack, n - 1);
    {
        //@ open stack::<T>(stack, n);
        //@ open nodes::<T>((*stack).head, n);
        
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack::<T>(stack, n - 1);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req (*stack).head |-> ?h &*& nodes::<T>(h, ?n);
    //@ ens true;
    {
        //@ open nodes::<T>(h, n);
        
        
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
    //@ ens result != std::ptr::null_mut() &*& (*result).x |-> x &*& (*result).y |-> y;
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
        //@ close stack::<*mut Vector>(s, 0);
        
        loop {
            //@ inv stack::<*mut Vector>(s, ?n);
            
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
                    
                    
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ open (*v1).x |-> _; open (*v1).y |-> _;
                    //@ open (*v2).x |-> _; open (*v2).y |-> _;
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    
                    
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    //@ open (*v_).x |-> _; open (*v_).y |-> _;
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}