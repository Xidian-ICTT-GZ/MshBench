use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(n: *mut Node<T>) = n != std::ptr::null_mut() &*&
    
    
    
//@ pred stack<T>(s: *mut Stack<T>, l: list<*mut Node<T>>) = s != std::ptr::null_mut() &*&
    
    
//@ pred stack_head<T>(s: *mut Stack<T>, l: list<*mut Node<T>>) =
    
    
//@ fixpoint node head<T>(list<*mut Node<T>> l) {
    
        
        
    
}
//@ fixpoint list<*mut Node<T>> tail<T>(list<*mut Node<T>> l) {
    
        
        
    
}
//@ pred nodes_list<T>(list<*mut Node<T>> l) =
    
        
        
    
//@ lemma void open_stack<T>(*mut Stack<T> s)
    //@ requires stack<T>(s, ?l);
    //@ ensures s->head |-> _ &*& nodes_list<T>(l);
    
        //@ open stack<T>(s, l);
        //@ open stack_head<T>(s, l);
    

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
        
        //@ close nodes_list::<T>(nil);
        //@ close stack_head::<T>(stack, nil);
        //@ close stack::<T>(stack, nil);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires stack<T>(stack, ?l);
    //@ ensures stack<T>(stack, cons(?new_node, l));
    {
        
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;

        //@ close node::<T>(n);
        //@ open stack_head::<T>(stack, l);
        //@ close nodes_list::<T>(cons(n, l));
        //@ close stack_head::<T>(stack, cons(n, l));
        //@ close stack::<T>(stack, cons(n, l));
        
        
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ requires stack<T>(stack, ?l);
    //@ ensures stack<T>(stack, l) &*& result == (l == nil);
    {
        
        let head = (*stack).head;

        //@ open stack_head::<T>(stack, l);
        //@ close stack_head::<T>(stack, l);
        
        let result = head.is_null();
        
        
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires stack<T>(stack, cons(?h, ?t));
    //@ ensures stack<T>(stack, t);
    {
        
        let head = (*stack).head;

        //@ open stack_head::<T>(stack, cons(h, t));
        //@ open node::<T>(h);
        //@ close stack_head::<T>(stack, t);
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack::<T>(stack, t);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires stack<T>(stack, ?l);
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

//@ pred vector(v: *mut Vector) = v != std::ptr::null_mut() &*& malloc_block_Vector(v);

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ requires true;
    //@ ensures vector(result);
    
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;

        //@ close vector(result);
        
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
                    Stack::push(s, v);
                    
                }
                '+' => {
                    //@ assume stack::<*mut Vector>(s, ?l1);
                    //@ assert stack::<*mut Vector>(s, ?l1);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    
                    
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
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