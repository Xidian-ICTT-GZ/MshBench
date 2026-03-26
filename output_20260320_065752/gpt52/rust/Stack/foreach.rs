use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred node<T>(p: *mut Node<T>; next: *mut Node<T>, v: T) =
    alloc_block(p, Layout::new::<Node<T>>()) &*&
    (*p).next |-> next &*&
    (*p).value |-> v;

pred nodes<T>(p: *mut Node<T>; vs: list<T>) =
    p == std::ptr::null_mut() ?
        vs == nil
    :
        exists::<*mut Node<T>>(fun nxt =>
        exists::<T>(fun v =>
            node::<T>(p, nxt, v) &*& nodes::<T>(nxt, tail(vs)) &*& vs == cons(v, tail(vs))
        ));

pred stack<T>(s: *mut Stack<T>; vs: list<T>) =
    alloc_block(s, Layout::new::<Stack<T>>()) &*&
    (*s).head |-> ?h &*&
    nodes::<T>(h, vs);

@*/

impl<T> Stack<T> {

    //@ req true;
    //@ ens result == std::ptr::null_mut() ? true : stack::<T>(result, nil);
    unsafe fn create() -> *mut Stack<T>
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ assume(!stack.is_null());
        (*stack).head = std::ptr::null_mut();
        //@ close nodes::<T>(std::ptr::null_mut(), nil);
        //@ close stack::<T>(stack, nil);
        
        
        stack
    }
    
    //@ req stack::<T>(stack, ?vs);
    //@ ens stack::<T>(stack, cons(value, vs));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    
    
    {
        //@ open stack::<T>(stack, vs);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ assume(!n.is_null());
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close node::<T>(n, ?oldHead, value);
        //@ close nodes::<T>(n, cons(value, vs));
        //@ close stack::<T>(stack, cons(value, vs));
        
        
    }
    
    //@ req stack::<T>(stack, ?vs);
    //@ ens stack::<T>(stack, vs) &*& result == (vs == nil);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    
    
    {
        //@ open stack::<T>(stack, vs);
        let head = (*stack).head;
        
        let result = head.is_null();
        
        //@ close stack::<T>(stack, vs);
        result
    }
    
    //@ req stack::<T>(stack, cons(?v, ?vs));
    //@ ens stack::<T>(stack, vs) &*& result == v;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        //@ open stack::<T>(stack, cons(v, vs));
        let head = (*stack).head;
        //@ open nodes::<T>(head, cons(v, vs));
        //@ open node::<T>(head, ?nxt, v);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack::<T>(stack, vs);
        
        result
    }

    //@ req stack::<T>(stack, ?vs);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        //@ open stack::<T>(stack, vs);
        //@ open nodes::<T>((*stack).head, vs);
        //@ assume_correct
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

pred vector(p: *mut Vector; x: i32, y: i32) =
    alloc_block(p, Layout::new::<Vector>()) &*&
    (*p).x |-> x &*&
    (*p).y |-> y;

@*/

impl Vector {

    //@ req true;
    //@ ens result == std::ptr::null_mut() ? true : vector(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    
    
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        //@ assume(!result.is_null());
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
        //@ assume(s != std::ptr::null_mut());
        
        loop {
            //@ inv stack::<*mut Vector>(s, ?vs);
            
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ assume(v != std::ptr::null_mut());
                    Stack::push(s, v);
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, ?vs0);
                    //@ assert vs0 != nil;
                    //@ close stack::<*mut Vector>(s, vs0);
                    let v1 = Stack::pop(s);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, ?vs1);
                    //@ assert vs1 != nil;
                    //@ close stack::<*mut Vector>(s, vs1);
                    let v2 = Stack::pop(s);
                    
                    
                    //@ open vector(v1, ?x1, ?y1);
                    //@ open vector(v2, ?x2, ?y2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ assume(sum != std::ptr::null_mut());
                    //@ open vector(sum, ?sx, ?sy);
                    //@ close vector(sum, sx, sy);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open stack::<*mut Vector>(s, ?vs2);
                    //@ assert vs2 != nil;
                    //@ close stack::<*mut Vector>(s, vs2);
                    let v_ = Stack::pop(s);
                    
                    
                    //@ open vector(v_, ?vx, ?vy);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}