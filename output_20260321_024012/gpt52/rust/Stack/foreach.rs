use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred vector(v: *mut Vector; x: i32, y: i32) =
    v != 0 &*& (*v).x |-> x &*& (*v).y |-> y;

pred node<T>(n: *mut Node<T>, nxt: *mut Node<T>, val: T) =
    n != 0 &*& (*n).next |-> nxt &*& (*n).value |-> val;

pred stack_nodes<T>(head: *mut Node<T>; vs: list<T>) =
    head == 0 ?
        vs == nil
    :
        exists::<*mut Node<T>, T, list<T> >(?nxt, ?v, ?vs0) &*&
        node::<T>(head, nxt, v) &*& stack_nodes::<T>(nxt, vs0) &*& vs == cons(v, vs0);

pred stack<T>(s: *mut Stack<T>; vs: list<T>) =
    s != 0 &*& (*s).head |-> ?h &*& stack_nodes::<T>(h, vs);

@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack::<T>(result, nil);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_nodes::<T>(0, nil);
        //@ close stack::<T>(stack, nil);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack::<T>(stack, ?vs);
    //@ ens stack::<T>(stack, cons(value, vs));
    {
        //@ open stack::<T>(stack, vs);
        //@ open stack_nodes::<T>((*stack).head, vs);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close node::<T>(n, (*n).next, value);
        //@ close stack_nodes::<T>(n, cons(value, vs));
        //@ close stack::<T>(stack, cons(value, vs));
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack::<T>(stack, ?vs);
    //@ ens stack::<T>(stack, vs) &*& result == (vs == nil);
    {
        //@ open stack::<T>(stack, vs);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close stack::<T>(stack, vs);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack::<T>(stack, cons(?v, ?vs0));
    //@ ens stack::<T>(stack, vs0) &*& result == v;
    {
        //@ open stack::<T>(stack, cons(v, vs0));
        //@ open stack_nodes::<T>((*stack).head, cons(v, vs0));
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open node::<T>(head, (*head).next, v);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack_nodes::<T>((*stack).head, vs0);
        //@ close stack::<T>(stack, vs0);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack::<T>(stack, ?vs);
    //@ ens true;
    {
        //@ open stack::<T>(stack, vs);
        //@ open stack_nodes::<T>((*stack).head, vs);
        //@ assert false;
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
    //@ ens vector(result, x, y);
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
        //@ open stack::<*mut Vector>(s, nil);
        //@ close stack::<*mut Vector>(s, nil);
        
        loop {
            //@ inv stack::<*mut Vector>(s, ?vs);
            
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
                    //@ open vector(v1, _, _);
                    //@ open vector(v2, _, _);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    
                    
                    //@ open vector(v_, _, _);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}