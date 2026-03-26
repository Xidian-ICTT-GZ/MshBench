use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred Node_own<T>(node: *mut Node<T>, next: *mut Node<T>, value: T) =
    (*node).next |-> next &*& (*node).value |-> value &*&
    alloc_block(node as *mut u8, Layout::new_::<Node<T>>());

pred Nodes<T>(node: *mut Node<T>) =
    if node == std::ptr::null_mut() {
        true
    } else {
        Node_own::<T>(node, ?next, ?value) &*& Nodes::<T>(next)
    };

pred Stack_own<T>(stack: *mut Stack<T>) =
    (*stack).head |-> ?head &*&
    alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>()) &*&
    Nodes::<T>(head);

pred Vector_own(v: *mut Vector, x: i32, y: i32) =
    (*v).x |-> x &*& (*v).y |-> y &*&
    alloc_block(v as *mut u8, Layout::new_::<Vector>());

pred Vectors(node: *mut Node<*mut Vector>) =
    if node == std::ptr::null_mut() {
        true
    } else {
        (*node).next |-> ?next &*& (*node).value |-> ?v &*&
        alloc_block(node as *mut u8, Layout::new_::<Node<*mut Vector>>()) &*&
        Vector_own(v, ?x, ?y) &*&
        Vectors(next)
    };

pred VectorStack(stack: *mut Stack<*mut Vector>) =
    (*stack).head |-> ?head &*&
    alloc_block(stack as *mut u8, Layout::new_::<Stack<*mut Vector>>()) &*&
    Vectors(head);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens Stack_own::<T>(result);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes::<T>(std::ptr::null_mut());
        //@ close Stack_own::<T>(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req Stack_own::<T>(stack);
    //@ ens Stack_own::<T>(stack);
    {
        //@ open Stack_own::<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Node_own::<T>(n, (*stack).head, value);
        //@ close Nodes::<T>(n);
        (*stack).head = n;
        //@ close Stack_own::<T>(stack);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req Stack_own::<T>(stack);
    //@ ens Stack_own::<T>(stack);
    {
        //@ open Stack_own::<T>(stack);
        let head = (*stack).head;
        //@ open Nodes::<T>(head);
        let result = head.is_null();
        //@ close Nodes::<T>(head);
        //@ close Stack_own::<T>(stack);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req Stack_own::<T>(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens Stack_own::<T>(stack);
    {
        //@ open Stack_own::<T>(stack);
        let head = (*stack).head;
        //@ open Nodes::<T>(head);
        //@ open Node_own::<T>(head, ?next, ?val);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack_own::<T>(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack_own::<T>(stack) &*& (*stack).head == std::ptr::null_mut();
    //@ ens true;
    {
        //@ open Stack_own::<T>(stack);
        //@ open Nodes::<T>(std::ptr::null_mut());
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
    //@ ens Vector_own(result, x, y);
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector_own(result, x, y);
        result
    }
    
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        //@ open Stack_own::<*mut Vector>(s);
        //@ close VectorStack(s);
        
        loop {
            //@ inv VectorStack(s);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ open VectorStack(s);
                    //@ close Stack_own::<*mut Vector>(s);
                    Stack::push(s, v);
                    //@ open Stack_own::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    //@ open Node_own::<*mut Vector>((*s).head, ?next1, v);
                    //@ close Vectors(next1);
                    //@ close Vectors((*s).head);
                    //@ close VectorStack(s);
                }
                '+' => {
                    //@ open VectorStack(s);
                    //@ open Vectors((*s).head);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Stack_own::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    //@ close Nodes::<*mut Vector>((*s).head);
                    //@ close Stack_own::<*mut Vector>(s);
                    let v1 = Stack::pop(s);
                    //@ open Stack_own::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    //@ close Nodes::<*mut Vector>((*s).head);
                    //@ close Stack_own::<*mut Vector>(s);
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Stack_own::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    //@ close Nodes::<*mut Vector>((*s).head);
                    //@ close Stack_own::<*mut Vector>(s);
                    let v2 = Stack::pop(s);
                    //@ open Stack_own::<*mut Vector>(s);
                    
                    //@ open Vector_own(v1, ?x1, ?y1);
                    //@ open Vector_own(v2, ?x2, ?y2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ close Stack_own::<*mut Vector>(s);
                    Stack::push(s, sum);
                    //@ open Stack_own::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    //@ open Node_own::<*mut Vector>((*s).head, ?next2, sum);
                    //@ close Vectors(next2);
                    //@ close Vectors((*s).head);
                    //@ close VectorStack(s);
                }
                '=' => {
                    //@ open VectorStack(s);
                    //@ open Vectors((*s).head);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Stack_own::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    //@ close Nodes::<*mut Vector>((*s).head);
                    //@ close Stack_own::<*mut Vector>(s);
                    let v_ = Stack::pop(s);
                    //@ open Stack_own::<*mut Vector>(s);
                    
                    //@ open Vector_own(v_, ?xv, ?yv);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                    //@ close VectorStack(s);
                }
                _ => panic!("Bad command")
            }
        }
    }
}