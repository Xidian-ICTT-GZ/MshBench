//@ predicate Stack_own<T>(Stack<T> *s; list<*mut Node<T>> nodes) =
//@   s != 0 &*& struct_Stack_padding(s) &*&
//@   (*s).head |-> ?head &*&
//@   nodes == if head == 0 then nil else cons(head, ?rest) &*&
//@   Nodes_own(head, rest);

//@ predicate Nodes_own<T>(*mut Node<T> node; list<*mut Node<T>> nodes) =
//@   match nodes {
//@     nil => node == 0,
//@     cons(h, t) => node == h &*& h != 0 &*& struct_Node_padding(h) &*&
//@                   (*h).next |-> ?next &*&
//@                   (*h).value |-> _ &*&
//@                   Nodes_own(next, t)
//@   };

//@ predicate Vector_own(Vector *v; i32 x, i32 y) =
//@   v != 0 &*& struct_Vector_padding(v) &*&
//@   (*v).x |-> x &*& (*v).y |-> y;

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
    //@ ens Stack_own(result, nil);
    unsafe fn create() -> *mut Stack<T>
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close struct_Stack_padding(stack)();
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack, nil);
        
        
        stack
    }
    
    //@ req Stack_own(stack, ?nodes) &*& Vector_own(value, ?x, ?y) &*& x*x + y*y <= limit*limit;
    //@ ens Stack_own(stack, cons(value, nodes));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    
    
    {
        //@ open Stack_own(stack, nodes);
        //@ close struct_Stack_padding(stack)();
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ close struct_Node_padding(n)();
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Nodes_own(n, nodes);
        //@ close Stack_own(stack, cons(n, nodes));
        
        
    }
    
    //@ req Stack_own(stack, ?nodes);
    //@ ens Stack_own(stack, nodes) &*& result == (nodes == nil);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    
    
    {
        //@ open Stack_own(stack, nodes);
        let head = (*stack).head;
        //@ close Stack_own(stack, nodes);
        
        let result = head.is_null();
        
        
        result
    }
    
    //@ req Stack_own(stack, cons(?node, ?rest)) &*& Nodes_own(node, cons(node, rest));
    //@ ens Stack_own(stack, rest) &*& Vector_own(result, _, _);
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        //@ open Stack_own(stack, cons(node, rest));
        //@ open Nodes_own(node, cons(node, rest));
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ close Stack_own(stack, rest);
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        result
    }

    //@ req Stack_own(stack, nil);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        //@ open Stack_own(stack, nil);
        //@ open struct_Stack_padding(stack)();
        
        
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

    //@ req x*x + y*y <= limit*limit;
    //@ ens Vector_own(result, x, y);
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    
    
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        //@ close struct_Vector_padding(result)();
        (*result).x = x;
        (*result).y = y;
        //@ close Vector_own(result, x, y);
        
        result
    }
    
}

fn main()

{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        //@ let limit0 = limit;
        
        loop {
            
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    //@ close Vector_own(v, x, y);
                    Stack::push(s, v);
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open Vector_own(v1, ?x1, ?y1);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open Vector_own(v2, ?x2, ?y2);
                    
                    
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open Vector_own(v_, ?x_, ?y_);
                    
                    
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