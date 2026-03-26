use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

//@ predicate node<T>(Node<T>* n; T v, Node<T>* next) = n != 0 &*& n->value |-> v &*& n->next |-> next;
//@ predicate stack<T>(Stack<T>* s; option<Node<T>*> head) = s != 0 &*& s->head |-> ?h &*& (head == Some(h) || (h == 0 && head == None));

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    //@ requires true;
    //@ ensures result != 0 &*& stack<T>(result, None);
    unsafe fn create() -> *mut Stack<T> 
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        stack
    }
    
    //@ requires stack<T>(stack, ?head);
    //@ ensures stack<T>(stack, Some(_));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }
    
    //@ requires stack<T>(stack, ?head);
    //@ ensures stack<T>(stack, head) &*& result == (head == None);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    //@ requires stack<T>(stack, ?head) &*& head != None;
    //@ ensures stack<T>(stack, head->next) &*& result == head->value;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    //@ requires stack<T>(stack, _);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack<T>)
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

impl Vector {

    //@ requires true;
    //@ ensures result != 0;
    unsafe fn create(x: i32, y: i32) -> *mut Vector
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