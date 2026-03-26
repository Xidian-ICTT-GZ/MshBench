use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ predicate node<T>(Node<T> *node_ptr;) =
//@     node_ptr != null &*& malloc_block_node<T>(node_ptr) &*&
//@     node_ptr->next |-> ?next &*& node_ptr->value |-> ?value &*& nodes_list<T>(next);

/// Here malloc_block_node and malloc_block_Stack are pseudo-predicates representing allocation blocks.
/// VeriFast doesn't have built-in malloc_block for Rust structs, so these are placeholders.

//@ predicate nodes_list<T>(Node<T> *head;) =
//@     head == null ?
//@         emp :
//@         node<T>(head) &*& nodes_list<T>(head->next);

unsafe impl<T> Stack<T> {
    unsafe fn create() -> *mut Stack<T>
    //@ requires true;
    //@ ensures result != std::ptr::null_mut();
    //@ ensures true;
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_invariant(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires stack != std::ptr::null_mut();
    //@ ensures true;
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ requires stack != std::ptr::null_mut();
    //@ ensures true;
    {
        let head = (*stack).head;
        head.is_null()
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires stack != std::ptr::null_mut();
    //@ ensures true;
    {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires stack != std::ptr::null_mut();
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

impl Vector {

    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ requires x * x + y * y <= limit * limit;
    //@ ensures result != std::ptr::null_mut();
    //@ ensures true;
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
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
        let limit = input_i32();
        let s = Stack::create();
        
        loop {
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
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