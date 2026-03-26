use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    //@ pred node<T>(node_ptr: *mut Node<T>) = node_ptr != std::ptr::null_mut() &*& malloc_block_node<T>(node_ptr, ?next, ?value) &*& next |-> ?nxt &*& heap_mem(value);
    //@ pred stack<T>(stack_ptr: *mut Stack<T>, ?head: *mut Node<T>) = stack_ptr != std::ptr::null_mut() &*& malloc_block_Stack<T>(stack_ptr, head) &*& head |-> ?h &*& nodes_list(head);
    //@ pred nodes_list<T>(head: *mut Node<T>) = head == std::ptr::null_mut() ? emp : node(head) &*& nodes_list(head->next);

    unsafe fn create() -> *mut Stack<T>
    //@ requires true;
    //@ ensures stack(result, std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        //@ close stack(stack, std::ptr::null_mut());
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires stack != std::ptr::null_mut() &*& stack<uint8>(stack, ?head) &*& heap_mem(value);
    //@ ensures stack(stack, ?new_head) &*& new_head == ?h &*& malloc_block_node::<T>(h, old_head, value);
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        
        //@ open stack(stack, ?old_head);
        //@ close node(n);
        //@ close stack(stack, n);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, ?head);
    //@ ensures stack(stack, head) &*& result == (head == std::ptr::null_mut());
    {
        let head = (*stack).head;
        
        let result = head.is_null();
        
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, ?head) &*& head != std::ptr::null_mut();
    //@ ensures stack(stack, (*head).next) &*& heap_mem(result);
    {
        let head = (*stack).head;
        //@ open stack(stack, head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        //@ open node(head);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, std::ptr::null_mut());
    //@ ensures true;
    {
        
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_char() -> char
//@ requires true;
//@ ensures heap_mem(result);
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
    //@ ensures malloc_block_Vector(result);
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        
        //@ close malloc_block_Vector(result);
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