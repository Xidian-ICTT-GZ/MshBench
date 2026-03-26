use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node<T>(node: *mut Node<T>, value: T, next: *mut Node<T>) =
    alloc_block(node, std::mem::size_of::<Node<T>>()) &*&
    struct_Node_padding(&(*node)) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

/*@
pred Stack<T>(stack: *mut Stack<T>, head: *mut Node<T>) =
    alloc_block(stack, std::mem::size_of::<Stack<T>>()) &*&
    struct_Stack_padding(&(*stack)) &*&
    (*stack).head |-> head;
@*/

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
pred StackNodes<T>(head: *mut Node<T>) =
    head == std::ptr::null_mut() ?
        true
    :
        Node<T>(head, ?value, ?next) &*& StackNodes<T>(next);
@*/

impl<T> Stack<T> {
    //@ req true;
    //@ ens Stack<T>(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack<T>(stack, std::ptr::null_mut());
        stack
    }
    
    //@ req Stack<T>(stack, ?head) &*& Node<T>(?n, value, head);
    //@ ens Stack<T>(stack, n);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open Stack<T>(stack, head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Node<T>(n, value, head);
        (*stack).head = n;
        //@ close Stack<T>(stack, n);
    }
    
    //@ req Stack<T>(stack, ?head);
    //@ ens Stack<T>(stack, head) &*& result == head.is_null();
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open Stack<T>(stack, head);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close Stack<T>(stack, head);
        result
    }
    
    //@ req Stack<T>(stack, ?head) &*& head != std::ptr::null_mut() &*& Node<T>(head, ?value, ?next);
    //@ ens Stack<T>(stack, next) &*& result == value;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open Stack<T>(stack, head);
        let head = (*stack).head;
        //@ open Node<T>(head, value, next);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack<T>(stack, next);
        result
    }

    //@ req Stack<T>(stack, std::ptr::null_mut());
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open Stack<T>(stack, std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

//@ assume_correct
unsafe fn input_char() -> char
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

//@ assume_correct
unsafe fn input_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

//@ assume_correct
unsafe fn output_i32(value: i32)
{
    println!("{}", value);
}

/*@
pred Vector(vec: *mut Vector, x: i32, y: i32) =
    alloc_block(vec, std::mem::size_of::<Vector>()) &*&
    struct_Vector_padding(&(*vec)) &*&
    (*vec).x |-> x &*&
    (*vec).y |-> y;
@*/

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {
    //@ req true;
    //@ ens Vector(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector(result, x, y);
        result
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        //@ close StackNodes<*mut Vector>(std::ptr::null_mut());
        //@ close Stack<*mut Vector>(s, std::ptr::null_mut());
        
        loop {
            //@ inv Stack<*mut Vector>(s, ?head) &*& StackNodes<*mut Vector>(head);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ close Node<*mut Vector>(v, v, head);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open StackNodes<*mut Vector>(head);
                    //@ open Node<*mut Vector>(head, v1, ?next1);
                    //@ open Vector(v1, ?x1, ?y1);
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open StackNodes<*mut Vector>(next1);
                    //@ open Node<*mut Vector>(next1, v2, ?next2);
                    //@ open Vector(v2, ?x2, ?y2);
                    
                    let sum = Vector::create(x1 + x2, y1 + y2);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ close Node<*mut Vector>(sum, sum, next2);
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open StackNodes<*mut Vector>(head);
                    //@ open Node<*mut Vector>(head, v_, ?next);
                    //@ open Vector(v_, ?x, ?y);
                    
                    output_i32(x);
                    output_i32(y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                    //@ close StackNodes<*mut Vector>(next);
                }
                _ => panic!("Bad command")
            }
        }
    }
}