use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node<T>(node: *mut Node<T>, value: T; next: *mut Node<T>) =
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
pred Stack<T>(stack: *mut Stack<T>; head: *mut Node<T>) =
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
        //@ close Stack::<T>(stack, std::ptr::null_mut());
        stack
    }
    
    //@ req Stack<T>(stack, ?head) &*& Node<T>(?n, value, head);
    //@ ens Stack<T>(stack, n);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open Stack::<T>(stack, head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Node::<T>(n, value, head);
        //@ close Stack::<T>(stack, n);
    }
    
    //@ req Stack<T>(stack, ?head);
    //@ ens Stack<T>(stack, head) &*& result == head.is_null();
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open Stack::<T>(stack, head);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close Stack::<T>(stack, head);
        result
    }
    
    //@ req Stack<T>(stack, ?head) &*& head != std::ptr::null_mut() &*& Node<T>(head, ?value, ?next);
    //@ ens Stack<T>(stack, next) &*& result == value;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open Stack::<T>(stack, head);
        //@ open Node::<T>(head, value, next);
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack::<T>(stack, next);
        result
    }

    //@ req Stack<T>(stack, std::ptr::null_mut());
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open Stack::<T>(stack, std::ptr::null_mut());
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
pred Vector(vec: *mut Vector; x: i32, y: i32) =
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
    //@ req x * x + y * y <= limit * limit;
    //@ ens Vector(result, x, y);
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
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
        let limit = input_i32();
        let s = Stack::create();
        //@ close StackNodes::<*mut Vector>(std::ptr::null_mut());
        
        loop {
            //@ inv Stack::<*mut Vector>(s, ?head) &*& StackNodes::<*mut Vector>(head);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    //@ close Node::<*mut Vector>(?n, v, head);
                    Stack::push(s, v);
                    //@ close StackNodes::<*mut Vector>(n);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open StackNodes::<*mut Vector>(head);
                    //@ assert Node::<*mut Vector>(head, ?v1, ?next1);
                    let v1 = Stack::pop(s);
                    //@ open StackNodes::<*mut Vector>(next1);
                    //@ assert Node::<*mut Vector>(next1, ?v2, ?next2);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open Vector(v1, ?x1, ?y1);
                    //@ open Vector(v2, ?x2, ?y2);
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ close Node::<*mut Vector>(?new_node, sum, next2);
                    Stack::push(s, sum);
                    //@ close StackNodes::<*mut Vector>(new_node);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open StackNodes::<*mut Vector>(head);
                    //@ assert Node::<*mut Vector>(head, ?v_, ?next);
                    let v_ = Stack::pop(s);
                    //@ open Vector(v_, ?x, ?y);
                    std::hint::assert_unchecked((*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                    //@ close StackNodes::<*mut Vector>(next);
                    break;
                }
                _ => panic!("Bad command")
            }
        }
        //@ open StackNodes::<*mut Vector>(_);
        Stack::dispose(s);
    }
}