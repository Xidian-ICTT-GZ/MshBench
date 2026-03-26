//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node<T>(n: *mut Node<T>, next: *mut Node<T>, value: T) =
    n != 0 &*&
    alloc_block_Node::<T>(n) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

/*@ pred stack<T>(s: *mut Stack<T>) =
    s != 0 &*&
    alloc_block_Stack::<T>(s) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    stack_nodes(head);
@*/

/*@ pred stack_nodes<T>(n: *mut Node<T>) =
    n == 0 ?
        true
    :
        node(n, ?next, ?value) &*& stack_nodes(next);
@*/

/*@ pred vector(v: *mut Vector, x: i32, y: i32) =
    v != 0 &*&
    alloc_block_Vector(v) &*&
    struct_Vector_padding(v) &*&
    (*v).x |-> x &*&
    (*v).y |-> y;
@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close stack_nodes(0);
        //@ close stack(stack);
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    //@ req stack(stack) &*& vector(value, ?x, ?y);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open stack(stack);
        //@ open stack_nodes((*stack).head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close node(n, (*stack).head, value);
        //@ close stack_nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == 0);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ close stack(stack);
        let result = head.is_null();
        result
    }
    
    //@ req stack(stack) &*& (*stack).head != 0;
    //@ ens stack(stack) &*& vector(result, ?x, ?y);
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open stack_nodes(head);
        //@ open node(head, ?next, ?value);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ close stack_nodes(next);
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack(stack);
        //@ open stack_nodes((*stack).head);
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

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {

    //@ req true;
    //@ ens vector(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Vector
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
        loop {
            //@ inv stack(s);
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