use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    //@ requires true;
    //@ ensures result != 0 as *mut Stack<T>;
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes::<T>(std::ptr::null_mut());
        stack
    }
    
    //@ requires nodes(stack, ?head);
    //@ ensures nodes(stack, ?new_head);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open nodes(stack, _);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close node(n, (*stack).head, value);
        //@ close nodes(stack, n);
    }
    
    //@ requires nodes(stack, ?head);
    //@ ensures nodes(stack, head) &*& result == head.is_null();
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open nodes(stack, _);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close nodes(stack, head);
        result
    }
    
    //@ requires nodes(stack, ?head) &*& head != 0 as *mut Node<T>;
    //@ ensures nodes(stack, (*old(head)).next) &*& result == (*old(head)).value;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open nodes(stack, head);
        let head = (*stack).head;
        //@ open node(head, _, _);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close nodes(stack, (*stack).head);
        result
    }

    //@ requires nodes(stack, std::ptr::null_mut());
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open nodes(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

//@ predicate_ctor node<T>(struct Node<T> *node; *mut Node<T> next, T value)() = 
//@     node != 0 &*&
//@     struct_Node_padding<T>(node) &*&
//@     (*node).next |-> next &*&
//@     (*node).value |-> value;

//@ predicate nodes<T>(*mut Stack<T> stack; *mut Node<T> head) = 
//@     stack != 0 &*&
//@     struct_Stack_padding<T>(stack) &*&
//@     (*stack).head |-> head &*&
//@     lseg(head, std::ptr::null_mut());

//@ predicate lseg<T>(*mut Node<T> first, *mut Node<T> last) =
//@     first == last ?
//@         true
//@     :
//@         node::<T>(first, ?next, ?value) &*& lseg(next, last);

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
    //@ ensures result != 0 as *mut Vector &*& (*result).x |-> x &*& (*result).y |-> y;
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
//@ requires true;
//@ ensures true;
{
    unsafe {
        let s = Stack::create();
        //@ close lseg::<*mut Vector>(std::ptr::null_mut(), std::ptr::null_mut());
        //@ close nodes::<*mut Vector>(s, std::ptr::null_mut());
        loop {
            //@ invariant nodes::<*mut Vector>(s, ?head);
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
                    //@ open lseg(head, _);
                    //@ open node(_, _, _);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open lseg(_, _);
                    //@ open node(_, _, _);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open lseg(head, _);
                    //@ open node(_, _, _);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}