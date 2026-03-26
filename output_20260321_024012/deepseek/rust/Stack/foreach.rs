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
    //@ ensures ptr::points_to_raw(result, Stack { head: 0 as *mut _ });
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close node_opt(0 as *mut _, _);
        //@ close stack_inv(stack, _);
        stack
    }
    
    //@ requires stack_inv(stack, ?nodes) &*& own::<T>(?v);
    //@ ensures stack_inv(stack, cons(?new_node, nodes)) &*& node(new_node, _, v);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open stack_inv(stack, nodes);
        //@ open node_opt(head, _);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close node_opt(n, _);
        //@ close stack_inv(stack, cons(n, nodes));
    }
    
    //@ requires stack_inv(stack, ?nodes);
    //@ ensures stack_inv(stack, nodes) &*& result == (nodes == Nil);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack_inv(stack, nodes);
        //@ open node_opt(head, nodes);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close node_opt(head, nodes);
        //@ close stack_inv(stack, nodes);
        result
    }
    
    //@ requires stack_inv(stack, cons(?h, ?tail)) &*& node(h, _, ?v);
    //@ ensures stack_inv(stack, tail) &*& own::<T>(v);
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack_inv(stack, cons(h, tail));
        //@ open node_opt(head, _);
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open node(head, _, _);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close node_opt((*stack).head, tail);
        //@ close stack_inv(stack, tail);
        result
    }

    //@ requires stack_inv(stack, Nil);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack_inv(stack, Nil);
        //@ open node_opt(head, _);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

//@ predicate node<T>(*mut Node<T> n, *mut Node<T> next, T v) = 
//@     struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> v;

//@ predicate node_opt<T>(*mut Node<T> n, list<*mut Node<T>> nodes) = 
//@     nodes == Nil ? n == 0 as *mut _ : node(n, ?next, ?v) &*& node_opt(next, ?tail) &*& nodes == cons(n, tail);

//@ predicate stack_inv<T>(*mut Stack<T> s, list<*mut Node<T>> nodes) = 
//@     (*s).head |-> ?head &*& node_opt(head, nodes);

//@ predicate own<T>(T t) = true;

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
    //@ ensures ptr::points_to_raw(result, Vector { x: x, y: y });
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

//@ predicate vector(*mut Vector v, i32 x, i32 y) = (*v).x |-> x &*& (*v).y |-> y;

fn main()
//@ requires true;
//@ ensures true;
{
    unsafe {
        let s = Stack::create();
        //@ close own::<*mut Vector>(0 as *mut _);
        //@ close stack_inv(s, Nil);
        loop {
            //@ invariant stack_inv(s, ?nodes);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ close vector(v, x, y);
                    //@ close own::<*mut Vector>(v);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open own::<*mut Vector>(v1);
                    //@ open vector(v1, ?x1, ?y1);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open own::<*mut Vector>(v2);
                    //@ open vector(v2, ?x2, ?y2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ close vector(sum, x1 + x2, y1 + y2);
                    //@ close own::<*mut Vector>(sum);
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open own::<*mut Vector>(v_);
                    //@ open vector(v_, ?x_, ?y_);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}