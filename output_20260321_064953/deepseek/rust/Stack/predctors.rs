use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens result != 0;
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close node_own::<T>(std::ptr::null_mut(), _);
        //@ close stack_own::<T>(stack);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack_own::<T>(stack) &*& own::<T>(value);
    //@ ens stack_own::<T>(stack);
    
    {
        //@ open stack_own::<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close node_own::<T>(n, value);
        //@ close stack_own::<T>(stack);
        
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack_own::<T>(stack);
    //@ ens stack_own::<T>(stack);
    
    {
        //@ open stack_own::<T>(stack);
        let head = (*stack).head;
        
        let result = head.is_null();
        //@ close stack_own::<T>(stack);
        
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack_own::<T>(stack);
    //@ ens stack_own::<T>(stack) &*& own::<T>(result);
    
    {
        //@ open stack_own::<T>(stack);
        let head = (*stack).head;
        //@ open node_own::<T>(head, _);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack_own::<T>(stack);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack_own::<T>(stack);
    //@ ens true;
    
    {
        //@ open stack_own::<T>(stack);
        //@ open node_own::<T>(_, _);
        
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

    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens result != 0;
    
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close vector_own(result);
        
        result
    }
    
}

fn main()
//@ req true;
//@ ens true;

{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        //@ close stack_own::<*mut Vector>(s);
        
        loop {
            //@ invariant stack_own::<*mut Vector>(s);
            
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    //@ close own::<*mut Vector>(v);
                    Stack::push(s, v);
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open own::<*mut Vector>(v1);
                    //@ open vector_own(v1);
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open own::<*mut Vector>(v2);
                    //@ open vector_own(v2);
                    
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ close own::<*mut Vector>(sum);
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open own::<*mut Vector>(v_);
                    //@ open vector_own(v_);
                    
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

/*@
predicate node_own<T>(*mut Node<T> node, T value) =
    node != 0 &*&
    struct_Node_padding(&(*node).next) &*&
    (*node).next |-> ?next &*&
    (*node).value |-> value;

predicate stack_own<T>(*mut Stack<T> stack) =
    stack != 0 &*&
    struct_Stack_padding(&(*stack).head) &*&
    (*stack).head |-> ?head &*&
    head == 0 ? true : node_own::<T>(head, _);

predicate vector_own(*mut Vector v) =
    v != 0 &*&
    struct_Vector_padding(&(*v).x) &*&
    (*v).x |-> ?x &*&
    (*v).y |-> ?y;

predicate own<T>(T t) = true;
@*/