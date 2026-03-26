use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(n: *mut Node<T>, next: *mut Node<T>, v: T) = n as *mut u8 |-> ?b &*& struct_Node_padding(b) &*& [?q]lifetime_token(?l) &*& struct_Node_fields(b, l, q, next, v);

//@ pred stack<T>(s: *mut Stack<T>) = s as *mut u8 |-> ?b &*& struct_Stack_padding(b) &*& [?q]lifetime_token(?l) &*& struct_Stack_fields(b, l, q, ?head) &*& nodes(head);

//@ fixpoint bool nodes<T>(*mut Node<T> n);
//@ pred nodes<T>(n: *mut Node<T>) =
//@   if n == null_mut() then true
//@   else node(n, ?next, ?v) &*& nodes(next);

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack(stack) &*& [?q]lifetime_token(?l) &*& struct_Node_padding(?b1) &*& struct_Node_fields(b1, l, q, _ , value);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == std::ptr::null_mut());
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ close stack(stack);
        let result = head.is_null();
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack) &*& [?q]lifetime_token(?l) &*& struct_Node_padding(?b1) &*& struct_Node_fields(b1, l, q, _ , result);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open node(head, ?next, ?v);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
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

//@ pred vector(v: *mut Vector, x: i32, y: i32) = v as *mut u8 |-> ?b &*& struct_Vector_padding(b) &*& [?q]lifetime_token(?l) &*& struct_Vector_fields(b, l, q, x, y);

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens vector(result, x, y);
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
//@ req true;
//@ ens true;
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