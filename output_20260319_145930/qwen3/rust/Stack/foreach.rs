//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node<T>(p: *mut Node<T>, next: *mut Node<T>, value: T) =
    alloc_block(p, Layout::new::<Node<T>>()) &*& struct_Node_padding(p) &*&
    (*p).next |-> next &*& (*p).value |-> value;
@*/

/*@ pred stack<T>(p: *mut Stack<T>) =
    alloc_block(p, Layout::new::<Stack<T>>()) &*& struct_Stack_padding(p) &*&
    (*p).head |-> ?head &*& nodes(head);
@*/

/*@ fixpoint bool nodes<T>(*mut Node<T> p); @*/
/*@ pred nodes<T>(p: *mut Node<T>) =
    p == std::ptr::null_mut() ?
        emp
    :
        node(p, ?next, ?value) &*& nodes(next);
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
        //@ close stack(stack);
        (*stack).head = std::ptr::null_mut();
        //@ open stack(stack);
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }
    
    //@ req stack(stack) &*& nodes(?old_head) &*& stack |-> ?s &*& s.head |-> old_head &*& nodes(old_head);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open stack(stack);
        //@ open nodes(?old_head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ close node(n, old_head, value);
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close nodes(n);
        //@ close stack(stack);
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == std::ptr::null_mut());
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ close stack(stack);
        let result = head.is_null();
        result
    }
    
    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack) &*& result |-> _;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open node(head, _, result);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close nodes((*stack).head);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack(stack);
        //@ open nodes(_);
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

/*@ pred vector(p: *mut Vector) =
    alloc_block(p, Layout::new::<Vector>()) &*& struct_Vector_padding(p) &*&
    (*p).x |-> ?x &*& (*p).y |-> ?y;
@*/

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {

    //@ req true;
    //@ ens vector(result);
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        //@ close vector(result);
        (*result).x = x;
        (*result).y = y;
        result
    }
    
}

fn main()
{
    unsafe {
        let s = Stack::create();
        //@ open stack(s);
        //@ close stack(s);
        
        loop {
            //@ inv stack(s);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ open vector(v);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open vector(v1);
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open vector(v2);
                    
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ open vector(sum);
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open vector(v_);
                    
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}