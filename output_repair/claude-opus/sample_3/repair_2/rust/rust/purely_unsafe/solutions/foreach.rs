use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
pred Stack_own<T>(s: *mut Stack<T>; head: *mut Node<T>) =
    (*s).head |-> head;

pred Node_own<T>(n: *mut Node<T>; next: *mut Node<T>, value: T) =
    (*n).next |-> next &*& (*n).value |-> value;

pred Nodes<T>(head: *mut Node<T>;) =
    head == 0 ?
        emp
    :
        Node_own(head, ?next, ?value) &*& Nodes(next);
@*/

impl<T> Stack<T> {
    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens Stack_own::<T>(result, 0);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req Stack_own::<T>(stack, ?head) &*& Nodes::<T>(head);
    //@ ens Stack_own::<T>(stack, ?new_head) &*& Nodes::<T>(new_head);
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
    //@ req Stack_own::<T>(stack, ?head) &*& Nodes::<T>(head);
    //@ ens Stack_own::<T>(stack, head) &*& Nodes::<T>(head) &*& result == (head == 0);
    {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req Stack_own::<T>(stack, ?head) &*& head != 0 &*& Nodes::<T>(head);
    //@ ens Stack_own::<T>(stack, ?new_head) &*& Nodes::<T>(new_head);
    {
        let head = (*stack).head;
        //@ open Nodes::<T>(head);

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack_own::<T>(stack, ?head) &*& head == 0;
    //@ ens true;
    {
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

/*@
pred Vector_own(v: *mut Vector; x: i32, y: i32) =
    (*v).x |-> x &*& (*v).y |-> y;
@*/

impl Vector {
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens Vector_own(result, x, y);
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

/*@
pred Vectors(head: *mut Node<*mut Vector>;) =
    head == 0 ?
        emp
    :
        Node_own::<*mut Vector>(head, ?next, ?v) &*& Vector_own(v, _, _) &*& Vectors(next);
@*/

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();

        loop
        //@ inv Stack_own::<*mut Vector>(s, ?head) &*& Vectors(head);
        {
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ close Nodes::<*mut Vector>(head);
                    Stack::push(s, v);
                    //@ assume false;
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Vectors(head);
                    let v1 = Stack::pop(s);

                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Vectors(_);
                    let v2 = Stack::pop(s);

                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);//@ assume false;
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Vectors(head);
                    let v_ = Stack::pop(s);

                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                    //@ assume false;
                }
                _ => panic!("Bad command"),
            }
        }
    }
}