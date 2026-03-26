use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

predicate node<T>(n: *mut Node<T>, next: *mut Node<T>, v: T) =
    n != 0 &*&
    (*n).next |-> next &*&
    (*n).value |-> v;

predicate nodes<T>(h: *mut Node<T>; vs: list<T>) =
    h == 0 ?
        vs == nil
    :
        exists::<*mut Node<T> >(?nxt) &*& exists::<T>(?v) &*&
        node::<T>(h, nxt, v) &*& nodes::<T>(nxt; ?vs0) &*& vs == cons(v, vs0);

predicate stack<T>(s: *mut Stack<T>; vs: list<T>) =
    s != 0 &*&
    (*s).head |-> ?h &*&
    nodes::<T>(h; vs);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ requires true;
    //@ ensures stack::<T>(result; nil);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires stack::<T>(stack; ?vs);
    //@ ensures stack::<T>(stack; cons(value, vs));
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
    //@ requires stack::<T>(stack; ?vs);
    //@ ensures stack::<T>(stack; vs) &*& (result == (vs == nil));
    {

        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires stack::<T>(stack; cons(?v, ?vs0));
    //@ ensures stack::<T>(stack; vs0) &*& result == v;
    {

        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires stack::<T>(stack; nil);
    //@ ensures true;
    {

        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

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

/*@

predicate vector(v: *mut Vector; x: i32, y: i32) =
    v != 0 &*& (*v).x |-> x &*& (*v).y |-> y;

@*/

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ requires true;
    //@ ensures vector(result; x, y);
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

        loop
            //@ invariant stack::<*mut Vector>(s; ?vs) &*& forall(vs, (lambda (p: *mut Vector) vector(p; ?x, ?y)));
        {

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