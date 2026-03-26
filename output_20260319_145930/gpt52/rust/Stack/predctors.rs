use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred stack<T>(s: *mut Stack<T>; n: isize) =
    s != 0 &*& alloc_block(s as *u8, Layout::new_::<Stack<T>>()) &*&
    (*s).head |-> ?h &*& nodes::<T>(h, n);

pred nodes<T>(h: *mut Node<T>, n: isize) =
    h == 0 ?
        n == 0
    :
        n > 0 &*& alloc_block(h as *u8, Layout::new_::<Node<T>>()) &*&
        (*h).next |-> ?t &*& (*h).value |-> _ &*& nodes::<T>(t, n - 1);

@*/

impl<T> Stack<T> {
    //@ req true;
    //@ ens result != 0 &*& stack::<T>(result, 0);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close nodes::<T>(std::ptr::null_mut(), 0);
        (*stack).head = std::ptr::null_mut();
        //@ close stack::<T>(stack, 0);

        stack
    }

    //@ req stack::<T>(stack, ?n);
    //@ ens stack::<T>(stack, n + 1);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open stack::<T>(stack, n);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close nodes::<T>(n, n0 + 1);
        //@ close stack::<T>(stack, n0 + 1);
    }

    //@ req stack::<T>(stack, ?n);
    //@ ens stack::<T>(stack, n) &*& result == (n == 0);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack::<T>(stack, n);
        let head = (*stack).head;

        let result = head.is_null();

        //@ close stack::<T>(stack, n);
        result
    }

    //@ req stack::<T>(stack, ?n) &*& n > 0;
    //@ ens stack::<T>(stack, n - 1) &*& result |-> _;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack::<T>(stack, n);
        let head = (*stack).head;
        //@ open nodes::<T>(head, n);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        //@ close stack::<T>(stack, n - 1);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    //@ req stack::<T>(stack, ?n);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack::<T>(stack, n);
        //@ assume_correct
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

//@ req true;
//@ ens true;
unsafe fn input_char() -> char
{
    //@ assume_correct
    let mut line = String::new();
    //@ assume_correct
    std::io::stdin().read_line(&mut line).unwrap();
    //@ assume_correct
    line.chars().next().unwrap()
}

//@ req true;
//@ ens true;
unsafe fn input_i32() -> i32
{
    //@ assume_correct
    let mut line = String::new();
    //@ assume_correct
    std::io::stdin().read_line(&mut line).unwrap();
    //@ assume_correct
    line.trim().parse().unwrap()
}

//@ req true;
//@ ens true;
unsafe fn output_i32(value: i32)
{
    //@ assume_correct
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

/*@

pred vector(v: *mut Vector) =
    v != 0 &*& alloc_block(v as *u8, Layout::new_::<Vector>()) &*&
    (*v).x |-> _ &*& (*v).y |-> _;

@*/

impl Vector {
    //@ req true;
    //@ ens result != 0 &*& vector(result);
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close vector(result);

        result
    }
}

fn main()
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();

        loop {
            //@ inv stack::<*mut Vector>(s, ?n);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);

                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);

                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ assume_correct
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    //@ assume_correct
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);

                    std::hint::assert_unchecked((*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    //@ assume_correct
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command"),
            }
        }
    }
}