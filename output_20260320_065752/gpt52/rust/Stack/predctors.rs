use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred stack<T>(s: *mut Stack<T>, xs: list<T>) =
    alloc_block_Stack(s) &*& (*s).head |-> ?h &*& nodes(h, xs);

pred nodes<T>(n: *mut Node<T>, xs: list<T>) =
    n == std::ptr::null_mut() ?
        xs == nil
    :
        alloc_block_Node(n) &*& (*n).next |-> ?next &*& (*n).value |-> ?v &*& nodes(next, ?xs0) &*& xs == cons(v, xs0);

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
    //@ ens stack::<T>(result, nil);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes::<T>((*stack).head, nil);
        //@ close stack::<T>(stack, nil);
        stack
    }

    //@ req stack::<T>(stack, ?xs);
    //@ ens stack::<T>(stack, cons(value, xs));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open stack::<T>(stack, xs);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;

        //@ close nodes::<T>(n, cons(value, xs));
        //@ close stack::<T>(stack, cons(value, xs));
    }

    //@ req stack::<T>(stack, ?xs);
    //@ ens stack::<T>(stack, xs) &*& result == (xs == nil);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack::<T>(stack, xs);
        let head = (*stack).head;

        let result = head.is_null();

        //@ close stack::<T>(stack, xs);
        result
    }

    //@ req stack::<T>(stack, cons(?v, ?vs));
    //@ ens stack::<T>(stack, vs) &*& result == v;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack::<T>(stack, cons(v, vs));
        //@ open nodes::<T>((*stack).head, cons(v, vs));
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        //@ open nodes::<T>((*head).next, vs);
        //@ close nodes::<T>((*stack).head, vs);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        //@ close stack::<T>(stack, vs);
        result
    }

    //@ req stack::<T>(stack, ?xs);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack::<T>(stack, xs);
        //@ open nodes::<T>((*stack).head, xs);
        
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

//@ req true;
//@ ens true;
//@ assume_correct
unsafe fn input_char() -> char
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

//@ req true;
//@ ens true;
//@ assume_correct
unsafe fn input_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

//@ req true;
//@ ens true;
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
    //@ ens alloc_block_Vector(result) &*& (*result).x |-> x &*& (*result).y |-> y;
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
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
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();

        loop {
            //@ inv stack::<*mut Vector>(s, ?xs);
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

                    //@ open alloc_block_Vector(v1);
                    //@ open (*v1).x |-> ?x1;
                    //@ open (*v1).y |-> ?y1;
                    //@ open alloc_block_Vector(v2);
                    //@ open (*v2).x |-> ?x2;
                    //@ open (*v2).y |-> ?y2;
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);

                    //@ open alloc_block_Vector(v_);
                    //@ open (*v_).x |-> ?x_;
                    //@ open (*v_).y |-> ?y_;
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