use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

struct Vector {
    x: i32,
    y: i32,
}

/*@

pred nodes_list<T>(head: *mut Node<T>;) =
    if head == 0 {
        true
    } else {
        (*head).next |-> ?next &*& (*head).value |-> ?value &*& struct_Node_padding(head) &*& alloc_block(head, std::alloc::Layout::new_::<Node<T>>()) &*& nodes_list::<T>(next)
    };

pred stack_own<T>(stack: *mut Stack<T>;) =
    (*stack).head |-> ?head &*& struct_Stack_padding(stack) &*& alloc_block(stack, std::alloc::Layout::new_::<Stack<T>>()) &*& nodes_list::<T>(head);

pred vector_own(v: *mut Vector, limit: i32;) =
    (*v).x |-> ?x &*& (*v).y |-> ?y &*& struct_Vector_padding(v) &*& alloc_block(v, std::alloc::Layout::new_::<Vector>()) &*& x * x + y * y <= limit * limit;

@*/

impl<T> Stack<T> {
    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack_own::<T>(result);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes_list::<T>(0);
        //@ close stack_own::<T>(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack_own::<T>(stack);
    //@ ens stack_own::<T>(stack);
    {
        //@ open stack_own::<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close nodes_list::<T>(n);
        (*stack).head = n;
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
    //@ req stack_own::<T>(stack) &*& (*stack).head != 0;
    //@ ens stack_own::<T>(stack);
    {
        //@ open stack_own::<T>(stack);
        let head = (*stack).head;
        //@ open nodes_list::<T>(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack_own::<T>(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack_own::<T>(stack) &*& (*stack).head == 0;
    //@ ens true;
    {
        //@ open stack_own::<T>(stack);
        //@ open nodes_list::<T>(0);
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

impl Vector {
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ req x * x + y * y <= limit * limit;
    //@ ens vector_own(result, limit);
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close vector_own(result, limit);
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

        loop {
            //@ inv stack_own::<*mut Vector>(s);
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
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);

                    std::hint::assert_unchecked(
                        (*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit,
                    );
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command"),
            }
        }
    }
}