use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred <T> Nodes(n: *mut Node<T>, count: i32) =
    if n == 0 {
        count == 0
    } else {
        count > 0 &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        struct_Node_padding(n) &*&
        alloc_block(n as *mut u8, Layout::new_::<Node<T>>()) &*&
        Nodes::<T>(next, count - 1)
    };

pred <T> Stack(s: *mut Stack<T>, count: i32) =
    (*s).head |-> ?head &*&
    struct_Stack_padding(s) &*&
    alloc_block(s as *mut u8, Layout::new_::<Stack<T>>()) &*&
    Nodes::<T>(head, count) &*&
    count >= 0;

pred Vector_own(v: *mut Vector) =
    (*v).x |-> ?x &*&
    (*v).y |-> ?y &*&
    struct_Vector_padding(v) &*&
    alloc_block(v as *mut u8, Layout::new_::<Vector>());

@*/

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(Stack::<T>(result, 0))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes::<T>(0 as *mut Node<T>, 0);
        //@ close Stack::<T>(stack, 0);
        stack
    }

    #[requires(Stack::<T>(stack, count))]
    #[ensures(Stack::<T>(stack, count + 1))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        //@ open Stack::<T>(stack, count);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ open Nodes::<T>((*stack).head, count);
        //@ close Nodes::<T>((*stack).head, count);
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Nodes::<T>(n, count + 1);
        //@ close Stack::<T>(stack, count + 1);
    }

    #[requires(Stack::<T>(stack, count))]
    #[ensures(Stack::<T>(stack, count) &*& (result == (count == 0)))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        //@ open Stack::<T>(stack, count);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, count);
        //@ close Nodes::<T>(head, count);
        let result = head.is_null();
        //@ close Stack::<T>(stack, count);
        result
    }

    #[requires(Stack::<T>(stack, count) &*& count > 0)]
    #[ensures(Stack::<T>(stack, count - 1))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        //@ open Stack::<T>(stack, count);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, count);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack::<T>(stack, count - 1);
        result
    }

    #[requires(Stack::<T>(stack, 0))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        //@ open Stack::<T>(stack, 0);
        //@ open Nodes::<T>(_, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

#[requires(true)]
#[ensures(true)]
unsafe fn input_char() -> char {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

#[requires(true)]
#[ensures(true)]
unsafe fn input_i32() -> i32 {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

#[requires(true)]
#[ensures(true)]
unsafe fn output_i32(value: i32) {
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {
    #[requires(true)]
    #[ensures(Vector_own(result) &*& (*result).x |-> x &*& (*result).y |-> y)]
    unsafe fn create(x: i32, y: i32) -> *mut Vector {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector_own(result);
        result
    }
}

fn main() {
    unsafe {
        let s: *mut Stack<*mut Vector> = Stack::create();

        loop {
            //@ inv Stack::<*mut Vector>(s, n) &*& n >= 0;
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
                _ => panic!("Bad command"),
            }
        }
    }
}