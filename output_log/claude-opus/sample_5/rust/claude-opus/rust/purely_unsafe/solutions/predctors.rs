use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate Node<T>(n: *mut Node<T>; next: *mut Node<T>, value: T) =
    (*n).next |-> next &*& (*n).value |-> value;

predicate Nodes<T>(head: *mut Node<T>; limit: i32) =
    head == std::ptr::null_mut() ?
        emp
    :
        Node::<T>(head, ?next, ?v) &*& Vector(v, limit) &*& Nodes::<T>(next, limit);

predicate Stack<T>(stack: *mut Stack<T>; limit: i32) =
    (*stack).head |-> ?head &*& Nodes::<T>(head, limit);

predicate Vector(v: *mut Vector; limit: int) =
    (*v).x |-> ?x &*& (*v).y |-> ?y &*& x * x + y * y <= limit * limit;

impl<T> Stack<T> {
    #[ensures(Stack::<T>(result, limit))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(Stack::<T>(stack, limit) &*& Vector(value, limit))]
    #[ensures(Stack::<T>(stack, limit))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(Stack::<T>(stack, limit))]
    #[ensures(Stack::<T>(stack, limit) &*& (result == true ? emp : Nodes::<T>((*stack).head, limit)))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(Stack::<T>(stack, limit) &*& Nodes::<T>((*stack).head, limit))]
    #[ensures(Stack::<T>(stack, limit) &*& Vector(result, limit))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires((*stack).head |-> ?head &*& head == std::ptr::null_mut())]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

#[ensures(emp)]
unsafe fn input_char() -> char {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

#[ensures(emp)]
unsafe fn input_i32() -> i32 {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

#[requires(emp)]
#[ensures(emp)]
unsafe fn output_i32(value: i32) {
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {
    #[requires(x * x + y * y <= limit * limit)]
    #[ensures(Vector(result, limit))]
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector {
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

fn main() {
    unsafe {
        let limit = input_i32();
        let s = Stack::create();

        #[invariant(Stack::<*mut Vector>(s, limit))]
        loop {
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