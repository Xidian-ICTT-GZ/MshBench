use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate stack_node<T>(node: *mut Node<T>, next: *mut Node<T>) =
    node != std::ptr::null_mut() &&
    Owned(node) &&
    (*node).next |-> next &&
    (*node).value |-> _ &&
    stack_list(next);

predicate stack_list<T>(head: *mut Node<T>) =
    head == std::ptr::null_mut() ||
    (exists(next: *mut Node<T>). stack_node(head, next));

predicate stack_inv<T>(stack: *mut Stack<T>) =
    stack != std::ptr::null_mut() &&
    Owned(stack) &&
    (*stack).head |-> ?head &&
    stack_list(head);

impl<T> Stack<T> {
    #[ensures(stack_inv(result))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack) && result == ((*old((*stack).head)) == std::ptr::null_mut()))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack_inv(stack) && (*stack).head != std::ptr::null_mut())]
    #[ensures(stack_inv(stack))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(stack_inv(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

unsafe fn input_char() -> char {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32 {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32) {
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

predicate vector_valid(v: *mut Vector, limit: i32) =
    v != std::ptr::null_mut() &&
    Owned(v) &&
    (*v).x |-> ?x &&
    (*v).y |-> ?y &&
    x * x + y * y <= limit * limit;

impl Vector {
    #[requires(x * x + y * y <= limit * limit)]
    #[ensures(vector_valid(result, limit))]
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

                    let sum_x = (*v1).x + (*v2).x;
                    let sum_y = (*v1).y + (*v2).y;
                    assert!(sum_x * sum_x + sum_y * sum_y <= limit * limit);
                    let sum = Vector::create(limit, sum_x, sum_y);
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