use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

#[predicate]
fn stack_own<T>(s: *mut Stack<T>, head: *mut Node<T>) = 
    s.points_to(Stack { head: head });

#[predicate]
fn node_own<T>(n: *mut Node<T>, next: *mut Node<T>) = 
    n.points_to(Node { next: next, value: _ });

#[predicate]
fn stack_list<T>(head: *mut Node<T>) = 
    head == std::ptr::null_mut() || 
    exists(next: *mut Node<T>) { node_own(head, next) * stack_list(next) };

impl<T> Stack<T> {
    #[ensures(stack_own(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_own(stack, head) * stack_list(head))]
    #[ensures(stack_own(stack, n) * stack_list(n))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack_own(stack, head) * stack_list(head))]
    #[ensures(stack_own(stack, head) * stack_list(head))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }

    #[requires(stack_own(stack, head) * node_own(head, next) * stack_list(next))]
    #[ensures(stack_own(stack, next) * stack_list(next))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(stack_own(stack, head) * stack_list(head))]
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

#[predicate]
fn vector_own(v: *mut Vector) = 
    v.points_to(Vector { x: _, y: _ });

impl Vector {
    #[ensures(vector_own(result))]
    unsafe fn create(x: i32, y: i32) -> *mut Vector {
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
                _ => panic!("Bad command"),
            }
        }
    }
}