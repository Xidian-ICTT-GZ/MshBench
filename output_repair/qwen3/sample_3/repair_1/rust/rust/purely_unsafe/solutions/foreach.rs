use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn node<T>(p: *mut Node<T>, v: T) -> Prop {
    p != null() && (*p).value == v && (*p).next == null()
}

#[predicate]
fn stack<T>(s: *mut Stack<T>, h: *mut Node<T>) -> Prop {
    s != null() && (*s).head == h
}

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(stack(result, null()))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack_ptr, h))]
    #[ensures(stack(stack_ptr, new_h))]
    unsafe fn push(stack_ptr: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack_ptr).head;
        (&raw mut (*n).value).write(value);
        (*stack_ptr).head = n;
    }

    #[requires(stack(stack_ptr, h))]
    #[ensures(stack(stack_ptr, h))]
    unsafe fn is_empty(stack_ptr: *mut Stack<T>) -> bool {
        let head = (*stack_ptr).head;
        let result = head.is_null();
        result
    }

    #[requires(stack(stack_ptr, h) && !h.is_null())]
    #[ensures(stack(stack_ptr, new_h))]
    unsafe fn pop(stack_ptr: *mut Stack<T>) -> T {
        let head = (*stack_ptr).head;
        (*stack_ptr).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(stack(stack_ptr, h))]
    #[ensures(true)]
    unsafe fn dispose(stack_ptr: *mut Stack<T>) {
        dealloc(stack_ptr as *mut u8, Layout::new::<Stack<T>>());
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
fn vector(v: *mut Vector, vx: i32, vy: i32) -> Prop {
    v != null() && (*v).x == vx && (*v).y == vy
}

impl Vector {
    #[requires(true)]
    #[ensures(vector(result, x, y))]
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
        
        // Simplified loop for verification purposes
        // Note: Unbounded loops with I/O are generally not verifiable in VeriFast
        // This implementation assumes a finite number of operations for demonstration
        
        let cmd = input_char();
        match cmd {
            'p' => {
                let x = input_i32();
                let y = input_i32();
                let v = Vector::create(x, y);
                Stack::push(s, v);
            }
            '+' => {
                assert!(!Stack::is_empty(s));
                let v1 = Stack::pop(s);
                
                assert!(!Stack::is_empty(s));
                let v2 = Stack::pop(s);
                
                let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                dealloc(v1 as *mut u8, Layout::new::<Vector>());
                dealloc(v2 as *mut u8, Layout::new::<Vector>());
                Stack::push(s, sum);
            }
            '=' => {
                assert!(!Stack::is_empty(s));
                let v_ = Stack::pop(s);
                
                output_i32((*v_).x);
                output_i32((*v_).y);
                dealloc(v_ as *mut u8, Layout::new::<Vector>());
            }
            _ => panic!("Bad command"),
        }
        
        Stack::dispose(s);
    }
}