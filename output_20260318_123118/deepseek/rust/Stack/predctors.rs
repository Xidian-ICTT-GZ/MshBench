use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

#[predicate]
fn node_points_to<T>(n: *mut Node<T>, next: *mut Node<T>, v: T) -> bool {
    struct_pred!(Node<T> { next, value: v }) @ n
}

#[predicate]
fn stack_points_to<T>(s: *mut Stack<T>, head: *mut Node<T>) -> bool {
    struct_pred!(Stack<T> { head }) @ s
}

#[predicate]
fn llist<T>(head: *mut Node<T>) -> bool {
    if head.is_null() {
        true
    } else {
        exists(|next: *mut Node<T>, v: T| 
            node_points_to(head, next, v) && llist(next)
        )
    }
}

#[predicate]
fn vector_points_to(v: *mut Vector, x: i32, y: i32) -> bool {
    struct_pred!(Vector { x, y }) @ v
}

#[predicate]
fn vector_within_limit(v: *mut Vector, limit: i32) -> bool {
    exists(|x: i32, y: i32| 
        vector_points_to(v, x, y) && x * x + y * y <= limit * limit
    )
}

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(
        if result.is_null() { false } else {
            stack_points_to(result, std::ptr::null_mut())
        }
    )]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(
        stack_points_to(stack, old_head) && llist(old_head)
    )]
    #[ensures(
        exists(|n: *mut Node<T>| 
            stack_points_to(stack, n) && 
            node_points_to(n, old_head, value) && 
            llist(n)
        )
    )]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }
    
    #[requires(
        stack_points_to(stack, head) && llist(head)
    )]
    #[ensures(
        stack_points_to(stack, head) && llist(head) &&
        result == head.is_null()
    )]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    #[requires(
        exists(|next: *mut Node<T>, v: T| 
            stack_points_to(stack, head) && 
            node_points_to(head, next, v) && 
            llist(head)
        )
    )]
    #[ensures(
        stack_points_to(stack, next) && llist(next) && result == v
    )]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(
        stack_points_to(stack, head) && llist(head)
    )]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
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
    #[requires(x * x + y * y <= limit * limit)]
    #[ensures(vector_points_to(result, x, y))]
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

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        
        #[invariant(
            stack_points_to(s, head) && 
            llist(head) &&
            forall(|node_ptr: *mut Node<*mut Vector>| 
                llist(head) && !node_ptr.is_null() ==> 
                exists(|next: *mut Node<*mut Vector>, v_ptr: *mut Vector| 
                    node_points_to(node_ptr, next, v_ptr) && 
                    vector_within_limit(v_ptr, limit)
                )
            )
        )]
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