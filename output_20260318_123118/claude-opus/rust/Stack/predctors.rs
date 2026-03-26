use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate_node<T>(node: *mut Node<T>, value: T, next: *mut Node<T>) =
    node |-> Node {
        next: next,
        value: value
    };

predicate_stack<T>(stack: *mut Stack<T>, contents: list<T>) =
    stack |-> Stack { head: ?head } &*& linked_nodes(head, contents);

predicate linked_nodes<T>(head: *mut Node<T>, contents: list<T>) =
    switch contents {
        case nil: head == std::ptr::null_mut() &*& emp
        case cons(h, t): head != std::ptr::null_mut() &*& predicate_node(head, h, ?next) &*& linked_nodes(next, t)
    };

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && predicate_stack(result, nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(predicate_stack(stack, ?contents))]
    #[ensures(predicate_stack(stack, cons(value, contents)))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(predicate_stack(stack, ?contents))]
    #[ensures(result == contents == nil)]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }

    #[requires(predicate_stack(stack, ?contents) &*& contents != nil)]
    #[ensures(predicate_stack(stack, tail(contents)) &*& result == head(contents))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(predicate_stack(stack, nil))]
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

predicate_vector(v: *mut Vector, x: i32, y: i32) = 
    v |-> Vector { x: x, y: y };

impl Vector {
    #[requires(x * x + y * y <= limit * limit)]
    #[ensures(predicate_vector(result, x, y))]
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
        #[invariant(predicate_stack(s, ?stk_contents))]
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