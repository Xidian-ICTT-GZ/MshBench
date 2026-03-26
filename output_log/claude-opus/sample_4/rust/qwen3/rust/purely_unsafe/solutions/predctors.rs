use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
fn node<T>(p: *mut Node<T>, v: T, next: *mut Node<T>) =
    p != 0 &*& data_at::<Node<T>>(p, Node { next: next, value: v });

#[pred]
fn stack<T>(p: *mut Stack<T>, nodes: list<*mut Node<T>>) =
    p != 0 &*& data_at::<Stack<T>>(p, Stack { head: if nodes == nil { std::ptr::null_mut() } else { hd(nodes) } }) &*&
    nodes_pred(nodes);

#[pred]
fn nodes_pred<T>(nodes: list<*mut Node<T>>) =
    switch(nodes) {
        case nil => emp,
        case cons(h, t) => node(h, _, _) &*& nodes_pred(t)
    };

#[pred]
fn vector(p: *mut Vector, x: int, y: int) =
    p != 0 &*& data_at::<Vector>(p, Vector { x: x, y: y });

impl<T> Stack<T> {
    #[requires(Layout::new::<Stack<T>>().size() > 0)]
    #[ensures(result != 0 &*& stack(result, nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != 0 &*& stack(stack, nodes))]
    #[ensures(stack(stack, cons(n, nodes)) &*& node(n, value, old(stack).head))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack != 0 &*& stack(stack, nodes))]
    #[ensures(result == (nodes == nil))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack != 0 &*& stack(stack, cons(h, t)) &*& node(h, v, next))]
    #[ensures(stack(stack, t) &*& result == v)]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(stack != 0 &*& stack(stack, nodes) &*& nodes_pred(nodes))]
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

impl Vector {
    #[requires(limit >= 0 &*& x * x + y * y <= limit * limit)]
    #[ensures(result != 0 &*& vector(result, x, y))]
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

                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v2).y + (*v1).y);
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