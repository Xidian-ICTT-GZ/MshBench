use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(n: *mut Node<T>, next: *mut Node<T>, value: T) =
    n as *mut u8 |-> ?layout &*& layout == Layout::new::<Node<T>>() &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

predicate stack<T>(s: *mut Stack<T>, nodes: list<*mut Node<T>>) =
    s as *mut u8 |-> ?layout &*& layout == Layout::new::<Stack<T>>() &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> match nodes { Nil => std::ptr::null_mut(), Cons(h, _) => h } &*&
    stack_nodes(nodes);

predicate stack_nodes<T>(nodes: list<*mut Node<T>>) =
    match nodes {
        Nil => emp,
        Cons(n, rest) => node(n, match rest { Nil => std::ptr::null_mut(), Cons(h, _) => h }, ?v) * stack_nodes(rest)
    };

predicate vector(v: *mut Vector, x: i32, y: i32) =
    v as *mut u8 |-> ?layout &*& layout == Layout::new::<Vector>() &*&
    struct_Vector_padding(v) &*&
    (*v).x |-> x &*&
    (*v).y |-> y;

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(stack(result, Nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?nodes) * vector(value, ?x, ?y))]
    #[ensures(stack(stack, Cons(value, nodes)))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, nodes) &*& result == (match nodes { Nil => true, _ => false }))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack(stack, Cons(?head_node, ?rest)))]
    #[ensures(stack(stack, rest) * vector(head_node, ?x, ?y))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(stack(stack, ?nodes))]
    #[ensures(emp)]
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
        #[invariant(stack(s, ?nodes))]
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