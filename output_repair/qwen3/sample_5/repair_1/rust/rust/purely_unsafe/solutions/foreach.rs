use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr;

// Predicates for separation logic
predicate stack_node<T>(p: *mut Node<T>, v: T) {
    p -> value == v &*& p -> next == _
}

predicate stack_list<T>(s: *mut Stack<T>) {
    s -> head == null() &*& true
  | s -> head != null() &*& node_ptr(s -> head, _) &*& stack_list(s)
}

predicate node_ptr<T>(p: *mut Node<T>, v: T) {
    alloc::<Node<T>>(p) &*& (*p).value == v &*& (*p).next == null()
}

predicate vector_ptr(v: *mut Vector, x: i32, y: i32) {
    alloc::<Vector>(v) &*& (*v).x == x &*& (*v).y == y
}

predicate stack<T>(s: *mut Stack<T>) {
    alloc::<Stack<T>>(s) &*& (*s).head == null()
}

predicate stack_with_nodes<T>(s: *mut Stack<T>) {
    alloc::<Stack<T>>(s) &*& (*s).head != null() &*& list_of_nodes((*s).head)
}

predicate list_of_nodes<T>(p: *mut Node<T>) {
    p == null()
  | alloc::<Node<T>>(p) &*& list_of_nodes((*p).next)
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
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = ptr::null_mut();
        stack
    }

    #[requires(stack_with_nodes(stack))]
    #[ensures(stack_with_nodes(result))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack_with_nodes(stack))]
    #[ensures(stack_with_nodes(stack))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;
        head.is_null()
    }

    #[requires(stack_with_nodes(stack))]
    #[ensures(stack_with_nodes(result))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;
        assert!(!head.is_null());
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(stack_with_nodes(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        // Dispose of all nodes in the list
        let mut current = (*stack).head;
        while !current.is_null() {
            let next = (*current).next;
            dealloc(current as *mut u8, Layout::new::<Node<T>>());
            current = next;
        }
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
    #[ensures(vector_ptr(result, x, y))]
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
        }
    }
}