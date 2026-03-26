use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr;

/*@

predicate_ctor stack<T>(s: *mut Stack<T>, h: *mut Node<T>)() = 
    s != null && [_]std_mmap(s as *u8, std::mem::size_of::<Stack<T>>()) && (*s).head |-> h;

predicate_ctor node<T>(n: *mut Node<T>, v: T, next: *mut Node<T>)() = 
    n != null && [_]std_mmap(n as *u8, std::mem::size_of::<Node<T>>()) && 
    (*n).value |-> v &*& (*n).next |-> next;

predicate_ctor vector(v: *mut Vector, vx: i32, vy: i32)() = 
    v != null && [_]std_mmap(v as *u8, std::mem::size_of::<Vector>()) && 
    (*v).x |-> vx &*& (*v).y |-> vy;

@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    /*@
    requires true;
    ensures stack(result, ptr::null_mut())();
    @*/
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    /*@
    requires 
        stack(stack_ptr, old_head)() &*& 
        node(n, value, old_head)();
    ensures stack(stack_ptr, n)();
    @*/
    unsafe fn push(stack_ptr: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack_ptr).head;
        (&raw mut (*n).value).write(value);
        (*stack_ptr).head = n;
    }

    /*@
    requires stack(stack_ptr, h)();
    ensures stack(stack_ptr, h)() &*& result == (h == ptr::null_mut());
    @*/
    unsafe fn is_empty(stack_ptr: *mut Stack<T>) -> bool {
        let head = (*stack_ptr).head;
        let result = head.is_null();
        result
    }

    /*@
    requires 
        stack(stack_ptr, h)() &*& 
        h != ptr::null_mut() &*& 
        node(h, v, new_h)();
    ensures stack(stack_ptr, new_h)() &*& result == v;
    @*/
    unsafe fn pop(stack_ptr: *mut Stack<T>) -> T {
        let head = (*stack_ptr).head;
        (*stack_ptr).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    /*@
    requires stack(stack_ptr, h)();
    ensures true;
    @*/
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

impl Vector {
    /*@
    requires true;
    ensures vector(result, x, y)();
    @*/
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
        
        // Single iteration for verification feasibility
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