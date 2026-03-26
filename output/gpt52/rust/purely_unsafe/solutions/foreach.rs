use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

predicate nodes<T>(n: *mut Node<T>, vs: list<T>) =
    n == 0 ?
        vs == nil
    :
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes(next, ?vs0) &*&
        vs == cons(v, vs0);

predicate stack<T>(s: *mut Stack<T>, vs: list<T>) =
    (*s).head |-> ?h &*&
    nodes(h, vs);

@*/

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(result != 0 &*& *result |> ?_st &*& stack(result, nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, vs) &*& result == (vs == nil))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack(stack, cons(?v, ?vs0)))]
    #[ensures(stack(stack, vs0) &*& result == v)]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(*stack |> ?_st &*& stack(stack, ?vs) &*& vs == nil)]
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

/*@

predicate vector(v: *mut Vector, x: i32, y: i32) =
    (*v).x |-> x &*& (*v).y |-> y;

@*/

impl Vector {
    #[requires(true)]
    #[ensures(result != 0 &*& *result |> ?_v &*& vector(result, x, y))]
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
            /*@ invariant *s |> ?_st &*& stack(s, ?vs); @*/
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