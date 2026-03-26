use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate nodes<T>(n: *mut Node<T>, list: list<T>) =
    n == std::ptr::null_mut() ?
        emp
    :
        n |-> Node { next: ?next, value: ?v } &*&
        nodes(next, ?rest) &*&
        list == cons(v, rest);

predicate stack<T>(s: *mut Stack<T>, list: list<T>) =
    s |-> Stack { head: ?head } &*&
    nodes(head, list);

impl<T> Stack<T> {

    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, list))]
    #[ensures(stack(stack, cons(value, list)))]
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, list))]
    #[ensures(result == (list == nil))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack(stack, cons(?v, ?rest)))]
    #[ensures(stack(stack, rest))]
    #[ensures(result == v)]
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(stack(stack, nil))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

unsafe fn input_char() -> char
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)
{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

predicate vector(v: *mut Vector, x: i32, y: i32) =
    v |-> Vector { x: x, y: y };

impl Vector {
    #[requires(true)]
    #[ensures(vector(result, x, y))]
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;

        result
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();

        
        
        
        
        
    }
}