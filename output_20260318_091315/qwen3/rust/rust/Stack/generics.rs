use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(n: *mut Node<T>, next: *mut Node<T>, value: T) =
    n != std::ptr::null_mut() &*&
    struct_Node { next: next, value: value } @ n;

predicate stack<T>(s: *mut Stack<T>, nodes: list<*mut Node<T>>) =
    s != std::ptr::null_mut() &*&
    match nodes {
        cons(hd, tl) => (*s).head |-> hd &*& node(hd, ?next, ?v) &*& stack_nodes(next, tl),
        nil => (*s).head |-> std::ptr::null_mut(),
    };

predicate stack_nodes<T>(curr: *mut Node<T>, rest: list<*mut Node<T>>) =
    match rest {
        cons(hd, tl) => curr == hd &*& node(hd, ?next, ?v) &*& stack_nodes(next, tl),
        nil => curr == std::ptr::null_mut(),
    };

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
    
    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, cons(n, nodes)) &*& node(n, ?_, value))]
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
    
    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, nodes) &*& result == (match nodes { cons(_, _) => false, nil => true }))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    #[requires(stack(stack, cons(head, ?rest)))]
    #[ensures(stack(stack, rest) &*& result == ?value &*& node(head, ?_, value))]
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, reverse(nodes)))]
    unsafe fn reverse(stack: *mut Stack<T>)
    {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        loop {
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
        }
        (*stack).head = m;
    }

    #[requires(stack(stack, _))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

predicate point(p: *mut Point, x: i32, y: i32) =
    p != std::ptr::null_mut() &*&
    struct_Point { x: x, y: y } @ p;

impl Point {

    #[requires(true)]
    #[ensures(point(result, x, y))]
    unsafe fn create(x: i32, y: i32) -> *mut Point
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
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
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        std::hint::assert_unchecked(Stack::pop(s) == p1);
        std::hint::assert_unchecked(Stack::pop(s) == p2);
        Stack::dispose(s);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}