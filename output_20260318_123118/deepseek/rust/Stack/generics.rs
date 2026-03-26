use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(n: *mut Node<T>, value: T, next: *mut Node<T>) {
    n != std::ptr::null_mut() &&
    struct_Node!<T>(n; next, value) &&
    &raw mut (*n).next |-> next &&
    &raw mut (*n).value |-> value
}

predicate nodes<T>(head: *mut Node<T>) {
    head == std::ptr::null_mut() ? true : 
        exists::<*mut Node<T>, T>(next, value)
        node(head, value, next) * nodes(next)
}

predicate stack<T>(s: *mut Stack<T>) {
    s != std::ptr::null_mut() &&
    struct_Stack!<T>(s; head) &&
    &raw mut (*s).head |-> head &&
    nodes::<T>(head)
}

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && stack::<T>(result))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack::<T>(stack))]
    #[ensures(stack::<T>(stack))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }
    
    #[requires(stack::<T>(stack))]
    #[ensures(stack::<T>(stack))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    #[requires(stack::<T>(stack) && (*stack).head != std::ptr::null_mut())]
    #[ensures(stack::<T>(stack))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(stack::<T>(stack))]
    #[ensures(stack::<T>(stack))]
    unsafe fn reverse(stack: *mut Stack<T>) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        #[invariant(nodes::<T>(n) * nodes::<T>(m))]
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

    #[requires(stack::<T>(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

struct Point {
    x: i32,
    y: i32,
}

predicate point(p: *mut Point, x: i32, y: i32) {
    p != std::ptr::null_mut() &&
    struct_Point!(p; x, y) &&
    &raw mut (*p).x |-> x &&
    &raw mut (*p).y |-> y
}

impl Point {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && point(result, x, y))]
    unsafe fn create(x: i32, y: i32) -> *mut Point {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        result
    }
}

fn main() {
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