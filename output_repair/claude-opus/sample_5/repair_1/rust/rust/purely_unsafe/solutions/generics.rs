use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate node_owns<T>(n: *mut Node<T>, next: *mut Node<T>) = 
  n != std::ptr::null_mut() && 
  (n as *mut u8) |-> _ &&
  (n as usize + std::mem::offset_of!(Node<T>, next)) |-> next &&
  (n as usize + std::mem::offset_of!(Node<T>, value)) |-> _;

predicate stack_owns<T>(s: *mut Stack<T>, head: *mut Node<T>) =
  s != std::ptr::null_mut() &&
  (s as *mut u8) |-> _ &&
  (s as usize + std::mem::offset_of!(Stack<T>, head)) |-> head;

predicate list_owns<T>(n: *mut Node<T>) =
  n == std::ptr::null_mut() ||
  (exists next: *mut Node<T>. node_owns(n, next) && list_owns(next));

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    #[ensures(result != std::ptr::null_mut() && stack_owns(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != std::ptr::null_mut() && stack_owns(stack, _))]
    #[ensures(stack_owns(stack, _))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack != std::ptr::null_mut() && stack_owns(stack, _))]
    #[ensures(true)]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack != std::ptr::null_mut() && stack_owns(stack, _))]
    #[ensures(stack_owns(stack, _))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(stack != std::ptr::null_mut() && stack_owns(stack, _))]
    #[ensures(stack_owns(stack, _))]
    unsafe fn reverse(stack: *mut Stack<T>) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        loop {
            #[invariant(stack != std::ptr::null_mut() && stack_owns(stack, _))]
            {
                if n.is_null() {
                    break;
                }
                let next = (*n).next;

                (*n).next = m;
                m = n;
                n = next;
            }
        }
        (*stack).head = m;
    }

    #[requires(stack != std::ptr::null_mut() && stack_owns(stack, _))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

struct Point {
    x: i32,
    y: i32,
}

impl Point {
    #[ensures(result != std::ptr::null_mut())]
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