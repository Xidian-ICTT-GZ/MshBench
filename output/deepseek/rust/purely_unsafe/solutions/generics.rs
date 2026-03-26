use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

#[predicate]
fn node_points_to<T>(n: *mut Node<T>, next: *mut Node<T>, value: T) -> bool {
    struct_pred!(Node<T> { next, value } @ n)
}

#[predicate]
fn stack_points_to<T>(s: *mut Stack<T>, head: *mut Node<T>) -> bool {
    struct_pred!(Stack<T> { head } @ s)
}

#[predicate]
fn lseg<T>(first: *mut Node<T>, last: *mut Node<T>) -> bool {
    first == last || exists!(next: *mut Node<T>, value: T => node_points_to(first, next, value) * lseg(next, last))
}

#[predicate]
fn stack<T>(s: *mut Stack<T>) -> bool {
    exists!(head: *mut Node<T> => stack_points_to(s, head) * lseg(head, std::ptr::null_mut()))
}

#[predicate]
fn point_points_to(p: *mut Point, x: i32, y: i32) -> bool {
    struct_pred!(Point { x, y } @ p)
}

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(s) * point_points_to(value, _, _))]
    #[ensures(stack(s))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack(s))]
    #[ensures(stack(s) * result == ((*s).head).is_null())]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack(s) * (*s).head != std::ptr::null_mut())]
    #[ensures(stack(s) * point_points_to(result, _, _))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(stack(s))]
    #[ensures(stack(s))]
    unsafe fn reverse(stack: *mut Stack<T>) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant(stack_points_to(stack, n) * lseg(m, std::ptr::null_mut()) * lseg(n, std::ptr::null_mut()))]
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

    #[requires(stack(s))]
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
    #[requires(true)]
    #[ensures(point_points_to(result, x, y))]
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