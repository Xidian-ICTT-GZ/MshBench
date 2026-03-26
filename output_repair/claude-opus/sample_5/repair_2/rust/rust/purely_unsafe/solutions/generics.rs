use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred Node_next<T>(n: *mut Node<T>; next: *mut Node<T>) = (*n).next |-> next;

pred Node_value<T>(n: *mut Node<T>; value: T) = (*n).value |-> value;

pred Node<T>(n: *mut Node<T>; next: *mut Node<T>, value: T) =
    Node_next(n, next) &*& Node_value(n, value);

pred Stack_head<T>(s: *mut Stack<T>; head: *mut Node<T>) = (*s).head |-> head;

pred Nodes<T>(n: *mut Node<T>; count: i32) =
    if n == 0 {
        count == 0
    } else {
        count > 0 &*&
        Node_next::<T>(n, ?next) &*& Node_value::<T>(n, ?value) &*&
        Nodes::<T>(next, count - 1)
    };

pred Stack<T>(s: *mut Stack<T>; count: i32) =
    Stack_head(s, ?head) &*& Nodes::<T>(head, count);

@*/

impl<T> Stack<T> {
    /*@
    req true;
    ens Stack::<T>(result, 0);
    @*/
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes::<T>(std::ptr::null_mut(), 0);
        //@ close Stack::<T>(stack, 0);
        stack
    }

    /*@
    req Stack::<T>(stack, ?count);
    ens Stack::<T>(stack, count + 1);
    @*/
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        //@ open Stack::<T>(stack, count);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ open Stack_head::<T>(stack, ?head);
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Node_next::<T>(n, head);
        //@ close Node_value::<T>(n, value);
        //@ close Nodes::<T>(n, count + 1);
        (*stack).head = n;
        //@ close Stack_head::<T>(stack, n);
        //@ close Stack::<T>(stack, count + 1);
    }

    /*@
    req Stack::<T>(stack, ?count);
    ens Stack::<T>(stack, count) &*& result == (count == 0);
    @*/
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        //@ open Stack::<T>(stack, count);
        //@ open Stack_head::<T>(stack, ?head);
        let head = (*stack).head;
        //@ close Stack_head::<T>(stack, head);
        //@ close Stack::<T>(stack, count);
        let result = head.is_null();

        result
    }

    /*@
    req Stack::<T>(stack, ?count) &*& count > 0;
    ens Stack::<T>(stack, count - 1);
    @*/
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        //@ open Stack::<T>(stack, count);
        //@ open Stack_head::<T>(stack, ?head);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, count);
        //@ open Node_next::<T>(head, ?next);
        //@ open Node_value::<T>(head, ?value);

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack_head::<T>(stack, next);
        //@ close Stack::<T>(stack, count - 1);
        result
    }

    /*@
    req Stack::<T>(stack, ?count);
    ens Stack::<T>(stack, count);
    @*/
    unsafe fn reverse(stack: *mut Stack<T>) {
        //@ open Stack::<T>(stack, count);
        //@ open Stack_head::<T>(stack, ?head);
        let mut n = (*stack).head;
        let mut m: *mut Node<T> = std::ptr::null_mut();
        //@ close Nodes::<T>(m, 0);
        //@ let mut n_count = count;
        //@ let mut m_count = 0i32;

        loop {
            /*@
            inv Nodes::<T>(n, n_count) &*& Nodes::<T>(m, m_count) &*&
                n_count >= 0 &*& m_count >= 0 &*& n_count + m_count == count &*&
                (*stack).head |-> _;
            @*/
            if n.is_null() {
                break;
            }
            //@ open Nodes::<T>(n, n_count);
            //@ open Node_next::<T>(n, ?next);
            let next = (*n).next;

            (*n).next = m;
            //@ close Node_next::<T>(n, m);
            //@ close Nodes::<T>(n, m_count + 1);
            m = n;
            n = next;
            //@ n_count = n_count - 1;
            //@ m_count = m_count + 1;
        }
        //@ open Nodes::<T>(n, n_count);
        (*stack).head = m;
        //@ close Stack_head::<T>(stack, m);
        //@ close Stack::<T>(stack, count);
    }

    /*@
    req Stack::<T>(stack, 0);
    ens true;
    @*/
    unsafe fn dispose(stack: *mut Stack<T>) {
        //@ open Stack::<T>(stack, 0);
        //@ open Stack_head::<T>(stack, ?head);
        //@ open Nodes::<T>(head, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

struct Point {
    x: i32,
    y: i32,
}

/*@

pred Point(p: *mut Point; x: i32, y: i32) =
    (*p).x |-> x &*& (*p).y |-> y;

@*/

impl Point {
    /*@
    req true;
    ens Point(result, x, y);
    @*/
    unsafe fn create(x: i32, y: i32) -> *mut Point {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Point(result, x, y);
        result
    }
}

fn main() {
    unsafe {
        let s: *mut Stack<*mut Point> = Stack::create();
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        let r1 = Stack::pop(s);
        let r2 = Stack::pop(s);
        Stack::dispose(s);
        //@ open Point(p1, _, _);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open Point(p2, _, _);
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}