use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate_node<T>(node: *mut Node<T>, stack: *mut Stack<T>, next: option<*mut Node<T>>, val: T) = 
    node |-> Node { next: ?next_ptr, value: val } &*&
    next == next_ptr ? true : false;

predicate_nodes<T>(node: *mut Node<T>, stack: *mut Stack<T>, contents: list<T>) =
    switch(contents) {
        case nil => node == std::ptr::null_mut()
        case cons(head, tail) => 
            node != std::ptr::null_mut() &*&
            node |-> Node { next: ?next_ptr, value: head } &*&
            predicate_nodes(next_ptr, stack, tail)
    };

predicate_stack<T>(stack: *mut Stack<T>, contents: list<T>) = 
    stack |-> Stack { head: ?head } &*&
    predicate_nodes(head, stack, contents);

predicate_point(point: *mut Point, x: i32, y: i32) =
    point |-> Point { x: x, y: y };

impl<T> Stack<T> {

    #[requires(true)]
    #[ensures(predicate_stack(result, nil))]
    unsafe fn create() -> *mut Stack<T> 
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        stack
    }

    #[requires(predicate_stack(stack, ?contents))]
    #[ensures(predicate_stack(stack, cons(value, contents)))]
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

    #[requires(predicate_stack(stack, ?contents))]
    #[ensures(predicate_stack(stack, contents))]
    #[ensures(result == (contents == nil))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }

    #[requires(predicate_stack(stack, ?contents) &*& contents != nil)]
    #[ensures(predicate_stack(stack, tail(contents)))]
    #[ensures(result == head(contents))]
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(predicate_stack(stack, ?contents))]
    #[ensures(predicate_stack(stack, rev(contents)))]
    unsafe fn reverse(stack: *mut Stack<T>)
    {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant
            predicate_nodes(n, stack, ?rcontents) &*&
            predicate_nodes(m, stack, ?mcontents) &*&
            contents == append(rcontents, rev(mcontents))
        ]
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

    #[requires(predicate_stack(stack, nil))]
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

impl Point {
    #[requires(true)]
    #[ensures(predicate_point(result, x, y))]
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