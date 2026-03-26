use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

predicate_node<T>(Node<T>* n; T value, Node<T>* next) = 
    n != null &*&
    n->next |-> next &*&
    n->value |-> value;

predicate_stack<T>(Stack<T>* s; list<T> vs) =
    s != null &*&
    s->head |-> ?head &*&
    predicate_list<T>(head, vs);

predicate_list<T>(Node<T>* n, list<T> vs) =
    switch(vs) {
        case nil: return n == null;
        case cons(h, t): return predicate_node<T>(n, h, ?next) &*& predicate_list<T>(next, t);
    };

@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    //@ req true;
    //@ ens result != null &*& predicate_stack<T>(result, nil);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close predicate_stack<T>(stack, nil);
        stack
    }

    //@ req predicate_stack<T>(stack, ?vs);
    //@ ensures predicate_stack<T>(stack, cons(value, vs));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open predicate_stack<T>(stack, vs);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;

        //@ close predicate_node<T>(n, value, ?old_head);
        //@ close predicate_list<T>(n, cons(value, vs));
        //@ close predicate_stack<T>(stack, cons(value, vs));
    }

    //@ req predicate_stack<T>(stack, ?vs);
    //@ ensures predicate_stack<T>(stack, vs);
    //@ ensures result == (vs == nil);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open predicate_stack<T>(stack, vs);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close predicate_stack<T>(stack, vs);
        result
    }

    //@ req predicate_stack<T>(stack, ?vs) &*& vs != nil;
    //@ ensures predicate_stack<T>(stack, tail(vs));
    //@ ensures result == head(vs);
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open predicate_stack<T>(stack, vs);
        let head = (*stack).head;
        //@ open predicate_list<T>(head, vs);
        //@ open predicate_node<T>(head, ?v, ?next);

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        //@ close predicate_stack<T>(stack, next == null ? nil : ?tail_vs);
        //@ if next == null { close predicate_list<T>(null, nil); }
        //@ else { close predicate_list<T>(next, tail(vs)); }
        //@ close predicate_stack<T>(stack, tail(vs));
        result
    }

    //@ req predicate_stack<T>(stack, ?vs);
    //@ ensures predicate_stack<T>(stack, reverse(vs));
    unsafe fn reverse(stack: *mut Stack<T>) {
        //@ open predicate_stack<T>(stack, vs);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        //@ predicate_invariant(n, m, ?prefix, ?suffix) =
        //@     predicate_list<T>(n, suffix) &*&
        //@     predicate_list<T>(m, prefix) &*&
        //@     vs == reverse(prefix) + suffix;

        //@ close predicate_invariant(n, m, nil, vs);
        loop {
            //@ open predicate_invariant(n, m, ?prefix, ?suffix);
            if n.is_null() {
                break;
            }

            //@ open predicate_list<T>(n, suffix);
            //@ open predicate_node<T>(n, ?vh, ?next);
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;

            //@ close predicate_list<T>(m, cons(vh, prefix));
            //@ close predicate_invariant(n, m, cons(vh, prefix), suffix);
        }
        (*stack).head = m;
        //@ close predicate_stack<T>(stack, reverse(vs));
    }

    //@ req predicate_stack<T>(stack, ?vs);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open predicate_stack<T>(stack, vs);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

/*@
predicate_point(Point* p; int x, int y) = 
    p != null &*& 
    p->x |-> x &*& 
    p->y |-> y;
@*/

impl Point {
    //@ req true;
    //@ ensures result != null &*& predicate_point(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Point
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close predicate_point(result, x, y);
        result
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        //@ open predicate_point(p1, 10, 0);
        //@ open predicate_point(p2, 0, 10);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        std::hint::assert_unchecked(Stack::pop(s) == p1);
        std::hint::assert_unchecked(Stack::pop(s) == p2);
        Stack::dispose(s);
        //@ open predicate_point(p1, 10, 0);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open predicate_point(p2, 0, 10);
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}