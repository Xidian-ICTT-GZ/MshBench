use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate Node<T>(*n: *mut Node<T>, value: T, next: *mut Node<T>) =
    n |-> Node<T> { next: next, value: value };

predicate Nodes<T>(*head: *mut Node<T>) =
    head == std::ptr::null_mut() ?
        emp
    :
        exists(value: T, next: *mut Node<T>) &*&
            Node(head, value, next) &*& Nodes(next);

predicate StackPred<T>(*stack: *mut Stack<T>, l: list<T>) =
    stack |-> Stack<T> { head: ?head } &*&
    head == l.head ? emp : emp &*& Nodes(head) &*& l == linked_list(head);

fixpoint list<T> linked_list<T>(*head: *mut Node<T>)
{
    switch(head) {
        case std::ptr::null_mut(): return nil;
        case cons: return cons(((Node)(cons)).value, linked_list(((Node)(cons)).next));
    }
}

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    #[requires(true)]
    #[ensures(StackPred(result, nil))]
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(StackPred(stack, l))]
    #[ensures(StackPred(stack, cons(value, l)))]
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

    #[requires(StackPred(stack, l))]
    #[ensures(StackPred(stack, l))]
    #[ensures(result == l.is_empty())]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }

    #[requires(StackPred(stack, cons(v, l)))]
    #[ensures(StackPred(stack, l))]
    #[ensures(result == v)]
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(StackPred(stack, l))]
    #[ensures(StackPred(stack, reverse(l)))]
    unsafe fn reverse(stack: *mut Stack<T>)
    {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant(
            (StackPred(stack, _) &*& 
            Nodes(n) &*& Nodes(m) &*& 
            concat(reverse_list(nodes_to_list(m)), nodes_to_list(n)) == linked_list((*stack).head))
        )]
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

    #[requires(StackPred(stack, l))]
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

predicate PointPred(*p: *mut Point, x: int, y: int) =
    p |-> Point { x: x, y: y };

impl Point {

    #[requires(true)]
    #[ensures(PointPred(result, x, y))]
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

fixpoint list<T> reverse<T>(list<T> l) {
    switch(l) {
        case nil: return nil;
        case cons(h, t): return append(reverse(t), cons(h, nil));
    }
}

fixpoint list<T> append<T>(list<T> l1, list<T> l2) {
    switch(l1) {
        case nil: return l2;
        case cons(h, t): return cons(h, append(t, l2));
    }
}

fixpoint list<T> nodes_to_list<T>(*head: *mut Node<T>) {
    switch(head) {
        case std::ptr::null_mut(): return nil;
        case cons: return cons(((Node)(cons)).value, nodes_to_list(((Node)(cons)).next));
    }
}

fixpoint list<T> reverse_list<T>(list<T> l) {
    switch(l) {
        case nil: return nil;
        case cons(h, t): return append(reverse_list(t), cons(h, nil));
    }
}

fixpoint list<T> concat<T>(list<T> l1, list<T> l2) {
    append(l1, l2)
}