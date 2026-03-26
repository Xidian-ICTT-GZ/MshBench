use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

predicate node<T>(n: *mut Node<T>, next: *mut Node<T>, v: T) =
    n != 0 &*&
    (*n).next |-> next &*&
    (*n).value |-> v;

predicate nodes<T>(n: *mut Node<T>, vs: list<T>) =
    n == 0 ?
        vs == nil
    :
        exists::<*mut Node<T>>(fun next =>
        exists::<T>(fun v =>
            vs == cons(v, ?vs0) &*& node::<T>(n, next, v) &*& nodes::<T>(next, vs0)
        ));

predicate stack<T>(s: *mut Stack<T>, vs: list<T>) =
    s != 0 &*&
    (*s).head |-> ?h &*&
    nodes::<T>(h, vs);

fixpoint list<T> rev_acc<T>(list<T> xs, list<T> acc) {
    switch(xs) {
        case nil: acc;
        case cons(h, t): rev_acc(t, cons(h, acc));
    }
}

fixpoint list<T> reverse_list<T>(list<T> xs) { rev_acc(xs, nil); }

lemma void nodes_append_cons<T>(list<T> xs, T x)
    requires true;
    ensures append(xs, cons(x, nil)) == append(xs, cons(x, nil));
{ }

lemma void nodes_rev_acc_step<T>(list<T> xs, list<T> acc)
    requires true;
    ensures rev_acc(xs, acc) == reverse_list(xs) ==? false ? rev_acc(xs, acc) : rev_acc(xs, acc);
{ }

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ requires true;
    //@ ensures stack::<T>(result, nil);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes::<T>(0, nil);
        //@ close stack::<T>(stack, nil);
        stack
    }

    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires stack::<T>(stack, ?vs);
    //@ ensures stack::<T>(stack, cons(value, vs));
    {
        //@ open stack::<T>(stack, vs);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close node::<T>(n, ?oldHead, value);
        //@ close nodes::<T>(n, cons(value, vs));
        //@ close stack::<T>(stack, cons(value, vs));
    }

    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ requires stack::<T>(stack, ?vs);
    //@ ensures stack::<T>(stack, vs) &*& result == (vs == nil);
    {
        //@ open stack::<T>(stack, vs);
        let head = (*stack).head;
        let result = head.is_null();
        //@ assert (head == 0) == (vs == nil);
        //@ close stack::<T>(stack, vs);
        result
    }

    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires stack::<T>(stack, cons(?v, ?vs0));
    //@ ensures stack::<T>(stack, vs0) &*& result == v;
    {
        //@ open stack::<T>(stack, cons(v, vs0));
        //@ open nodes::<T>(?h, cons(v, vs0));
        let head = (*stack).head;
        //@ assert head == h;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open node::<T>(head, ?next, v);
        //@ assert result == v;
        //@ close nodes::<T>(next, vs0);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack::<T>(stack, vs0);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ requires stack::<T>(stack, ?vs);
    //@ ensures stack::<T>(stack, reverse_list(vs));
    {
        //@ open stack::<T>(stack, vs);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes::<T>(m, nil);
        //@ close nodes::<T>(n, vs);
        //@ assert nodes::<T>(n, vs) &*& nodes::<T>(m, nil);

        loop {
            //@ invariant nodes::<T>(n, ?xs) &*& nodes::<T>(m, ?acc) &*& reverse_list(vs) == rev_acc(xs, acc);
            if n.is_null() {
                break;
            }
            //@ open nodes::<T>(n, xs);
            //@ assert xs == cons(?v, ?xs0);
            //@ open node::<T>(n, ?next0, v);
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
            //@ close node::<T>(m, ?mnext, v); // mnext is old m
            //@ close nodes::<T>(m, cons(v, acc));
            //@ close nodes::<T>(n, xs0);
            //@ assert rev_acc(xs, acc) == rev_acc(xs0, cons(v, acc));
        }
        //@ open nodes::<T>(n, ?xsEnd);
        //@ assert xsEnd == nil;
        //@ close nodes::<T>(0, nil);
        (*stack).head = m;
        //@ close stack::<T>(stack, rev_acc(nil, ?accFinal));
        //@ assert rev_acc(nil, accFinal) == accFinal;
        //@ assert reverse_list(vs) == accFinal;
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires stack::<T>(stack, nil);
    //@ ensures true;
    {
        //@ open stack::<T>(stack, nil);
        //@ open nodes::<T>((*stack).head, nil);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
    //@ requires true;
    //@ ensures result != 0 &*& (*result).x |-> x &*& (*result).y |-> y;
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
        //@ open (*p1).x |-> 10;
        //@ open (*p1).y |-> 0;
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open (*p2).x |-> 0;
        //@ open (*p2).y |-> 10;
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}