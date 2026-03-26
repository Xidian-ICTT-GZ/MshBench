use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(n: *mut Node<T>) {
    n != std::ptr::null_mut() && struct_Node!<T> { next: ?next, value: ?v }(n) && 
    (next == std::ptr::null_mut() ? true : node::<T>(next))
}

predicate stack<T>(s: *mut Stack<T>) {
    s != std::ptr::null_mut() && struct_Stack!<T> { head: ?head }(s) &&
    (head == std::ptr::null_mut() ? true : node::<T>(head))
}

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close node(n);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close stack(stack);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack(stack) &*& !((*stack).head).is_null();
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open node(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack(stack);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close node(m);
        loop {
            //@ invariant node(n) &*& node(m);
            //@ open node(n);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
            //@ close node(m);
        }
        (*stack).head = m;
        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open node(_);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

predicate point(p: *mut Point) {
    p != std::ptr::null_mut() && struct_Point { x: ?x, y: ?y }(p)
}

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
    //@ req true;
    //@ ens point(result);
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close point(result);
        result
    }
    
}

fn main()
//@ req true;
//@ ens true;
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
        //@ open point(p1);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open point(p2);
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}