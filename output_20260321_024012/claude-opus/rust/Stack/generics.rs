use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(n: *mut Node<T>) = n->next |-> ?next &*& n->value |-> ?v;
//@ pred stack<T>(s: *mut Stack<T>) = s->head |-> ?head &*& (head == std::ptr::null_mut() || node(head));

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
        //@ requires true;
        //@ ensures stack(result);
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
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
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
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
        //@ requires stack(stack) &*& (*stack).head != std::ptr::null_mut();
        //@ ensures stack(stack);
    {
        let head = (*stack).head;
        //@ open stack(stack);
        //@ open node(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack(stack);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        
        loop {
            if n.is_null() {
                break;
            }
            //@ open node(n);
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
        }
        (*stack).head = m;
        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack<T>)
        //@ requires stack(stack);
        //@ ensures true;
    {
        //@ open stack(stack);
        //@ while (*stack).head != std::ptr::null_mut() {
        //@   let head = (*stack).head;
        //@   open node(head);
        //@   (*stack).head = (*head).next;
        //@   dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ }
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

//@ pred point(p: *mut Point) = p->x |-> _ &*& p->y |-> _;

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
        //@ requires true;
        //@ ensures point(result);
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