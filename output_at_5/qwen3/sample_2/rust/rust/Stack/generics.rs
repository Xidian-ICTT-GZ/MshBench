use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
use std::ptr;

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ requires true;
    //@ ensures result != null && is_stack(result);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = ptr::null_mut();
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ requires is_stack(stack);
    //@ ensures is_stack(stack);
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ requires is_stack(stack);
    //@ ensures result == ((*stack).head == null);
    {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ requires is_stack(stack) && !(*stack).head.is_null();
    //@ ensures is_stack(stack) && result == old((*stack).head).value;
    {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ requires is_stack(stack);
    //@ ensures is_stack(stack);
    {
        let mut n = (*stack).head;
        let mut m = ptr::null_mut();
        
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

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ requires is_stack(stack);
    //@ ensures true;
    {
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
    //@ ensures result != null && is_point(result) && result.x == x && result.y == y;
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