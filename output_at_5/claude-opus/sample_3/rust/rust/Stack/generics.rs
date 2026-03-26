use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(p: *mut Node<T>) = 
//@     p->next |-> _ &*& p->value |-> _;
//@ pred stack<T>(s: *mut Stack<T>, list: option<list<pair<*mut Node<T>, T>>>) = 
//@     s->head |-> _;

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ensures stack(result, None);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close stack(stack, None);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack(stack, ?list);
    //@ ensures stack(stack, Some(_));
    {
        //@ open stack(stack, list);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;

        //@ close node(n);
        //@ close stack(stack, Some(_));
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack(stack, ?list);
    //@ ensures stack(stack, list);
    {
        //@ open stack(stack, list);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close stack(stack, list);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack(stack, Some(_));
    //@ ensures stack(stack, ?rest);
    {
        //@ open stack(stack, Some(_));
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        //@ open node(head);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        //@ close stack(stack, ?rest);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req stack(stack, ?list);
    //@ ensures stack(stack, list);
    {
        //@ open stack(stack, list);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        while n != std::ptr::null_mut()
        //@ invariant stack(stack, ?l);
        //@ invariant true;
        {
            //@ open node(n);
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
            //@ close node(m);
        }
        (*stack).head = m;
        //@ close stack(stack, list);
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack(stack, None);
    //@ ensures true;
    {
        //@ open stack(stack, None);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
    //@ req true;
    //@ ensures true;
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