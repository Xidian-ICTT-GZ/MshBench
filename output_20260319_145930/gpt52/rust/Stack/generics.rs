use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred nodes<T>(n: *mut Node<T>) =
    n == std::ptr::null_mut() ?
        true
    :
        alloc_block(n as *mut u8, Layout::new::<Node<T>>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes::<T>(next);

pred stack<T>(s: *mut Stack<T>) =
    alloc_block(s as *mut u8, Layout::new::<Stack<T>>()) &*&
    (*s).head |-> ?h &*&
    nodes::<T>(h);

@*/

impl<T> Stack<T> {

    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& stack::<T>(result);
    unsafe fn create() -> *mut Stack<T>
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        //@ close nodes::<T>(std::ptr::null_mut());
        //@ close stack::<T>(stack);
        stack
    }
    
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    
    
    {
        
        //@ open stack::<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        
        
        //@ close nodes::<T>((*n).next);
        //@ close nodes::<T>(n);
        //@ close stack::<T>(stack);
    }
    
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack) &*& result == ((*stack).head == std::ptr::null_mut());
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    
    
    {
        
        //@ open stack::<T>(stack);
        let head = (*stack).head;
        
        let result = head.is_null();
        
        
        //@ close stack::<T>(stack);
        result
    }
    
    //@ req stack::<T>(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack::<T>(stack);
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        
        //@ open stack::<T>(stack);
        let head = (*stack).head;
        
        //@ open nodes::<T>(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack::<T>(stack);
        result
    }

    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    unsafe fn reverse(stack: *mut Stack<T>)
    
    
    {
        
        //@ open stack::<T>(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        
        
        //@ close nodes::<T>(m);
        loop {
            
            
            //@ inv nodes::<T>(n) &*& nodes::<T>(m);
            if n.is_null() {
                break;
            }
            //@ open nodes::<T>(n);
            let next = (*n).next;
            
            (*n).next = m;
            m = n;
            n = next;
            
            //@ close nodes::<T>(m);
            
        }
        (*stack).head = m;
        
        //@ close stack::<T>(stack);
    }

    //@ req stack::<T>(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        
        //@ open stack::<T>(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

/*@

pred point(p: *mut Point; x: i32, y: i32) =
    alloc_block(p as *mut u8, Layout::new::<Point>()) &*&
    (*p).x |-> x &*&
    (*p).y |-> y;

@*/

impl Point {

    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& point(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Point
    
    
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close point(result, x, y);
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