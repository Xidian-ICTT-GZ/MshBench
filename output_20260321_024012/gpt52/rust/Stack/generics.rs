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
    n == 0 ?
        true
    :
        std::alloc::alloc_block(n as *mut u8, Layout::new::<Node<T>>()) &*&
        struct_Node_next(n, ?next) &*&
        struct_Node_value(n, _) &*&
        nodes::<T>(next);

pred stack<T>(s: *mut Stack<T>) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack<T>>()) &*&
    struct_Stack_head(s, ?h) &*&
    nodes::<T>(h);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens result == 0 ? true : stack::<T>(result);
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close nodes::<T>(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close stack::<T>(stack);
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    
    
    {
        //@ open stack::<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close nodes::<T>((*n).next);
        //@ close nodes::<T>(n);
        (*stack).head = n;
        //@ close stack::<T>(stack);
        
        
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    
    
    {
        //@ open stack::<T>(stack);
        let head = (*stack).head;
        
        let result = head.is_null();
        
        //@ close stack::<T>(stack);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack::<T>(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack::<T>(stack);
    
    
    {
        //@ open stack::<T>(stack);
        let head = (*stack).head;
        //@ open nodes::<T>(head);
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close nodes::<T>((*stack).head);
        //@ close stack::<T>(stack);
        
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req stack::<T>(stack);
    //@ ens stack::<T>(stack);
    
    
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
            //@ close nodes::<T>((*n).next);
            //@ close nodes::<T>(n);
            m = n;
            n = next;
            
            
        }
        //@ open nodes::<T>(n);
        (*stack).head = m;
        //@ close stack::<T>(stack);
        
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack::<T>(stack) &*& (*stack).head == std::ptr::null_mut();
    //@ ens true;
    
    
    {
        //@ open stack::<T>(stack);
        //@ open nodes::<T>((*stack).head);
        
        
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
    //@ ens result == 0 ? true : std::alloc::alloc_block(result as *mut u8, Layout::new::<Point>()) &*& struct_Point_x(result, x) &*& struct_Point_y(result, y);
    
    
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
    //@ req true;
    //@ ens true;

{
    unsafe {
        let s = Stack::create();
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        //@ open stack::<Point>(s);
        //@ close stack::<Point>(s);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        std::hint::assert_unchecked(Stack::pop(s) == p1);
        std::hint::assert_unchecked(Stack::pop(s) == p2);
        //@ open stack::<Point>(s);
        //@ assert (*s).head == std::ptr::null_mut();
        //@ close stack::<Point>(s);
        Stack::dispose(s);
        //@ open std::alloc::alloc_block(p1 as *mut u8, Layout::new::<Point>());
        //@ open std::alloc::alloc_block(p2 as *mut u8, Layout::new::<Point>());
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}