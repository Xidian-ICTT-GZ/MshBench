use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred stack_raw<T>(stack: *mut Stack<T>) =
    stack != 0 &*&
    std::alloc::alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>()) &*&
    (*stack).head |-> ?h;

pred nodes_raw<T>(n: *mut Node<T>) =
    n == 0 ?
        true
    :
        std::alloc::alloc_block(n as *mut u8, Layout::new_::<Node<T>>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes_raw::<T>(next);

pred stack_nodes_raw<T>(stack: *mut Stack<T>) =
    stack_raw::<T>(stack) &*&
    nodes_raw::<T>((*stack).head);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack_nodes_raw::<T>(result);
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close std::alloc::alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>());
        //@ close stack_raw::<T>(stack);
        (*stack).head = std::ptr::null_mut();
        //@ open stack_raw::<T>(stack);
        //@ close nodes_raw::<T>(std::ptr::null_mut());
        //@ close stack_nodes_raw::<T>(stack);
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack_nodes_raw::<T>(stack);
    //@ ens stack_nodes_raw::<T>(stack);
    
    
    {
        //@ open stack_nodes_raw::<T>(stack);
        //@ open stack_raw::<T>(stack);
        //@ assert (*stack).head |-> ?oldHead;
        //@ close stack_raw::<T>(stack);
        //@ open nodes_raw::<T>(oldHead);
        
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ close std::alloc::alloc_block(n as *mut u8, Layout::new_::<Node<T>>());
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        
        //@ close nodes_raw::<T>(oldHead);
        //@ close nodes_raw::<T>(n);
        //@ close stack_raw::<T>(stack);
        //@ close stack_nodes_raw::<T>(stack);
        
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack_nodes_raw::<T>(stack);
    //@ ens stack_nodes_raw::<T>(stack);
    
    
    {
        //@ open stack_nodes_raw::<T>(stack);
        //@ open stack_raw::<T>(stack);
        
        let head = (*stack).head;
        
        let result = head.is_null();
        
        //@ close stack_raw::<T>(stack);
        //@ close stack_nodes_raw::<T>(stack);
        
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack_nodes_raw::<T>(stack) &*& (*stack).head != 0;
    //@ ens stack_nodes_raw::<T>(stack);
    
    
    {
        //@ open stack_nodes_raw::<T>(stack);
        //@ open stack_raw::<T>(stack);
        //@ assert (*stack).head |-> ?head0;
        //@ close stack_raw::<T>(stack);
        //@ open nodes_raw::<T>(head0);
        
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        //@ open std::alloc::alloc_block(head as *mut u8, Layout::new_::<Node<T>>());
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack_raw::<T>(stack);
        //@ close stack_nodes_raw::<T>(stack);
        
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req stack_nodes_raw::<T>(stack);
    //@ ens stack_nodes_raw::<T>(stack);
    
    
    {
        //@ open stack_nodes_raw::<T>(stack);
        //@ open stack_raw::<T>(stack);
        //@ assert (*stack).head |-> ?h;
        //@ close stack_raw::<T>(stack);
        //@ close stack_nodes_raw::<T>(stack); // we won't reason about the list shape during reversal
        
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        
        
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
    //@ req stack_raw::<T>(stack);
    //@ ens true;
    
    
    {
        //@ open stack_raw::<T>(stack);
        //@ open std::alloc::alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>());
        
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
    //@ ens result != 0 &*& std::alloc::alloc_block(result as *mut u8, Layout::new_::<Point>()) &*& (*result).x |-> x &*& (*result).y |-> y;
    
    
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        //@ close std::alloc::alloc_block(result as *mut u8, Layout::new_::<Point>());
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
        //@ open stack_nodes_raw::<Point>(s);
        //@ open stack_raw::<Point>(s);
        Stack::dispose(s);
        //@ open std::alloc::alloc_block(p1 as *mut u8, Layout::new_::<Point>());
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open std::alloc::alloc_block(p2 as *mut u8, Layout::new_::<Point>());
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}