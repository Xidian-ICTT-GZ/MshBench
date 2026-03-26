use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

fixpoint *mut Node<T> null_node<T>() { 0 as *mut Node<T> }
fixpoint *mut Stack<T> null_stack<T>() { 0 as *mut Stack<T> }

pred node_next_only<T>(p: *mut Node<T>; next: *mut Node<T>) =
    p != null_node::<T>() &*&
    alloc_block(p as *mut u8, Layout::new::<Node<T>>()) &*&
    (*p).next |-> next;

pred nodes_next_only<T>(p: *mut Node<T>) =
    if p == null_node::<T>() {
        true
    } else {
        node_next_only::<T>(p, ?nxt) &*& nodes_next_only::<T>(nxt)
    };

pred stack_next_only<T>(s: *mut Stack<T>) =
    s != null_stack::<T>() &*&
    alloc_block(s as *mut u8, Layout::new::<Stack<T>>()) &*&
    (*s).head |-> ?h &*& nodes_next_only::<T>(h);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack_next_only::<T>(result);
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        //@ close nodes_next_only::<T>(null_node::<T>());
        //@ close stack_next_only::<T>(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack_next_only::<T>(stack);
    //@ ens stack_next_only::<T>(stack);
    
    
    {
        //@ open stack_next_only::<T>(stack);
        
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        
        
        //@ close node_next_only::<T>(n, (*n).next);
        //@ close nodes_next_only::<T>(n);
        //@ close stack_next_only::<T>(stack);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack_next_only::<T>(stack);
    //@ ens stack_next_only::<T>(stack);
    
    
    {
        //@ open stack_next_only::<T>(stack);
        
        let head = (*stack).head;
        
        let result = head.is_null();
        
        
        //@ close stack_next_only::<T>(stack);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack_next_only::<T>(stack) &*& (*stack).head |-> ?h &*& h != null_node::<T>();
    //@ ens stack_next_only::<T>(stack);
    
    
    {
        //@ open stack_next_only::<T>(stack);
        //@ open nodes_next_only::<T>((*stack).head);
        
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        //@ open node_next_only::<T>(head, (*head).next);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        
        //@ close stack_next_only::<T>(stack);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req stack_next_only::<T>(stack);
    //@ ens stack_next_only::<T>(stack);
    
    
    {
        //@ open stack_next_only::<T>(stack);
        
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        
        
        //@ close nodes_next_only::<T>(null_node::<T>());
        loop {
            //@ inv alloc_block(stack as *mut u8, Layout::new::<Stack<T>>()) &*& (*stack).head |-> _ &*& nodes_next_only::<T>(m) &*& nodes_next_only::<T>(n);
            
            
            if n.is_null() {
                break;
            }
            //@ open nodes_next_only::<T>(n);
            let next = (*n).next;
            
            (*n).next = m;
            //@ close node_next_only::<T>(n, m);
            //@ close nodes_next_only::<T>(n);
            m = n;
            n = next;
            
            
        }
        (*stack).head = m;
        
        
        //@ close stack_next_only::<T>(stack);
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack_next_only::<T>(stack);
    //@ ens true;
    
    
    {
        //@ open stack_next_only::<T>(stack);
        
        
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
    //@ ens alloc_block(result as *mut u8, Layout::new::<Point>());
    
    
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