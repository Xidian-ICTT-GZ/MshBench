use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(n: *mut Node<T>, next: *mut Node<T>, v: T) = n as *mut u8 |-> ?b &*& struct_Node_padding(b) &*& [0.5]std::ptr::raw_ptr_to_unique(n) &*& (*n).next |-> next &*& (*n).value |-> v;
//@ pred stack<T>(s: *mut Stack<T>) = s as *mut u8 |-> ?b &*& struct_Stack_padding(b) &*& [0.5]std::ptr::raw_ptr_to_unique(s) &*& (*s).head |-> ?h &*& stack_nodes(h);
//@ pred stack_nodes<T>(n: *mut Node<T>) =
//@   if n == std::ptr::null_mut() then true
//@   else node(n, ?next, ?v) &*& stack_nodes(next);

//@ pred point(p: *mut Point, x: i32, y: i32) = p as *mut u8 |-> ?b &*& struct_Point_padding(b) &*& [0.5]std::ptr::raw_ptr_to_unique(p) &*& (*p).x |-> x &*& (*p).y |-> y;

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    
    
    {
        //@ req true;
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        
        
        stack
        //@ ens stack(result);
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    
    
    {
        //@ req stack(stack);
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }
    //@ ens stack(stack);
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    
    
    {
        //@ req stack(stack);
        //@ open stack(stack);
        let head = (*stack).head;
        
        let result = head.is_null();
        //@ close stack(stack);
        
        
        result
        //@ ens stack(stack) &*& result == (head == std::ptr::null_mut::<Node<T>>());
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        //@ req stack(stack) &*& !is_empty(stack);
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open stack_nodes(head);
        //@ open node(head, ?next, ?v);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ close stack_nodes(next);
        //@ close stack(stack);
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        result
        //@ ens stack(stack) &*& result == v;
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    
    
    {
        //@ req stack(stack);
        //@ open stack(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close stack_nodes(m);
        
        
        loop {
            //@ inv stack_nodes(n) &*& stack_nodes(m);
            
            
            if n.is_null() {
                break;
            }
            //@ open stack_nodes(n);
            //@ open node(n, ?next, ?v);
            let next = (*n).next;
            
            (*n).next = m;
            //@ close node(n, m, v);
            //@ close stack_nodes(n);
            m = n;
            n = next;
            
            
        }
        (*stack).head = m;
        //@ close stack(stack);
        
    }
    //@ ens stack(stack);

    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        //@ req stack(stack);
        //@ open stack(stack);
        //@ open stack_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
    //@ ens true;

}

struct Point {
    x: i32,
    y: i32,
}

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
    
    
    {
        //@ req true;
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close point(result, x, y);
        result
        //@ ens point(result, x, y);
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