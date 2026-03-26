use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred Nodes<T>(n: *mut Node<T>, nodes: list<*mut Node<T>>) =
    if n == 0 {
        nodes == nil
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        Nodes(next, ?rest) &*&
        nodes == cons(n, rest)
    };

pred Stack<T>(s: *mut Stack<T>, nodes: list<*mut Node<T>>) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, nodes);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens Stack::<T>(result, nil);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes::<T>(0 as *mut Node<T>, nil);
        //@ close Stack::<T>(stack, nil);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req Stack::<T>(stack, ?nodes);
    //@ ens Stack::<T>(stack, cons(?n, nodes));
    {
        //@ open Stack::<T>(stack, nodes);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Nodes::<T>(n, cons(n, nodes));
        //@ close Stack::<T>(stack, cons(n, nodes));
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req Stack::<T>(stack, ?nodes);
    //@ ens Stack::<T>(stack, nodes) &*& result == (nodes == nil);
    {
        //@ open Stack::<T>(stack, nodes);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, nodes);
        let result = head.is_null();
        //@ close Nodes::<T>(head, nodes);
        //@ close Stack::<T>(stack, nodes);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req Stack::<T>(stack, cons(?n, ?rest));
    //@ ens Stack::<T>(stack, rest);
    {
        //@ open Stack::<T>(stack, cons(n, rest));
        let head = (*stack).head;
        //@ open Nodes::<T>(head, cons(n, rest));
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack::<T>(stack, rest);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req Stack::<T>(stack, ?nodes);
    //@ ens Stack::<T>(stack, _);
    {
        //@ open Stack::<T>(stack, nodes);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close Nodes::<T>(0 as *mut Node<T>, nil);
        //@ let mut n_nodes = nodes;
        //@ let mut m_nodes: list<*mut Node<T>> = nil;
        
        loop {
            //@ inv Nodes::<T>(n, _) &*& Nodes::<T>(m, _) &*& (*stack).head |-> _;
            //@ open Nodes::<T>(n, _);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            
            (*n).next = m;
            //@ close Nodes::<T>(n, _);
            m = n;
            n = next;
            
        }
        (*stack).head = m;
        //@ close Stack::<T>(stack, _);
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack::<T>(stack, nil);
    //@ ens true;
    {
        //@ open Stack::<T>(stack, nil);
        //@ open Nodes::<T>(_, nil);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

/*@

pred Point(p: *mut Point) =
    alloc_block_Point(p) &*&
    (*p).x |-> _ &*&
    (*p).y |-> _;

@*/

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
    //@ req true;
    //@ ens Point(result);
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Point(result);
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
        let r1 = Stack::pop(s);
        //@ assume(r1 == p1);
        std::hint::assert_unchecked(r1 == p1);
        let r2 = Stack::pop(s);
        //@ assume(r2 == p2);
        std::hint::assert_unchecked(r2 == p2);
        Stack::dispose(s);
        //@ open Point(p1);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open Point(p2);
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}