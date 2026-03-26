//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred Node_own<T>(n: *mut Node<T>) = n != 0 &*& alloc_block(n as *u8, std::mem::size_of::<Node<T>>()) &*& struct_Node_padding(n) &*& (*n).next |-> ?next &*& (*n).value |-> ?v &*& if next == 0 then true else Node_own(next); @*/

/*@ pred Stack_own<T>(s: *mut Stack<T>) = s != 0 &*& alloc_block(s as *u8, std::mem::size_of::<Stack<T>>()) &*& struct_Stack_padding(s) &*& (*s).head |-> ?head &*& if head == 0 then true else Node_own(head); @*/

/*@ pred Point_own(p: *mut Point) = p != 0 &*& alloc_block(p as *u8, std::mem::size_of::<Point>()) &*& struct_Point_padding(p) &*& (*p).x |-> _ &*& (*p).y |-> _; @*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {

    //@ req true;
    //@ ens Stack_own(result);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close Stack_own(stack);
        (*stack).head = std::ptr::null_mut();
        //@ open Stack_own(stack);
        //@ (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack);
        stack
    }
    
    //@ req Stack_own(stack) &*& if (*stack).head == 0 then true else Node_own((*stack).head) &*& Stack_own_full::<T>(stack) &*& value |-> ?v;
    //@ ens Stack_own(stack) &*& if (*stack).head == 0 then false else Node_own((*stack).head);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open Stack_own(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ close Node_own(n);
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Stack_own(stack);
    }
    
    //@ req Stack_own(stack);
    //@ ens Stack_own(stack) &*& result == ((*stack).head == 0);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open Stack_own(stack);
        let head = (*stack).head;
        //@ close Stack_own(stack);
        let result = head.is_null();
        result
    }
    
    //@ req Stack_own(stack) &*& (*stack).head != 0 &*& Node_own((*stack).head);
    //@ ens Stack_own(stack) &*& result |-> ?v;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open Stack_own(stack);
        let head = (*stack).head;
        //@ open Node_own(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack_own(stack);
        result
    }

    //@ req Stack_own(stack);
    //@ ens Stack_own(stack);
    unsafe fn reverse(stack: *mut Stack<T>)
    {
        //@ open Stack_own(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ Stack_reverse_loop(n, m, stack);
        loop {
            //@ inv Stack_reverse_inv(n, m, stack);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
        }
        (*stack).head = m;
        //@ close Stack_own(stack);
    }

    //@ req Stack_own(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open Stack_own(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

/*@ pred Stack_reverse_inv<T>(n: *mut Node<T>, m: *mut Node<T>, s: *mut Stack<T>) =
    s != 0 &*& alloc_block(s as *u8, std::mem::size_of::<Stack<T>>()) &*& struct_Stack_padding(s) &*& (*s).head |-> _ &*& 
    (m == 0 ? true : Node_own(m)) &*& 
    (n == 0 ? true : Node_own(n)); @*/

/*@ lemma void Stack_reverse_loop<T>(n: *mut Node<T>, m: *mut Node<T>, s: *mut Stack<T>)
    req Stack_own(s) &*& (*s).head == n;
    ens Stack_reverse_inv(n, m, s);
{
    open Stack_own(s);
    close Stack_reverse_inv(n, m, s);
}
@*/

struct Point {
    x: i32,
    y: i32,
}

impl Point {

    //@ req true;
    //@ ens Point_own(result);
    unsafe fn create(x: i32, y: i32) -> *mut Point
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        //@ close Point_own(result);
        (*result).x = x;
        (*result).y = y;
        result
    }
    
}

fn main()
{
    //@ req true;
    //@ ens true;
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