use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node<T>(node: *mut Node<T>, next: *mut Node<T>, value: T) =
    alloc_block(node, std::mem::size_of::<Node<T>>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

/*@
pred StackNodes<T>(head: *mut Node<T>) =
    head == std::ptr::null_mut() ?
        true
    :
        Node<T>(head, next, value) &*& StackNodes<T>(next);
@*/

/*@
pred Stack<T>(stack: *mut Stack<T>) =
    alloc_block(stack, std::mem::size_of::<Stack<T>>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head &*&
    StackNodes<T>(head);
@*/

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    //@ req true;
    //@ ens Stack<T>(result);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackNodes<T>(std::ptr::null_mut());
        //@ close Stack<T>(stack);
        stack
    }
    
    //@ req Stack<T>(stack) &*& value == value;
    //@ ens Stack<T>(stack);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open Stack<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Node<T>(n, (*stack).head, value);
        //@ close StackNodes<T>(n);
        (*stack).head = n;
        //@ close Stack<T>(stack);
    }
    
    //@ req Stack<T>(stack);
    //@ ens Stack<T>(stack) &*& result == ((*stack).head == std::ptr::null_mut());
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open Stack<T>(stack);
        let head = (*stack).head;
        //@ open StackNodes<T>(head);
        let result = head.is_null();
        //@ close StackNodes<T>(head);
        //@ close Stack<T>(stack);
        result
    }
    
    //@ req Stack<T>(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens Stack<T>(stack) &*& result == old_value;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open Stack<T>(stack);
        let head = (*stack).head;
        //@ open StackNodes<T>(head);
        //@ open Node<T>(head, next, old_value);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack<T>(stack);
        result
    }

    //@ req Stack<T>(stack);
    //@ ens Stack<T>(stack);
    unsafe fn reverse(stack: *mut Stack<T>)
    {
        //@ open Stack<T>(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close StackNodes<T>(m);
        //@ invariant StackNodes<T>(m) &*& StackNodes<T>(n);
        loop {
            //@ open StackNodes<T>(n);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            //@ open Node<T>(n, next, value);
            (*n).next = m;
            //@ close Node<T>(n, m, value);
            m = n;
            n = next;
            //@ close StackNodes<T>(n);
        }
        (*stack).head = m;
        //@ close Stack<T>(stack);
    }

    //@ req Stack<T>(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open Stack<T>(stack);
        //@ open StackNodes<T>((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

/*@
pred Point(point: *mut Point) =
    alloc_block(point, std::mem::size_of::<Point>()) &*&
    struct_Point_padding(point) &*&
    (*point).x |-> x &*&
    (*point).y |-> y;
@*/

struct Point {
    x: i32,
    y: i32,
}

impl Point {
    //@ req true;
    //@ ens Point(result);
    unsafe fn create(x: i32, y: i32) -> *mut Point
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
        //@ open Point(p1);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open Point(p2);
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}