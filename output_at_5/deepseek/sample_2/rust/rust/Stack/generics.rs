use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
predicate Node<T>(struct Node<T> *node; struct Node<T> *next, T value) =
    node != 0 &*&
    struct_Node_padding<T>(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;

predicate Stack<T>(struct Stack<T> *stack; struct Node<T> *head) =
    stack != 0 &*&
    struct_Stack_padding<T>(stack) &*&
    (*stack).head |-> head;
@*/

impl<T> Stack<T> {
    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens Stack<T>(result, 0);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack::<T>(stack, 0);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req Stack<T>(stack, ?head) &*& value |-> _;
    //@ ens Stack<T>(stack, ?new_head) &*& Node<T>(new_head, head, value);
    {
        //@ open Stack<T>(stack, head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Node::<T>(n, head, value);
        //@ close Stack<T>(stack, n);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req Stack<T>(stack, ?head);
    //@ ens Stack<T>(stack, head) &*& result == (head == 0);
    {
        //@ open Stack<T>(stack, ?head);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close Stack<T>(stack, head);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req Stack<T>(stack, ?head) &*& head != 0 &*& Node<T>(head, ?next, ?value);
    //@ ens Stack<T>(stack, next) &*& result == value;
    {
        //@ open Stack<T>(stack, head);
        //@ open Node<T>(head, next, value);
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack<T>(stack, next);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req Stack<T>(stack, ?head);
    //@ ens Stack<T>(stack, ?new_head);
    {
        //@ open Stack<T>(stack, head);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close lseg<T>(m, 0);
        //@ open lseg<T>(m, 0);
        loop {
            //@ invariant lseg<T>(m, ?prev) &*& lseg<T>(n, 0) &*& lseg<T>(prev, 0);
            if n.is_null() {
                break;
            }
            //@ open lseg<T>(n, 0);
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
            //@ close lseg<T>(m, prev);
            //@ open lseg<T>(n, 0);
        }
        (*stack).head = m;
        //@ close Stack<T>(stack, m);
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack<T>(stack, 0);
    //@ ens true;
    {
        //@ open Stack<T>(stack, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

/*@
predicate lseg<T>(struct Node<T> *first, struct Node<T> *last) =
    first == last ?
        true
    :
        Node<T>(first, ?next, ?value) &*& lseg<T>(next, last);
@*/

struct Point {
    x: i32,
    y: i32,
}

/*@
predicate Point(struct Point *point; i32 x, i32 y) =
    point != 0 &*&
    struct_Point_padding(point) &*&
    (*point).x |-> x &*&
    (*point).y |-> y;
@*/

impl Point {
    unsafe fn create(x: i32, y: i32) -> *mut Point
    //@ req true;
    //@ ens Point(result, x, y);
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Point(result, x, y);
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
        std::hint::assert_unchecked(Stack::pop(s) == p1);
        std::hint::assert_unchecked(Stack::pop(s) == p2);
        Stack::dispose(s);
        //@ open Point(p1, 10, 0);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open Point(p2, 0, 10);
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}