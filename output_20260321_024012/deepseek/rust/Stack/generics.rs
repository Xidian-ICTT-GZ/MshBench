use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens result != 0;
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes::<T>(std::ptr::null_mut());
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req nodes(stack, ?head) &*& true;
    //@ ens nodes(stack, ?new_head) &*& true;
    {
        //@ open nodes(stack, head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close node(n, head, value);
        //@ close nodes(stack, n);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req nodes(stack, ?head);
    //@ ens nodes(stack, head) &*& result == head.is_null();
    {
        //@ open nodes(stack, head);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close nodes(stack, head);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req nodes(stack, ?head) &*& head != 0;
    //@ ens nodes(stack, ?next) &*& result == ?v &*& head->Node<T> { next: next, value: v };
    {
        //@ open nodes(stack, head);
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open node(head, _, _);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close nodes(stack, (*stack).head);
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req nodes(stack, ?head);
    //@ ens nodes(stack, ?new_head);
    {
        //@ open nodes(stack, head);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes(stack, m);
        //@ close rev_loop(n, m, head);
        loop {
            //@ open rev_loop(n, m, ?orig_head);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            //@ open node(n, next, ?v);
            (*n).next = m;
            m = n;
            n = next;
            //@ close rev_loop(n, m, orig_head);
        }
        //@ open rev_loop(std::ptr::null_mut(), m, head);
        (*stack).head = m;
        //@ close nodes(stack, m);
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req nodes(stack, std::ptr::null_mut());
    //@ ens true;
    {
        //@ open nodes(stack, std::ptr::null_mut());
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
    //@ ens result != 0 &*& result->Point { x: x, y: y };
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
        //@ open point(p1, _, _);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        //@ open point(p2, _, _);
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}

/*@
predicate node<T>(*mut Node<T> n; *mut Node<T> next, T v) =
    alloc_block(n, std::mem::size_of::<Node<T>>()) &*&
    struct_Node_padding(n) &*&
    n->next |-> next &*&
    n->value |-> v;

predicate nodes<T>(*mut Stack<T> stack; *mut Node<T> head) =
    alloc_block(stack, std::mem::size_of::<Stack<T>>()) &*&
    struct_Stack_padding(stack) &*&
    stack->head |-> head &*&
    lseg(head, std::ptr::null_mut());

predicate lseg<T>(*mut Node<T> first, *mut Node<T> last) =
    first == last ?
        true
    :
        node(first, ?next, ?v) &*& lseg(next, last);

predicate rev_loop<T>(*mut Node<T> n, *mut Node<T> m, *mut Node<T> orig_head) =
    lseg(n, std::ptr::null_mut()) &*& lseg(m, orig_head);

predicate point(*mut Point p; i32 x, i32 y) =
    alloc_block(p, std::mem::size_of::<Point>()) &*&
    struct_Point_padding(p) &*&
    p->x |-> x &*&
    p->y |-> y;
@*/