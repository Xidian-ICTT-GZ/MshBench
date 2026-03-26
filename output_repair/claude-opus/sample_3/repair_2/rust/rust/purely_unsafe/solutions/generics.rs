use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
pred Nodes<T>(node: *mut Node<T>; elems: list<T>) =
    if node == 0 {
        elems == nil
    } else {
        alloc_block(node as *mut u8, Layout::new_::<Node<T>>()) &*&
        struct_Node_padding(node) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?v &*&
        Nodes::<T>(next, ?elems0) &*&
        elems == cons(v, elems0)
    };

pred Stack_own<T>(stack: *mut Stack<T>; elems: list<T>) =
    alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes::<T>(head, elems);
@*/

impl<T> Stack<T> {
    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens Stack_own::<T>(result, nil);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes::<T>(0 as *mut Node<T>, nil);
        //@ close Stack_own::<T>(stack, nil);
        stack
    }

    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req Stack_own::<T>(stack, ?elems);
    //@ ens Stack_own::<T>(stack, cons(value, elems));
    {
        //@ open Stack_own::<T>(stack, elems);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ close_struct(n);
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Nodes::<T>(n, cons(value, elems));
        (*stack).head = n;
        //@ close Stack_own::<T>(stack, cons(value, elems));
    }

    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req Stack_own::<T>(stack, ?elems);
    //@ ens Stack_own::<T>(stack, elems) &*& result == (elems == nil);
    {
        //@ open Stack_own::<T>(stack, elems);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, elems);
        let result = head.is_null();
        //@ close Nodes::<T>(head, elems);
        //@ close Stack_own::<T>(stack, elems);
        result
    }

    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req Stack_own::<T>(stack, ?elems) &*& elems != nil;
    //@ ens Stack_own::<T>(stack, tail(elems)) &*& result == head(elems);
    {
        //@ open Stack_own::<T>(stack, elems);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, elems);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open_struct(head);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack_own::<T>(stack, tail(elems));
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req Stack_own::<T>(stack, ?elems);
    //@ ens Stack_own::<T>(stack, reverse(elems));
    {
        //@ open Stack_own::<T>(stack, elems);
        let mut n = (*stack).head;
        let mut m: *mut Node<T> = std::ptr::null_mut();
        //@ close Nodes::<T>(m, nil);
        //@ append_nil(reverse(nil:list<T>));
        loop
        //@ inv Nodes::<T>(n, ?elems_n) &*& Nodes::<T>(m, ?elems_m) &*& reverse(elems) == append(reverse(elems_n), elems_m);
        {
            //@ open Nodes::<T>(n, elems_n);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            //@ close Nodes::<T>(n, cons(head(elems_n), elems_m));
            //@ append_assoc(reverse(tail(elems_n)), cons(head(elems_n), nil), elems_m);
            m = n;
            n = next;
        }
        (*stack).head = m;
        //@ close Stack_own::<T>(stack, reverse(elems));
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack_own::<T>(stack, nil);
    //@ ens true;
    {
        //@ open Stack_own::<T>(stack, nil);
        //@ open Nodes::<T>(_, nil);
        //@ open_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

/*@
pred Point_own(p: *mut Point;) =
    alloc_block(p as *mut u8, Layout::new_::<Point>()) &*&
    struct_Point_padding(p) &*&
    (*p).x |-> _ &*&
    (*p).y |-> _;
@*/

struct Point {
    x: i32,
    y: i32,
}

impl Point {
    unsafe fn create(x: i32, y: i32) -> *mut Point
    //@ req true;
    //@ ens Point_own(result);
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        //@ close_struct(result);
        (*result).x = x;
        (*result).y = y;
        //@ close Point_own(result);
        result
    }

    unsafe fn dispose(p: *mut Point)
    //@ req Point_own(p);
    //@ ens true;
    {
        //@ open Point_own(p);
        //@ open_struct(p);
        dealloc(p as *mut u8, Layout::new::<Point>());
    }
}

fn main() {
    unsafe {
        let s: *mut Stack<*mut Point> = Stack::create();
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        let r1 = Stack::pop(s);
        //@ assert r1 == p1;
        let r2 = Stack::pop(s);
        //@ assert r2 == p2;
        Stack::dispose(s);
        Point::dispose(p1);
        Point::dispose(p2);}
}