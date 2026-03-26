#![allow(unused_attributes)]
#![feature(const_raw_ptr_to_usize_cast)]

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(list: list<i32>; *mut Node s) =
    s == std::ptr::null_mut() ?
        list == nil :
        s |-> Node { next: ?next, value: ?v } &*& nodes(?rest, next) &*& list == cons(v, rest);

predicate stack(s: *mut Stack; list<i32>) =
    s |-> Stack { head: ?head } &*& nodes(list, head);

type I32Predicate = unsafe fn(i32) -> bool;

#[requires(n |-> ?ptr &*& nodes(?list, ptr) &*& p :: (i32) -> bool)] 
#[ensures(n |-> ?ptr_new &*& nodes(?list_new, ptr_new) &*& p :: (i32) -> bool)]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ requires n |-> ?np &*& nodes(?list, np);
    //@ ensures n |-> ?np2 &*& nodes(?list2, np2);
{
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

#[requires(n |-> ?ptr &*& nodes(?list, ptr))]
#[ensures(nodes(nil, std::ptr::null_mut()))]
unsafe fn dispose_nodes(n: *mut Node)
    //@ requires nodes(?list, n);
    //@ ensures nodes(nil, std::ptr::null_mut());
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack
    //@ ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, cons(value, list)))]
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?list);
    //@ ensures stack(stack, cons(value, list));
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, cons(?v, ?tail)))]
    #[ensures(stack(stack, tail))]
    #[ensures(result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, cons(?v, ?tail));
    //@ ensures stack(stack, tail) &*& result == v;
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, ?filtered))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ requires stack(stack, ?list);
    //@ ensures stack(stack, ?filtered);
    {
        filter_nodes(&raw mut (*stack).head, p);
    }
    
    #[requires(stack(stack, ?list))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, ?list);
    //@ ensures true;
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[predicate]
fn p_inv(p: I32Predicate; v: i32) = true;

unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}