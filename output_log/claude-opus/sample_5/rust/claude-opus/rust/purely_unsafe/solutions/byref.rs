use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

/*@
pred nodes(n: *mut Node) = 
    if n.is_null() {
        true
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& nodes(next) &*& alloc_block(n as *mut u8, Layout::new_::<Node>())
    };

pred stack(s: *mut Stack) = 
    (*s).head |-> ?h &*& nodes(h) &*& alloc_block(s as *mut u8, Layout::new_::<Stack>());

pred pointer_to_nodes(n: *mut *mut Node) =
    *n |-> ?node &*& nodes(node);
@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req pointer_to_nodes(n);
//@ ens pointer_to_nodes(n);
{
    //@ open pointer_to_nodes(n);
    if !(*n).is_null() {
        //@ open nodes(*n);
        let keep = p((**n).value);
        if keep {
            //@ close nodes(*n);
            //@ close pointer_to_nodes(&raw mut (**n).next);
            filter_nodes(&raw mut (**n).next, p);
            //@ open pointer_to_nodes(&raw mut (**n).next);
            //@ close nodes(*n);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close pointer_to_nodes(n);
            filter_nodes(n, p);
            //@ open pointer_to_nodes(n);
        }
    }
    //@ close pointer_to_nodes(n);
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    //@ open nodes(n);
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        //@ close pointer_to_nodes(&raw mut (*stack).head);
        filter_nodes(&raw mut (*stack).head, p);
        //@ open pointer_to_nodes(&raw mut (*stack).head);
        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;
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