use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(n: *mut Node;) =
    n == std::ptr::null_mut() ?
        true
    :
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes(next);

pred stack(s: *mut Stack;) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?h &*&
    nodes(h);

@*/

type I32Predicate = unsafe fn(i32) -> bool;

//@ req n != std::ptr::null_mut() &*& *n |-> ?head &*& nodes(head);
//@ ens n != std::ptr::null_mut() &*& *n |-> ?head2 &*& nodes(head2);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    //@ open nodes(?head0);
    if !(*n).is_null() {
        //@ open nodes(*n);
        let keep = p((**n).value);
        if keep {
            //@ close nodes((**n).next);
            filter_nodes(&raw mut (**n).next, p);
            //@ open nodes((**n).next);
            //@ close nodes(*n);
            //@ close nodes(*n);
        } else {
            let next_ = (**n).next;
            //@ open nodes((**n).next);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close nodes(*n);
            filter_nodes(n, p);
            //@ open nodes(*n);
            //@ close nodes(*n);
            //@ close nodes(*n);
        }
        //@ open nodes(*n);
    }
    //@ close nodes(*n);
}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open nodes((*n).next);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack
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

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes((*n).next);
        //@ close nodes(n);
        //@ close stack(stack);
    }

    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open nodes((*head).next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes((*stack).head);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        //@ open stack(stack);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close stack(stack);
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ req true;
//@ ens true;
unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        //@ open stack(s);
        //@ close stack(s);
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}