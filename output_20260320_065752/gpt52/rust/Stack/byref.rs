use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node_(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n as *u8, Layout::new::<Node>()) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        node_(n; ?next, ?value) &*& nodes(next);

pred stack_(s: *mut Stack; head: *mut Node) =
    alloc_block(s as *u8, Layout::new::<Stack>()) &*&
    (*s).head |-> head;

pred stack(s: *mut Stack) =
    stack_(s; ?head) &*& nodes(head);

@*/

type I32Predicate = unsafe fn(i32) -> bool;

//@ req *n |-> ?head &*& nodes(head);
//@ ens *n |-> ?head2 &*& nodes(head2);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    //@ open nodes(?head0);
    if !(*n).is_null() {
        //@ assert *n |-> ?head1;
        //@ open nodes(head1);
        //@ open node_(head1; ?next1, ?value1);
        let keep = p((**n).value);
        if keep {
            //@ close node_(head1; next1, value1);
            //@ close nodes(head1);
            filter_nodes(&raw mut (**n).next, p);
            //@ open nodes(head1);
            //@ open node_(head1; ?next2, value1);
            //@ close node_(head1; next2, value1);
            //@ close nodes(head1);
        } else {
            let next_ = (**n).next;
            //@ close node_(head1; next1, value1);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close nodes(next1);
            filter_nodes(n, p);
        }
    } else {
        //@ close nodes(std::ptr::null_mut());
    }
}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open node_(n; ?next, ?value);
        dispose_nodes((*n).next);
        //@ close node_(n; next, value);
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
        //@ close stack_(stack; std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        //@ open stack_(stack; ?head0);
        //@ open nodes(head0);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node_(n; head0, value);
        //@ close nodes(n);
        //@ close stack_(stack; n);
        //@ close stack(stack);
    }

    //@ req stack(stack) &*& stack_(stack; ?head0) &*& head0 != std::ptr::null_mut();
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        //@ open stack_(stack; ?head0_);
        //@ open nodes(head0_);
        let head = (*stack).head;
        //@ open node_(head; ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close node_(head; next, value);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes(next);
        //@ close stack_(stack; next);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        //@ open stack(stack);
        //@ open stack_(stack; ?head0);
        filter_nodes(&raw mut (*stack).head, p);
        //@ assert (*stack).head |-> ?head1;
        //@ close stack_(stack; head1);
        //@ close stack(stack);
    }

    //@ req stack(stack);
//@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ open stack_(stack; ?head0);
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
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}