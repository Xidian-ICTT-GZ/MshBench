use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(n: *mut Node) =
    n == 0 ?
        true
    :
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes(next);

pred stack(s: *mut Stack) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?h &*&
    nodes(h);

@*/

type I32Predicate = unsafe fn(i32) -> bool;

//@ req nodes(n);
//@ req true;
//@ ens nodes(result);
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        //@ open nodes(n);
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);

            (*n).next = next;
            //@ close nodes(n);
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open nodes(n);
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
        //@ close nodes(0);
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
        //@ close nodes(n);
        (*stack).head = n;

        //@ close stack(stack);
    }

    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);

        let head = (*stack).head;
        //@ open nodes(head);

        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        //@ open stack(stack);

        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;

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

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}