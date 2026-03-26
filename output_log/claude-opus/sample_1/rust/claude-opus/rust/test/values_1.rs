use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

/*@

pred Node(node: *mut Node; next: *mut Node, value: i32) =
    (*node).next |-> next &*& (*node).value |-> value &*&
    alloc_block(node as *mut u8, Layout::new::<Node>());

pred Nodes(head: *mut Node;) =
    if head == 0 as *mut Node {
        emp
    } else {
        Node(head, ?next, ?value) &*& Nodes(next)
    };

pred Stack(stack: *mut Stack; head: *mut Node) =
    (*stack).head |-> head &*&
    alloc_block(stack as *mut u8, Layout::new::<Stack>()) &*&
    Nodes(head);

lemma void nodes_dispose(head: *mut Node)
    requires Nodes(head);
    ensures emp;
{
    open Nodes(head);
    if (head != 0 as *mut Node) {
        open Node(head, ?next, ?value);
        nodes_dispose(next);
        close Node(head, next, value);
        open Node(head, next, value);
        dealloc(head as *mut u8, Layout::new::<Node>());
    }
    close Nodes(head);
}

@*/

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires emp;
    //@ ensures Stack(result, 0 as *mut Node);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node);
        //@ close Stack(stack, 0 as *mut Node);
        stack
    }
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires Stack(stack, ?head0);
    //@ ensures Stack(stack, ?head1) &*& head1 != 0 as *mut Node;
    {
        //@ open Stack(stack, head0);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node(n, head0, value);
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close Stack(stack, n);
    }
    unsafe fn dispose(stack: *mut Stack)
    //@ requires Stack(stack, 0 as *mut Node);
    //@ ensures emp;
    {
        //@ open Stack(stack, 0 as *mut Node);
        //@ open Nodes(0 as *mut Node);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}