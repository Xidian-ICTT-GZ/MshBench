use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes_list(node: *mut Node) =
    node == 0 ?
        true
    :
        alloc_block_Node(node) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?v &*&
        nodes_list(next);

pred stack(stack: *mut Stack) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?h &*&
    nodes_list(h);

@*/

//@ req nodes_list(node);
//@ ens nodes_list(node) &*& result == get_nodes_sum(node);
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    //@ open nodes_list(node);
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes_list(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes_list((*node).next);
        //@ close nodes_list(node);
    } else {
        //@ close nodes_list(node);
    }

    result
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
        //@ close nodes_list(0);
        //@ close stack(stack);

        stack
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);

        result
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
        //@ close nodes_list((*n).next);
        //@ close nodes_list(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes_list(head);

        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes_list((*stack).head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);

        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ open nodes_list((*stack).head);
        //@ assume_correct
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);

        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}