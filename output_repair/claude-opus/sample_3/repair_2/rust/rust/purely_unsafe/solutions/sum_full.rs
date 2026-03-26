use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(node: *mut Node; sum: i32) =
    if node == 0 as *mut Node {
        sum == 0
    } else {
        (*node).value |-> ?v &*&
        (*node).next |-> ?next &*&
        alloc_block(node as *mut u8, Layout::new_::<Node>()) &*&
        struct_Node_padding(node) &*&
        Nodes(next, ?tailSum) &*&
        sum == v + tailSum
    };

pred Stack(stack: *mut Stack; sum: i32) =
    (*stack).head |-> ?head &*&
    alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    Nodes(head, sum);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req Nodes(node, ?sum);
//@ ens Nodes(node, sum) &*& result == sum;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open Nodes(node, sum);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close Nodes(node, sum);
    } else {
        //@ open Nodes(node, sum);
        //@ close Nodes(node, sum);
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node, 0);
        //@ close Stack(stack, 0);

        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?sum);
    //@ ens Stack(stack, sum) &*& result == sum;
    {
        //@ open Stack(stack, sum);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, sum);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?sum);
    //@ ens Stack(stack, sum + value);
    {
        //@ open Stack(stack, sum);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, sum + value);
        //@ close Stack(stack, sum + value);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?sum) &*& sum != 0;
    //@ ens Stack(stack, sum - result);
    {
        //@ open Stack(stack, sum);
        let head = (*stack).head;
        //@ open Nodes(head, sum);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, sum - result);

        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, 0);
    //@ ens true;
    {
        //@ open Stack(stack, 0);
        //@ open Nodes(0 as *mut Node, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
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