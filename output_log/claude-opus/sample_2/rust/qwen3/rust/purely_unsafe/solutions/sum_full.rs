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
        (*node).next |-> ?next &*&
        (*node).value |-> ?val &*&
        struct_Node_padding(node) &*&
        Nodes(next, ?tail_sum) &*&
        sum == val + tail_sum
    };

pred StackOwn(stack: *mut Stack; head: *mut Node) =
    (*stack).head |-> head &*&
    struct_Stack_padding(stack) &*&
    alloc_block(stack as *mut u8, Layout::new_::<Stack>());

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
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens StackOwn(result, 0 as *mut Node) &*& Nodes(0 as *mut Node, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node, 0);
        //@ close StackOwn(stack, 0 as *mut Node);

        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req StackOwn(stack, ?head) &*& Nodes(head, ?sum);
    //@ ens StackOwn(stack, head) &*& Nodes(head, sum) &*& result == sum;
    {
        //@ open StackOwn(stack, head);
        let result = get_nodes_sum((*stack).head);
        //@ close StackOwn(stack, head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackOwn(stack, ?old_head) &*& Nodes(old_head, ?old_sum);
    //@ ens StackOwn(stack, ?new_head) &*& Nodes(new_head, old_sum + value) &*& new_head != 0 as *mut Node;
    {
        //@ open StackOwn(stack, old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, old_sum + value);
        //@ close StackOwn(stack, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackOwn(stack, ?head) &*& head != 0 as *mut Node &*& Nodes(head, ?sum);
    //@ ens StackOwn(stack, ?new_head) &*& Nodes(new_head, ?new_sum) &*& result == sum - new_sum;
    {
        //@ open StackOwn(stack, head);
        let head = (*stack).head;
        //@ open Nodes(head, sum);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackOwn(stack, (*head).next);

        result
    }

    unsafe fn dispose_nodes(node: *mut Node)
    //@ req Nodes(node, ?sum);
    //@ ens true;
    {
        //@ open Nodes(node, sum);
        if !node.is_null() {
            Stack::dispose_nodes((*node).next);
            dealloc(node as *mut u8, Layout::new::<Node>());
        }
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackOwn(stack, ?head) &*& Nodes(head, ?sum);
    //@ ens true;
    {
        //@ open StackOwn(stack, head);
        Stack::dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
//@ req true;
//@ ens true;
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