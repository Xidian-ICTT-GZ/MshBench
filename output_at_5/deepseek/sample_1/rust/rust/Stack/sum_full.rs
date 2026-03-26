use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate nodes(node: *mut Node; i32 sum) =
//@     node == 0 ? sum == 0 :
//@     alloc_block(node, std::mem::size_of::<Node>()) &*&
//@     struct_Node_padding(node) &*&
//@     (*node).next |-> ?next &*&
//@     (*node).value |-> ?val &*&
//@     nodes(next, ?tail_sum) &*&
//@     sum == val + tail_sum;

//@ predicate stack(stack: *mut Stack) =
//@     alloc_block(stack, std::mem::size_of::<Stack>()) &*&
//@     struct_Stack_padding(stack) &*&
//@     (*stack).head |-> ?head &*&
//@     nodes(head, _);

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node, ?sum);
//@ ens nodes(node, sum) &*& result == sum;
{
    //@ open nodes(node, sum);
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node, sum);
        //@ assert alloc_block(node, _);
        //@ assert (*node).next |-> ?next;
        //@ assert (*node).value |-> ?val;
        //@ assert nodes(next, ?tail_sum);
        //@ close nodes(next, tail_sum);
        let tail_sum = get_nodes_sum((*node).next);
        //@ open nodes(next, tail_sum);
        //@ close nodes(next, tail_sum);
        result = (*node).value + tail_sum;
        //@ close nodes(node, val + tail_sum);
    } else {
        //@ close nodes(0 as *mut Node, 0);
    }
    //@ close nodes(node, sum);
    result
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
        //@ close nodes(0 as *mut Node, 0);
        //@ close stack(stack);
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ?sum &*& nodes((*stack).head, sum);
    {
        //@ open stack(stack);
        //@ assert (*stack).head |-> ?head;
        //@ close nodes(head, _);
        let result = get_nodes_sum((*stack).head);
        //@ open nodes(head, _);
        //@ close stack(stack);
        result
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
        //@ close nodes(n, value + ?old_sum);
        //@ open nodes((*stack).head, ?old_sum);
        //@ close nodes((*stack).head, old_sum);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, ?sum);
        //@ assert alloc_block(head, _);
        //@ assert (*head).next |-> ?next;
        //@ assert (*head).value |-> ?val;
        //@ assert nodes(next, ?tail_sum);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes(next, tail_sum);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head, _);
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
        //@ assert sum == 30;
        let result1 = Stack::pop(s);
        //@ assert result1 == 20;
        let result2 = Stack::pop(s);
        //@ assert result2 == 10;
        Stack::dispose(s);
    }
}