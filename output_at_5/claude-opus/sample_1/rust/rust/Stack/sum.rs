use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ pred node<n>(node_ptr: *mut Node) = node_ptr != std::ptr::null_mut() &*&
    //@     malloc_block_node(node_ptr) &*&
    //@     node_ptr->next |-> ?next_ptr &*&
    //@     node_ptr->value |-> ?val &*&
    //@     (next_ptr == std::ptr::null_mut() ? true : node<n-1>(next_ptr)) &*& n > 0;

struct Stack {
    head: *mut Node,
}

//@ pred nodes(sum: int, nodes_ptr: *mut Node) = 
//@     nodes_ptr == std::ptr::null_mut() ? sum == 0 :
//@       malloc_block_node(nodes_ptr) &*& nodes_ptr->next |-> ?next_ptr &*& nodes_ptr->value |-> ?val &*&
//@       nodes(sum - val, next_ptr);

impl Stack {
    //@ pred stack(stack_ptr: *mut Stack, nodes_sum: int) = 
    //@   malloc_block_stack(stack_ptr) &*& stack_ptr->head |-> ?head_ptr &*& nodes(nodes_sum, head_ptr);

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, 0);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ requires stack(stack, ?sum);
    //@ ensures stack(stack, sum) &*& result == ((*stack).head == std::ptr::null_mut());
    {
        //@ open stack(stack, sum);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ close stack(stack, sum);
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?sum);
    //@ ensures stack(stack, sum) &*& result == sum;
    {
        //@ open stack(stack, sum);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, sum);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?sum);
    //@ ensures stack(stack, sum + value);
    {
        //@ open stack(stack, sum);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(1)(n);
        //@ close stack(stack, sum + value);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?sum) &*& (*stack).head != std::ptr::null_mut();
    //@ ensures stack(stack, ?new_sum) &*& result == sum - new_sum;
    {
        //@ open stack(stack, sum);
        let head = (*stack).head;
        //@ open node(1)(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, sum - result);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, _);
    //@ ensures true;
    {
        //@ open stack(stack, _);
        let mut n = (*stack).head;
        loop {
            if n.is_null() {
                break;
            }
            //@ open node(1)(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes == std::ptr::null_mut() || node(1)(nodes);
//@ ensures true;
{
    let mut result = 0;
    if !nodes.is_null() {
        //@ open node(1)(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(1)(nodes);
    }
    result
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}