use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ predicate nodes_sum_pred(Node* node;) =
//@     node == std::ptr::null_mut() ? emp : node->value |-> _ &*& node->next |-> ?next &*& nodes_sum_pred(next);

struct Stack {
    head: *mut Node,
}

//@ predicate stack_pred(Stack* stack;) =
//@     stack->head |-> ?head &*& nodes_sum_pred(head);

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires nodes_sum_pred(node);
//@ ensures nodes_sum_pred(node) &*& result == (exists i32 v; node != std::ptr::null_mut() && node->value |-> v) ? v + get_nodes_sum(node->next) : 0;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes_sum_pred(node);
        let tail_sum = get_nodes_sum((*node).next);
        //@ close nodes_sum_pred(node);
        result = (*node).value + tail_sum;
    }
    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack_pred(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_pred(stack);
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
    {
        //@ open stack_pred(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack_pred(stack);
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack_pred(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes_sum_pred(n);
        //@ close stack_pred(stack);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
    {
        //@ open stack_pred(stack);
        let head = (*stack).head;
        //@ open nodes_sum_pred(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack_pred(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack_pred(stack);
    //@ ensures true;
    {
        //@ open stack_pred(stack);
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