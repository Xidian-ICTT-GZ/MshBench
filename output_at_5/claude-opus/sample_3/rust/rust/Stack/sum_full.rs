use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate nodes(struct Node* node) =
    node == null ? 
        true 
    : 
        node->next |-> ?next &*& node->value |-> _ &*& malloc_block<Node>(node) &*& nodes(next);

predicate stack(struct Stack* stack) =
    stack->head |-> ?head &*& nodes(head) &*& malloc_block<Stack>(stack);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires nodes(node);
//@ ensures nodes(node);
//@ ensures result == (if node == std::ptr::null_mut() { 0 } else { (*node).value + get_nodes_sum((*node).next) });
{
    if node.is_null() {
        0
    } else {
        //@ open nodes(node);
        let tail_sum = get_nodes_sum((*node).next);
        let result = (*node).value + tail_sum;
        //@ close nodes(node);
        result
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack);
    //@ ensures stack(stack);
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
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        if head.is_null() {
            //@ close stack(stack);
            0
        } else {
            //@ open nodes(head);
            let result = (*head).value;
            (*stack).head = (*head).next;
            //@ close stack(stack);
            dealloc(head as *mut u8, Layout::new::<Node>());
            result
        }
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack);
    //@ ensures true;
    {
        //@ open stack(stack);
        // Recursively open all nodes to dealloc properly
        let mut curr = (*stack).head;
        while !curr.is_null()
            //@ invariant nodes(curr) &*& malloc_block<Stack>(stack);
        {
            //@ open nodes(curr);
            let next = (*curr).next;
            dealloc(curr as *mut u8, Layout::new::<Node>());
            curr = next;
        }
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