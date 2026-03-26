use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
/*@
predicate_nodes(Node* nodes) = 
    nodes == NULL ?
        emp
    :
        nodes->next |-> ?next &*& nodes->value |-> _ &*& malloc_block_Node(nodes) &*& predicate_nodes(next);
@*/
struct Stack {
    head: *mut Node,
}
/*@
predicate_stack(Stack* stack) = 
    stack->head |-> ?head &*& malloc_block_Stack(stack) &*& predicate_nodes(head);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires predicate_nodes(nodes);
//@ ensures predicate_nodes(nodes);
//@ ensures true;
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open predicate_nodes(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close predicate_nodes(nodes);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires emp;
    //@ ensures predicate_stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close predicate_nodes(std::ptr::null_mut());
        //@ close predicate_stack(stack);
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ requires predicate_stack(stack);
    //@ ensures predicate_stack(stack);
    //@ ensures result == ((*stack).head.is_null());
    {
        
        let head = (*stack).head;
        //@ open predicate_stack(stack);
        //@ assert predicate_nodes(head);
        
        let result = (*stack).head.is_null();
        
        //@ close predicate_stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires predicate_stack(stack);
    //@ ensures predicate_stack(stack);
    //@ ensures true;
    {
        //@ open predicate_stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close predicate_stack(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires predicate_stack(stack);
    //@ ensures predicate_stack(stack);
    {
        //@ open predicate_stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close predicate_nodes(n);
        //@ close predicate_stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires predicate_stack(stack);
    //@ ensures predicate_stack(stack);
    {
        //@ open predicate_stack(stack);
        let head = (*stack).head;
        //@ open predicate_nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close predicate_stack(stack);
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ requires predicate_stack(stack);
    //@ ensures predicate_stack(stack);
    {
        let mut i = 0;
        loop {
            //@ open predicate_stack(stack);
            if i == n {
                //@ close predicate_stack(stack);
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ requires predicate_stack(stack);
    //@ ensures emp;
    {
        //@ open predicate_stack(stack);
        
        let mut n = (*stack).head;
        loop {
            if n.is_null() {
                break;
            }
            //@ open predicate_nodes(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}