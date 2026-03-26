use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ 
predicate node_pred(Node *node; int value, Node *next) = 
    node != null &*&
    acc(node, sizeof(Node)) &*&
    *node.next |-> next &*&
    *node.value |-> value;
@*/

/*@
predicate stack_pred(Stack *stack; Node *head) = 
    stack != null &*&
    acc(stack, sizeof(Stack)) &*&
    *stack.head |-> head;
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ req true;
//@ ens true;
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open node_pred(nodes, _, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node_pred(nodes, (*nodes).value, (*nodes).next);
    }
    
    result
}

impl Stack {

    //@ req true;
    //@ ensures stack_pred(result, null);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_pred(stack, null);
        stack
    }
    
    //@ req stack_pred(stack, ?head);
    //@ ensures stack_pred(stack, head) &*& result == ((*stack).head).is_null();
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        //@ open stack_pred(stack, head);
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        //@ close stack_pred(stack, head);
        result
    }
    
    //@ req stack_pred(stack, ?head);
    //@ ensures stack_pred(stack, head);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack_pred(stack, head);
        let result = get_nodes_sum((*stack).head);
        //@ close stack_pred(stack, head);
        result
    }

    //@ req stack_pred(stack, ?old_head);
    //@ ensures stack_pred(stack, n);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack_pred(stack, old_head);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node_pred(n, value, old_head);
        
        (*stack).head = n;
        
        //@ close stack_pred(stack, n);
    }

    //@ req stack_pred(stack, ?old_head) &*& old_head != null &*& node_pred(old_head, ?value, ?next);
    //@ ensures stack_pred(stack, next) &*& node_pred(old_head, value, next);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack_pred(stack, old_head);
        //@ open node_pred(old_head, _, _);
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack_pred(stack, (*head).next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack_pred(stack, (*head).next);
        result
    }
    
    //@ req stack_pred(stack, ?head) &*& n >= 0;
    //@ ensures stack_pred(stack, ?final_head);
    unsafe fn popn(stack: *mut Stack, n: i32)
    {
        let mut i = 0;
        //@ open stack_pred(stack, head);
        let mut cur_head = (*stack).head;
        //@ close stack_pred(stack, cur_head);
        loop {
            //@ inv stack_pred(stack, cur_head) &*& 0 <= i &*& i <= n;
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
            //@ open stack_pred(stack, cur_head);
            cur_head = (*stack).head;
            //@ close stack_pred(stack, cur_head);
        }
    }
    
    //@ req stack_pred(stack, ?head);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack_pred(stack, head);
        
        let mut n = (*stack).head;
        loop {
            //@ if n == null { break; }
            if n.is_null() {
                break;
            }
            //@ open node_pred(n, _, _);
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