//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node(node: *mut Node, next: *mut Node, value: i32) =
    alloc_block_(node as *mut u8, Layout::new::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack, head: *mut Node) =
    alloc_block_(stack as *mut u8, Layout::new::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

/*@ pred nodes(head: *mut Node) =
    head == null_mut() ?
        emp
    :
        node(head, ?next, ?val) &*& nodes(next);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(nodes);
//@ ens nodes(nodes) &*& result == sum_nodes(nodes);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(nodes);
    }
    
    result
}

/*@ fixpoint i32 sum_nodes(*mut Node head); @*/
/*@ lemma_auto sum_nodes_def()
    requires true;
    ensures
        sum_nodes(null_mut()) == 0 &*&
        forall(*mut Node n, *mut Node next, i32 val,
            node(n, next, val) ==>
            sum_nodes(n) == val + sum_nodes(next));
@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, null_mut());
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack, ?head);
    //@ ens stack(stack, head) &*& result == (head == null_mut());
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens stack(stack, head) &*& nodes(head) &*& result == sum_nodes(head);
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?old_head) &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head);
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, old_head, value);
        (*stack).head = n;
        //@ close nodes(n);
        //@ open stack(stack, old_head);
        //@ close stack(stack, n);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?old_head) &*& old_head != null_mut() &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head);
    {
        
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req stack(stack, ?head) &*& nodes(head) &*& n >= 0;
    //@ ens stack(stack, ?final_head) &*& nodes(final_head);
    {
        let mut i = 0;
        //@ loop_invariant stack(stack, ?curr_head) &*& nodes(curr_head) &*& i <= n;
        loop {
            
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens true;
    {
        
        let mut n = (*stack).head;
        //@ open stack(stack, head);
        loop {
            //@ inv nodes(n);
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            //@ open nodes(n);
            //@ open node(n, _, _);
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}