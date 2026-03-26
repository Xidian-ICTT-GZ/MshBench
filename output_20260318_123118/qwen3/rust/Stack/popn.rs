use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate Nodes(*mut Node nodes; i32 sum, *mut Node end) =
    match nodes {
        null => sum == 0 && end == null,
        _ => (*nodes).next |-> ?next &*& (*nodes).value |-> ?val &*& Nodes(next, ?sum_rest, end) &*& sum == val + sum_rest
    };

predicate Stack(*mut Stack stack; i32 sum) =
    (*stack).head |-> ?head &*& Nodes(head, sum, null);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires Nodes(nodes, ?sum, null);
    ensures Nodes(nodes, sum, null) &*& result == sum;
{
    let mut result = 0;
    
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        requires true;
        ensures Stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires Stack(stack, ?sum);
        ensures Stack(stack, sum) &*& result == (sum == 0);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires Stack(stack, ?sum);
        ensures Stack(stack, sum) &*& result == sum;
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires Stack(stack, ?old_sum);
        ensures Stack(stack, old_sum + value);
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires Stack(stack, ?sum) &*& sum != 0;
        ensures Stack(stack, ?new_sum) &*& result + new_sum == sum;
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
        requires Stack(stack, ?sum) &*& n >= 0 &*& sum >= sum_of_first_n_elements(n); 
        ensures Stack(stack, ?new_sum) &*& new_sum == sum - sum_of_popped_values(n); 
    {
        let mut i = 0;
        loop 
            invariant Stack(stack, ?current_sum) &*& i <= n &*& current_sum == sum - sum_of_popped_values(i);
        {
            
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
        requires Stack(stack, ?sum);
        ensures true;
    {
        
        let mut n = (*stack).head;
        loop 
            invariant Nodes(n, ?remaining_sum, null) &*& remaining_sum >= 0;
        {
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

lemma void sum_of_first_n_elements(int n);
    requires n >= 0;
    ensures true;

lemma void sum_of_popped_values(int n);
    requires n >= 0;
    ensures true;

fn main()
    requires true;
    ensures true;
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