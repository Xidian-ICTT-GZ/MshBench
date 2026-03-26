use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes_list(node: *mut Node; vs: list<i32>) =
    node == 0 ?
        vs == nil
    :
        node->next |-> ?nxt &*& node->value |-> ?v &*& nodes_list(nxt, ?vs0) &*& vs == cons(v, vs0);

predicate stack(stack: *mut Stack; vs: list<i32>) =
    stack->head |-> ?h &*& nodes_list(h, vs);

@*/

#[requires(nodes_list(nodes, ?vs))]
#[ensures(nodes_list(nodes, vs) &*& result == sum(vs))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    let mut result = 0;
    
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    
    result
}

impl Stack {

    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, vs) &*& result == (vs == nil))]
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, vs) &*& result == sum(vs))]
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        
    }

    #[requires(stack(stack, cons(?v, ?vs0)))]
    #[ensures(stack(stack, vs0) &*& result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    #[requires(stack(stack, ?vs))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        
        let mut n = (*stack).head;
        /*@
        open stack(stack, vs);
        @*/
        loop {
            /*@
            invariant nodes_list(n, ?vsn);
            @*/
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            /*@
            open nodes_list(n, vsn);
            @*/
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        /*@
        open nodes_list(n, ?vsfinal);
        @*/
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

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