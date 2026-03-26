use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node_ptr(struct Node *n; struct Node *next, i32 value) =
    n->next |-> next &*& n->value |-> value;

predicate nodes(struct Node *n; list<i32> vs) =
    n == 0 ?
        vs == nil
    :
        node_ptr(n, ?next, ?v) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate stack(struct Stack *s; list<i32> vs) =
    s->head |-> ?h &*& nodes(h, vs);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes(nodes, ?vs);
//@ ensures nodes(nodes, vs) &*& result == (i32_of_int(sum(vs)));
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
    //@ requires true;
    //@ ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, vs) &*& result == (vs == nil);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, vs) &*& result == (i32_of_int(sum(vs)));
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, cons(value, vs));
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
    //@ requires stack(stack, ?vs) &*& vs != nil;
    //@ ensures stack(stack, tail(vs)) &*& result == head(vs);
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ requires stack(stack, ?vs) &*& 0 <= n &*& n <= length(vs);
    //@ ensures stack(stack, drop(n, vs));
    {
        let mut i = 0;
        loop {
            /*@
            invariant stack(stack, ?vs2) &*& 0 <= i &*& i <= n
                &*& vs2 == drop(i, vs);
            @*/
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, ?vs);
    //@ ensures true;
    {
        
        let mut n = (*stack).head;
        /*@
        open stack(stack, vs);
        @*/
        loop {
            /*@
            invariant nodes(n, ?vs2);
            @*/
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            /*@
            open nodes(n, vs2);
            open node_ptr(n, next, ?v);
            @*/
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        /*@
        open nodes(n, ?vs3);
        @*/
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