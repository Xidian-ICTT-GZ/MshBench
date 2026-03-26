use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; i32 value, *mut Node next) =
    n != null &*&
    struct_Node_padding(n) &*&
    struct_Node_next(n, next) &*&
    struct_Node_value(n, value);

predicate stack(*mut Stack s; list<i32> values) =
    s != null &*&
    struct_Stack_padding(s) &*&
    struct_Stack_head(s, ?head) &*&
    nodes(head, values);

predicate nodes(*mut Node n; list<i32> values) =
    match values {
        nil => n == null,
        cons(h, t) => node(n, h, ?next) &*& nodes(next, t)
    };

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
    requires nodes(n, ?vs) &*& foreach(vs, (p as *const ()) as *const ());
    ensures nodes(result, ?ws) &*& foreach(ws, (p as *const ()) as *const ()) &*&
            bag(ws) == bag(filter(vs, p));

{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            
            
            (*n).next = next;
            
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n, _);
    ensures true;

{
    
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        requires true;
        ensures stack(result, nil);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?vs);
        ensures stack(stack, cons(value, vs));
    
    
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
        requires stack(stack, cons(?v, ?vs));
        ensures stack(stack, vs) &*& result == v;
    
    
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack(stack, ?vs) &*& foreach(vs, (p as *const ()) as *const ());
        ensures stack(stack, ?ws) &*& foreach(ws, (p as *const ()) as *const ()) &*&
                bag(ws) == bag(filter(vs, p));
    
    
    {
        
        let head = filter_nodes((*stack).head, p);
        
        (*stack).head = head;
        
        
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, _);
        ensures true;
    
    
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
    requires true;
    ensures result == (x != 20);

{
    x != 20
}

fn main()
    requires true;
    ensures true;

{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}