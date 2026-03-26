use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        alloc::points_to(n, Node { next: (*n).next, value: (*n).value }) 
        &*& nodes((*n).next)
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    alloc::points_to(s, Stack { head: (*s).head }) &*& nodes((*s).head)
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    #[requires(nodes(nodes))]
    #[ensures(result >= 0 && nodes(nodes))]
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
        #[ensures(stack(result))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        close nodes(std::ptr::null_mut());
        close stack(stack);
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        open stack(stack);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        close stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        open stack(stack);
        let result = get_nodes_sum((*stack).head);
        close stack(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        close nodes(n);
        close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        open stack(stack);
        let head = (*stack).head;
        open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        close stack(stack);
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        let mut i = 0;
        loop {
            #[invariant(stack(stack))]
            #[invariant(i >= 0 && i <= n)]
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack(stack))]
        #[ensures(true)]
    {
        open stack(stack);
        let mut n = (*stack).head;
        loop {
            #[invariant(nodes(n))]
            if n.is_null() {
                break;
            }
            
            open nodes(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
    #[ensures(true)]
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