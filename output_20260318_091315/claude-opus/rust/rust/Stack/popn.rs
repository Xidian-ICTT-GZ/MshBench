use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate nodes(struct Node *n;) =
    n == std::ptr::null_mut() ?
        emp :
        n->value |-> ?v &*& n->next |-> ?nx &*& malloc_block_Node(n) &*& nodes(nx);

predicate stack(struct Stack *s;) =
    s->head |-> ?h &*& malloc_block_Stack(s) &*& nodes(h);

unsafe fn get_nodes_sum(nodes: *mut Node) 
    #[requires nodes(nodes)]
    #[ensures nodes(nodes)]
-> i32
{
    let mut result = 0;
    
    if !nodes.is_null() {
        open nodes(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        close nodes(nodes);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        #[requires emp]
        #[ensures stack(result)]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        close stack(stack);
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        #[requires stack(stack)]
        #[ensures stack(stack)]
    {
        open stack(stack);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        close stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires stack(stack)]
        #[ensures stack(stack)]
    {
        open stack(stack);
        let result = get_nodes_sum((*stack).head);
        close stack(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires stack(stack)]
        #[ensures stack(stack)]
    {
        open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        close nodes(n);
        (*stack).head = n;
        close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires stack(stack) &*& (*stack).head != std::ptr::null_mut()]
        #[ensures stack(stack)]
    {
        open stack(stack);
        let head = (*stack).head;
        open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
        #[requires stack(stack) &*& n >= 0]
        #[ensures stack(stack)]
    {
        open stack(stack);
        let mut i = 0;
        while(i < n)
            #[invariant 0 <= i &*& i <= n &*& stack(stack)]
        {
            Stack::pop(stack);
            i += 1;
        }
        close stack(stack);
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires stack(stack)]
        #[ensures emp]
    {
        open stack(stack);
        let mut n = (*stack).head;
        while(n != std::ptr::null_mut()) 
            #[invariant nodes(n)]
        {
            open nodes(n);
            let next = (*n).next;
            close nodes(n);
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