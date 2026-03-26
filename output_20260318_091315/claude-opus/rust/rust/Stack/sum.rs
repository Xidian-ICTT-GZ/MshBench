use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
  
predicate nodes(struct Node* nodes;) = 
    nodes == std::ptr::null_mut() ?
      emp
    : nodes->value |-> ?v &*& nodes->next |-> ?next &*& malloc_block<Node>(nodes) &*& nodes(next);

predicate stack(struct Stack* stack;) = 
    stack->head |-> ?head &*& nodes(head) &*& malloc_block<Stack>(stack);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    #[requires(nodes(nodes))]
    #[ensures(nodes(nodes) &*& result == nodes_sum(nodes))]
{
    let mut result = 0;
    
    if !nodes.is_null() {
        let n = &*nodes;
        open nodes(nodes);
        result = get_nodes_sum(n.next);
        result += n.value;
        close nodes(nodes);
    }
    
    result
}

predicate nodes_sum(struct Node* n;) =
    n == std::ptr::null_mut() ? 0 : (*n).value + nodes_sum((*n).next);

impl Stack {
    unsafe fn create() -> *mut Stack
        #[requires(true)]
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
        #[ensures stack(stack) &*& result == (((*stack).head) == std::ptr::null_mut())]
    {
        open stack(stack);
        let head = (*stack).head;
        let result = head.is_null();
        close stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires stack(stack)]
        #[ensures stack(stack) &*& result == nodes_sum((*stack).head)]
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
        let head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = head;
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
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires stack(stack)]
        #[ensures true]
    {
        open stack(stack);
        let mut n = (*stack).head;
        while n != std::ptr::null_mut()
            invariant nodes(n)
        {
            open nodes(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
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