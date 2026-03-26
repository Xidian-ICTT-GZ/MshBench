use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

predicate node(struct Node* n) = 
    n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_Node(n) &*& (next == null ? true : node(next));

predicate stack(struct Stack* s; struct Node* head) = 
    s->head |-> head &*& malloc_block_Stack(s) &*& (head == null ? true : node(head));

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    #[requires(nodes == std::ptr::null_mut() || node(nodes))]
    #[ensures(result == 0 || nodes == null && result == 0 || nodes != null && node(nodes) && result == get_nodes_sum((*nodes).next) + (*nodes).value)]
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
        #[requires(true)]
        #[ensures(stack(result, std::ptr::null_mut()))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        #[requires(stack != std::ptr::null_mut() &*& stack(stack, ?head))]
        #[ensures(stack(stack, head) &*& result == (head == std::ptr::null_mut()))]
    {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(stack != std::ptr::null_mut() &*& stack(stack, ?head))]
        #[ensures(stack(stack, head) &*& result == get_nodes_sum(head))]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack != std::ptr::null_mut() &*& stack(stack, ?head))]
        #[ensures(stack(stack, ?newHead) &*& newHead != std::ptr::null_mut() &*& (*newHead).value == value &*& (*newHead).next == head)]
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
        #[requires(stack != std::ptr::null_mut() &*& stack(stack, ?head) &*& head != std::ptr::null_mut() &*& node(head))]
        #[ensures(stack(stack, (*head).next) &*& result == (*head).value)]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack != std::ptr::null_mut() &*& stack(stack, ?head))]
        #[ensures(true)]
    {
        let mut n = (*stack).head;
        while n != std::ptr::null_mut()
            #[invariant((stack(stack, n)) &*& (n == std::ptr::null_mut() || node(n)))]
        {
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