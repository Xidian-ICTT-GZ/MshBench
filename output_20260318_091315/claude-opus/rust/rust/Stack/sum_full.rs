use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes_list(struct Node* node;) =
    node == std::ptr::null_mut() ?
        emp
    :
        node |-> Node { next: ?next, value: _ } &*& nodes_list(next);

predicate nodes_list_with_sum(struct Node* node, int sum;) =
    node == std::ptr::null_mut() ?
        emp &*& sum == 0
    :
        node |-> Node { next: ?next, value: ?v } &*&
        nodes_list_with_sum(next, ?tail_sum) &*&
        sum == v + tail_sum;

predicate stack(Stack* stack, struct Node* head, int sum;) =
    stack |-> Stack { head: head } &*&
    nodes_list_with_sum(head, sum);

unsafe fn get_nodes_sum(node: *mut Node)
    #[requires(nodes_list_with_sum(node, ?sum))]
    #[ensures(nodes_list_with_sum(node, sum) &*& result == sum)]
    -> i32
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        #[requires(true)]
        #[ensures(stack(result, std::ptr::null_mut(), 0))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(stack(stack, ?head, ?sum))]
        #[ensures(stack(stack, head, sum) &*& result == sum)]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack(stack, ?head, ?sum))]
        #[ensures(stack(stack, ?new_head, sum + value) &*& (*new_head).value == value)]
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
        #[requires(stack(stack, ?head, ?sum) &*& head != std::ptr::null_mut() &*& head |-> Node { next: ?next, value: ?v } &*& nodes_list(next))]
        #[ensures(stack(stack, next, sum - v) &*& result == v)]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack(stack, std::ptr::null_mut(), 0))]
        #[ensures(true)]
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}