use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes_list(struct Node* nodes;) =
    nodes == std::ptr::null_mut() ?
        emp
    :
        nodes |-> Node { next: ?next, value: ?v } * nodes_list(next);

predicate stack(struct Stack* s;) =
    s |-> Stack { head: ?head } * nodes_list(head);

#[requires(nodes_list(nodes))]
#[ensures(nodes_list(nodes) &*& result == fold_sum(nodes))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    //@ decreases nodes
{
    if nodes.is_null() {
        0
    } else {
        open nodes_list(nodes);
        let result = get_nodes_sum((*nodes).next);
        close nodes_list(nodes);
        result + (*nodes).value
    }
}

fixpoint int fold_sum(struct Node* nodes) {
    return nodes == std::ptr::null_mut() ? 0 : (*nodes).value + fold_sum((*nodes).next);
}

impl Stack {

    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack);
        stack
    }

    #[requires(stack(stack0))]
    #[ensures(stack(stack0) &*& result == ((*stack0).head.is_null()))]
    unsafe fn is_empty(stack0: *mut Stack) -> bool
    {
        open stack(stack0);
        let head = (*stack0).head;
        close stack(stack0);
        head.is_null()
    }

    #[requires(stack(stack0))]
    #[ensures(stack(stack0) &*& result == fold_sum((*stack0).head))]
    unsafe fn get_sum(stack0: *mut Stack) -> i32
    {
        open stack(stack0);
        let result = get_nodes_sum((*stack0).head);
        close stack(stack0);
        result
    }

    #[requires(stack(stack0))]
    #[ensures(stack(stack0))]
    unsafe fn push(stack0: *mut Stack, value: i32)
    {
        open stack(stack0);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack0).head;
        (*n).value = value;
        (*stack0).head = n;
        close nodes_list(n);
        close stack(stack0);
    }

    #[requires(stack(stack0) &*& (*stack0).head != std::ptr::null_mut())]
    #[ensures(stack(stack0))]
    unsafe fn pop(stack0: *mut Stack) -> i32
    {
        open stack(stack0);
        let head = (*stack0).head;
        open nodes_list(head);
        let result = (*head).value;
        (*stack0).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack(stack0);
        result
    }

    #[requires(stack(stack0))]
    #[ensures(true)]
    unsafe fn dispose(stack0: *mut Stack)
    {
        open stack(stack0);
        let mut n = (*stack0).head;
        while n != std::ptr::null_mut()
            #[invariant(nodes_list(n))]
        {
            open nodes_list(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        dealloc(stack0 as *mut u8, Layout::new::<Stack>());
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