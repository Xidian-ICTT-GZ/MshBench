use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
pub unsafe fn node_pred(node: *mut Node, next: *mut Node, value: i32) =  
    node |-> Node { next: next, value: value };

#[predicate]
pub unsafe fn nodes_list(node: *mut Node, sum: int) = 
    if node == std::ptr::null_mut() {
        true && sum == 0
    } else {
        node_pred(node, ?next, ?val) &*&
        nodes_list(next, ?tail_sum) &*&
        sum == val + tail_sum
    };

#[predicate]
pub unsafe fn stack_pred(stack: *mut Stack, head: *mut Node) =
    stack |-> Stack { head: head };

#[predicate]
pub unsafe fn stack_list(stack: *mut Stack, head: *mut Node) =
    stack_pred(stack, head) &*& nodes_list(head, ?sum);

#[lemma]
pub unsafe fn node_pred_valid(node: *mut Node) 
    requires node != std::ptr::null_mut() &*& node |-> Node { next: ?next, value: ?value };
    ensures node_pred(node, next, value);
{
}

#[lemma]
pub unsafe fn stack_pred_valid(stack: *mut Stack)
    requires stack != std::ptr::null_mut() &*& stack |-> Stack { head: ?head };
    ensures stack_pred(stack, head);
{
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32 
    requires node == std::ptr::null_mut() ||  
             (node_pred(node, ?next, ?val) &*& nodes_list(next, ?tail_sum));
    ensures nodes_list(node, result);
{
    if node.is_null() {
        0
    } else {
        let tail_sum = get_nodes_sum((*node).next);
        (*node).value + tail_sum
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires true;
        ensures result != std::ptr::null_mut() &*& stack_pred(result, std::ptr::null_mut()) &*& nodes_list(std::ptr::null_mut(), 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack != std::ptr::null_mut() &*& stack_list(stack, ?head);
        ensures nodes_list(head, result);
    {
        get_nodes_sum((*stack).head)
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack != std::ptr::null_mut() &*& stack_list(stack, ?old_head);
        ensures stack_list(stack, ?new_head) &*& new_head != std::ptr::null_mut() &*& node_pred(new_head, old_head, value);
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
        requires stack != std::ptr::null_mut() &*& stack_list(stack, ?head) &*& head != std::ptr::null_mut() &*& node_pred(head, ?next, ?val);
        ensures stack_list(stack, next) &*& result == val;
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack != std::ptr::null_mut() &*& stack_list(stack, ?head);
        ensures true;
    {
        let mut cur = (*stack).head;
        while cur != std::ptr::null_mut()
            invariant stack_pred(stack, ?head0) &*& nodes_list(cur, ?restSum) &*& head0 == cur || (head0 != cur)
        {
            let next = (*cur).next;
            dealloc(cur as *mut u8, Layout::new::<Node>());
            cur = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

fn main() {
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