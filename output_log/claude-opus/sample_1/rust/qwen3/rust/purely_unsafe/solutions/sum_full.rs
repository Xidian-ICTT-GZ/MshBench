use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

#[predicate]
pub unsafe fn node_pred(node: *mut Node, next: *mut Node, value: i32) = 
    node |-> Node { next: next, value: value };

#[predicate]
pub unsafe fn stack_pred(stack: *mut Stack, head: *mut Node) =
    stack |-> Stack { head: head };

#[predicate]
pub unsafe fn list_pred(mut node: *mut Node) {
    if node == std::ptr::null_mut() {
        emp()
    } else {
        exists |next: *mut Node, val: i32| 
            node_pred(node, next, val) &*&
            list_pred(next)
    }
}

#[predicate]
pub unsafe fn stack_list_pred(stack: *mut Stack, head: *mut Node) =
    stack_pred(stack, head) &*& list_pred(head);

#[predicate]
pub unsafe fn list_sum_pred(node: *mut Node, sum: int) {
    if node == std::ptr::null_mut() {
        emp() &*& sum == 0
    } else {
        exists |next: *mut Node, val: i32, tail_sum: int| 
            node_pred(node, next, val) &*&
            list_sum_pred(next, tail_sum) &*&
            sum == val as int + tail_sum
    }
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    #[requires(
        node == std::ptr::null_mut() ?
            emp() :
            list_pred(node)
    )]
    #[ensures(
        list_sum_pred(node, result as int)
    )]
{
    if node.is_null() {
        0
    } else {
        let next = (*node).next;
        let tail_sum = get_nodes_sum(next);
        let val = (*node).value;
        val + tail_sum
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        #[requires(true)]
        #[ensures(
            result != std::ptr::null_mut() &*&
            stack_list_pred(result, std::ptr::null_mut())
        )]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(
            stack != std::ptr::null_mut() &*&
            stack_list_pred(stack, ?head)
        )]
        #[ensures(
            stack_list_pred(stack, head) &*&
            list_sum_pred(head, result as int)
        )]
    {
        let head = (*stack).head;
        get_nodes_sum(head)
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(
            stack != std::ptr::null_mut() &*&
            stack_list_pred(stack, ?old_head)
        )]
        #[ensures(
            stack_list_pred(stack, ?new_head) &*&
            new_head != std::ptr::null_mut() &*&
            node_pred(new_head, old_head, value) &*&
            list_pred(old_head)
        )]
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
        #[requires(
            stack != std::ptr::null_mut() &*&
            stack_list_pred(stack, ?head) &*&
            head != std::ptr::null_mut() &*&
            node_pred(head, ?next, ?val) &*&
            list_pred(next)
        )]
        #[ensures(
            stack_list_pred(stack, next) &*&
            result == val
        )]
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires(
            stack != std::ptr::null_mut() &*&
            stack_list_pred(stack, ?head)
        )]
        #[ensures(true)]
    {
        let mut curr = (*stack).head;
        while curr != std::ptr::null_mut()
            #[invariant(
                exists |h: *mut Node| stack_pred(stack, h) &*& list_pred(h)
            )]
        {
            let next = (*curr).next;
            dealloc(curr as *mut u8, Layout::new::<Node>());
            curr = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
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