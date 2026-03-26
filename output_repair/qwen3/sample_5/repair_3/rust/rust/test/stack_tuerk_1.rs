#![feature(stmt_expr_attributes)]
use std::ptr;

struct Stack {
    head: *mut StackNode,
}

struct StackNode {
    next: *mut StackNode,
}

#[verifast::predicate]
pub fn stack_node(node: *mut StackNode) = 
    node != ptr::null_mut() && verifast::points_to((*node).next, ?next);

#[verifast::predicate]
pub fn stack(stack_ptr: *mut Stack, head: *mut StackNode) = 
    stack_ptr != ptr::null_mut() && verifast::points_to((*stack_ptr).head, head);

#[verifast::predicate]
pub fn stack_nodes(node: *mut StackNode, tail: *mut StackNode) = 
    if node == ptr::null_mut() {
        tail == ptr::null_mut()
    } else {
        stack_node(node) && stack_nodes(verifast::field_access!((*node).next), tail)
    };

#[verifast::pure]
pub fn stack_length(node: *mut StackNode) -> i32 {
    if node == ptr::null_mut() {
        0
    } else {
        1 + stack_length(unsafe { (*node).next })
    }
}

unsafe fn stack_get_count_specified(stack: *mut Stack) -> i32 {
    #[verifast::requires(stack(stack, ?head) && stack_nodes(head, ptr::null_mut()))]
    #[verifast::ensures(stack(stack, head) && stack_nodes(head, ptr::null_mut()) && result == stack_length(head))]
    {
        let mut n = (*stack).head;
        let mut i = 0;
        #[verifast::invariant(
            stack(stack, ?s_head) &&
            stack_nodes(n, ?current_tail) &&
            stack_nodes(current_tail, ptr::null_mut()) &&
            i + stack_length(current_tail) == stack_length(s_head)
        )]
        loop {
            if n == ptr::null_mut() {
                break;
            }
            let next = (*n).next;
            verifast::consume(stack_nodes(n, current_tail));
            verifast::produce(stack_node(n));
            verifast::produce(verifast::points_to((*n).next, next));
            verifast::consume(stack_nodes(next, current_tail));
            n = next;
            i += 1;
        }

        i
    }
}