use vstd::prelude::*;
use vstd::ptr::*;

verus! {

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_points_to(node: *mut Node, value: i32, next: *mut Node) {
    &&& is_valid_node(node)
    &&& (*node).value == value
    &&& (*node).next == next
}

predicate nodes(node: *mut Node) {
    if node.is_null() {
        true
    } else {
        node_points_to(node, ?value, ?next) *&* nodes(next)
    }
}

predicate stack_points_to(stack: *mut Stack, head: *mut Node) {
    &&& is_valid_stack(stack)
    &&& (*stack).head == head
}

#[requires(nodes(node))]
#[ensures(result == nodes_sum(node))]
#[ensures(nodes(node))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    let mut result = 0;
    if !node.is_null() {
        let next = (*node).next;
        proof {
            open nodes(node);
            open node_points_to(node, _, _);
        }
        let tail_sum = get_nodes_sum(next);
        result = (*node).value + tail_sum;
        proof {
            close node_points_to(node, _, _);
            close nodes(node);
        }
    } else {
        proof {
            open nodes(node);
        }
    }
    result
}

impl Stack {
    #[requires(stack_points_to(stack, ?head) *&* nodes(head))]
    #[ensures(result == nodes_sum(head))]
    #[ensures(stack_points_to(stack, head) *&* nodes(head))]
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = get_nodes_sum(head);
        result
    }
}

#[predicate]
fn nodes_sum(node: *mut Node) -> i32
    decreases nodes_depth(node)
{
    if node.is_null() {
        0
    } else {
        open nodes(node);
        open node_points_to(node, ?value, ?next);
        let tail_sum = nodes_sum(next);
        value + tail_sum
    }
}

#[predicate]
fn nodes_depth(node: *mut Node) -> nat
    decreases 1
{
    if node.is_null() {
        0
    } else {
        open nodes(node);
        open node_points_to(node, _, ?next);
        1 + nodes_depth(next)
    }
}

#[predicate]
fn is_valid_node(node: *mut Node) -> bool {
    addr_of!((*node).value).is_nonoverlapping_with(addr_of!((*node).next))
}

#[predicate]
fn is_valid_stack(stack: *mut Stack) -> bool {
    true
}

}