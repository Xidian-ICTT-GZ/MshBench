unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires list_from_node(node, result);
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_ptr(stack, ?h) ** list_from_node(?h, result);
        ensures stack_ptr(stack, ?h) ** list_from_node(?h, result);
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}


use std::ptr;

#[predicate]
fn node_ptr(p: *mut Node, v: i32) -> Prop {
    p != null() && *p |-> Node { value: v, next: null() }
}

#[predicate]
fn list_from_node(p: *mut Node, total: i32) -> Prop {
    if p == null() {
        total == 0
    } else {
        let v = (*p).value;
        let n = (*p).next;
        node_ptr(p, v) ** list_from_node(n, total - v)
    }
}

#[predicate]
fn stack_ptr(s: *mut Stack, h: *mut Node) -> Prop {
    s != null() && *s |-> Stack { head: h }
}