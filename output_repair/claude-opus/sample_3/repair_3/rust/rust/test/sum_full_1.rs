use std::ptr;

/*@
pred node_list(node: *mut Node, sum: i32) =
    if node == ptr::null_mut() {
        sum == 0
    } else {
        (*node).value |-> ?v &*& (*node).next |-> ?nxt &*&
        node_list(nxt, ?tail_sum) &*&
        sum == v + tail_sum
    };

pred stack_pred(stack: *mut Stack, sum: i32) =
    (*stack).head |-> ?h &*& node_list(h, sum);
@*/

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
req node_list(node, ?sum);
ens node_list(node, sum) &*& result == sum;
@*/
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    /*@
    req stack_pred(stack, ?sum);
    ens stack_pred(stack, sum) &*& result == sum;
    @*/
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}