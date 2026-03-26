struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node_list(node: *mut Node, sum: i32) =
    if node == std::ptr::null_mut() {
        sum == 0
    } else {
        (*node).value |-> ?v &*& (*node).next |-> ?nxt &*&
        node_list(nxt, ?tail_sum) &*&
        sum == v + tail_sum
    };

pred stack_pred(stack: *mut Stack, sum: i32) =
    (*stack).head |-> ?h &*& node_list(h, sum);
@*/

/*@
#[requires(node_list(node, sum))]
#[ensures(node_list(node, sum) &*& result == sum)]
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
    #[requires(stack_pred(stack, sum))]
    #[ensures(stack_pred(stack, sum) &*& result == sum)]
    @*/
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}