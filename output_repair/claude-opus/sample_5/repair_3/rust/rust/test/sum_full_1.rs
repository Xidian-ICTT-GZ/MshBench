struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(node: *mut Node, sum: i32) =
  node.is_null() ? sum == 0 : 
    exists head_val: i32, tail_sum: i32 ::
      points_to(node, ?n) &*& n.value == head_val &*& 
      node_list(n.next, tail_sum) &*& sum == head_val + tail_sum;

predicate stack_valid(stack: *mut Stack, sum: i32) =
  points_to(stack, ?s) &*& node_list(s.head, sum);

#[requires(node_list(node, ?sum))]
#[ensures(node_list(node, sum) &*& result == sum)]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    #[requires(stack_valid(stack, ?sum))]
    #[ensures(stack_valid(stack, sum) &*& result == sum)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}