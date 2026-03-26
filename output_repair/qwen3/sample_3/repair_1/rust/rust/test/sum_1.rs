#[predicate]
fn node_pred(n: *mut Node, value: i32, next: *mut Node) -> bool {
    (*n).value |-> value * (*n).next |-> next
}

#[predicate]
fn nodes_sum_pred(nodes: *mut Node, sum: i32) -> bool {
    if nodes.is_null() {
        true
    } else {
        exists(value: i32, next: *mut Node, rest_sum: i32).
            node_pred(nodes, value, next) *
            nodes_sum_pred(next, rest_sum) *
            (sum == value + rest_sum)
    }
}

#[predicate]
fn stack_pred(s: *mut Stack, head: *mut Node) -> bool {
    (*s).head |-> head
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    #[requires(nodes_sum_pred(nodes, ?sum))]
    #[ensures(nodes_sum_pred(nodes, sum) &*& result == sum)]
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[requires(exists(head: *mut Node, sum: i32).
                   stack_pred(stack, head) *
                   nodes_sum_pred(head, sum))]
        #[ensures(exists(head: *mut Node, sum: i32).
                  stack_pred(stack, head) *
                  nodes_sum_pred(head, sum) *
                  result == sum)]
        let result = get_nodes_sum((*stack).head);

        result
    }
}