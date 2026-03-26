struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; sum: i32) =
    if n.is_null() {
        sum == 0
    } else {
        (*n).value |-> ?v &*& (*n).next |-> ?next &*& nodes(next, ?rest_sum) &*& sum == v + rest_sum
    };

predicate stack(s: *mut Stack; sum: i32) =
    (*s).head |-> ?h &*& nodes(h, sum);

#[requires(nodes(nodes, ?s))]
#[ensures(nodes(nodes, s) &*& result == s)]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[requires(stack(stack, ?s))]
    #[ensures(stack(stack, s) &*& result == s)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}