struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; sum: int) =
    n == 0 ? sum == 0 :
        n->value |-> ?v &*& n->next |-> ?next &*& nodes(next, ?rest_sum) &*& sum == v + rest_sum;

predicate stack(s: *mut Stack; sum: int) =
    s->head |-> ?h &*& nodes(h, sum);

#[requires(nodes(nodes, ?s))]
#[ensures(nodes(nodes, s) &*& result == s)]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    if nodes.is_null() {
        0
    } else {
        nodes->value |-> ?v &*& nodes->next |-> ?next &*& nodes(next, ?rest_sum);
        let res = get_nodes_sum(next);
        res + v
    }
}

impl Stack {
    #[requires(stack(stack, ?s))]
    #[ensures(stack(stack, s) &*& result == s)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        stack->head |-> ?h &*& nodes(h, ?sum);
        let res = get_nodes_sum(h);
        res
    }
}