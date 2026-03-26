struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; sum: int) =
    n == null ?
        sum == 0
    :
        n->value |-> ?v &*& n->next |-> ?next &*& nodes(next, ?rest_sum) &*& sum == v + rest_sum;

predicate stack(s: *mut Stack; sum: int) =
    s->head |-> ?h &*& nodes(h, sum);

#[requires(nodes(nodes, ?s))]
#[ensures(nodes(nodes, s) &*& result == s)]
unsafe fn get_nodes_sum(nodes: *mut Node) -> int {
    if nodes == null {
        0
    } else {
        let v = (*nodes).value;
        let next = (*nodes).next;
        // Fold before recursive call
        open nodes(nodes, ?sum);
        close nodes(next, ?rest_sum);
        let res = get_nodes_sum(next);
        close nodes(nodes, v + res);
        res + v
    }
}

impl Stack {
    #[requires(stack(stack, ?s))]
    #[ensures(stack(stack, s) &*& result == s)]
    unsafe fn get_sum(stack: *mut Stack) -> int {
        open stack(stack, ?sum);
        let result = get_nodes_sum((*stack).head);
        close stack(stack, result);
        result
    }
}