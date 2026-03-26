#[allow(dead_code)]
struct Node {
    value: i32,
    next: *mut Node,
}

#[allow(dead_code)]
struct Stack {
    head: *mut Node,
}

pred node_pred(p: *mut Node, v: i32, q: *mut Node) =
    p != 0 &*& 
    points_to(p, Node { value: v, next: q }) &*&
    if q != 0 { node_pred(q, _, _) } else { true };

pred list_pred(p: *mut Node, sum: i32) =
    p == 0 ? sum == 0 :
    exists v: i32, q: *mut Node, s: i32.
        node_pred(p, v, q) &*&
        list_pred(q, s) &*&
        sum == v + s;

unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    #[requires(node_pred(node, _, _) || node == 0)]
    #[ensures(result == ?sum; list_pred(node, sum))]
    let mut result = 0;
    if !node.is_null() {
        #[requires(node_pred(node, ?v, ?q) &*& list_pred(q, ?tail_sum))]
        #[ensures(result == v + tail_sum &*& list_pred(node, result))]
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[requires(points_to(stack, Stack { head: ?head }) &*& list_pred(head, ?sum))]
        #[ensures(result == sum)]
        let result = get_nodes_sum((*stack).head);

        result
    }
}