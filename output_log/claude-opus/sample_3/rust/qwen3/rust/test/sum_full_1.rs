#[allow(dead_code)]
struct Node {
    value: i32,
    next: *mut Node,
}

#[allow(dead_code)]
struct Stack {
    head: *mut Node,
}

pred node_pred(p: *mut Node, v: int, q: *mut Node) =
    p != 0 &*& 
    points_to(p, Node { value: v, next: q }) &*&
    (q != 0 ? node_pred(q, _, _) : emp);

pred list_pred(p: *mut Node, sum: int) =
    p == 0 ? sum == 0 : 
    exists v: int, q: *mut Node, s: int.
        node_pred(p, v, q) &*&
        list_pred(q, s) &*&
        sum == v + s;

unsafe fn get_nodes_sum(node: *mut Node) -> int
    #[requires(node == 0 ? emp : node_pred(node, _, _))]
    #[ensures(list_pred(node, result))]
{
    let mut result = 0;
    if !node.is_null() {
        let v;
        let q;
        open node_pred(node, v, q);
        let tail_sum = get_nodes_sum(q);
        result = v + tail_sum;
        close node_pred(node, v, q);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> int
        #[requires(points_to(stack, Stack { head: ?head }) &*& list_pred(head, ?sum))]
        #[ensures(result == sum &*& points_to(stack, Stack { head: head }) &*& list_pred(head, sum))]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
}