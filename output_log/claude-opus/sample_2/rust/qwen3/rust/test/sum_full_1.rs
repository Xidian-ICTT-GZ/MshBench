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
    (q == 0 || node_pred(q, _, _));

pred list_pred(p: *mut Node, sum: i32) =
    p == 0 ? sum == 0 :
    exists v: i32, q: *mut Node, s: int.
        node_pred(p, v, q) &*&
        list_pred(q, s) &*&
        sum == v + s;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    #[requires(node == 0 || node_pred(node, _, _))]
    #[ensures(list_pred(node, result))]
{
    let mut result = 0;
    if !node.is_null() {
        // Open node_pred(node, v, q) to reveal value and next
        open node_pred(node, ?v, ?q);
        // We have points_to(node, Node { value: v, next: q }) and if q!=0 node_pred(q,...)
        // Also list_pred(q, tail_sum) is needed, prove by recursive call
        close list_pred(q, ?tail_sum);
        #[requires(list_pred(q, tail_sum))]
        #[ensures(result == v + tail_sum && list_pred(node, result))]
        let tail_sum = get_nodes_sum(q);
        // After call, we have list_pred(q, tail_sum) and result == tail_sum
        result = v + tail_sum;
        close node_pred(node, v, q);
        close list_pred(node, result);
    } else {
        close list_pred(0, 0);
        result = 0;
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(points_to(stack, Stack { head: ?head }) &*& list_pred(head, ?sum))]
        #[ensures(result == sum &*& points_to(stack, Stack { head: head }) &*& list_pred(head, sum))]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
}