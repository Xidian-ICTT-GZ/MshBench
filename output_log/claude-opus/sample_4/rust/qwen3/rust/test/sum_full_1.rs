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
    (q == 0 ? true : node_pred(q, _, _));

predicate list_pred(p: *mut Node, sum: int) =
    p == 0 ?
        sum == 0
    :
        exists<v: int, q: *mut Node, s: int>. 
            node_pred(p, v, q) &*&
            list_pred(q, s) &*&
            sum == v + s;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    #[requires(node == 0 ? emp : node_pred(node, _, _))]
    #[ensures(list_pred(node, result))]
{
    if node.is_null() == false {
        open node_pred(node, ?v, ?q);
        open list_pred(q, ?tail_sum);
        let tail_sum = get_nodes_sum(q);
        close list_pred(q, tail_sum);
        close node_pred(node, v, q);
        close list_pred(node, v + tail_sum);
        v + tail_sum
    } else {
        close list_pred(node, 0);
        0
    }
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(points_to(stack, Stack { head: ?head }) &*& list_pred(head, ?sum))]
        #[ensures(result == sum)]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
}