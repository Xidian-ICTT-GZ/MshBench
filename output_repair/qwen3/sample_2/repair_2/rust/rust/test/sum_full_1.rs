unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}


#[derive(Clone, Copy)]
struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(node: *mut Node; sum: i32) =
    node == std::ptr::null_mut() &*& sum == 0
    || 
    node != std::ptr::null_mut() &*& 
    *node |-> ?v &*& 
    node->next |-> ?nxt &*& 
    Nodes(nxt, ?tail_sum) &*& 
    sum == v + tail_sum;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires Nodes(node, ?s);
    ensures Nodes(node, s) &*& result == s;
{
    let mut result = 0;
    if !node.is_null() {
        open Nodes(node, _);
        let v = *node;
        let nxt = node->next;
        let tail_sum = get_nodes_sum(nxt);
        close Nodes(node, v + tail_sum);
        result = v + tail_sum;
    } else {
        open Nodes(node, _);
        close Nodes(node, 0);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires *stack |-> ?h &*& Nodes(h, ?s);
        ensures *stack |-> h &*& Nodes(h, s) &*& result == s;
    {
        open *stack |-> _;
        let h = stack->head;
        let result = get_nodes_sum(h);
        close *stack |-> h;
        result
    }
}