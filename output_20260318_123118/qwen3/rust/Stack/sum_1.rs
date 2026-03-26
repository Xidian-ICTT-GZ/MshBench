#[predicate]
pub pred Node(node: *mut Node; value: i32, next: *mut Node) =
    (*node).value |-> value &*& (*node).next |-> next;

#[predicate]
pub pred Nodes(nodes: *mut Node; values: list<i32>) =
    match values {
        cons(h, t) => exists(next: *mut Node). Node(nodes, h, next) * Nodes(next, t),
        nil => nodes == null_mut(),
    };

#[predicate]
pub pred Stack(stack: *mut Stack; values: list<i32>) =
    (*stack).head |-> ?head &*& Nodes(head, values);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires Nodes(nodes, ?values);
    ensures Nodes(nodes, values) &*& result == sum(values);
{
    let mut result = 0;

    if !nodes.is_null() {
        let value = (*nodes).value;
        let next = (*nodes).next;
        close Node(nodes, value, next);
        open Nodes(nodes, _);
        result = get_nodes_sum(next);
        result += value;
        close Nodes(nodes, cons(value, _));
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires Stack(stack, ?values);
        ensures Stack(stack, values) &*& result == sum(values);
    {
        open Stack(stack, values);
        let head = (*stack).head;
        let result = get_nodes_sum(head);
        close Stack(stack, values);
        result
    }
}