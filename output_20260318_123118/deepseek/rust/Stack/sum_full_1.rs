use crate::verifast::*;

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate NodeOwned(node: *mut Node; value: i32, next: *mut Node) {
    alloc::allocated(node) &*&
    struct_Node_padding(node) &*&
    (*node).value |-> value &*&
    (*node).next |-> next
}

predicate Nodes(node: *mut Node; list: Seq<i32>) {
    node.is_null() ?
        list == Seq::empty()
    :
        NodeOwned(node, ?value, ?next) &*&
        Nodes(next, ?tail) &*&
        list == Seq::cons(value, tail)
}

predicate StackOwned(stack: *mut Stack; list: Seq<i32>) {
    alloc::allocated(stack) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, list)
}

#[requires(NodeOwned(node, ?value, ?next))]
#[ensures(NodeOwned(node, value, next))]
#[ensures(result == value)]
unsafe fn node_value(node: *mut Node) -> i32 {
    (*node).value
}

#[requires(NodeOwned(node, ?value, ?next))]
#[ensures(NodeOwned(node, value, next))]
#[ensures(result == next)]
unsafe fn node_next(node: *mut Node) -> *mut Node {
    (*node).next
}

#[requires(Nodes(node, ?list))]
#[ensures(Nodes(node, list))]
#[ensures(result == list.fold_left(0, |acc, x| acc + x))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let current_node = node;
        let value = node_value(current_node);
        let next = node_next(current_node);
        let tail_sum = get_nodes_sum(next);
        result = value + tail_sum;
    }
    result
}

impl Stack {
    #[requires(StackOwned(stack, ?list))]
    #[ensures(StackOwned(stack, list))]
    #[ensures(result == list.fold_left(0, |acc, x| acc + x))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = get_nodes_sum(head);
        result
    }
}