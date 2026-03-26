use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
struct NodePred {
    next: *mut Node,
    value: i32,
    #[field] next_p: Box<NodePred>,
}

#[pred]
struct StackPred {
    head: *mut Node,
    #[field] nodes: Box<ListPred>,
}

#[pred]
struct ListPred {
    head: *mut Node,
    tail: *mut Node,
    #[field] nodes: Box<NodeListPred>,
}

#[pred]
struct NodeListPred {
    head: *mut Node,
    tail: *mut Node,
    #[field] nodes: Option<Box<NodeListPred>>,
}

#[lemma]
fn node_pred_valid(n: *mut Node) -> bool
where
    n != 0,
{
    requires([
        node_pred(n),
    ]);
    ensures([
        true,
    ]);
    // trivial lemma to allow reasoning about node structure
}

#[lemma]
fn list_pred_valid(head: *mut Node, tail: *mut Node) -> bool
where
    head != 0,
    tail != 0,
{
    requires([
        list_pred(head, tail),
    ]);
    ensures([
        true,
    ]);
}

#[predicate]
fn node_pred(n: *mut Node) -> bool {
    n != 0 && exists!(next: *mut Node, value: i32, next_p: Box<NodePred> |
        n == next_p.ptr &&
        (*n).next == next &&
        (*n).value == value &&
        node_pred(next) == (next != 0) &&
        (next == 0 ==> next_p == Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(NodePred { next: 0 as *mut Node, value: 0, next_p: Box::new(Node