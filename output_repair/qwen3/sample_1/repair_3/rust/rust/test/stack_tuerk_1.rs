unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}


#![feature(stmt_expr_attributes)]

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate stack_node(*Node node; *Node next) =
    node != null && [_]node |-> ?n &*& n.next |-> next &*& stack_node(next, _);

predicate stack_node_null() = true;

predicate stack_nodes(*Node node) =
    switch node { null => stack_node_null(), _ => stack_node(node, _) };

predicate stack(*Stack s; *Node head) =
    s != null &*& [_]s |-> ?st &*& st.head |-> head;

pure fn count_nodes(*Node node) -> i32 {
    switch node { null => 0, _ => 1 + count_nodes(unsafe { (*node).next }) }
}

pure fn count_from_to(*Node start, *Node end) -> i32 {
    if start == end { 0 } else {
        switch start { null => 0, _ => 1 + count_from_to(unsafe { (*start).next }, end) }
    }
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    requires stack(stack, ?head) &*& stack_nodes(head),
    ensures stack(stack, head) &*& stack_nodes(head) &*& result == count_nodes(head);
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop_invariant stack(stack, ?s_head) &*& stack_nodes(n) &*& i == count_from_to(s_head, n);
    while !n.is_null() {
        n = (*n).next;
        i += 1;
    }

    i
}