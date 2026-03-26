#[predicate]
fn node_pred(n: *mut Node, value: i32, next: *mut Node) -> bool {
    (*n).value |-> value &*& (*n).next |-> next
}

#[predicate]
fn nodes_list(nodes: *mut Node) -> bool {
    if nodes.is_null() {
        true
    } else {
        exists(value: i32, next: *mut Node).
        node_pred(nodes, value, next) &*& nodes_list(next)
    }
}

#[predicate]
fn stack_pred(stack: *mut Stack, head: *mut Node) -> bool {
    (*stack).head |-> head &*& nodes_list(head)
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    #[requires(nodes_list(nodes))]
    #[ensures(nodes_list(nodes) &*& result == sum_nodes(nodes))]
    let mut result = 0;

    if !nodes.is_null() {
        let value = (*nodes).value;
        let next = (*nodes).next;
        close node_pred(nodes, value, next);
        close nodes_list(nodes);
        result = get_nodes_sum(next);
        open nodes_list(nodes);
        open node_pred(nodes, value, next);
        result += value;
    }

    result
}

#[lemma]
fn sum_nodes(nodes: *mut Node) -> i32
    requires nodes_list(nodes),
    ensures nodes_list(nodes);

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[requires(stack_pred(stack, ?head))]
        #[ensures(stack_pred(stack, head) &*& result == sum_nodes(head))]
        let head = (*stack).head;
        close nodes_list(head);
        let result = get_nodes_sum(head);
        open nodes_list(head);
        result
    }
}