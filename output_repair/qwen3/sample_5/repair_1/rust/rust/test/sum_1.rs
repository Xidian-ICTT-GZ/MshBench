#[predicate]
fn node_pred(n: *mut Node, value: i32, next: *mut Node) -> bool {
    (*n).value |-> value &*& (*n).next |-> next
}

#[predicate]
fn stack_pred(s: *mut Stack, head: *mut Node) -> bool {
    (*s).head |-> head
}

#[predicate]
fn nodes_sum(nodes: *mut Node, sum: i32) -> bool {
    if nodes.is_null() {
        sum == 0
    } else {
        exists::<i32>(|v| exists::<*mut Node>(|next|
            node_pred(nodes, v, next) &*& nodes_sum(next, sum - v)
        ))
    }
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires nodes_sum(nodes, ?sum);
    ensures nodes_sum(nodes, sum) &*& result == sum;
{
    let mut result = 0;

    if !nodes.is_null() {
        let v = (*nodes).value;
        let next = (*nodes).next;
        close node_pred(nodes, v, next)();
        assert nodes_sum(nodes, ?s);
        open nodes_sum(nodes, s)();
        result = get_nodes_sum(next);
        result += v;
        close nodes_sum(nodes, result)();
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_pred(stack, ?head) &*& nodes_sum(head, ?sum);
        ensures stack_pred(stack, head) &*& nodes_sum(head, sum) &*& result == sum;
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}