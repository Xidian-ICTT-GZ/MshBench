predicate_node(struct Node* n; int sum) = n != 0 &*& pointer(n) &*& n->value |-> ?v &*& n->next |-> ?nx &*& (nx == 0 ? true : predicate_node(nx, ?s)) &*& sum == (v + (nx == 0 ? 0 : s));

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    #[requires(nodes == 0 ? true : predicate_node(nodes, ?sum))]
    #[ensures(result == (nodes == 0 ? 0 : sum) &*& (nodes == 0 ? true : predicate_node(nodes, sum)))]
{
    let mut result = 0;
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    result
}

predicate_stack(struct Stack* s; int sum) = 
    s != 0 &*& pointer(s) &*& s->head |-> ?h &*& predicate_node(h, sum);

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(predicate_stack(stack, ?sum))]
        #[ensures(result == sum &*& predicate_stack(stack, sum))]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
}