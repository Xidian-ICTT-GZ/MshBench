predicate nodes(struct Node* n; int sum) =
    n == NULL ?
        emp &*& sum == 0
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_Node(n) &*&
        nodes(next, ?rest_sum) &*& sum == v + rest_sum;

unsafe fn get_nodes_sum(nodes: *mut Node) 
    #[requires nodes == NULL ? emp : nodes(nodes, ?sum)]
    #[ensures nodes == NULL ? emp : nodes(nodes, sum) &*& result == sum]
    -> i32
{
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack)
        #[requires stack->head |-> ?h &*& nodes(h, ?sum) &*& malloc_block_Stack(stack)]
        #[ensures stack->head |-> h &*& nodes(h, sum) &*& malloc_block_Stack(stack) &*& result == sum]
        -> i32
    {

        let result = get_nodes_sum((*stack).head);

        result
    }
}