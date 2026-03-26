/*@ 
predicate nodes(struct Node *node) = 
    node == 0 ?
        true
    :
        alloc_node(node, _) &*& nodes((*node).next) &*& node->value |-> _ &*& node->next |-> _;

predicate stack(struct Stack *stack) = 
    stack->head |-> ?head &*& nodes(head);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node);
//@ ens nodes(node) &*& result >= 0;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node);
        let tail_sum = get_nodes_sum((*node).next);
        //@ open nodes((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes((*node).next);
        //@ close nodes(node);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }
}