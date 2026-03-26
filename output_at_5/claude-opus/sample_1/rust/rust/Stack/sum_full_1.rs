/*@ 
predicate node_pred(Node* n;) = n->value |-> ?v &*& n->next |-> ?nx &*& (nx == null ? true : node_pred(nx));
predicate stack_pred(Stack* s;) = s->head |-> ?h &*& (h == null ? true : node_pred(h));
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires (node == core::ptr::null_mut() ? true : node_pred(node));
//@ ensures  true;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open node_pred(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close node_pred(node);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack_pred(stack);
    //@ ensures true;
    {
        //@ open stack_pred(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack_pred(stack);
        result
    }
}