//@ predicate node_pred(Node* n;) = 
//@     n != 0 ? field<n, i32>("value") &*& field<n, Node*>("next") &*& node_pred(*(Node**)&field<n, Node*>("next")) : true;
//
//@ predicate stack_pred(Stack* s;) = 
//@     s != 0 ? field<s, Node*>("head") &*& node_pred(*(Node**)&field<s, Node*>("head")) : true;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires node == core::ptr::null_mut() || node_pred(node as _);
//@ ensures true;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open node_pred(node as _);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close node_pred(node as _);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack_pred(stack as _);
    //@ ensures true;
    {
        //@ open stack_pred(stack as _);
        let result = get_nodes_sum((*stack).head);
        //@ close stack_pred(stack as _);
        result
    }
}