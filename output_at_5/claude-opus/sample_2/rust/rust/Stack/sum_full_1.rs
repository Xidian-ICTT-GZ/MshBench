/*@ 
predicate node_pred(void* n;) =
    n != 0 ?
        (field<n, i32>("value") &*&
         field<n, void*>("next") &*& node_pred(*(void**)&field<n, void*>("next"))) 
    : true;

predicate stack_pred(void* s;) =
    s != 0 ?
        (field<s, void*>("head") &*& node_pred(*(void**)&field<s, void*>("head")))
    : true;
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires (node == core::ptr::null_mut() ? true : node_pred(node as _));
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