unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == std::ptr::null_mut() || nodes_inv(nodes);
//@ ensures true;
{
    let mut result = 0;
    if !nodes.is_null() {
        //@ open nodes_inv(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes_inv(nodes);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack_inv(stack);
    //@ ensures true;
    {
        //@ open stack_inv(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack_inv(stack);
        result
    }
}

//@ predicate nodes_inv(Node* node) = 
//@     node != std::ptr::null_mut() &*& pointer<Node>(node) &*& integer((*node).value) &*& nodes_inv((*node).next) || 
//@     node == std::ptr::null_mut();

//@ predicate stack_inv(Stack* stack) = pointer<Stack>(stack) &*& nodes_inv((*stack).head);

//@ predicate pointer<T>(T* p) = p != std::ptr::null_mut();

//@ predicate integer(int v) = true;

// verifast_options{}
// Note: The predicates assume external definitions of 'Node' and 'Stack'.