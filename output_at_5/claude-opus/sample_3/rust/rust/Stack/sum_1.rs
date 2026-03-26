unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == std::ptr::null_mut() || nodes_inv(nodes);
//@ ens true;
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
  //@ ens true;
  {
    //@ open stack_inv(stack);
    let result = get_nodes_sum((*stack).head);
    //@ close stack_inv(stack);
    result
  }
}

//@ predicate nodes_inv(Node* node) = node != std::ptr::null_mut() &*& pointer(node) &*& nodes_inv((*node).next) &*& integer((*node).value) || node == std::ptr::null_mut();
//@ predicate stack_inv(Stack* stack) = pointer(stack) &*& nodes_inv((*stack).head);

//@ predicate pointer<T>(T* p) = p != 0 &*& true; // placeholder for valid pointer
//@ predicate integer(int v) = true; // placeholder for integral value representation