unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == 0 || pointer(nodes, _) &*& nodes_inv(nodes);
//@ ens  pointer(nodes, _) &*& nodes_inv(nodes);
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
  //@ req pointer(stack, _) &*& stack_inv(stack);
  //@ ens  pointer(stack, _) &*& stack_inv(stack);
  {
    //@ open stack_inv(stack);
    let result = get_nodes_sum((*stack).head);
    //@ close stack_inv(stack);
    result
  }
}

//@ predicate nodes_inv(Node* node) = node != 0 && pointer(node, _) &*& nodes_inv((*node).next) || node == 0;
//@ predicate stack_inv(Stack* stack) = pointer(stack, _) &*& nodes_inv((*stack).head);