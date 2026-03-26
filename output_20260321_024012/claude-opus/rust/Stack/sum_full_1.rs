unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires node == 0 || malloc_block<Node>(node);
//@ ensures true;
{
  let mut result = 0;
  if !node.is_null() {
    //@ open malloc_block<Node>(node);
    let tail_sum = get_nodes_sum((*node).next);
    result = (*node).value + tail_sum;
    //@ close malloc_block<Node>(node);
  }
  result
}

impl Stack {
  unsafe fn get_sum(stack: *mut Stack) -> i32
  //@ requires malloc_block<Stack>(stack);
  //@ ensures true;
  {
    //@ open malloc_block<Stack>(stack);
    let result = get_nodes_sum((*stack).head);
    //@ close malloc_block<Stack>(stack);
    result
  }
}