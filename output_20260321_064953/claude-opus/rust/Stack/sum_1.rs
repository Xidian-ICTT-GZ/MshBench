unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == 0 || pointer(nodes, _) &*& malloc_block_node(nodes);
//@ ens true;
{
  let mut result = 0;
  if !nodes.is_null() {
    //@ open pointer(nodes, _);
    result = get_nodes_sum((*nodes).next);
    //@ open pointer((*nodes).next, _);
    //@ open pointer(&(*nodes).value, _);
    result += (*nodes).value;
    //@ close pointer(nodes, _);
  }
  result
}

impl Stack {
  unsafe fn get_sum(stack: *mut Stack) -> i32
  //@ req stack == 0 || pointer(stack, _) &*& malloc_block_stack(stack);
  //@ ens true;
  {
    let result = get_nodes_sum((*stack).head);
    result
  }
}