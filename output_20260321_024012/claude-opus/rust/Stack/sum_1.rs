unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == 0 || nodes |-> _;
//@ ensures true;
{
  let mut result = 0;

  if !nodes.is_null() {
    //@ open nodes |-> _;
    result = get_nodes_sum((*nodes).next);
    result += (*nodes).value;
    //@ close nodes |-> _;
  }

  result
}
impl Stack {
  unsafe fn get_sum(stack: *mut Stack) -> i32
  //@ req stack |-> _;
  //@ ensures true;
  {
    let result = get_nodes_sum((*stack).head);
    result
  }
}