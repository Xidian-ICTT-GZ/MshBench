unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == 0 || pointer(nodes, ?n) &*& nodes_inv(n);
//@ ens  pointer(nodes, ?n) &*& nodes_inv(n) &*& result == list_sum(n);
{
  let mut result = 0;
  if !nodes.is_null() {
    //@ open nodes_inv(?node);
    result = get_nodes_sum((*nodes).next);
    result += (*nodes).value;
    //@ close nodes_inv(node);
  }
  result
}

impl Stack {
  unsafe fn get_sum(stack: *mut Stack) -> i32
  //@ req pointer(stack, ?s) &*& stack_inv(s);
  //@ ens  pointer(stack, s) &*& stack_inv(s) &*& result == list_sum(s.head);
  {
    //@ open stack_inv(?st);
    let result = get_nodes_sum((*stack).head);
    //@ close stack_inv(st);
    result
  }
}

//@ predicate nodes_inv(Node node) = node != null && pointer(node, _) &*& nodes_inv(node.next);
//@ predicate stack_inv(Stack stack) = pointer(stack.head, _) &*& nodes_inv(stack.head);
//@ fixpoint int list_sum(Node node) { node == null ? 0 : node.value + list_sum(node.next) }