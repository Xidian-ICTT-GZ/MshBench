predicate node(struct Node* node; int sum) =
  node != 0 &*& 
  node->value |-> ?v &*&
  node->next |-> ?next &*&
  (next == 0 ? sum == v : node(next, ?tail_sum) &*& sum == v + tail_sum);

unsafe fn get_nodes_sum(node: *mut Node) -> i32
  #[requires node == 0 ? true : node(node, ?s)]
  #[ensures node == 0 ? result == 0 : result == s &*& node(node, s)]
{
  let mut result = 0;
  if !node.is_null() {
    let tail_sum = get_nodes_sum((*node).next);
    //@ open node(node, ?_sum);
    //@ close node(node, (*node).value + tail_sum);
    result = (*node).value + tail_sum;
  }
  result
}

predicate stack(struct Stack* stack; int sum) =
  stack != 0 &*&
  stack->head |-> ?head &*&
  (head == 0 ? sum == 0 : node(head, ?head_sum) &*& sum == head_sum);

impl Stack {
  unsafe fn get_sum(stack: *mut Stack) -> i32
    #[requires stack != 0 &*& stack(stack, ?s)]
    #[ensures stack(stack, s) &*& result == s]
  {
    let result = get_nodes_sum((*stack).head);
    result
  }
}