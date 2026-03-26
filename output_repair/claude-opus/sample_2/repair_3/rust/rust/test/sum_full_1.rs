predicate node_list(node: *mut Node, sum: i32) =
  node.is_null() ? sum == 0 : 
    exists n: i32, s: i32, next: *mut Node ::
      node->Node { value: n, next: next } &*& 
      node_list(next, s) &*&
      sum == n + s;

predicate stack_valid(stack: *mut Stack) =
  exists head: *mut Node, sum: i32 ::
    stack->Stack { head: head } &*&
    node_list(head, sum);

unsafe fn get_nodes_sum(node: *mut Node) -> i32
  requires node_list(node, ?sum)
  ensures node_list(node, sum) &*& result == sum
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
      requires stack_valid(stack)
      ensures stack_valid(stack)
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}