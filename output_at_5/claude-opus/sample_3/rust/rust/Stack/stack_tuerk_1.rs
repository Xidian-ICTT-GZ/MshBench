unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack != std::ptr::null_mut();
//@ requires Stack_inv(stack);
//@ ensures Stack_inv(stack);
//@ ensures result >= 0;
{
  let mut n = (*stack).head;
  let mut i = 0;
  //@ open Stack_inv(stack);
  loop {
    if n.is_null() {
      break;
    }
    //@ open Node_inv(n);
    n = (*n).next;
    i += 1;
  }
  //@ close Stack_inv(stack);
  i
}

//@ predicate Stack_inv(Stack* stack) = stack->head |-> ?head &*& Node_chain(head);
//@ predicate Node_chain(Node* n) = n == std::ptr::null() ? true : Node_inv(n) &*& Node_chain((*n).next);
//@ predicate Node_inv(Node* n) = n->next |-> ?next &*& node_data(n); 
//@ fixpoint bool node_data(Node* n) { true; }  // Placeholder: adjust as needed