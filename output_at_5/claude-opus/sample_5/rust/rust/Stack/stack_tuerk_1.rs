unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack != std::ptr::null_mut();
//@ requires stack->head |-> ?head &*& nodes(head, ?count);
//@ ensures stack->head |-> head &*& nodes(head, count);
//@ ensures result == count;
{
  let mut n = (*stack).head;
  let mut i = 0;
  //@ open nodes(n, ?c);
  loop {
    if n.is_null() {
      //@ close nodes(n, 0);
      break;
    }
    //@ open node(n, ?next);
    n = (*n).next;
    i += 1;
    //@ open nodes(n, ?c2);
  }
  i
}

//@ predicate nodes(*Node n, int count) = 
//@     n == std::ptr::null_mut() ? count == 0 : node(n, ?next) &*& nodes(next, count - 1);
//@ predicate node(*Node n, *Node next) = n->next |-> next;