unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack != 0 && is_stack(stack);
//@ ensures true;
{
  let mut n = (*stack).head;
  let mut i = 0;
  loop {
    //@ if n != 0 { open node(n); }
    if n.is_null() {
      //@ if n != 0 { close node(n); }
      break;
    }
    n = (*n).next;
    i += 1;
  }
  i
}