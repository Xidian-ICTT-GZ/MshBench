unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack != std::ptr::null_mut();
//@ requires chars(stack, _);
//@ ensures chars(stack, _);
//@ ensures result >= 0;
{
  let mut n = (*stack).head;
  let mut i = 0;
  loop {
    //@ if n.is_null() { } else { /* open_node(n); */ }
    if n.is_null() {
      break;
    }
    n = (*n).next;
    i += 1;
  }
  i
}