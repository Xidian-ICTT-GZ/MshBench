unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack != std::ptr::null_mut() &*& pointer(stack, _) &*& chars(stack as *const u8, _) &*& true;
//@ ens true;
{
  let mut n = (*stack).head;
  let mut i = 0;
  loop
  //@ inv 0 <= i &*& (n == std::ptr::null_mut() || pointer(n, _));
  {
    if n.is_null() {
      break;
    }
    n = (*n).next;
    i += 1;
  }
  i
}