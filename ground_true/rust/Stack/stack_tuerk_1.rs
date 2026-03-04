unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack(stack, ?count);
//@ ens Stack(stack, count) &*& result == count;
{
//@ open Stack(stack, count);
let mut n = (*stack).head;
let mut i = 0;
loop {
/*@
req Nodes(n, ?count1);
ens Nodes(old_n, count1) &*& i == old_i + count1;
@*/
//@ open Nodes(n, count1);
if n.is_null() {
//@ close Nodes(n, count1);
break;
}
n = (*n).next;
i += 1;
//@ recursive_call();
//@ close Nodes(old_n, count1);
}
//@ close Stack(stack, count);
i
}