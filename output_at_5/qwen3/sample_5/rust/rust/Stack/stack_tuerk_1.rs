unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack != null;
//@ requires exists(Stack* s; s == stack);
{

let mut n = (*stack).head;
let mut i = 0;
loop {
//@ invariant i >= 0 && (n == null || list_node_is_valid(n, i));
if n.is_null() {
break;
}
n = (*n).next;
i += 1;

}

i
}