unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack != 0;
//@ ens true;
{

let mut n = (*stack).head;
let mut i = 0;
loop {
//@ inv true;

if n.is_null() {

break;
}
n = (*n).next;
i += 1;

}

i
}