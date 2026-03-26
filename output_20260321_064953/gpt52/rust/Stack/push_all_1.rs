impl Stack {
//@ req stack != 0 &*& other != 0;
/*@ ens true; @*/
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)

{

let head0 = (*other).head;
dealloc(other as *mut u8, Layout::new::<Stack>());
let mut n = head0;

if !n.is_null() {

loop {
//@ inv true;

if (*n).next.is_null() {
break;
}
n = (*n).next;

}

(*n).next = (*stack).head;

(*stack).head = head0;
}

}
}