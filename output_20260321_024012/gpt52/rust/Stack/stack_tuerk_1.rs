unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack::stack(stack, _);
//@ ens stack::stack(stack, _);

{

//@ open stack::stack(stack, ?xs);
let mut n = (*stack).head;
//@ let n0 = n;
//@ if !n.is_null() { open stack::nodes(n, xs); }
let mut i = 0;
//@ let ys = xs;
//@ let k = 0;
//@ close stack::iter_state(n, ys, k);
loop 
//@ inv stack::iter_state(n, ys, k) &*& i == k;
{

//@ open stack::iter_state(n, ys, k);
if n.is_null() {
//@ close stack::iter_state(n, ys, k);
break;
}
//@ open stack::nodes(n, ys);
n = (*n).next;
i += 1;
//@ close stack::iter_state(n, tail(ys), k + 1);

}

//@ open stack::iter_state(n, ys, k);
//@ assert ys == nil;
//@ close stack::nodes(n0, xs);
//@ close stack::stack(stack, xs);
i
}