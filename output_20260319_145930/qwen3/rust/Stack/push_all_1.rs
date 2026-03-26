/*@ pred node(n: *mut Node, v: i32, next: *mut Node) = 
  n != 0 &*& struct_Node_padding(n) &*& (*n).val |-> v &*& (*n).next |-> next;
@*/

/*@ pred nodes(n: *mut Node, vs: list<i32>) =
  match vs {
    nil => n == 0,
    cons(v, rest) => node(n, v, ?n1) &*& nodes(n1, rest)
  };
@*/

/*@ pred stack(s: *mut Stack, vs: list<i32>) =
  s != 0 &*& struct_Stack_padding(s) &*& (*s).head |-> ?h &*& nodes(h, vs);
@*/

impl Stack {
//@ req stack(stack, ?vs1) &*& stack(other, ?vs2);
//@ ens stack(stack, append(vs2, vs1));
unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
    //@ open stack(other, vs2);
    let head0 = (*other).head;
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open nodes(head0, vs2);
        loop {
            //@ inv n != 0 &*& nodes(n, ?tail_vs) &*& tail_vs != nil &*& stack(stack, vs1);
            if (*n).next.is_null() {
                break;
            }
            n = (*n).next;
        }
        //@ open nodes(n, cons(?v_last, nil));
        (*n).next = (*stack).head;
        (*stack).head = head0;
        //@ close nodes(n, cons(v_last, vs1));
        //@ close stack(stack, append(vs2, vs1));
    } else {
        //@ close stack(stack, append(vs2, vs1));
    }
}
}