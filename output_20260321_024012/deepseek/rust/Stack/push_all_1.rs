// verifast_options{}

impl Stack {
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ req [?q]Stack(stack) &*& [?q2]Stack(other);
//@ ens [q]Stack(stack);
{
    //@ open Stack(other);
    let head0 = (*other).head;
    //@ close Stack(other);
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open nodes(n, _);
        loop {
            //@ open node(n);
            if (*n).next.is_null() {
                //@ close node(n);
                break;
            }
            n = (*n).next;
            //@ close node(prev);
            //@ open nodes(n, _);
        }
        //@ close nodes(n, _);
        //@ open Stack(stack);
        (*n).next = (*stack).head;
        (*stack).head = head0;
        //@ close Stack(stack);
    } else {
        //@ open Stack(stack);
        //@ close Stack(stack);
    }
}
}