//@ verifast_options{disable_ghost_warnings}

impl Stack {
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ req stack |-> ?s &*& [_]Stack_own(s) &*& other |-> ?o &*& [_]Stack_own(o);
//@ ens stack |-> ?s2 &*& [_]Stack_own(s2) &*& other |-> _ &*& struct_Stack_padding(other);
{
    let head0 = (*other).head;
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        loop {
            //@ open Nodes(?nodes);
            if (*n).next.is_null() {
                break;
            }
            n = (*n).next;
            //@ close Nodes(nodes);
        }
        //@ open Nodes(?nodes);
        (*n).next = (*stack).head;
        (*stack).head = head0;
        //@ close Nodes(nodes);
    }
}
}