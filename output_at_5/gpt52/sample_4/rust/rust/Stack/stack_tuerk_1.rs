struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node_chain(n: *mut Node) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& node_chain(next);

pred stackp(s: *mut Stack) =
    s->head |-> ?h &*& node_chain(h);

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack != 0 &*& stackp(stack);
//@ ens stackp(stack);
{

//@ open stackp(stack);
let mut n = (*stack).head;
//@ close stackp(stack);
let mut i = 0;
loop {
//@ inv stackp(stack) &*& node_chain(n);

if n.is_null() {

break;
}
//@ open node_chain(n);
n = (*n).next;
//@ close node_chain(n);
i += 1;

}

i
}