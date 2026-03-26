// verifast_options{}

struct Stack {
    head: *mut Node,
}

struct Node {
    next: *mut Node,
    data: i32,
}

/*@
predicate nodes(n: *mut Node) =
    n.is_null() ?
        emp
    :
        struct_Node_padding(n) &*& (*n).next |-> ?next &*& (*n).data |-> _ &*& nodes(next);

predicate stack(s: *mut Stack) =
    struct_Stack_padding(s) &*& (*s).head |-> ?head &*& nodes(head);
@*/

impl Stack {
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ req ptr::nonnull(stack) &*& stack(stack) &*& ptr::nonnull(other) &*& stack(other);
//@ ens ptr::nonnull(stack) &*& stack(stack);
{
    //@ open stack(other);
    let head0 = (*other).head;
    //@ close stack(other);
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open nodes(n);
        loop {
            //@ invariant nodes(n);
            //@ open nodes(n);
            if (*n).next.is_null() {
                //@ close nodes(n);
                break;
            }
            n = (*n).next;
            //@ close nodes(n);
        }
        //@ open nodes(n);
        (*n).next = (*stack).head;
        //@ close nodes(n);
        //@ close nodes(head0);
        //@ open stack(stack);
        (*stack).head = head0;
        //@ close stack(stack);
    } else {
        //@ open stack(stack);
        //@ close stack(stack);
    }
}
}