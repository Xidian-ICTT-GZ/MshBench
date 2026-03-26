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
    if n.is_null() {
        emp
    } else {
        struct_Node_padding(n) &*& (*n).next |-> ?next &*& (*n).data |-> _ &*& nodes(next)
    };

predicate own_stack(s: *mut Stack) =
    struct_Stack_padding(s) &*& (*s).head |-> ?head &*& nodes(head);
@*/

impl Stack {
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ req ptr::nonnull(stack) &*& own_stack(stack) &*& ptr::nonnull(other) &*& own_stack(other);
//@ ens ptr::nonnull(stack) &*& own_stack(stack);
{
    //@ open own_stack(other);
    let head0 = (*other).head;
    //@ close own_stack(other);
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open nodes(n);
        loop {
            //@ open nodes(n);
            if (*n).next.is_null() {
                //@ close nodes(n);
                break;
            }
            n = (*n).next;
            //@ close nodes(n);
        }
        //@ open nodes(n);
        //@ open own_stack(stack);
        (*n).next = (*stack).head;
        //@ close nodes(n);
        //@ close nodes(head0);
        (*stack).head = head0;
        //@ close own_stack(stack);
    } else {
        //@ open own_stack(stack);
        //@ close own_stack(stack);
    }
}
}