struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes(struct Node* n, int count) =
    n == 0 ?
        count == 0
    :
        (*n).next |-> ?next &*& nodes(next, ?c) &*& count == c + 1;

predicate stack(struct Stack* s, int count) =
    (*s).head |-> ?h &*& nodes(h, count);

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack(stack, ?count);
//@ ensures stack(stack, count) &*& result == count;
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        /*@
        invariant nodes(n, ?k) &*& i + k == count;
        @*/

        if n.is_null() {
            break;
        }
        //@ open nodes(n, k);
        n = (*n).next;
        i += 1;
        //@ close nodes(n, k - 1);
    }
    //@ assert nodes(n, ?k2) &*& i + k2 == count;
    //@ assert n == 0;
    //@ open nodes(n, k2);
    //@ close stack(stack, count);
    i
}