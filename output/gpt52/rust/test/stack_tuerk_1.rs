struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes(struct Node *n; int count) =
    n == 0 ?
        count == 0
    :
        struct_Node_next(n, ?next) &*& nodes(next, ?c) &*& count == c + 1;

predicate stack(struct Stack *s; int count) =
    struct_Stack_head(s, ?h) &*& nodes(h, count);

@*/

#[requires(stack(stack, ?count))]
#[ensures(stack(stack, count) &*& result == count)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    /*@
    open stack(stack, count);
    @*/
    loop {
        /*@
        invariant nodes(n, ?k) &*& i + k == count;
        @*/
        if n.is_null() {
            /*@
            open nodes(n, k);
            @*/
            break;
        }
        /*@
        open nodes(n, k);
        @*/
        n = (*n).next;
        i += 1;
        /*@
        close nodes(n, k - 1);
        @*/
    }

    /*@
    close stack(stack, count);
    @*/
    i
}