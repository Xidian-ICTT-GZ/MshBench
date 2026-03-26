struct Node {
    next: *mut Node,
    value: i32,
}

/*@

predicate node(struct Node *n; struct Node *next, i32 value) =
    n->next |-> next &*& n->value |-> value;

predicate nodes(struct Node *n; int count) =
    n == 0 ?
        count == 0
    :
        node(n, ?next, ?value) &*& nodes(next, ?c) &*& count == c + 1;

predicate stack(struct Stack *s; int count) =
    s->head |-> ?h &*& nodes(h, count);

@*/

struct Stack {
    head: *mut Node,
}

#[requires(stack(stack, ?count))]
#[ensures(stack(stack, count) &*& result == count)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
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
            close nodes(n, k);
            @*/
            break;
        }
        /*@
        open nodes(n, k);
        open node(n, ?next, ?value);
        close node(n, next, value);
        close nodes(n, k);
        @*/
        n = (*n).next;
        i += 1;

        /*@
        open nodes(n, ?k2);
        close nodes(n, k2);
        @*/
    }
    /*@
    close stack(stack, count);
    @*/
    i
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}