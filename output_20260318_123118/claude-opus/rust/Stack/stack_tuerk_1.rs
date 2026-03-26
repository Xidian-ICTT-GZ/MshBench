predicate node(struct Node* n) = n->next |-> ?next &*& n->count |-> _ &*& malloc_block_Node(n);
predicate stack(struct Stack* s; int count) = s->head |-> ?h &*& nodes(h, count);

predicate nodes(struct Node* n, int count) =
    count == 0 ? n == 0 :
    node(n) &*& nodes(n->next, count - 1);

#[requires(stack(s, ?c))]
#[ensures(stack(s, c) &*& result == c)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(nodes(n, c - i) &*& 0 <= i &*& i <= c)]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}