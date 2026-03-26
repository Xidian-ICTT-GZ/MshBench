predicate node(struct Node* n) = n != 0 &*& n->next |-> ?next &*& node(next);
predicate nodes(struct Node* n) = n == 0 ? true : node(n);

predicate stack(struct Stack* s; struct Node* head) =
    s->head |-> head &*& nodes(head);

predicate node(struct Node* n) = n != 0 &*& n->next |-> ?next &*& nodes(next);

predicate nodes(struct Node* n) =
    n == 0 ? true : (node(n));

#[requires(stack(s, ?sh) &*& stack(other, ?oh))]
#[ensures(stack(s, oh + sh) &*& stack(other, 0))]
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    where
        stack: struct Stack*,
        other: struct Stack*
{
    let head0 = (*other).head;
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        #[invariant nodes(n)]
        loop {
            if (*n).next.is_null() {
                break;
            }
            n = (*n).next;
        }

        (*n).next = (*stack).head;
        (*stack).head = head0;
    }
}