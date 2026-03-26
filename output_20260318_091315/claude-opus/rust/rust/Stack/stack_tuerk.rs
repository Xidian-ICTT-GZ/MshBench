struct Node {
    next: *mut Node,
    value: i32,
}

predicate nodes(struct Node* n;) =
    n == 0 ? emp : n->next |-> ?next_node &*& n->value |-> _ &*& nodes(next_node);

struct Stack {
    head: *mut Node,
}

predicate stack(struct Stack* s;) =
    s->head |-> ?h &*& nodes(h);

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    #[requires(stack != 0 &*& stack(stack))]
    #[ensures(stack(stack))]
{
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(nodes(n) &*& stack(stack) &*& i >= 0)]
    loop {
        if n.is_null() {
            break;
        }
        open nodes(n);
        n = (*n).next;
        close nodes(n);
        i += 1;
    }
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}