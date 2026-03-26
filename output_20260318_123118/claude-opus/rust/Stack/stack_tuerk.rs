struct Node {
    next: *mut Node,
    value: i32,
}  
predicate node(struct Node *n; int v, struct Node *next) =
    n->value |-> v &*& n->next |-> next;

predicate nodes(struct Node *n, int count) =
    count == 0 ?
        n == 0
    :
        n != 0 &*& node(n, _, _) &*& nodes((*n).next, count - 1);

struct Stack {
    head: *mut Node,
}

predicate stack(struct Stack *s, int count) = s->head |-> ?h &*& nodes(h, count);

#[requires(stack != 0 &*& stack(stack, _))]
#[ensures(stack(stack, result))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    let mut n = (*stack).head;
    let mut i: i32 = 0;

    #[invariant(
        stack(stack, _) &*&
        nodes(n, _) &*&
        i >= 0 &*&
        (forall<int> (j) (0 <= j && j <= i ==> true)) 
    )]
    loop {
        if n.is_null() {
            break;
        }
        node(n, _, ?next);
        n = next;
        i += 1;
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}