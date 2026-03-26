struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(struct Node *n) = n->next |-> ?next &*& n->value |-> ?v;
//@ pred stack(struct Stack *s) = s->head |-> ?h &*& nodes(h);

//@ pred nodes(struct Node *n) = n == 0 ? true : node(n) &*& nodes((*n).next);

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack(stack);
//@ ensures stack(stack);
//@ ensures result >= 0;
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop 
    //@ invariant stack(stack) &*& nodes(n) &*& i >= 0;
    {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}