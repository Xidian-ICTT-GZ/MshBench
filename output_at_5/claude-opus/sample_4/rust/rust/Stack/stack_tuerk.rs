struct Node {
    next: *mut Node,
    value: i32,
}

/*@
predicate node(Node* n) =
    n->next |-> ?next &*& n->value |-> _ &*& (next == null ? true : node(next));
@*/

struct Stack {
    head: *mut Node,
}

/*@
predicate stack(Stack* s) =
    s->head |-> ?head &*& (head == null ? true : node(head));
@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack(stack);
//@ ensures stack(stack);
{
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open stack(stack);
    loop {
        if n.is_null() {
            //@ close stack(stack);
            break;
        }
        //@ open node(n);
        n = (*n).next;
        i += 1;
    }
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}