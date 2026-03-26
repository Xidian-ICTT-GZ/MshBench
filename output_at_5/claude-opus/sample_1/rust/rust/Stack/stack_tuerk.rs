struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred node(struct Node *n;) =
    n->next |-> ?next &*& n->value |-> _; 
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred stack(struct Stack *s;) =
    s->head |-> ?head &*& (head == 0 ? true : node(head));
@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ requires stack(stack);
//@ ensures stack(stack);
{
    let mut n = (*stack).head;
    let mut i = 0;
    /*@ open stack(stack); @*/
    loop {
        //@ if (n != 0) { open node(n); }
        if n.is_null() {
            //@ close stack(stack);
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