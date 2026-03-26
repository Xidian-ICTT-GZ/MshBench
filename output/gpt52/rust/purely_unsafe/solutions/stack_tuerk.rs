struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node_own(node: *mut Node; next: *mut Node, value: i32) =
    node->next |-> next &*& node->value |-> value;

predicate nodes(n: *mut Node; count: i32) =
    n == 0 ?
        count == 0
    :
        node_own(n, ?next, ?v) &*& nodes(next, ?c) &*& count == c + 1;

predicate stack_own(stack: *mut Stack; count: i32) =
    stack->head |-> ?h &*& nodes(h, count);

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    //@ requires stack_own(stack, ?count);
    //@ ensures stack_own(stack, count) &*& result == count;
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        //@ invariant stack->head |-> ?h &*& nodes(h, count) &*& nodes(n, ?rem) &*& 0 <= i &*& i + rem == count;
        if n.is_null() {
            //@ assert rem == 0;
            break;
        }
        //@ open nodes(n, rem);
        n = (*n).next;
        i += 1;
        //@ close nodes(n, rem - 1);
    }

    i
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}