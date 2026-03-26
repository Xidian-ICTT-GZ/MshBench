struct Node {
    next: *mut Node,
    value: i32,
}

/*@

pred node(node: *mut Node; next: *mut Node) =
    node->next |-> next &*& node->value |-> _;

pred nodes(n: *mut Node) =
    n == 0 ?
        true
    :
        node(n, ?next) &*& nodes(next);

pred stack(s: *mut Stack) =
    s->head |-> ?h &*& nodes(h);

@*/

struct Stack {
    head: *mut Node,
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack(stack);
//@ ens stack(stack) &*& result >= 0;
{
    //@ open stack(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close nodes(n);
    loop {
        //@ inv nodes(n) &*& i >= 0;
        if n.is_null() {
            //@ open nodes(n);
            break;
        }
        //@ open nodes(n);
        n = (*n).next;
        //@ close nodes(n);
        i += 1;
    }
    //@ close stack(stack);
    i
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}