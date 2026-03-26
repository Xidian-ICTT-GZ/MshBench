struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node_chain(n: *mut Node) =
    n == 0 ?
        true
    :
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& node_chain(next);

pred stack(stack: *mut Stack) =
    (*stack).head |-> ?h &*& node_chain(h);
@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack(stack);
//@ ens stack(stack);
{
    //@ open stack(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close node_chain(n);
    loop {
        //@ inv node_chain(n) &*& (*stack).head |-> ?h0;
        //@ open node_chain(n);

        if n.is_null() {
            //@ close node_chain(n);
            break;
        }
        //@ assert (*n).next |-> ?next;
        n = (*n).next;
        i += 1;
        //@ close node_chain(n);
    }
    //@ close stack(stack);
    i
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}