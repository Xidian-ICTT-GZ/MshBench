struct Node {
    next: *mut Node,
    value: i32,
}

/*@

pred node_raw(n: *mut Node; next: *mut Node, value: i32) =
    std::alloc::alloc_block(n as *u8, std::mem::size_of::<Node>()) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

pred nodes(n: *mut Node;) =
    n == std::ptr::null_mut() ?
        true
    :
        node_raw(n, ?next, ?value) &*& nodes(next);

pred stack_raw(s: *mut Stack; head: *mut Node) =
    std::alloc::alloc_block(s as *u8, std::mem::size_of::<Stack>()) &*&
    (*s).head |-> head;

pred stack(s: *mut Stack;) =
    stack_raw(s, ?head) &*& nodes(head);

@*/

struct Stack {
    head: *mut Node,
}

//@ req stack(stack);
//@ ens stack(stack);
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open stack(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close stack_raw(stack, n);
    loop {
        //@ inv stack_raw(stack, n) &*& nodes(n);

        if n.is_null() {
            break;
        }
        //@ open nodes(n);
        //@ open node_raw(n, ?next, ?value);
        n = (*n).next;
        //@ close node_raw(_ as *mut Node, next, value);
        //@ close nodes(next);
        i += 1;
    }
    //@ open stack_raw(stack, n);
    //@ close stack_raw(stack, n);
    //@ close stack(stack);
    i
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}