/*@
pred Node(next: *mut Node, value: i32) = 
    alloc_block(next, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(next) &*&
    (*next).next |-> ?next_next &*&
    (*next).value |-> value &*&
    next_next is *mut Node;
@*/

/*@
pred lseg(first: *mut Node, last: *mut Node) =
    first == last ?
        true
    :
        Node(first, ?val) &*&
        (*first).next |-> ?next &*&
        lseg(next, last);
@*/

/*@
pred Stack(head: *mut Stack) =
    alloc_block(head, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(head) &*&
    (*head).head |-> ?h &*&
    h is *mut Node &*&
    lseg(h, std::ptr::null_mut());
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ req Stack(stack);
//@ ens Stack(stack) &*& result >= 0;
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open Stack(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close lseg(n, std::ptr::null_mut());
    //@ open lseg(n, std::ptr::null_mut());
    loop {
        if n.is_null() {
            //@ close lseg(std::ptr::null_mut(), std::ptr::null_mut());
            break;
        }
        //@ open Node(n, _);
        n = (*n).next;
        i += 1;
        //@ close lseg(n, std::ptr::null_mut());
        //@ open lseg(n, std::ptr::null_mut());
    }
    //@ close lseg(std::ptr::null_mut(), std::ptr::null_mut());
    //@ close Stack(stack);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}