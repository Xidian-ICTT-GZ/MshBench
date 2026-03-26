/*@
pred Node(next: *mut Node, value: i32) =
    alloc_block(next, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(next) &*&
    (*next).next |-> ?next_next &*&
    (*next).value |-> value;
@*/

/*@
pred lseg(start: *mut Node, end: *mut Node; count: int) =
    start == end ?
        count == 0
    :
        Node(start, ?val) &*&
        lseg((*start).next, end, ?c) &*&
        count == c + 1;
@*/

/*@
pred Stack(head: *mut Stack) =
    alloc_block(head, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(head) &*&
    (*head).head |-> ?h &*&
    lseg(h, 0 as *mut Node, ?count);
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack(stack);
//@ ens Stack(stack) &*& result >= 0;
{
    //@ open Stack(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close lseg(n, n, 0);
    loop {
        //@ inv lseg(n, 0 as *mut Node, ?rem) &*& i >= 0 &*& i + rem == count;
        
        if n.is_null() {
            //@ open lseg(0 as *mut Node, 0 as *mut Node, _);
            break;
        }
        //@ open lseg(n, 0 as *mut Node, _);
        //@ open Node(n, _);
        n = (*n).next;
        i += 1;
        //@ close lseg(n, n, 0);
        
    }
    //@ close lseg(0 as *mut Node, 0 as *mut Node, 0);
    //@ close Stack(stack);
    i
}
    fn main() {
        println!("stack_tuerk.rs compiles successfully!");
}