struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list: *mut Node) =
    list == std::ptr::null_mut() ?
        true
    :
        alloc_block(list as *u8, std::mem::size_of::<Node>()) &*&
        (*list).next |-> ?nxt &*&
        nodes(nxt);

pred stack(stack: *mut Stack) =
    alloc_block(stack as *u8, std::mem::size_of::<Stack>()) &*&
    (*stack).head |-> ?h &*&
    nodes(h);

@*/

//@ req stack(stack);
//@ ens stack(stack);
unsafe fn stack_get_count(stack: *mut Stack) -> i32

{

//@ open stack(stack);
let mut n = (*stack).head;
let mut i = 0;
//@ close stack(stack);
loop {

    //@ inv stack(stack) &*& nodes(n);

    if n.is_null() {

        break;
    }
    //@ open nodes(n);
    n = (*n).next;
    //@ close nodes(n);
    i += 1;

}

i
}