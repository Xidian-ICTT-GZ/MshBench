struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred Nodes(n: *mut Node, count: i32) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        count > 0 &*&
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, count - 1)
    };
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred Stack(stack: *mut Stack, count: i32) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, count) &*&
    count >= 0;
@*/

//@ req Stack(stack, ?count);
//@ ens Stack(stack, count) &*& result == count;
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open Stack(stack, count);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open Nodes(n, count);
    loop {
        //@ inv Nodes(n, count - i) &*& i >= 0 &*& i <= count;
        
        if n.is_null() {
            //@ close Nodes(n, count - i);
            break;
        }
        let next = (*n).next;
        //@ open Nodes(next, count - i - 1);
        n = next;
        i += 1;
        //@ close Nodes(n, count - i);
    }
    //@ close Stack(stack, count);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}