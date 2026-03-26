struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred Nodes(n: *mut Node, count: i32) =
    if n == 0 {
        count == 0
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& Nodes(next, ?c) &*& count == c + 1 &*& count > 0
    };
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred Stack(stack: *mut Stack, count: i32) =
    (*stack).head |-> ?head &*& Nodes(head, count) &*& count >= 0;
@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack(stack, ?count);
//@ ens Stack(stack, count) &*& result == count;
{
    //@ open Stack(stack, count);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open Nodes(n, count);
    loop {
        //@ inv Nodes(n, ?remaining) &*& i + remaining == count &*& i >= 0;
        
        if n.is_null() {
            //@ close Nodes(n, remaining);
            break;
        }
        let next = (*n).next;
        //@ open Nodes(next, ?r2);
        n = next;
        i += 1;
        //@ close Nodes(next, r2);
    }
    //@ close Stack(stack, count);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}