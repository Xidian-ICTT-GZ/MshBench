struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Node(n: *mut Node, count: i32) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        count > 0 &*&
        (*n).value |-> _ &*&
        (*n).next |-> ?next &*&
        Node(next, count - 1)
    };

pred Stack(s: *mut Stack, count: i32) =
    (*s).head |-> ?h &*&
    Node(h, count);

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack(stack, ?count) &*& count >= 0;
//@ ens Stack(stack, count) &*& result == count;
{
    //@ open Stack(stack, count);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ let mut remaining = count;
    loop
    //@ inv Node(n, remaining) &*& i + remaining == count &*& i >= 0 &*& remaining >= 0;
    {
        //@ open Node(n, remaining);
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;//@ remaining = remaining - 1;
    }
    //@ close Stack(stack, count);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}