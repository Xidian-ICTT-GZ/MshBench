//@ pred nodes(*mut Node; int) = true;

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ req stack as S |-> ?head &*& nodes(head, _);
//@ ens stack as S |-> head &*& nodes(head, _);
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open nodes(?n, _);
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        if n.is_null() {
            break;
        }
        //@ open nodes(n, _);
        n = (*n).next;
        i += 1;
        //@ close nodes(n, _);
    }
    //@ close nodes(n, _);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}