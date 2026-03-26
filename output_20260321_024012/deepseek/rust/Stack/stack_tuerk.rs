// verifast_options{}

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req true;
//@ ens true;
{
    //@ open Stack?(_);
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        //@ open Node?(_);
        if n.is_null() {
            //@ close Node?(_);
            break;
        }
        n = (*n).next;
        i += 1;
        //@ close Node?(_);
    }
    //@ close Stack?(_);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}