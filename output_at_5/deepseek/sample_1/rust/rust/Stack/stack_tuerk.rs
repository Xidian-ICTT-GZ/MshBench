// verifast_options{}

struct Node {
    next: *mut Node,
    value: i32,
}

pred_ctor Node_own(n: *mut Node) {
    |-> true;
}

struct Stack {
    head: *mut Node,
}

pred_ctor Stack_own(s: *mut Stack) {
    |-> true;
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack_own(stack)();
//@ ens Stack_own(stack)() &*& result >= 0;
{
    //@ open Stack_own(stack)();
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        //@ open Node_own(n)();
        if n.is_null() {
            //@ close Node_own(n)();
            break;
        }
        n = (*n).next;
        i += 1;
        //@ close Node_own(n)();
    }
    //@ close Stack_own(stack)();
    i
}
    fn main() {
        println!("stack_tuerk.rs compiles successfully!");
}