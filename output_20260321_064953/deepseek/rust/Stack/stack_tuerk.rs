// verifast_options{}

struct Node {
    next: *mut Node,
    value: i32,
}

pred_ctor Node_own(n: *mut Node) {
    |-> n : Node @ {
        next: *mut Node,
        value: i32,
    }
}

struct Stack {
    head: *mut Node,
}

pred_ctor Stack_own(s: *mut Stack) {
    |-> s : Stack @ {
        head: *mut Node,
    }
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack_own(stack) &*& (*stack).head |-> ?head;
//@ ens Stack_own(stack) &*& (*stack).head |-> head;
{
    //@ open Stack_own(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close exists(0);
    loop {
        //@ inv n |-> ?cur &*& i |-> ?count &*& exists(count);
        //@ open exists(count);
        if n.is_null() {
            //@ close exists(count);
            break;
        }
        //@ open Node_own(n);
        n = (*n).next;
        i += 1;
        //@ close exists(count + 1);
    }
    //@ close Stack_own(stack);
    i
}
    fn main() {
        println!("stack_tuerk.rs compiles successfully!");
}