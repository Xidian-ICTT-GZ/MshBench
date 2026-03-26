//@ verifast_options{disable_ghost_refs}

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(*Node n;);

//@ pred stack(Stack* s;);

unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open stack(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        if n.is_null() {
            break;
        }
        //@ open nodes(n);
        n = (*n).next;
        i += 1;
    }
    //@ close stack(stack);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}