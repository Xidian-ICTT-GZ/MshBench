struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ ghost pred node_ptr(p: *mut Node) = p != null;
    //@ ghost pred stack_ptr(s: *mut Stack) = s != null && (*s).head != null;
    
    let mut n = (*stack).head;
    let mut i = 0;
    
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}