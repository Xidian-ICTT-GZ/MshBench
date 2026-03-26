struct Node {
    next: *mut Node,
    value: i32,
}

/*@

pred node(n: *mut Node; next: *mut Node, value: i32) =
    struct_Node_next(n, next) &*& struct_Node_value(n, value);

pred nodes(n: *mut Node; count: i32) =
    n == 0 ?
        count == 0
    :
        count > 0 &*& node(n, ?next, ?value) &*& nodes(next, count - 1);

pred stack(s: *mut Stack; count: i32) =
    struct_Stack_head(s, ?head) &*& nodes(head, count);

@*/

struct Stack {
    head: *mut Node,
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req true;
//@ ens true;
{
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