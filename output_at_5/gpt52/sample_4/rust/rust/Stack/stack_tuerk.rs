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

@*/

struct Stack {
    head: *mut Node,
}

/*@

pred stack(s: *mut Stack; count: i32) =
    struct_Stack_head(s, ?head) &*& nodes(head, count);

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack(stack, ?c);
//@ ens stack(stack, c) &*& result == c;
{
    //@ open stack(stack, c);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close nodes(n, c);
    loop
    //@ inv nodes(n, ?k) &*& i + k == c;
    {
        if n.is_null() {
            //@ open nodes(n, k);
            break;
        }
        //@ open nodes(n, k);
        //@ open node(n, ?next, ?value);
        n = (*n).next;
        //@ close node(n, next, value);
        i += 1;
        //@ close nodes(n, k - 1);
    }
    //@ close stack(stack, c);
    i
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}