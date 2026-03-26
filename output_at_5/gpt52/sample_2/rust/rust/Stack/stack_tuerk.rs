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
//@ req stack(stack, ?count);
//@ ens stack(stack, count) &*& result == count;
{
    //@ open stack(stack, count);
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        //@ inv nodes(n, ?k) &*& i + k == count;
        if n.is_null() {
            //@ assert n == 0;
            //@ assert k == 0;
            //@ close nodes(0, 0);
            break;
        }
        //@ open nodes(n, k);
        //@ open node(n, ?next, ?value);
        n = (*n).next;
        //@ close node(n, next, value);
        //@ close nodes(n, k - 1);
        i += 1;
    }
    //@ close stack(stack, count);
    i
}
    fn main() {
        println!("stack_tuerk.rs compiles successfully!");
}