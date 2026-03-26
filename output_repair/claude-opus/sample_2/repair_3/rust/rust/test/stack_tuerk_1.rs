struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Node_next(n: *mut Node; next: *mut Node) = (*n).next |-> next;

pred node_list(n: *mut Node, len: i32) =
    if len == 0 {
        n == 0
    } else {
        n != 0 &*& Node_next(n, ?next) &*& node_list(next, len - 1)
    };

pred Stack_head(s: *mut Stack; head: *mut Node) = (*s).head |-> head;

pred stack(s: *mut Stack, len: i32) =
    s != 0 &*& Stack_head(s, ?head) &*& node_list(head, len);

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack(stack, ?len) &*& len >= 0;
//@ ens stack(stack, len) &*& result == len;
{
    //@ open stack(stack, len);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close stack(stack, len);
    //@ open stack(stack, len);
    //@ assert Stack_head(stack, ?head);
    //@ assert node_list(head, len);
    //@ close Stack_head(stack, head);
    loop
    //@ inv Stack_head(stack, head) &*& node_list(n, len - i) &*& i >= 0 &*& i <= len;
    {
        //@ open node_list(n, len - i);
        if n.is_null() {
            //@ close node_list(n, len - i);
            break;
        }
        let next = (*n).next;
        //@ close Node_next(n, next);
        n = next;
        i += 1;
    }
    //@ close stack(stack, len);

    i
}