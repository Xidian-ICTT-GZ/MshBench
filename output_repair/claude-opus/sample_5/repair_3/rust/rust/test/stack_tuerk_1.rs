struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node_list(n: *mut Node; count: i32) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        (*n).next |-> ?next &*& node_list(next, ?rest_count) &*& count == rest_count + 1 &*& count >= 1
    };

pred stack(s: *mut Stack) =
    (*s).head |-> ?head &*& node_list(head, ?count) &*& count >= 0;
@*/

/*@
lemma void node_list_nonneg(n: *mut Node, count: i32)
    requires node_list(n, count);
    ensures node_list(n, count) &*& count >= 0;
{
    open node_list(n, count);
    if (n == 0 as *mut Node) {
    } else {
        node_list_nonneg((*n).next, _);
    }
    close node_list(n, count);
}
@*/

/*@
lemma void node_list_open_close(n: *mut Node, count: i32)
    requires node_list(n, count);
    ensures node_list(n, count);
{
    open node_list(n, count);
    if (n != 0 as *mut Node) {
        node_list_open_close((*n).next, _);
    }
    close node_list(n, count);
}
@*/

#[requires(stack(stack))]
#[ensures(stack(stack) &*& result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    //@ open stack(stack);
    let mut n = (*stack).head;
    //@ assert node_list(n, ?total_count);
    //@ node_list_nonneg(n, total_count);
    let mut i = 0;
    loop {
        //@ invariant node_list(n, ?remaining) &*& i >= 0 &*& remaining >= 0 &*& (*stack).head |-> ?head &*& node_list(head, ?head_count) &*& head_count >= 0 &*& i == total_count - remaining
        //@ open node_list(n, remaining);
        if n.is_null() {
            //@ close node_list(n, remaining);
            break;
        }
        n = (*n).next;
        i += 1;
        //@ close node_list(n, _);
    }
    //@ close stack(stack);
    i
}